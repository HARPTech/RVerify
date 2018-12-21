import logging
from typing import List
import z3

import multiprocessing
multiprocessing.cpu_count()
from concurrent.futures import ThreadPoolExecutor as ThreadPoolExecutor

from RVerify.parser import predefined as predefined

import threading

class Checker():
    def __init__(self, tree, visitorSMT, checkLen, lineLookupTable):
        self.tree = tree
        self.visitorSMT = visitorSMT
        self.checkLen = checkLen
        self.logger = logging.getLogger('Checker')
        self.found = False
        self.foundLock = threading.Lock()
        self.lineLookupTable = lineLookupTable
        self.fullSMTLen = self.visitorSMT.count("\n")

    def getCommonFailureAssertions(self, ctx):
        return predefined.checks

    def checkSolver(self, stmt, endLine, expanderGenerator):
        """Check the given statement for correctness and return True if it is satisfyable."""
        # Context Creation
        ctx = z3.Context()
        model = None

        sat = False
        try:
            s = z3.Solver(ctx=ctx)

            if expanderGenerator is not None:
                stmt += expanderGenerator(ctx)

            expression = z3.parse_smt2_string(stmt, ctx=ctx)
            s.add(expression)
            check = s.check()
            sat = check.r > 0

            if sat:
                model = s.model()
        except z3.Z3Exception as e:
            self.logger.error("Invalid SMT!")

        return sat, endLine, model, ctx

    def debugStatement(self, statement, expectedSat, expanderGenerator=None):
        """Spawns as many threads as the current computer has CPUs and analyses the given statements line-per-line."""

        # Define a TaskQueue for coming check tasks.
        threadCount = multiprocessing.cpu_count()
        # threadCount = 1
        executor = ThreadPoolExecutor(max_workers=threadCount)

        # Generate statements.
        lines = statement.splitlines()
        statements = []
        statements.append([statement, self.checkLen])
        
        for i in range(1, self.checkLen):
            statements.append(["\n".join(lines[0:-i]), self.checkLen - i])

        resultFutures = []

        # Parse SMT2 Strings
        for stmt in statements:
            resultFutures.append(executor.submit(self.checkSolver, stmt[0], stmt[1], expanderGenerator))

        # Wait for all results.
        executor.shutdown(wait=False)

        # Print results.
        for future in resultFutures:
            sat, line, model, ctx = future.result()
            if sat != expectedSat:
                return False, line, model, ctx

        return True, 0, None, None

    def check(self, important_declarations: List[str] = [
                            "_forward_velocity_",
                            "_steer_direction_",
                            "_motor_fl_",
                            "_motor_fr_",
                            "_motor_rl_",
                            "_motor_rr_",
                            "_servo_fl_",
                            "_servo_fr_",
                            "_servo_rl_",
                            "_servo_rr_"
                            ]):
        # Checks the tree using the z3 SMT parser.
        s = z3.Solver()

        expression = None

        # Parse SMT2 Strings
        try:
            expression = z3.parse_smt2_string(self.visitorSMT)
            s.add(expression)
        except z3.Z3Exception as e:
            self.logger.error("Invalid SMT produced!")
            return False

        # Pre-Check if the program itself passes.
        check = s.check().r > 0

        if check:
            # Code passes, begin checking failure conditions.
            print("CODE SOUNDNESS PASSED, CHECK FAILURE STATES")
            s = z3.Solver()

            try:
                expression = z3.parse_smt2_string(self.visitorSMT + predefined.checks)
                s.add(expression)
            except z3.Z3Exception as e:
                self.logger.error("Invalid SMT produced!")
                return False

            # Pre-Check if there are any problems with the assertions.
            check = s.check().r > 0

            if check is False:
                print("SUCCESS! NO FAILURE STATES DETECTED!")
            else:
                print("FAILURE STATES DETECTED!")

                # Print only important variables.
                m = s.model()

                declarations = m.decls()

                printed_decls = []

                for decl in declarations:
                    if ((important_declarations is None or decl.name() in important_declarations)
                        and not "!" in decl.name() and not "tan" in decl.name()):
                        printed_decls.append(decl)

                # Sort by keys.
                printed_decls.sort(key=lambda x: x.name())

                for decl in printed_decls:
                    print("  " + decl.name() + " = " + str(m[decl]) + ",")

        else:
            # Begin debugging. This happens by removing one line at a time.
            print("CODE NOT PASSED, DETAILED ANALYSIS")
            resultAsExpected, line, model, ctx = self.debugStatement(self.visitorSMT, False)
            if not resultAsExpected:
                pyline = self.lineLookupTable.getLineInPy(line)
                print("ERROR: Line in Python: " + str(pyline))
                print(self.lineLookupTable.getSurroundingLines(pyline))
