import logging
import z3

import multiprocessing
multiprocessing.cpu_count()
from concurrent.futures import ThreadPoolExecutor as ThreadPoolExecutor

import threading

class Checker():
    def __init__(self, tree, visitorSMT, checkLen):
        self.tree = tree
        self.visitorSMT = visitorSMT
        self.checkLen = checkLen
        self.logger = logging.getLogger('Checker')
        self.found = False
        self.foundLock = threading.Lock()

    def checkSolver(self, stmt, endLine):
        """Check the given solver for correctness and return True if it is satisfyable."""
        # Context Creation
        ctx = z3.Context()

        #print("CHECKING STATEMENT: " + stmt)
        
        sat = False
        try:
            s = z3.Solver(ctx=ctx)
            expression = z3.parse_smt2_string(stmt, ctx=ctx)
            s.add(expression)
            check = s.check()
            sat = check.r > 0
        except z3.Z3Exception as e:
            self.logger.error("Invalid SMT produced in permutation!")

        return sat, endLine

    def debugStatement(self, statement, expectedSat):
        """Spawns as many threads as the current computer has CPUs and analyses the given statements line-per-line."""

        # Define a TaskQueue for coming check tasks.
        threadCount = multiprocessing.cpu_count()
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
            resultFutures.append(executor.submit(self.checkSolver, stmt[0], stmt[1]))

        # Wait for all results.
        executor.shutdown(wait=False)

        # Print results.
        for future in resultFutures:
            sat, line = future.result()
            if sat != expectedSat:
                return False, line
        return True

    def check(self):
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
            print("CODE SOUNDNESS PASSED")

        else:
            # Begin debugging. This happens by removing one line at a time.
            print("CODE NOT PASSED, DETAILED ANALYSIS")
            resultAsExpected, line = self.debugStatement(self.visitorSMT, False)
            if not resultAsExpected:
                print("ERROR: Line " + str(line))
