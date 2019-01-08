from . import result as res
from RVerify.parser import predefined as predefined
from typing import Sequence, Dict, List, Tuple

import z3

import multiprocessing
multiprocessing.cpu_count()
from concurrent.futures import ThreadPoolExecutor as ThreadPoolExecutor

class ExpressionBuilder():
    def __init__(self):
        self.cases = predefined.checkCases

    def buildSMTFromSequence(self, l: Sequence[Dict[str, str]], notted: bool = True):
        smt = "(assert "
        if notted:
            smt += "(not "
        smt += "(and \n"
        smt += "(= 1 1)\n"
        for d in l:
            # Insert pre- and suffix for assert not as specified in the source material.
            if notted:
                smt += d['expression'] + "\n"
            else:
                smt += d['expression'] + " \n"
        smt += "))"
        if notted:
            smt += ")"
        return smt

    def buildSMT(self, iteration: int, notted: bool = True):
        """Generates a SMT expression for the specified iteration.

        Iteration 0 includes all checks, iteration 1 includes one check less, and so on.

        To get the name of the test that failed the suite, call getIterationTestFailed(iteration).
        """
        cases = self.cases
        if iteration != 0:
            cases = cases[0:-iteration]

        return self.buildSMTFromSequence(cases, notted)

    def getIterationTestFailed(self, iteration: int) -> List[Dict[str, str]]:
        if iteration == 0:
            return []

        return self.cases[-(iteration - 1)]

    def getIterationTestFailedMessage(self, iteration: int) -> str:
        fail = self.getIterationTestFailed(iteration)
        msg = "  Failed: " + fail['name'] + "\n"
        msg += "    With Statement: " + fail['expression'] + "\n"
        return msg

    def buildSMTIntAssertChain(self, values : List[Tuple[str, int]]) -> str:
        smt = ""
        for v in values:
            smt += "(declare-fun " + v[0] + " () Int)\n"
            if v[1] >= 0:
                smt += "(assert (= " + v[0] + " " + str(v[1]) + "))\n"
            else:
                smt += "(assert (= " + v[0] + " (- " + str(-v[1]) + ")))\n"
        return smt

    def checkSMT(self, smt: str, checkSolver, notted: bool = True):
        # Define a TaskQueue for coming check tasks.
        threadCount = multiprocessing.cpu_count()
        executor = ThreadPoolExecutor(max_workers=threadCount)

        # Generate statements.
        counter = 1
        resultFutures = []
        for d in self.cases:
            resultFutures.append(executor.submit(checkSolver, smt + self.buildSMT(counter, True), counter, None))
            counter += 1

        # Wait for all results.
        executor.shutdown(wait=False)

        # Print results.
        matches = []
        
        for future in resultFutures:
            sat, line, model, ctx, check = future.result()
            if sat != True:
                matches.append({'sat': False, 'check': check, 'msg': self.getIterationTestFailedMessage(line + 1)})
                # Early return, because no more matches would be found with different results normally.
                return matches

        return matches
