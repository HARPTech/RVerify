import logging
import z3

class Checker():
    def __init__(self, tree, treeSMT):
        self.tree = tree
        self.treeSMT = treeSMT

    def check(self):
        # Checks the tree using the z3 SMT parser.
        s = z3.Solver()
