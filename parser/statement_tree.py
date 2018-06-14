import re
from .var_store import VariableStore as VariableStore

class StatementTree():
    def __init__(self):
        self.nodes = []

    def add(self, node):
        self.nodes.append(node)

    def getSMT(self):
        s = ""
        store = VariableStore()
        for node in self.nodes:
            # String trimming taken from https://stackoverflow.com/a/1546244
            s += re.sub(' +', ' ', node.__str__(level=0, var_store=store)).strip() + "\n"
        return s, store

    def __str__(self):
        s, store = self.getSMT()

        s = store.getDeclarationsStr() + s

        return s