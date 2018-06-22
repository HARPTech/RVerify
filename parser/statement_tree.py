import re
from .var_store import VariableStore as VariableStore

class StatementTree():
    def __init__(self, lineLookupTable = None):
        self.nodes = []
        self.lineLookupTable = lineLookupTable

    def add(self, node):
        self.nodes.append(node)

    def getSMT(self):
        s = ""
        store = VariableStore()
        i = 0

        for node in self.nodes:
            # String trimming taken from https://stackoverflow.com/a/1546244
            s += re.sub(' +', ' ', node.__str__(level=0, var_store=store,lineLookupTable=self.lineLookupTable,line=i)).strip() + "\n"
            if self.lineLookupTable is not None:
                self.lineLookupTable.insertLine(node.pyline, i)
                i += 1

        return s, store

    def getFullSMT(self):
        s, store = self.getSMT()

        lines = s.count("\n")
        s = store.getDeclarationsStr() + s

        return s, lines

    def __str__(self):
        s, lines = self.getFullSMT()

        return s
