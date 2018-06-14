from collections import defaultdict

class VariableStore():
    def __init__(self):
        self.store = defaultdict(int)

    def getRef(self, name):
        self.store[name] += 1
        return name

    def getVarList(self):
        variables = []
        for key, value in self.store.items():
            variables.append(key)
        return variables

    def getDeclarationsStr(self):
        s = ""
        for key, value in self.store.items():
            s += "(declare-fun " + key + " () Real)\n"
        s += "\n"
        return s

