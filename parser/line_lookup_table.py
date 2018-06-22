class LineLookupTable():
    def __init__(self, pythonCode):
        self.pythonCode = pythonCode
        self.pythonLines = pythonCode.count("\n")
        self.pythonLinesList = pythonCode.splitlines()
        self.smtLookups = {}
        self.counter = 1
        
    def insertLine(self, lineInPy, lineInSMT):
        self.smtLookups[lineInSMT] = lineInPy;

    def getLineInPy(self, smtLine):
        if not smtLine in self.smtLookups:
            return -1
        return self.smtLookups[smtLine]

    def count(self):
        self.counter += 1

    def getSurroundingLines(self, pyLine):
        startLine = max(0, pyLine - 2)
        endLine = min(self.pythonLines, pyLine + 2)

        output = "\n".join(self.pythonLinesList[startLine:endLine])
        return output
        
