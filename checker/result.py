class Result:
    def __init__(self, passed:bool,msg:str=""):
        self.decls = {}
        self.passed = passed
        self.msg = msg

    def add_decl(self, name, str_rep):
        self.decls[name] = str_rep

    def __str__(self):
        s = ""
        for key,val in self.decls.items():
            s += key + " = " + val + ",\n"
        return s

    def __bool__(self):
        return self.passed
