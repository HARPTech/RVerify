from xml.sax.saxutils import escape

class Result:
    def __init__(self, passed:bool,msg:str="Success!"):
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

    def as_rtest_input(self):
        s = ""
        if self.passed:
            s += "<set key='+rverify_passed+' val='True' />\n"
        else:
            s += "<set key='+rverify_passed+' val='False' />\n"
        
        for key,val in self.decls.items():
            s += "<set key='" + key + "' val='" + val + "' />\n"

        # Replace important XML chars.
        s += "<status>" + escape(self.msg) + "</status>\n"

        return s

    def __bool__(self):
        return self.passed
