import logging

class Node():
    list_typenames = ["While", "For"]
    
    def __init__(self, typename = "Node", strrep = "", pyline=0):
        self.logger = logging.getLogger('Node:' + typename)
        self.logger.setLevel(logging.DEBUG)

        self.children = []
        self.typename = typename
        self.strrep = strrep
        self.left_delimiter = "("
        self.right_delimiter = ")"
        self.node_delimiter = ""
        self.pyline = pyline

        # Loops in this use-case are not represented as nodes.
        if typename in self.list_typenames:
            self.left_delimiter = ""
            self.right_delimiter = ""
            self.node_delimiter = "\n"

        if strrep == " ":
            self.left_delimiter = ""
            self.right_delimiter = ""

    def visit(self, var):
        pass

    def add(self, node):
        self.children.append(node)

    def __str__(self, level=-100000, line = 0, var_store=None, lineLookupTable = None):
        if len(self.children) <= 1 and self.typename != "FunctionCall":
            self.left_delimiter = " "
            self.right_delimiter = " "

        if lineLookupTable is not None:
            lineLookupTable.insertLine(self.pyline, line + 1)

        if self.typename in self.list_typenames:
            level -= 1

        # Operations
        if self.typename == "BinOp" or self.typename == "UnOp":
            # The operation must be extracted from the child nodes.
            ops = list(filter(lambda c: c.typename == "OP", self.children))
            if len(ops) == 0:
                # There was an error finding an operation in this Op!
                self.logger.warning("No OP found!")
            else:
                op = ops[0]
                self.strrep = op.strrep
                self.children.remove(op)

        # Comparisons
        if self.typename == "Compare":
            # The comparison must be extracted from the child nodes.
            cmps = list(filter(lambda c: c.typename == "CMP", self.children))
            if len(cmps) > 0:
                cmp = cmps[0]
                self.strrep = cmp.strrep
                self.children.remove(cmp)

        if self.typename == "ReservedFunctionCall":
            # Search for NAMEREF nodes in child nodes to find reference for correct variable, if this is level 0
            if level == 0:
                for node in self.children:
                    if node.typename == "NAMEREF":
                        self.strrep = "(assert (= " + node.strrep
                    else:
                        self.strrep += " (to_int " + node.__str__(level=level+1,line=line+1,var_store=var_store,lineLookupTable=lineLookupTable) + ")))"
            else:
                for node in self.children:
                    self.strrep = node.__str__(level=level+1,var_store=var_store,line=line+1,lineLookupTable=lineLookupTable)
            
            return self.strrep 

        # Name
        if self.typename == "Name":
            # Get the target name, if there is a store defined.
            if var_store is not None:
                self.strrep = var_store.getRef(self.strrep)

        # Ifs
        # Ifs always have two children: The condition, the body and the else branch. The condition always implies
        # the body and NOT the condition implies the else branch, so there must be an assert for every entry. This handling is special.
        if self.typename == "If":
            s = ""
            # There is a body that can be handled.
            body = self.children[1]
            for node in body.children:
                s += self.left_delimiter
                s += "assert (" + self.strrep
                s += self.children[0].__str__(level=level+1, var_store=var_store,line=line+1,lineLookupTable=lineLookupTable) + " "
                s += node.__str__(level=level + 1, var_store=var_store,line=line+1,lineLookupTable=lineLookupTable)
                s += self.right_delimiter + ")\n"
            # There is an else branch that can be handled.
            orelse = self.children[2]
            for node in orelse.children:
                s += self.left_delimiter
                s += "assert (" + self.strrep + " (not " + self.children[0].__str__(level=level+1, var_store=var_store,line=line+1,lineLookupTable=lineLookupTable) + ") "
                s += node.__str__(level=level + 1, var_store=var_store,line=line+1,lineLookupTable=lineLookupTable)
                s += self.right_delimiter + ")\n"
        else:
            if level == 0:
                self.strrep = "assert (" + self.strrep
                self.left_delimiter = "("
                self.right_delimiter = "))"

            s = self.left_delimiter

            s += self.strrep
            for child in self.children:
                s += child.__str__(level=level + 1, var_store=var_store,line=line,lineLookupTable=lineLookupTable) + self.node_delimiter

                if lineLookupTable is not None and self.node_delimiter == "\n":
                    lineLookupTable.insertLine(child.pyline, line)
                    line += 1

            s += self.right_delimiter

        return s
