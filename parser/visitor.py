import typed_ast
from typed_ast.ast3 import NodeVisitor
import logging
import math
from pprint import pprint
from collections import defaultdict
import re

variable_rules = """
(set-logic AUFNIRA)
(declare-fun _forward_velocity_ () Int)
(declare-fun _steer_direction_ () Int)
(assert (>= _forward_velocity_ -32768))
(assert (<= _forward_velocity_ 32767))

(assert (or 
    (and (>= _steer_direction_ -32768) (<= _steer_direction_ -10))
    (and (>= _steer_direction_ 10) (<= _steer_direction_ 32767))))

(declare-fun _motor_fl_ () Int)
(declare-fun _motor_fr_ () Int)
(declare-fun _motor_rl_ () Int)
(declare-fun _motor_rr_ () Int)
(declare-fun _servo_fl_ () Int)
(declare-fun _servo_fr_ () Int)
(declare-fun _servo_rl_ () Int)
(declare-fun _servo_rr_ () Int)

(define-fun mapReal ((x Real) (min Real) (max Real) (outMin Real) (outMax Real)) Real 
    (* (/ (- x min) (- max min)) (+ (- outMax outMin) outMin))) 
 
(define-fun mapInt ((x Int) (min Int) (max Int) (outMin Int) (outMax Int)) Int 
    (* (div (- x min) (- max min)) (+ (- outMax outMin) outMin))) 

(declare-fun pi () Real)
(assert (= pi 3.14159265359))
"""

final_asserts = """
(assert (not (and

(>= _motor_fl_ -255)
(<= _motor_fl_ 255)
(>= _motor_fr_ -255)
(<= _motor_fr_ 255)
(>= _motor_rl_ -255)
(<= _motor_rl_ 255)
(>= _motor_rr_ -255)
(<= _motor_rr_ 255)

(=> (or (> _steer_direction_ 1) (< _steer_direction_ (- 1)))
    (and
     (>= _servo_fl_ 0)
     (<= _servo_fl_ 255)
     (>= _servo_fr_ 0)
     (<= _servo_fr_ 255)
     (>= _servo_rl_ 0)
     (<= _servo_rl_ 255)
     (>= _servo_rr_ 0)
     (<= _servo_rr_ 255)
     ))

;; Combined Properties
;; -------------------

;;(=> (and (>= _servo_fl_ 128) (<= _servo_fr_ 128)) (or (and (>= _motor_fl_ 0) (<= _motor_fr_ 0)) (and (<= _motor_fl_ 0) (>= _motor_fr_ 0))))
;;(=> (and (>= _servo_rl_ 128) (<= _servo_rr_ 128)) (or (and (>= _motor_rl_ 0) (<= _motor_rr_ 0)) (and (<= _motor_rl_ 0) (>= _motor_rr_ 0))))
;;(=> (and (>= _servo_fl_ 128) (>= _servo_fr_ 128)) (or (and (>= _motor_fl_ 0) (>= _motor_fr_ 0)) (and (<= _motor_fl_ 0) (<= _motor_fr_ 0))))
;;(=> (and (>= _servo_rl_ 128) (>= _servo_rr_ 128)) (or (and (>= _motor_rl_ 0) (>= _motor_rr_ 0)) (and (<= _motor_rl_ 0) (<= _motor_rr_ 0))))

)))

(check-sat)
(get-model)
"""

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

class Node():
    list_typenames = ["While", "For"]
    
    def __init__(self, typename = "Node", strrep = ""):
        self.logger = logging.getLogger('Node:' + typename)
        self.logger.setLevel(logging.DEBUG)

        self.children = []
        self.typename = typename
        self.strrep = strrep
        self.left_delimiter = "("
        self.right_delimiter = ")"
        self.node_delimiter = ""

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

    def __str__(self, level=-100000, var_store=None):
        if len(self.children) <= 1 and self.typename != "FunctionCall":
            self.left_delimiter = " "
            self.right_delimiter = " "

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
                        self.strrep += " (to_int " + node.__str__(level=level+1,var_store=var_store) + ")))"
            else:
                for node in self.children:
                    self.strrep = node.__str__(level=level+1,var_store=var_store)
            
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
                s += self.children[0].__str__(level=level+1, var_store=var_store) + " "
                s += node.__str__(level=level + 1, var_store=var_store)
                s += self.right_delimiter + ")\n"
            # There is an else branch that can be handled.
            orelse = self.children[2]
            for node in orelse.children:
                s += self.left_delimiter
                s += "assert (" + self.strrep + " (not " + self.children[0].__str__(level=level+1, var_store=var_store) + ") "
                s += node.__str__(level=level + 1, var_store=var_store)
                s += self.right_delimiter + ")\n"
        else:
            if level == 0:
                self.strrep = "assert (" + self.strrep
                self.left_delimiter = "("
                self.right_delimiter = "))"

            s = self.left_delimiter

            s += self.strrep
            for child in self.children:
                s += child.__str__(level=level + 1, var_store=var_store) + self.node_delimiter
            s += self.right_delimiter

        return s

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

class Visitor(NodeVisitor):
    def __init__(self):
        self.logger = logging.getLogger('Visitor')
        self.logger.setLevel(logging.DEBUG)
        self.logger.info("Created Visitor instance.")
        self.active = []
        self.tree = StatementTree()
        self.list_expected = 0
        self.wrap_to_real = 0

    def currentNode(self):
        if len(self.active) > 0:
            return self.active[len(self.active) - 1]
        return None

    def addToCurrentNode(self, node):
        current = self.currentNode()
        if current is None:
            self.tree.add(node)
        else:
            current.add(node)

    # Good resources for nodes are also here:
    # https://greentreesnakes.readthedocs.io/en/latest/nodes.html
    #
    # This visitor has to work recursively!
    # Nice resource: https://stackoverflow.com/a/14661325
    def recursive(func):
        def wrapper(self, node):
            # Calls the decorated function first and iterates
            # through all child nodes afterwards.

            old_size = len(self.active)
            
            func(self,node)
            for child in typed_ast.ast3.iter_child_nodes(node):
                wrapping = self.wrap_to_real > 0 and self.wrap_to_real <= 1 and type(child) is not typed_ast.ast3.Load
                if wrapping:
                    wrapper = Node("FunctionCall", "to_real")
                    self.addToCurrentNode(wrapper)
                    self.active.append(wrapper)
                    self.wrap_to_real += 1
                self.visit(child)
                if wrapping:
                    self.active.pop()
                    self.wrap_to_real -= 1

            # After each recursive call, the active list has to be popped.
            # Recursive elements MUST have a node! If they do not, nothing will be removed.
            if len(self.active) > 0 and old_size < len(self.active):
                self.active.pop()
                self.logger.debug("Popped current node.")
        return wrapper
    
    @recursive
    def visit_Module(self, module):
        self.logger.debug("Visiting Module.")

    @recursive
    def visit_FunctionDef(self, func):
        self.logger.debug("Visiting Function Name: " + func.name)

    def visit_arguments(self, arg):
        self.logger.debug("Visiting Function Arguments.")

    def visit_Import(self, node):
        pass

    @recursive
    def visit_Assign(self, node):
        self.logger.debug("Visiting Assignment! Recursive solution.")
        assignment = Node("Assignment", "=")
        self.addToCurrentNode(assignment)
        self.active.append(assignment)


    def visit_Name(self, node):
        self.logger.debug("Visiting Name of a variable! Name=" + node.id)

        n = Node("Name", node.id)
        self.addToCurrentNode(n)

        # Not added to active nodes, because a name is just that, a name. It has no more child nodes.

    def visit_NameConstant(self, node):
        self.logger.debug("Visiting Name Constant of a variable! Name=" + str(node))

    def visit_Num(self, node):
        self.logger.debug("Visiting Num! Value=" + str(node.n))

        num = Node("Num", str(node.n))
        self.addToCurrentNode(num)

    def visit_Attribute(self, node):
        attr = str(node.value.id) + "." + str(node.attr)
        self.logger.debug("Visiting Attribute! Name:" + attr)

        visited = False
        
        if attr == "math.pi":
            self.logger.debug("Pi detected, inserting as value.")
            num = Node("Num", str(math.pi))
            self.addToCurrentNode(num)
            visited = True

        # Attributes with rules
        
        if attr == "RR.Int16_MVMT_FORWARD_VELOCITY":
            rule = Node("NAMEREF", "(to_real _forward_velocity_)")
            self.addToCurrentNode(rule)
            visited = True
        if attr == "RR.Int16_MVMT_STEER_DIRECTION":
            rule = Node("NAMEREF", "_steer_direction_")
            self.addToCurrentNode(rule)
            visited = True
        if attr == "RR.Int16_MVMT_MOTOR_PWM_FL":
            rule = Node("NAMEREF", "_motor_fl_")
            self.addToCurrentNode(rule)
            visited = True
        if attr == "RR.Int16_MVMT_MOTOR_PWM_FR":
            rule = Node("NAMEREF", "_motor_fr_")
            self.addToCurrentNode(rule)
            visited = True
        if attr == "RR.Int16_MVMT_MOTOR_PWM_RL":
            rule = Node("NAMEREF", "_motor_rl_")
            self.addToCurrentNode(rule)
            visited = True
        if attr == "RR.Int16_MVMT_MOTOR_PWM_RR":
            rule = Node("NAMEREF", "_motor_rr_")
            self.addToCurrentNode(rule)
            visited = True

        if attr == "RR.Uint8_MVMT_SERVO_FL_POSITION":
            rule = Node("NAMEREF", "_servo_fl_")
            self.addToCurrentNode(rule)
            visited = True
        if attr == "RR.Uint8_MVMT_SERVO_FR_POSITION":
            rule = Node("NAMEREF", "_servo_fr_")
            self.addToCurrentNode(rule)
            visited = True
        if attr == "RR.Uint8_MVMT_SERVO_RL_POSITION":
            rule = Node("NAMEREF", "_servo_rl_")
            self.addToCurrentNode(rule)
            visited = True
        if attr == "RR.Uint8_MVMT_SERVO_RR_POSITION":
            rule = Node("NAMEREF", "_servo_rr_")
            self.addToCurrentNode(rule)
            visited = True

        if not visited:
            self.logger.error("Could not resolve attribute: " + attr)
            

    @recursive
    def visit_BinOp(self, node):
        self.logger.debug("Visiting BinOp! This operation is between a " + type(node.left).__name__ + " and a " + type(node.right).__name__ + ", which could also be variables.")
        binop = Node("BinOp")
        self.addToCurrentNode(binop)
        self.active.append(binop)

    @recursive
    def visit_UnaryOp(self, node):
        self.logger.debug("Visiting UnaryOp!")
        unop = Node("UnOp")
        self.addToCurrentNode(unop)
        self.active.append(unop)

    def visit_Add(self, node):
        self.logger.debug("Visiting Add!")
        op = Node("OP", "+")
        self.addToCurrentNode(op)

    def visit_Sub(self, node):
        self.logger.debug("Visiting Sub!")
        op = Node("OP", "- ")
        self.addToCurrentNode(op)

    def visit_USub(self, node):
        self.logger.debug("Visiting USub!")
        op = Node("OP", "- ")
        self.addToCurrentNode(op)

    def visit_Mult(self, node):
        self.logger.debug("Visiting Mult!")
        op = Node("OP", "* ")
        self.addToCurrentNode(op)

    def visit_Div(self, node):
        self.logger.debug("Visiting Div!")
        op = Node("OP", "/ ")
        self.addToCurrentNode(op)

    def visit_AugAssign(self, node):
        self.logger.debug("Visiting AugAssign!")

    def visit_Lt(self, node):
        self.logger.debug("Visiting Less Than!")
        cmp = Node("CMP", "<")
        self.addToCurrentNode(cmp)

    def visit_Lt(self, node):
        self.logger.debug("Visiting Less Than!")
        cmp = Node("CMP", "<")
        self.addToCurrentNode(cmp)

    def visit_LtE(self, node):
        self.logger.debug("Visiting Less Than Equal!")
        cmp = Node("CMP", "<=")
        self.addToCurrentNode(cmp)

    def visit_Gt(self, node):
        self.logger.debug("Visiting Greater Than!")
        cmp = Node("CMP", ">")
        self.addToCurrentNode(cmp)

    def visit_GtE(self, node):
        self.logger.debug("Visiting Greater Than Equal!")
        cmp = Node("CMP", ">=")
        self.addToCurrentNode(cmp)

    def visit_Tuple(self, node):
        logstr = "Visiting Tuple! Containing: "
        for e in node.elts:
            logstr += "\n   > " + type(e).__name__
            if type(e) is ast.Name:
                logstr += " (" + e.id + ")"
        self.logger.debug(logstr)

    @recursive
    def visit_List(self, node):
        self.logger.info("Visiting List!")
        if self.list_expected > 0:
            # Lists are visited recursively.
            pass
        else:
            self.logger.error("Cannot parse unexpected lists!")

    @recursive
    def visit_Expr(self, node):
        self.logger.debug("Visiting Expr! Recursive solution.")

    @recursive
    def visit_ClassDef(self, node):
        self.logger.debug("Visiting Class Definition! Recursive solution.")

    def visit_If(self, node):
        self.logger.debug("Visiting If! Manual Recursive solution.")
        iff = Node("If", "=> ")
        self.addToCurrentNode(iff)
        self.active.append(iff)

        # Visit condition
        self.visit(node.test)

        # Add Body
        body = Node("IfBody")
        self.addToCurrentNode(body)
        self.active.append(body)
        for n in node.body:
            self.visit(n)

        # Add else branch
        self.active.pop()
        orelse = Node("IfElse")
        self.addToCurrentNode(orelse)
        self.active.append(orelse)
        for n in node.orelse:
            self.visit(n)

        self.active.pop()
        self.active.pop()

    @recursive
    def visit_Compare(self, node):
        self.logger.debug("Visiting Compare! Recursive solution.")
        compare = Node("Compare")
        self.addToCurrentNode(compare)
        self.active.append(compare)

    def visit_Call(self, node):
        strrep = ""
        obj = ""
        func = ""
        name = "FunctionCall"
        wrapping_call = False
        list_expected_call = False
        
        if hasattr(node, 'func') and hasattr(node.func, 'value') and hasattr(node.func.value, 'id'):
            obj = node.func.value.id
            func = node.func.attr
            if obj == "math":
                if func == "tan":
                    strrep = "tan"
                if func == "atan":
                    strrep = "atan"
            if obj == "registry":
                name = "ReservedFunctionCall"
                if func == "setInt16":
                    strrep = "setInt16"
                if func == "setUint8":
                    strrep = "setUint8"
                if func == "getInt16":
                    strrep = "getInt16"
                if func == "getInt8":
                    strrep = "getInt16"
            if obj == "rsupport":
                if func == "service":
                    # This is the service call, this can be ignored.
                    strrep = "---"

        if type(node.func) is typed_ast.ast3.Name:
            func = node.func.id
            if func == "int":
                strrep = " "
            if func == "interp":
                strrep = "mapReal"
                self.list_expected += 1
                self.wrap_to_real = 1
                wrapping_call = True
                list_expected_call = True

        if strrep != "" and strrep != "---":
            call = Node(name, strrep)
            self.addToCurrentNode(call)
            self.active.append(call)

            # Visit arguments if there are any.
            for arg in node.args:
                self.visit(arg)
            self.active.pop()
            if list_expected_call:
                self.list_expected -= 1
            if wrapping_call:
                self.wrap_to_real = 0

            return 
        if strrep != "---":
            self.logger.error("Function Call unsupported (" + obj + "." + func + ")! Line: " + str(node.lineno))

    @recursive
    def visit_For(self, node):
        f = Node("For")
        self.addToCurrentNode(f)
        self.active.append(f)

    @recursive
    def visit_While(self, node):
        w = Node("While")
        self.addToCurrentNode(w)
        self.active.append(w)

    def visit_Return(self, node):
        self.logger.debug("Returning from current function.")
        pass
    
    def generic_visit(self, node):
        self.logger.warn("No visit() implemented for node! Node: " + str(node))

    def __str__(self):
        return str(self.tree)
