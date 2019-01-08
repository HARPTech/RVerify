import sys
import logging

from typing import Dict

import parser
import RVerify.parser.visitor
import astpretty
from RVerify.parser.visitor import Visitor as Visitor
from RVerify.parser.line_lookup_table import LineLookupTable as LineLookupTable
import typed_ast.ast3
from RVerify.checker.checker import Checker
from RVerify.checker.result import Result
import RVerify.parser.predefined as predefined
import RVerify.checker.expression_builder as ex

# Monkey-Patch the used ast package to typed_ast.
astpretty.ast = typed_ast.ast3

class FileChecker():
    def __init__(self, approximations: str, source: str):
        self.ast_tree = None
        self.line_lookup_table = None
        self.visitor = None
        self.source = source
        self.approximations = approximations
        self.visitor_smt = ""
        self.lines = 0
        self.logger = logging.getLogger("FileChecker")

    def parse(self):
        """Parses the embedded source into an AST and transform the AST into SMT formulas.

        To update the internal source, update the source field with new contents.
        """
        try:
            self.ast_tree = typed_ast.ast3.parse(self.source, mode='exec')

            self.line_lookup_table = LineLookupTable(self.source)

            self.visitor = Visitor(self.line_lookup_table)
            self.visitor.visit(self.ast_tree)

            self.visitor_smt, self.lines = self.visitor.getFullSMT()
        except Exception as e:
            self.logger.error("Could not parse source file! Error during parsing. Error:")
            self.logger.error(e)

    def check(self, print_complete_model:bool=False) -> Result:
        """Check the embedded source using the generated SMT formulas.
        """
        checker = Checker(self.visitor,
                          predefined.logic + predefined.internals
                          + self.approximations + self.visitor_smt,
                          self.lines,
                          self.line_lookup_table)

        if print_complete_model:
            return checker.check(important_declarations=None)
        else:
            return checker.check()

    def dump_ast(self):
        """Prints the AST read from the file.
        """
        print("AST DUMP (Excluding Line-Numbers):")
        astpretty.pprint(self.ast_tree, indent='  ', show_offsets=False)

    def dump_smt(self, included: Dict[str, bool]):
        """Prints the generated SMT formulas for the file.
        """
        smt = self.approximations + self.visitor_smt
        if included["internals"]:
            smt = predefined.internals + smt

        if included["logic"]:
            smt = predefined.logic + smt

        if included["checks"]:
            builder = ex.ExpressionBuilder()
            smt += builder.buildSMT(0)

        if included["check_sat"]:
            smt += predefined.check_sat

        if included["get_model"]:
            smt += predefined.get_model

        print(smt)
