import os

import unittest
import yaml

import typed_ast.ast3
import RVerify.parser.visitor

from RVerify.parser.visitor import Visitor as Visitor

dirpath = os.path.dirname(os.path.realpath(__file__))

class ParserTest(unittest.TestCase):

    def setUp(self):
        self.tests = []
        
        # Load test strings.
        with open(dirpath + "/tests.yml") as test_statements:
            doc = yaml.load(test_statements)
            for test in doc["tests"]:
                self.tests.append({
                    'source' : test["source"],
                    'smt': test["smt"],
                    'name': test["test"],
                    'expected_variables': test["expected_variables"]
                })
    
    def test_predefined_outputs(self):
        for test in self.tests:
            astTree = typed_ast.ast3.parse(test["source"], mode='exec')
            visitor = Visitor()
            visitor.visit(astTree)

            smtOut, store = visitor.tree.getSMT()

            # Test SMT Output
            self.assertEqual(test["smt"], smtOut, "Test Name: " + test["name"])

            # Test variables
            self.assertEqual(test["expected_variables"], store.getVarList())
        pass
