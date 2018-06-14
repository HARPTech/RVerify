import argparse

import logging
import parser
import RVerify.parser.visitor

from RVerify.parser.visitor import Visitor as Visitor
import RVerify.parser.predefined as predefined

import sys
import typed_ast.ast3

import RVerify.smt_gen as smt_gen

if __name__ == "__main__":
    argparser = argparse.ArgumentParser(
        description="Verify regulation kernels using a SMT checking backend adaptive complexity regulation.")

    argparser.add_argument('-f', help='Input file', required=False)
    argparser.add_argument('--precision', help='Precision of the trigonometric approximations.', required=False, default=1, type=float)
    argparser.add_argument('--stdin', action='store_true', help='Use stdin instead of file.', required=False)
    argparser.add_argument('--print-smt', action='store_true', help='Print full generated SMT code.', default=False)
    argparser.add_argument('--display-approximations', action='store_true', help='Display trigonometric approximations. Needs matplotlib.', default=False)

    argparser.add_argument('--smt-include-logic', action='store_true', help='Include default logic declaration.', default=True)
    argparser.add_argument('--smt-include-internals', action='store_true', help='Include predefined internals.', default=True)
    argparser.add_argument('--smt-include-checks', action='store_true', help='Include checks', default=True)
    argparser.add_argument('--smt-include-check-sat', action='store_true', help='Include (check-sat)', default=True)
    argparser.add_argument('--smt-include-get-model', action='store_true', help='Include (get-model)', default=False)

    args = argparser.parse_args()

    source = ""
    
    if args.stdin:
        # Read the source from standard input.
        source = sys.stdin.readlines()

    if args.f:
        # Read from file.
        filename = args.f 
        with open(filename) as inFile:
            source = inFile.read()

    if source == "":
        logging.error("Must provide source as input either through file or stdin!")
        exit(-1)

    precision = args.precision

    # Commence Parsing

    astTree = typed_ast.ast3.parse(source, mode='exec')

    visitor = Visitor()
    visitor.visit(astTree)

    if args.display_approximations:
        smt_gen.generate_and_display("tan", precision)
        smt_gen.generate_and_display("atan", precision)

    if args.print_smt:
        smt = str(visitor)

        approximations = smt_gen.generate("tan", precision)
        approximations += smt_gen.generate("atan", precision)

        smt = approximations + smt

        if args.smt_include_internals:
            smt = predefined.internals + smt

        if args.smt_include_logic:
            smt = predefined.logic + smt

        if args.smt_include_checks:
            smt += predefined.checks 

        if args.smt_include_check_sat:
            smt += predefined.check_sat 

        if args.smt_include_get_model:
            smt += predefined.get_model

        print(smt)
