import argparse

import logging
import parser
import RVerify.parser.Visitor

from RVerify.parser.Visitor import Visitor as Visitor

import sys
import typed_ast.ast3

if __name__ == "__main__":
    argparser = argparse.ArgumentParser(
        description="Verify regulation kernels using a SMT checking backend adaptive complexity regulation.")

    argparser.add_argument('-f', help='Input file', required=False)
    argparser.add_argument('--stdin', action='store_true', help='Use stdin instead of file.', required=False)

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

    # Commence Parsing

    astTree = typed_ast.ast3.parse(source, mode='exec')

    visitor = Visitor()
    visitor.visit(astTree)

