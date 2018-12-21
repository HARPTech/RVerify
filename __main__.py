"""Checker for VERNER rover regulation kernels.

This module provides a SMT based checking utility to be used during
development of regulation kernel software for the VERNER rover platform.
"""
import sys
import argparse

import logging

import RVerify.smt_gen as smt_gen

from RVerify.file_checker import FileChecker

if __name__ == "__main__":
    argparser = argparse.ArgumentParser(
        description="Verify regulation kernels using a SMT checking backend adaptive complexity regulation.")

    argparser.add_argument('-f', help='Input file', required=False)
    argparser.add_argument('--precision', help='Precision of the trigonometric approximations.', required=False, default=1, type=float)
    argparser.add_argument('--stdin', action='store_true', help='Use stdin instead of file.', required=False)
    argparser.add_argument('--check', action='store_true', help='Check the given source code using the z3 SMT parser against the embedded rule-set.', default=False)
    argparser.add_argument('--print-smt', action='store_true', help='Print full generated SMT code.', default=False)
    argparser.add_argument('--dump-ast', action='store_true', help='Dump the AST of the parsed Python code.', default=False)
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
        source = sys.stdin.read()

    if args.f:
        # Read from file.
        filename = args.f 
        with open(filename) as inFile:
            source = inFile.read()

    if source == "":
        logging.error("Must provide source as input either through file or stdin!")
        exit(-1)

    # Filter source for keyword RVERIFY_BEGIN

    phraseFound = False
    filteredSource = ""
    for line in source.splitlines():
        if phraseFound:
            filteredSource += line + "\n"
        if "RVERIFY_BEGIN" in line:
            phraseFound = True

    if phraseFound:
        source = filteredSource

    precision = args.precision

    # Generate approximations.
    approximations = smt_gen.generate("tan", precision)
    approximations += smt_gen.generate("atan", precision)

    if args.display_approximations:
        smt_gen.generate_and_display("tan", precision)
        smt_gen.generate_and_display("atan", precision)

    # Commence Parsing
    file_checker = FileChecker(approximations, source)

    file_checker.parse()

    if args.dump_ast:
        file_checker.dump_ast()

    if args.check:
        file_checker.check()

    if args.print_smt:
        file_checker.dump_smt({
            'internals': args.smt_include_internals,
            'logic': args.smt_include_logic,
            'checks': args.smt_include_checks,
            'check_sat': args.smt_include_check_sat,
            'get_model': args.smt_include_get_model,
        })
