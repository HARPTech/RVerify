"""Checker for VERNER rover regulation kernels.

This module provides a SMT based checking utility to be used during
development of regulation kernel software for the VERNER rover platform.
"""
import os
import argparse

import logging

import RVerify.smt_gen as smt_gen
from RVerify.watcher import Watcher

if __name__ == "__main__":
    argparser = argparse.ArgumentParser(
        description="Verify regulation kernels using a SMT and adaptive complexity regulation.")

    argparser.add_argument('-f', help='Input file', required=False)
    argparser.add_argument('--precision',
                           help='Precision of the trigonometric approximations.',
                           required=False, default=1, type=float)
    argparser.add_argument('--stdin', action='store_true',
                           help='Use stdin instead of file.', required=False)
    argparser.add_argument('--check',
                           action='store_true', default=False,
                           help='Check the given source using z3 against the embedded rule-set.')
    argparser.add_argument('--watch',
                           action='store_true', default=False,
                           help='Watch the given file for changes and re-check on change.')
    argparser.add_argument('--verbose', '-v', action='store_const', dest='loglevel',
                           const=logging.INFO, help='Activate verbose logging.')
    argparser.add_argument('--debug', '-d', action='store_const', dest='loglevel',
                           const=logging.DEBUG, help='Activate development (debugging) logging.')
    argparser.add_argument('--print-smt', action='store_true', default=False,
                           help='Print full generated SMT code.')
    argparser.add_argument('--dump-ast', action='store_true', default=False,
                           help='Dump the AST of the parsed Python code.')
    argparser.add_argument('--display-approximations', action='store_true', default=False,
                           help='Display trigonometric approximations. Needs matplotlib.')
    argparser.add_argument('--print-complete-model', action='store_true', default=False,
                           help="Displays values for all variables in case a model was found.")

    argparser.add_argument('--smt-include-logic', action='store_true',
                           help='Include default logic declaration.', default=True)
    argparser.add_argument('--smt-include-internals', action='store_true',
                           help='Include predefined internals.', default=True)
    argparser.add_argument('--smt-include-checks', action='store_true',
                           help='Include checks', default=True)
    argparser.add_argument('--smt-include-check-sat', action='store_true',
                           help='Include (check-sat)', default=True)
    argparser.add_argument('--smt-include-get-model', action='store_true',
                           help='Include (get-model)', default=False)

    args = argparser.parse_args()

    logging.basicConfig(level=args.loglevel)
    
    if not args.stdin and not args.f:
        logging.error("Must provide source as input either through file or stdin!")
        exit(-1)

    if args.stdin and args.watch:
        logging.error("Cannot watch for changes on stdin!")
        
    path = None
    if args.f:
        path = args.f

        if not os.path.exists(path):
            logging.error("File does not exist!")
            exit(-2)

        if not os.path.isfile(path):
            logging.error("Must provide a file, not a directory!")
            exit(-2)

    precision = args.precision

    # Generate approximations.
    approximations = smt_gen.generate("tan", precision)
    approximations += smt_gen.generate("atan", precision)

    if args.display_approximations:
        smt_gen.generate_and_display("tan", precision)
        smt_gen.generate_and_display("atan", precision)

    watcher = Watcher(approximations, path,
        args.dump_ast,
        args.print_smt,
        args.check,
        args.print_complete_model,
        {
            'internals': args.smt_include_internals,
            'logic': args.smt_include_logic,
            'checks': args.smt_include_checks,
            'check_sat': args.smt_include_check_sat,
            'get_model': args.smt_include_get_model,
        })

    if args.watch:
        watcher.watch()
    else:
        watcher.run_checker()
