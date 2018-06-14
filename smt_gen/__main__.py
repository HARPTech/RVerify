if __name__ == "__main__":
    import sys
    import argparse

    available_approx = ['tan', 'atan', 'space',]

    parser = argparse.ArgumentParser(description='View generated approximations as graphs.')
    parser.add_argument('approx', nargs='?', help='Choose the approximation to display.')
    parser.add_argument('--generate', action='store_true', help='Output SMT formula to STDOUT.')
    args = parser.parse_args()

    approx = args.approx
    
    if approx not in available_approx:
        print("Approximation needs to be one of " + str(available_approx))
        exit()

    lst, lst2 = gen_from_approx(approx)

    if not args.generate:
        display(approx, lst, lst2)
    else:
        statement = output.make_statement(approx, lst, lst2, get_comparator(approx))
        print(statement)

    
