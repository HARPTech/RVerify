def make_statement(name, arr1, arr2, comparator):
    """Generates the SMT-output for a given list.
    """
    pusher = "+"
    puller = "-"
    if comparator == ">=":
        pusher = "-"
        puller = "+"
    
    statement = ""
    statement += "(define-fun-rec " + name + " ((x Real)) Real "
    #statement += "(ite (" + comparator + " x " + str(arr1[0]) + ") (" + name + " (" + pusher + " x pi)) "
    statement += "(ite (" + comparator + " x " + str(arr1[0]) + ") " + str(arr2[0]) + " " 

    for a1, a2 in zip(arr1, arr2):
        statement += " (ite (" + comparator + " x " + str(a1) + ") " + str(a2) + " "

    # Last ITE
    statement += " " + "(" + name + " (" + puller + " x pi))"
    #statement += " " + str(arr2[-1])
        
    for a1, a2 in zip(arr1, arr2):
        statement += ")"

    statement += "))"

    return statement
