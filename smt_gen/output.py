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

    val1 = arr1[0]
    val2 = arr2[0]
    if arr1[0] < 0:
        val1 = "(- " + str(- arr1[0]) + ")"
    else:
        val1 = str(arr1[0])
    if arr2[0] < 0:
        val2 = "(- " + str(- arr2[0]) + ")"
    else:
        val2 = str(arr2[0])
    
    statement += "(ite (" + comparator + " x " + val1 + ") " + val2 + " " 

    for a1, a2 in zip(arr1, arr2):
        val1 = a1
        val2 = a2
        if a1 < 0:
            val1 = "(- " + str(- a1) + ")"
        else:
            val1 = str(a1)
        if a2 < 0:
            val2 = "(- " + str(- a2) + ")"
        else:
            val2 = str(a2)
        
        statement += " (ite (" + comparator + " x " + val1 + ") " + val2 + " "

    # Last ITE
    statement += " " + "(" + name + " (" + puller + " x pi))"
    #statement += " " + str(arr2[-1])
        
    for a1, a2 in zip(arr1, arr2):
        statement += ")"

    statement += "))"

    return statement
