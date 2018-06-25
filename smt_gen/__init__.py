from functools import lru_cache

@lru_cache(maxsize=32)
def gen_from_approx(approx, num=2000):
    from . import trigonometric
    from . import output
    return {
        'space': lambda: trigonometric.gen_space(num),
        'tan': lambda: trigonometric.gen_tan_range(num),
        'atan': lambda: trigonometric.gen_atan_range(num),
    }[approx]()

@lru_cache(maxsize=32)
def get_comparator(approx):
    return {
        'tan': "<=",
        'atan': ">="
    }[approx]

@lru_cache(maxsize=32)
def generate(approx, scale):
    from . import trigonometric
    from . import output

    lst, lst2 = gen_from_approx(approx, scale)
    statement = output.make_statement(approx, lst, lst2, get_comparator(approx)) + "\n"
    return statement

def generate_and_display(approx, scale):
    from . import trigonometric
    from . import output

    lst, lst2 = gen_from_approx(approx, scale)
    display(approx, lst, lst2, scale)

def display(approx, lst, lst2, scale):
    from . import trigonometric
    from . import output
    import matplotlib
    import numpy as np
    matplotlib.use("TkAgg")
    import matplotlib.pyplot as plt

    if lst2 is None:
        lst2 = np.zeros_like(lst)

    plt.plot(lst, lst2, 'x')
    plt.grid()
    plt.show()
