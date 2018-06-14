import numpy as np
import math

limit_linear = 5000
limit = 50000

def gen_space(scale):
    linearRange = np.arange(0, limit_linear - (limit_linear / 20), 200 * (1 / scale))
    linearRange2 = np.arange(0, limit - (limit / 20), 8000 * (1 / scale))

    logSpace = np.logspace(0, 3.0, num=10)

    inverseLogSpace = limit - logSpace

    c = []
    for i in linearRange:
        c.append(i)
    for i in linearRange2:
        c.append(i)
    for i in inverseLogSpace:
        c.append(i)

    c.sort()
    
    return np.array(c), None

def gen_tan_range(scale):
    logSpace, c = gen_space(scale)

    inverseLogSpace = limit - logSpace
    
    tanRange = []
    for i in inverseLogSpace:
        tanRange.append(np.interp(i, [0, limit], [-math.pi / 2, 0]))

    for i in logSpace:
        tanRange.append(np.interp(i, [0, limit], [0, math.pi / 2]))

    tanRange.sort()

    tans = []
    for i in tanRange:
        tans.append(math.tan(i))

    return tanRange, tans

def gen_atan_range(scale):
    logSpace, c = gen_space(scale)

    inverseLogSpace = limit - logSpace
    
    tanRange = []
    for i in inverseLogSpace:
        tanRange.append(np.interp(i, [0, limit], [-math.pi / 2, 0]))

    for i in logSpace:
        tanRange.append(np.interp(i, [0, limit], [0, math.pi / 2]))

    tanRange.sort()

    tans = []
    for i in tanRange:
        tans.append(math.tan(i))

    # Reverse
    tanRange.sort(reverse=True)
    tans.sort(reverse=True)

    return tans, tanRange
