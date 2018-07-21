RVerify
=======

Verification application for regulation kernels. 

Requirements
------------

Install the python dependencies from `requirements.txt`. The dependencies are:

	boto==2.48.0
	numpy==1.14.5
	pkg-resources==0.0.0
	PyYAML==3.12
	typed-ast==1.1.0
	z3-solver==4.5.1.0.post2
	
On Ubuntu, the following packages are also needed:

    python3-tk

Example Usage
-------------

### Check a given Regulation Kernel for known failure states 

    python3 -m RVerify -f example/kernel_code.py --check
	
### Show the used approximations for trigonometric functions

    python3 -m RVerify -f example/kernel_code.py --display-approximations

### Display internally generated SMT2 code

    python3 -m RVerify -f example/kernel_code.py --print-smt 
	
If this command is used to be directly processed with z3, the following switch is
also useful `--smt-include-get-model`. This activates the output of
`(get-model)` at the end of the output.

### Switch for piping in python code

Python code can also be piped into the SDTIN of the tool. To use this, use the
`--stdin` switch. Something like this works:

    cat example/kernel_code.py | python3 -m RVerify --stdin --check
	
### Accuracy changes of the checker

The checker internally used a set accuracy scale for the trigonometric lookup tables. This
scale can be made more exact or more lenient. For this functionality, the `--precision` switch
is used. Values > 1 make the checker more exact and compute times longer, values < 1 
do the opposite.

Contributing and Mode of Development
------------------------------------

This repository is hosted at [phabricator.harptech.eu](https://phabricator.harptech.eu).
A public mirror is provided
at [github.com/HARPTech/RVerify](https://github.com/HARPTech/RVerify). Contributions
are welcome and will be merged into the repository after they have been reviewed
in the internal system.

Another related repository of this project is [RTest](../RTest), providing a visualisation
of regulation kernels.
