# math 157 final project - by samarth ghodke
welcome! this is the README file for my MATH 157 final project, integrating foundational contract-law principles with formal verification in Lean and comparing it with Z3 which is implemented in Python. The project demonstrates how mathematical logic can be applied to encode and analyze legal structures.

a key observation was that Lean proved things actively (engaging with user, intermediate goals), whereas Z3 would check automatically. 

## INSTALLATION INSTRUCTIONS

dependency installation instructions are written in ContractsZ3.py. as a reminder, ensuring Python3 (or version of Python) is installed will help to see how the .py file works in comparison to the .lean files.

### z3-solver installation
to reiterate instructions: pip install z3-solver==4.13.3.0 and using a virtual environment (venv) are useful in the backup case the commands don't work on your end. please ensure to use this specific version because on newer versions of z3-solver, the API may have changed and the code might not work as intended. it should work immediately, but if you have technical issues with the virtual environment, try this command in your terminal: source .venv_z3/bin/activate

### python installation/running the file
to run the python file: python3 [or whichever version you're using] ContractsZ3.py

## LEAN4 vs. Z3

proof style: interactive (goal by goal) - lean, fully automated - Z3
output: proof formalized output - lean, "sat/unsat" model - Z3
expressiveness: full dependent type theory - lean, SMT & quantifier-free - Z3
best for: structural reasoning - lean, rapid instantaneous checks - Z3

a detailed written analysis of these tradeoffs are are included in the written component.

## theorems proven:

here is a selective list of the various different theorems proven and verified in this project:
-void and voidable contracts and mutually excl.
-duress (no mutual assent) negates validity
-voidable contract is currently valid
-oral contract fails statute of frauds enforceability
-minor lacking capacity form an enforceable contract
-performance and breach are mutually excl.
-breach presupposes a valid contract (must have been valid for there to have been an official breach)
-novation needs consent from all parties (requires original contract to be valid)










