# math157-finalproject-law-lean
Welcome! This is the README file for my MATH 157 final project, integrating foundational contract-law principles with formal verification in Lean and comparing it with Z3 which is implemented in Python. The project demonstrates how mathematical logic can be applied to encode and analyze legal structures.

A key observation was that Lean proved things actively (engaging with user, intermediate goals), whereas Z3 would check automatically. 

Dependency installation instructions are written in ContractsZ3.py. As a reminder, ensuring Python3 (or version of Python) is installed will help to see how the .py file works in comparison to the .lean files.

To reiterate instructions: pip install z3-solver==4.13.3.0 and using a virtual environment (venv) are useful in the backup case the commands don't work on your end. Please ensure to use this specific version because on newer versions of z3-solver, the API may have changed and the code might not work as intended. It should work immediately, but if you have technical issues with the virtual environment, try this command in your terminal: source .venv_z3/bin/activate

To run the Python file: python3 [or whichever version you're using] ContractsZ3.py






