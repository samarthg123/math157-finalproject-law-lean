"""
contractsz3.py by samarth ghodke // math 157 final project
--------------- *
this file contains the Z3 encoding of the contract model, including definitions of parties, agreements, and contracts,
as well as theorems about their properties. The code is structured to mirror the Lean 
formalization in Parties.lean, with adjustments for Z3's syntax and capabilities.

i wanted to create a Z3-SMT version to see how the model could be used for automated reasoning 
which tool expresses logical relationships more naturally? Z3 is made for automated reasoning
while Lean is made for interactive thm proofs, goal by goal. i expand more on the differences of this
in my written analysis as per the project rubric and requirements.


** dependencies to install: pip install z3-solver==4.13.3.0

MAKE SURE PYTHON3 IS INSTALLED TO RUN THE Z3.

if this does not work for some reason (unlikely), backup: try to run it on a venv (virtual environment on an earlier python version)

ex. source .venv_z3/bin/activate
    python3 contractsz3.py

^ *** note *** ensure to use this specific version because on newer versions of z3-solver, the API may have changed and the code might not work as intended.

"""

try:
    from z3 import (  # type: ignore[import]
        Bool, BoolVal, Solver, Not, And, Or, Implies,
        sat, unsat, is_true
    )
except Exception as e:
    raise ImportError(
        "z3-solver is required but could not be imported. install with: pip install z3-solver"
    ) from e
 
# sec 1 - core contract elements
 
def make_agreement(name=""):
    "create a named set of contract element boolean variables."
    prefix = f"{name}_" if name else ""
    return {
        "offer":          Bool(f"{prefix}offer"),
        "acceptance":     Bool(f"{prefix}acceptance"),
        "consideration":  Bool(f"{prefix}consideration"),
        "mutual_assent":  Bool(f"{prefix}mutual_assent"),
    }
 
def valid_contract(a):
    return And(a["offer"], a["acceptance"], a["consideration"], a["mutual_assent"])
 
def void_contract(a):
    return Not(valid_contract(a))
 
def voidable_contract(a, rescinded):
    return And(valid_contract(a), rescinded)
 
 
# sec 2 - validity thms
 
def check(label, claim):
# checks if claim valid or invalid (claim is boolean expr.)
    s = Solver()
    s.add(Not(claim))
    result = s.check()
    if result == unsat:
        print(f"PROVEN:       {label}")
    elif result == sat:
        print(f"COUNTER FOUND: {label}")
        print(f"MODEL: {s.model()}")
    else:
        print(f"UNKNOWN:      {label}")
 
 
print("=" * 60)
print("sec 2 - validity thms")
print("=" * 60)
 
a = make_agreement("a")
 
# reminder, void and voidable are mutually exclusive.
# In Lean: theorem void_and_voidable_exclusive ... : False
# In Z3: there is no assignment where both void_contract and voidable_contract hold simultaneously.
rescinded = Bool("rescinded")
check(
    "void and voidable are mutually exclusive",
    Not(And(void_contract(a), voidable_contract(a, rescinded)))
)
 
# thm: duress (¬mutual_assent) implies ¬valid_contract.
# Lean: theorem duress_negates_contract
check(
    "duress negates contract validity",
    Implies(Not(a["mutual_assent"]), void_contract(a))
)
 
# thm: a voidable contract is currently valid.
# Lean: theorem voidable_is_valid
check(
    "voidable contract is currently valid",
    Implies(voidable_contract(a, rescinded), valid_contract(a))
)
 
 
# sec 3 - statute of frauds (sof)
 
print()
print("=" * 60)
print("sec 3 - statute of frauds (sof)")
print("=" * 60)
 
def statute_of_frauds_valid(a, written_form):
    return And(valid_contract(a), written_form)
 
written = Bool("written_form")
 
# thm: no writing means not enforceable under sof.
# Lean: theorem no_writing_not_enforceable
check(
    "oral contract fails SOF validity",
    Implies(
        And(valid_contract(a), Not(written)),
        Not(statute_of_frauds_valid(a, written))
    )
)
 
# thm: sof validity implies ordinary validity.
# Lean: theorem sof_implies_valid
check(
    "SOF validity implies ordinary validity",
    Implies(statute_of_frauds_valid(a, written), valid_contract(a))
)
 
 
# sec 4 - capacity & parties
 
print()
print("=" * 60)
print("sec 4 - capacity & parties")
print("=" * 60)
 
def two_party_enforceable(a, p1_capacity, p2_capacity):
    return And(valid_contract(a), p1_capacity, p2_capacity)
 
p1_capacity = Bool("p1_capacity")
p2_capacity = Bool("p2_capacity")
p1_is_minor = Bool("p1_is_minor")
 
# thm: a minor lacks capacity, so the contract is not enforceable.
# Lean: theorem minor_not_enforceable
check(
    "minor contract is not enforceable",
    Implies(
        And(p1_is_minor, Not(p1_capacity)),
        Not(two_party_enforceable(a, p1_capacity, p2_capacity))
    )
)
 
# thm: no capacity blocks enforcement even if contract is valid.
# Lean: theorem no_capacity_blocks_enforcement
check(
    "lack of capacity blocks enforcement",
    Implies(
        And(valid_contract(a), Not(p1_capacity)),
        Not(two_party_enforceable(a, p1_capacity, p2_capacity))
    )
)
 
 
# sec 5 - breach
 
print()
print("=" * 60)
print("sec 5 - breach")
print("=" * 60)
 
performed = Bool("performed")
breached  = Bool("breached")
 
def is_breach(a, performed, breached):
    # below i've added a mirror example just to see what it looks like in comparison to Lean syntax.
    """
    mirror example: def is_breach (c : Contract) : Prop :=
               valid_contract c.agreement ∧ c.breached ∧ ¬c.performed
    """
    return And(valid_contract(a), breached, Not(performed))
 
# thm: performance and breach mutually exclusive.
# Lean: theorem performance_excludes_breach
check(
    "performance and breach are mutually exclusive",
    Implies(performed, Not(is_breach(a, performed, breached)))
)
 
# thm: breach assumes a valid contract was in place prior.
# Lean: theorem breach_requires_valid_contract
check(
    "breach requires a valid contract",
    Implies(is_breach(a, performed, breached), valid_contract(a))
)
 
# thm: nonperformance of valid contract = breach.
# Lean: theorem nonperformance_is_breach
check(
    "nonperformance of valid contract is breach",
    Implies(
        And(valid_contract(a), breached, Not(performed)),
        is_breach(a, performed, breached)
    )
)
 
 
# sec 6 - novation
 
print()
print("=" * 60)
print("sec 6 - novation")
print("=" * 60)
 
orig      = make_agreement("orig")
repl      = make_agreement("repl")
consent   = Bool("all_parties_consent")
 
def valid_novation(orig, repl, consent):
    return And(valid_contract(orig), valid_contract(repl), consent)
 
# thm: novation without consent is invalid (replacing existing contract w/ new one).
check(
    "novation without consent fails",
    Implies(Not(consent), Not(valid_novation(orig, repl, consent)))
)
 
# thm: valid novation implies the replacement contract is valid.

check(
    "valid novation produces a valid replacement contract",
    Implies(valid_novation(orig, repl, consent), valid_contract(repl))
)
 
# thm: novation requires the original contract to be valid.
check(
    "novation requires valid original contract",
    Implies(valid_novation(orig, repl, consent), valid_contract(orig))
)

# sec 7 - z3-specific capabilities: advantages

# this part shows basically what z3 can do that Lean can't easily do
# often, in Lean you have to construct examples by hand which z3 can do for you.
 
print()
print("=" * 60)
print("sec 7 - z3-specific capabilities: advantages")
print("=" * 60)
 
s = Solver()
ex = make_agreement("ex")
 
# asks z3 - find an example of contract that is voidable but not void
ex_rescinded = Bool("ex_rescinded")
s.add(voidable_contract(ex, ex_rescinded))  # must be voidable
s.add(Not(void_contract(ex)))               # must not be void
 
if s.check() == sat:
    m = s.model()
    print("z3 found an example of voidable but not void contract.")
    for var in [ex["offer"], ex["acceptance"], ex["consideration"],
                ex["mutual_assent"], ex_rescinded]:
        print(f" {var} = {m[var]}")
else:
    print("contract doesn't exist.")
 
# asks z3 whether there is a case of duress where contract is still present.
# contract is still valid? should be no, but z3 confirms this for us.
s2 = Solver()
b = make_agreement("b")
s2.add(Not(b["mutual_assent"]))  # duress present
s2.add(valid_contract(b))        # but contract is valid? how could this be?
result2 = s2.check()
print()
if result2 == unsat:
    print(" z3 confirmation: no scenario exists where duress is present")
    print(" and the contract is still valid. (unsat)")
elif result2 == sat:
    print(" z3 has a counterexample", s2.model())
 
print()
print("=" * 60)
print("checks are completed.")
print("=" * 60)
