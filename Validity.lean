/-
validity in lean4 by samarth ghodke // math 157 final project
--------------- *
this file models more advanced legal concepts that align with contract validity
invalidity and distinguish between voidable and unvoidable contracts. void contracts
have no legal effect and cannot be ratified. a voidable contract however is active until
the affected party chooses to void it. we model this by defining a predicate `voidable_contract`
when a contract is valid but one party lacks capacity. how i've modeled this is through the following
logical structure: every void contract fails the validity test, but a voidABLE contract still actually
satisfies the validity predicate until rescinded rights are exercised. i also model and
formalize two important doctrines that affect the mutualAssent element: duress and fraud.

both negate true assent. duress is defined as forced against acting in own will
through coercion or psychological pressure. how can we model this mathematically?
essentially, any agreement dependent on them fails the validity test automatically.

lastly we include the statute of frauds which requires certain contracts
to be in written form. we model this by adding a new field to the agreement structure
and including it in the validity predicate.

-/

import ContractModel.Definitions

-- basic validity thms (SECTION 1)

-- given explicit witnesses for all four elements, contract is valid.
-- fundamental introduction rule for valid_contract.
theorem contract_valid_intro
    (a : Agreement)
    (h1 : a.offer)
    (h2 : a.acceptance)
    (h3 : a.consideration)
    (h4 : a.mutualAssent) :
    valid_contract a :=
  ⟨h1, h2, h3, h4⟩

-- if a contract is valid, each individual element can be extracted.
-- elim rules for downstream proofs.
theorem valid_has_offer (a : Agreement) (h : valid_contract a) : a.offer :=
  h.1

theorem valid_has_acceptance (a : Agreement) (h : valid_contract a) : a.acceptance :=
  h.2.1

theorem valid_has_consideration (a : Agreement) (h : valid_contract a) : a.consideration :=
  h.2.2.1

theorem valid_has_assent (a : Agreement) (h : valid_contract a) : a.mutualAssent :=
  h.2.2.2

-- void vs. voidable contracts (SECTION 2)

-- void contract is never valid by definition of void_contract

theorem void_not_valid (a : Agreement) (h : void_contract a) : ¬valid_contract a :=
  h

-- voidable contract IS currently valid. this logical structure actually shows you the difference
-- voidable doesn't mean invalid
theorem voidable_is_valid
    (a : Agreement)
    (rescinded : Prop)
    (h : voidable_contract a rescinded) :
    valid_contract a :=
  h.1

-- void and voidable are mutually exclusive. cannot be simultaneously both.
-- reminder of defs: be void (lacking validity) and voidable (presently valid but rescindable).
theorem void_and_voidable_exclusive
    (a : Agreement)
    (rescinded : Prop)
    (hv : void_contract a)
    (hvoid : voidable_contract a rescinded) :
    False :=
  hv hvoid.1

-- duress and fraud (SECTION 3)

-- if mutual assent was obtained through duress, the assent element of validity fails.
-- duress means the party did not genuinely agree, so mutualAssent is false.
-- w/o this, the contract cannot be valid.
theorem duress_negates_contract
    (a : Agreement)
    (hDuress : ¬a.mutualAssent) :
    ¬valid_contract a := by
  intro h
  exact hDuress h.2.2.2

-- fraud is similar in the notion it negates genuine assent.
-- for ex. a party was tricked into a contract, then mutualAssent fails and contract is not valid.
theorem fraud_negates_contract
    (a : Agreement)
    (hFraud : ¬a.mutualAssent) :
    ¬valid_contract a :=
  duress_negates_contract a hFraud -- fraud operates similarly due to negating true assent

-- statute of frauds (SECTION 4)

-- we add a writtenForm field and define a stricter validity predicate for contracts subject to this legality.
structure WrittenAgreement extends Agreement where
  writtenForm : Prop

-- contract subject to the statute of frauds is only enforceable if it
-- satisfies the four standard elements AND is in written form.
def statute_of_frauds_valid (wa : WrittenAgreement) : Prop :=
  valid_contract wa.toAgreement ∧ wa.writtenForm

-- written agreement satisfies the statute of frauds, it is also a
-- valid contract in the ordinary sense.
theorem sof_implies_valid
    (wa : WrittenAgreement)
    (h : statute_of_frauds_valid wa) :
    valid_contract wa.toAgreement :=
  h.1

-- otherwise valid contract that lacks written form is NOT enforceable
-- under the sof. this essentially is how i figured to model the writing req.
theorem no_writing_not_enforceable
    (wa : WrittenAgreement)
    (hNoWrite : ¬wa.writtenForm) :
    ¬statute_of_frauds_valid wa := by
  intro h
  exact hNoWrite h.2
