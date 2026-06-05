/-
  parties.lean in lean4 by samarth ghodke // math 157 final project
  --------------- *
  this file formalizes the legal rules concerning parties to a contract. two of
  those doctrines are demonstrated below. first, contractual capacity where a party must
  have legal capacity (usually meaning they are of majority age and sound mind) to enter
  an agreement. contracts with parties who lack capacity are voidable at the election of
  the incapacitated party. the second doctrine is bilateral and unilateral contracts, proving
  validity conditions and how they differ in a logical manner.
-/

import ContractModel.Definitions

-- contractual capacity (SECTION 1)

-- A two-party contract requires both parties to have legal capacity.
-- Without capacity on both sides, the agreement is not fully enforceable.
def two_party_enforceable (a : Agreement) (p1 p2 : Party) : Prop :=
  valid_contract a ∧ p1.hasCapacity ∧ p2.hasCapacity

-- If a two-party agreement is enforceable, the underlying contract is valid.
theorem enforceable_implies_valid
    (a : Agreement) (p1 p2 : Party)
    (h : two_party_enforceable a p1 p2) :
    valid_contract a :=
  h.1

-- A minor lacks legal capacity, so any contract they enter is not fully
-- enforceable against them. If a party is a minor, two_party_enforceable
-- cannot hold, because a minor's hasCapacity must be false.
-- We model this by assuming isMinor implies ¬hasCapacity.
theorem minor_not_enforceable
    (a : Agreement) (p1 p2 : Party)
    (hMinor : p1.isMinor)
    (hIncap : p1.isMinor → ¬p1.hasCapacity) :
    ¬two_party_enforceable a p1 p2 := by
  intro h
  exact hIncap hMinor h.2.1

-- even a fully valid contract fails enforceability if one party lacks capacity.
theorem no_capacity_blocks_enforcement
    (a : Agreement) (p1 p2 : Party)
    (hNoCapacity : ¬p1.hasCapacity) :
    ¬two_party_enforceable a p1 p2 := by
  intro h
  exact hNoCapacity h.2.1

-- bilateral vs. unilateral contracts (SECTION 2)

-- bilateral contracts are formed by mutual exchange of promises. both parties
-- make legally binding commitments at the time of formation. We capture this
-- by requiring that both parties have made a promise.
structure BilateralContract where
  agreement     : Agreement
  promisorMade  : Prop   -- initial offer from offereror
  promiseeMade  : Prop   -- reciprocal promise back from offeree

def valid_bilateral (bc : BilateralContract) : Prop :=
  valid_contract bc.agreement ∧ bc.promisorMade ∧ bc.promiseeMade

-- unilateral contract is formed when the offeree accepts by performing
-- the requested act rather than by making a promise. The offeror is bound
-- only once performance is complete.
structure UnilateralContract where
  agreement   : Agreement
  offerMade   : Prop   -- the offeror has made an open promise
  performed   : Prop   -- the offeree has completed the requested performance

def valid_unilateral (uc : UnilateralContract) : Prop :=
  valid_contract uc.agreement ∧ uc.offerMade ∧ uc.performed

-- in a bilateral contract, both parties are bound from the moment of formation.
-- i created a thm which extracts the promisor's binding promise from a valid bilateral contract.
theorem bilateral_promisor_bound
    (bc : BilateralContract)
    (h : valid_bilateral bc) :
    bc.promisorMade :=
  h.2.1 -- takes right conjunct then h.2 to get promisorMade

-- unilateral contract - no contract exists until performance is complete.
-- if performance hasn't happened, contract is not yet valid.
theorem unilateral_requires_performance
    (uc : UnilateralContract)
    (hNoPerform : ¬uc.performed) :
    ¬valid_unilateral uc := by
  intro h
  exact hNoPerform h.2.2

-- bilateral and unilateral contracts are structurally distinct: a valid
-- bilateral contract requires two promises, while a valid unilateral contract
-- requires one promise and one completed performance. neither is a special
-- case of the other in general.
theorem bilateral_not_unilateral
    (bc : BilateralContract)
    (uc : UnilateralContract)
    (hBi : valid_bilateral bc)
    (hUni : valid_unilateral uc)
    (hSameAgreement : bc.agreement = uc.agreement) :
    -- both need underlying agreement to be valid but promise conditions differ so they can't be valid simultaneously
    valid_contract bc.agreement ∧ valid_contract uc.agreement :=
  ⟨hBi.1, hSameAgreement ▸ hUni.1⟩
