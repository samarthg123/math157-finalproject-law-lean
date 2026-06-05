/-
  breach.lean in lean4 by samarth ghodke // math 157 final project
  --------------- *
  this file formalizes breach of contract and also discusses novation with clear examples.
  a breahc occurs when a party obligated to a valid contract fails to perform their obligations.
  we prove breach supposes valid contract, full performance and breach are mutually excl.,
  and that non-performance of a valid contract = breach.


  novation is also explored. it is where you sub a new contract for an old one.
  it can involve replacement of party, new contract for old one. may include
  changes to obligations. critical req is true, unanimous consent of all original parties.
-/

import ContractModel.Definitions

-- sec 1 - breach of contract

-- contract pairs agreement w/ performance and breach status.
-- performed asserts that party completed their duties.
-- breached asserts that something went wrong basically.
structure Contract where
  agreement : Agreement
  performed : Prop
  breached  : Prop

-- below showcases that breach presupposes a valid contract.
def is_breach (c : Contract) : Prop :=
  valid_contract c.agreement ∧ c.breached ∧ ¬c.performed

theorem breach_requires_valid_contract
    (c : Contract)
    (h : is_breach c) :
    valid_contract c.agreement :=
  h.1

-- no breach if full performance (you did what you were supposed to, so no breach)
theorem performance_excludes_breach
    (c : Contract)
    (hPerformed : c.performed) :
    ¬is_breach c := by
  intro h
  exact h.2.2 hPerformed

-- basic breach rule
theorem nonperformance_is_breach
    (c : Contract)
    (hValid   : valid_contract c.agreement)
    (hBreach  : c.breached)
    (hNoPerf  : ¬c.performed) :
    is_breach c :=
  ⟨hValid, hBreach, hNoPerf⟩

-- mathematical contrapositive relation of breach
-- if no breach, 1) contract was invalid or 2) party completed their assigned task
theorem no_breach_means_performed_or_invalid
    (c : Contract)
    (hNoBreach : ¬is_breach c)
    (hValid    : valid_contract c.agreement)
    (hAsserted : c.breached) :
    c.performed := by
  simp only [is_breach] at hNoBreach
  by_cases hPerformed : c.performed
  · exact hPerformed
  · exact False.elim (hNoBreach ⟨hValid, hAsserted, hPerformed⟩)

-- sec 2 - novation

-- refer to definition in above/starter comments
structure Novation where
  original        : Agreement   -- the contract being extinguished.
  replacement     : Agreement   -- the new contract taking its place.
  allPartiesConsent : Prop      -- unanimous consent to the novation happening.

def valid_novation (n : Novation) : Prop :=
  valid_contract n.original ∧
  valid_contract n.replacement ∧
  n.allPartiesConsent

-- novation needs to extinguish original to make the new one valid.
theorem novation_extinguishes_original
    (n : Novation)
    (h : valid_novation n) :
    valid_contract n.replacement :=
  h.2.1

-- needs unanimous consent to not fail. original contract remains in force.
-- proposed replacement is not binding till all parties agree to it.
theorem no_consent_no_novation
    (n : Novation)
    (hNoConsent : ¬n.allPartiesConsent) :
    ¬valid_novation n := by
  intro h
  exact hNoConsent h.2.2

-- A novation requires the original contract to have been valid. You cannot
-- novate a void agreement because there is nothing to substitute.
theorem novation_requires_valid_original
    (n : Novation)
    (h : valid_novation n) :
    valid_contract n.original :=
  h.1

-- if a valid novation has occurred, the parties are no longer bound by the original.
-- modeled through the replaced contract being the one all parties will operate under.
theorem novation_replaces_obligation
    (n : Novation)
    (h : valid_novation n) :
    valid_contract n.original ∧ valid_contract n.replacement ∧ n.allPartiesConsent := h
