/-
  examples. lean by samarth ghodke // math 157 final project
  --------------- *
  this files gives you clear examples that actually bring abstract definitions to life
  from the rest of the project. each example either builds a proof that
  a specific agreement satisfies a legal predicate or that it does not.

  the examples are important since they show us how the definitions set in other files
  validate our legal logic. they illustrate how a practioner could use a specific fact pattern
  using formal methodology.
-/

import ContractModel.Definitions
import ContractModel.Validity
import ContractModel.Parties
import ContractModel.Breach

-- ex 1 - valid contract

-- all four elems are satisfied
-- standard commercial contract for sale of goods
def sale_of_goods : Agreement :=
  { offer         := True
  , acceptance    := True
  , consideration := True
  , mutualAssent  := True
  }

theorem sale_of_goods_valid : valid_contract sale_of_goods := by
  unfold valid_contract sale_of_goods
  repeat constructor

-- ex 2 - void contract

-- contract without consideration is void.
-- promise without consideration is unenforceable
def gratuitous_promise : Agreement := -- this is also a promise that maybe one does out of goodwill (charity, generosity)
  { offer         := True
  , acceptance    := True
  , consideration := False
  , mutualAssent  := True
  }

theorem gratuitous_promise_void : void_contract gratuitous_promise := by
  unfold void_contract valid_contract gratuitous_promise
  intro h
  obtain ⟨_, _, h3, _⟩ := h
  exact h3

-- ex 3 - duress

-- contract signed under duress lacks true mutual assent.
-- even if all other elements appear present, the contract is invalid.
def duress_agreement : Agreement :=
  { offer         := True
  , acceptance    := True
  , consideration := True
  , mutualAssent  := False   -- assent was coerced, not genuine
  }

theorem duress_agreement_invalid : ¬valid_contract duress_agreement :=
  duress_negates_contract duress_agreement (by unfold duress_agreement; exact id)

-- ex 4. statute of frauds (sof)

-- land sale was never reduced to writing so under sof, is unenforceable
def oral_land_sale : WrittenAgreement :=
  { offer         := True
  , acceptance    := True
  , consideration := True
  , mutualAssent  := True
  , writtenForm   := False   -- oral only; no written instrument
  }

theorem oral_land_sale_unenforceable : ¬statute_of_frauds_valid oral_land_sale := -- compares against the oral and reqs. of sof
  no_writing_not_enforceable oral_land_sale
    (by unfold oral_land_sale; exact id)

-- ex 5. contractual capacity

-- contract between an adult and a minor, one has capacity other doesn't
-- thus, agreement is therefore not fully enforceable.
def adult : Party := { hasCapacity := True,  isMinor := False }
def minor : Party := { hasCapacity := False, isMinor := True  }

theorem minor_contract_not_enforceable :
    ¬two_party_enforceable sale_of_goods adult minor := by
  unfold two_party_enforceable
  intro h
  obtain ⟨_, _, hCap⟩ := h
  unfold minor at hCap
  exact hCap

-- ex 6. breach of contract

-- contractor who was hired under a valid contract but failed to perform. a common example we see nowadays.
-- very simple, straightforward breach scenario.
def failed_construction : Contract :=
  { agreement := sale_of_goods
  , performed := False
  , breached  := True
  }

theorem failed_construction_is_breach : is_breach failed_construction :=
  nonperformance_is_breach failed_construction
    sale_of_goods_valid
    (by unfold failed_construction; trivial)
    (by unfold failed_construction; exact id)

-- ex 7. novation

-- novation where a new party assumes the obligations of an original party,
-- and all parties have consented. original contract is removed from liability of all parties now.
def novation_example : Novation :=
  { original := sale_of_goods
  , replacement := { offer := True, acceptance := True, consideration := True, mutualAssent := True }
  , allPartiesConsent := True
  }

theorem novation_example_valid : valid_novation novation_example := by
  unfold valid_novation valid_contract novation_example
  repeat constructor
