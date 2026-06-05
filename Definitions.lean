/-
  definitions.lean
  --------------- *
  this file defines the key data structs used throughout formalization.
  legal concepts are represented as lean4 propositions, using proof assistant to reason
  whether those propositions hold. the central structure is agreement, which
  captures the four classical elems required for a binding contract under
  common law: offer, acceptance, consideration, and mutual assent.

  party is also defined which models the legal capacity of a contracting party,
  and ContractType, which discerns bilateral contracts (mutual promises)
  from unilateral contracts (a promise in exchange for performance)
-/

-- a party represents an individual or entity/group entering a contract.
-- hasCapacity asserts that the party has legal capacity (i.e., is of majority
-- age and of sound mind). isMinor asserts the opposite condition.
structure Party where
  hasCapacity : Prop
  isMinor : Prop

-- agreement captures the four elements of contract formation.
-- each field is a Prop, meaning it is a logical claim that must be proved (or assumed) in order to establish contract validity.
structure Agreement where
  offer         : Prop
  acceptance    : Prop
  consideration : Prop
  mutualAssent  : Prop

-- ContractType below discners the two fundamental categories of contracts
-- in bilateral contracts, both parties exchange promises whereas in unilateral contracts one party makes a promise that is accepted by performance rather than by a reciprocal promise.
inductive ContractType where
  | bilateral  : ContractType
  | unilateral : ContractType

-- a valid contract requires all four elements of Agreement to hold.
def valid_contract (a : Agreement) : Prop :=
  a.offer ∧ a.acceptance ∧ a.consideration ∧ a.mutualAssent

-- a void contract has no legal effect and modeled as negation of validity
-- a contract is void if and only if it fails to satisfy at least one of the four required elements.
def void_contract (a : Agreement) : Prop :=
  ¬valid_contract a

-- a voidable contract is one that is presently valid but may be rescinded by
-- one of the parties due to a defect such as duress, fraud, or incapacity.
-- we represent this by pairing a valid agreement with a separate rescission flag.
def voidable_contract (a : Agreement) (rescinded : Prop) : Prop :=
  valid_contract a ∧ rescinded
