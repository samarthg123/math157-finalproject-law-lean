/-
  contract validity in lean4 by samarth ghodke // math 157 final project
  --------------- *
  this file models the basic elems of a legally valid contract using
  lean4 type system. A contract is represented as a structure (agreement)
  whose fields are propositions corresponding to the four classical elements
  of contract law: offer, acceptance, consideration, and mutual assent.

  predicate `valid_contract` asserts that all four elements hold. we then
  prove two thms: one showing a fully valid contract satisfies the
  predicate, and one showing that a contract missing consideration does not.
-/

-- struct representing the four elems required for a valid contract.
structure Agreement where
  offer : Prop
  acceptance : Prop
  consideration : Prop
  mutualAssent : Prop

-- contract is valid when all four elements hold simultaneously.
def valid_contract (a : Agreement) : Prop :=
  a.offer ∧ a.acceptance ∧ a.consideration ∧ a.mutualAssent -- utilized logical conjunction to combine the four conditions into one predicate.

/-
  general thm: given any Agreement whose four fields are individually
  witnessed, can construct a proof that the contract is valid.
-/
theorem contract_exists
    (a : Agreement)
    (h1 : a.offer)
    (h2 : a.acceptance)
    (h3 : a.consideration)
    (h4 : a.mutualAssent) :
    valid_contract a :=
  ⟨h1, h2, h3, h4⟩

-- concrete example of a fully valid contract (such that all fields are True).
def valid_example : Agreement :=
  Agreement.mk True True True True -- refer to the elements of the structure directly to create an instance of Agreement where all conditions are satisfied.

theorem valid_example_works : valid_contract valid_example := by
  unfold valid_contract valid_example -- unfold keyword here replaces defined func in the goal with actual underlying def'n
  repeat constructor

/-
  here's a concrete example of an invalid contract: consideration is False,
  meaning no exchange of value occurred.
-/
def invalid_example : Agreement :=
  { offer := True
  , acceptance := True
  , consideration := False
  , mutualAssent := True
  }

-- we prove the negation: this agreement does NOT satisfy valid_contract.
theorem invalid_contract : ¬ valid_contract invalid_example := by
  unfold valid_contract invalid_example
  intro h
  obtain ⟨_, _, h2, _⟩ := h
  exact h2
/-
this project is simply inspired by the work I'm currently working on in my contract law class, and is meant to be a fun exercise in modeling legal concepts using a formal proof assistant.
the goal is to capture what makes a contract valid in various different circumstances and explore logic tools.
i plan to add more legal concepts to make the scope and complexity of this project more advanced while easy for someone with a non-law background to understand (suggested ideas below)
my motivation for building this project is to use mathematical, formalized reasoning for me to gain a stronger understanding of the logical premises and predicates of my future career path with lean4, and to have fun exploring the intersection of law and logic.

legal concepts i plan to implement before submission of final project:

*void vs. voidable contracts --> proving disequivalence of these two concepts
*duress / frauds negate assent --> ¬mutualAssent → ¬valid_contract
*statute of frauds (written req.) --> adding a writtenForm field requiring necessity of written agreement for certain contract types
*bilateral and unilateral contracts --> modeling as sequence and requiring ordering
*novation --> replacing one party with another, or changing obligations extinguishing old contract and making a new one (requires mutual consent from all involved parties to release liability from original parties)
*capacity (must be majority age to enter a contract which could be another logical elem)

-/
