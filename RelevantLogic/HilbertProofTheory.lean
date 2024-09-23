
import Mathlib.Tactic.Lemma

import RelevantLogic.Formula

/-! # Hilbert Style Proof Theory for Relevance Logic

This file contains the definition of proofs in the minimal relevance logic B.
Proofs are inductively defined types where a formula is either an instance of
an axiom or derived via a rule of inference. Provability is defined as the
existence of a proof.
-/

/--
Proofs are inductively defined types where a formula is either an instance
of an axiom or derived via a rule of inference.
-/
inductive BProof : Formula -> Type
| id               {ϕ} : BProof (ϕ →ᵣ ϕ)
| and_elim_left  {ϕ ψ} : BProof (ϕ ∧ᵣ ψ →ᵣ ϕ)
| and_elim_right {ϕ ψ} : BProof (ϕ ∧ᵣ ψ →ᵣ ψ)
| and_intro    {ϕ ψ χ} : BProof ((ϕ →ᵣ ψ) →ᵣ (ϕ →ᵣ χ) →ᵣ (ϕ →ᵣ ψ ∧ᵣ χ))
| or_intro_left  {ϕ ψ} : BProof (ϕ →ᵣ ϕ ∨ᵣ ψ)
| or_intro_right {ϕ ψ} : BProof (ψ →ᵣ ϕ ∨ᵣ ψ)
| or_elim      {ϕ ψ χ} : BProof ((ϕ →ᵣ χ) →ᵣ (ψ →ᵣ χ) →ᵣ (ϕ ∨ᵣ ψ →ᵣ χ))
| and_or       {ϕ ψ χ} : BProof (ϕ ∧ᵣ (ψ ∨ᵣ χ) →ᵣ (ϕ ∧ᵣ ψ) ∨ᵣ (ϕ ∧ᵣ χ))
| dne              {ϕ} : BProof (¬ᵣ¬ᵣϕ →ᵣ ϕ)
| mp {ϕ ψ} : BProof ϕ → BProof (ϕ →ᵣ ψ) → BProof ψ
| CI {ϕ ψ} : BProof ϕ → BProof ψ → BProof (ϕ ∧ᵣ ψ)
| DI1 {ϕ ψ} : BProof (ϕ →ᵣ ψ) → BProof ((C →ᵣ ϕ) →ᵣ (C →ᵣ ψ))
| DI2 {ϕ ψ} : BProof (ϕ →ᵣ ψ) → BProof ((ψ →ᵣ C) →ᵣ (ϕ →ᵣ C))
| CO {ϕ ψ} : BProof (ϕ →ᵣ ψ) → BProof (¬ᵣψ →ᵣ ¬ᵣϕ)

-- Shorthand notation for the type of proofs of a formula
prefix:80 "T⊢ᴮ " => BProof

/-- Probability of a `Formula` ϕ is defined in terms of the type of proofs of ϕ
    (`BProof`) not being empty, in otherwords, the existance of at least
    one proof of ϕ -/
def BProvable (ϕ : Formula) := Nonempty (T⊢ᴮ ϕ)
prefix:80 "⊢ᴮ " => BProvable

/-- If given a proof of ϕ, you can always construct that ϕ is provable -/
lemma BProvable.ofProof {ϕ} (p : T⊢ᴮ ϕ) : ⊢ᴮϕ := ⟨p⟩

/-- ϕ is provable iff a proof of ϕ exists -/
lemma BProvable.iff_exists : ⊢ᴮϕ ↔ ∃ _ : T⊢ᴮ ϕ, True := by
  simp_all only [exists_prop', and_true]
  rfl
