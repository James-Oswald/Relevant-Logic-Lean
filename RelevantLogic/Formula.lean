
/-! # Relevant Logic Formulae
This file includes the definition of formulae in relevant logic.
It takes a minimalist approach, keeping the set of primitives
small (negation, conjunction, and relevant implication) and
defines other connectives in terms of these primitives.
-/

/-- Formulae are defined in terms of negation, conjunction, and
relevant implication. Atoms are defined as ℕs but one could
swap this out for any arbitrary atom type -/
inductive Formula where
| Atom : Nat -> Formula
| Not : Formula -> Formula
| And : Formula -> Formula -> Formula
| Imp : Formula -> Formula -> Formula

--Convenince Notations for constructing formulae
prefix:80 "¬ᵣ" => Formula.Not
infixr:70 " ∧ᵣ " => Formula.And
infixr:60 " →ᵣ " => Formula.Imp

/-- Or is defined in terms of Not and And -/
def Formula.Or (ϕ ψ : Formula) : Formula :=  ¬ᵣ(¬ᵣϕ ∧ᵣ ¬ᵣψ)
infixr:65 " ∨ᵣ " => Formula.Or

/-- Material implication is defined in terms of Or and Not -/
def Formula.MImp (ϕ ψ : Formula) : Formula := ¬ᵣϕ ∨ᵣ ψ
infixr:55 " ⊃ᵣ " => Formula.MImp

/-- Material Biconditional is defined in terms of Implication -/
def Formula.MBicond (ϕ ψ : Formula) : Formula := (ϕ ⊃ᵣ ψ) ∧ᵣ (ψ ⊃ᵣ ϕ)
infixr:50 " ≡ᵣ " => Formula.MBicond

/-- The Intensional conjunction/fusion/consistence/cotenability operator
    defined in terms of not and relevant implication note that this
    definition is only valid in R and stronger systems. See
    https://consequently.org/papers/rle.pdf page 12.
    -/
def Formula.Fusion (ϕ ψ : Formula) : Formula := ¬ᵣ(ϕ →ᵣ ¬ᵣψ)
infixr:63 " ∘ᵣ " => Formula.Fusion

/--
numeric literals can be automatically coerced to atoms.
For example we can write:
```
example : Formula := 2 ∧ᵣ (¬ᵣ1 →ᵣ 3)
```
-/
instance : OfNat Formula n := ⟨Formula.Atom n⟩
example : Formula := 2 ∧ᵣ (¬ᵣ1 →ᵣ 3)

/--
Nats be automatically coerced to atoms.
For example we can write:
```
example (n : Nat) : Formula := n →ᵣ n
```
-/
instance : Coe Nat Formula := ⟨Formula.Atom⟩
example (n : Nat) : Formula := n →ᵣ n
