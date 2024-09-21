
import Aesop
import Mathlib.Tactic.Contrapose


inductive Formula : Type where
| Atom : Nat -> Formula
| Not : Formula -> Formula
| And : Formula -> Formula -> Formula
| Or : Formula -> Formula -> Formula
| Imp : Formula -> Formula -> Formula

instance : Coe Nat Formula := ⟨Formula.Atom⟩

--Notations for term level formulae
prefix:80 " ¬ᵣ " => Formula.Not
infixr:70 " ∧ᵣ " => Formula.And
infixr:65 " ∨ᵣ " => Formula.Or
infixr:60 " →ᵣ " => Formula.Imp

-- Unconditioned Routley–Meyer frames
structure URMFrame where
  W : Type
  R : W -> W -> W → Prop
  S : W -> W    -- *
  O : W         -- 0

def URMFrame.Star {F : URMFrame} (a : F.W) : F.W := F.S a
postfix:80 "*ᵣ"  => URMFrame.Star

def URMFrame.Leq {F : URMFrame} (a b : F.W) : Prop := F.R F.O a b
infix:70 " ≤ᵣ " => URMFrame.Leq

-- Conditioned Routley–Meyer frames
structure RMFrame extends URMFrame where
  leq_symm  (a : W)       : a ≤ᵣ a
  leq_trans (a b c : W)   : a ≤ᵣ b → b ≤ᵣ c → a ≤ᵣ c
  leq_?     (a b c d : W) : d ≤ᵣ a -> R a b c -> R d b c
  star_star (a : W)       : a*ᵣ*ᵣ = a
  leq_star  (a b : W)     : a ≤ᵣ b -> b*ᵣ ≤ᵣ a*ᵣ

-- An Unconditioned Routley–Meyer model is a frame along with a valuation function
structure URMModel extends RMFrame where
  -- Valuation function on atoms
  V : W -> Formula -> Prop

-- Notation for a formula being true at a world in a model
def URMModel.holds {M : URMModel} (w : M.W) (φ : Formula) : Prop := M.V w φ
infix:50 " ⊩ " => URMModel.holds
def URMModel.nholds {M : URMModel} (w : M.W) (φ : Formula) : Prop := ¬(w ⊩ φ)
infix:50 " ⊮ " => URMModel.nholds

-- Conditioned Routley–Meyer models
structure RMModel extends URMModel where
  -- Basic Conditions
  V_not (φ : Formula)   (w : W) :    (w ⊩ ¬ᵣφ) ↔ (w*ᵣ ⊮ φ)
  V_and (φ ψ : Formula) (w : W) : (w ⊩ φ ∧ᵣ ψ) ↔ (w ⊩ φ) ∧ (w ⊩ ψ)
  V_or  (φ ψ : Formula) (w : W) : (w ⊩ φ ∨ᵣ ψ) ↔ (w ⊩ φ) ∨ (w ⊩ ψ)
  V_imp (φ ψ : Formula) (a : W) : (w ⊩ φ →ᵣ ψ) ↔ ∀ b c, (R a b c ∧ b ⊩ φ) → (c ⊩ ψ)
  -- Hereditariness on atoms condition
  V_her (n : Nat) (a b : W) : (a ⊩ n) → (a ≤ᵣ b) → (b ⊩ n)

def valid (φ : Formula) : Prop := ∀ (M : RMModel) (w : M.W), w ⊩ φ
notation "⊨ " φ => valid φ

lemma RMModel.V_not' (M : RMModel) (φ : Formula) (w : M.W) : (w*ᵣ ⊩ ¬ᵣφ) ↔ (w ⊮ φ) := by
  apply Iff.intro
  . case mp =>
    intro H
    simp [M.V_not, M.star_star] at H
    exact H
  . case mpr =>
    intro H
    simp [M.V_not, M.star_star]
    exact H

lemma RMModel.V_not'' (M : RMModel) (φ : Formula) (w : M.W) : (w*ᵣ ⊮ ¬ᵣφ) ↔ (w ⊩ φ) := by
  apply Iff.intro
  . case mp =>
    intro H
    simp [URMModel.nholds, M.V_not, M.star_star] at H
    exact H
  . case mpr =>
    intro H
    simp [URMModel.nholds, M.V_not, M.star_star]
    exact H

lemma RMModel.V_not''' (M : RMModel) (φ : Formula) (w : M.W) : (w ⊮ ¬ᵣφ) ↔ (w*ᵣ ⊩ φ) := by
  apply Iff.intro
  . case mp =>
    intro H
    simp [URMModel.nholds, M.V_not, M.star_star] at H
    exact H
  . case mpr =>
    intro H
    simp [URMModel.nholds, M.V_not, M.star_star]
    exact H

lemma starm (M : RMModel) (φ : Formula) (w : M.W) : (w*ᵣ ⊮ φ) ↔ (w ⊩ φ) := by
  apply Iff.intro
  . case mp =>
    sorry
  . case mpr =>
    intro H
    by_contra H
    simp [URMModel.nholds, M.V_not, M.star_star] at H


--This is totally in Mathlib somewhere but I sure can't find it
lemma impl_or_n {a b : Prop} : (a → b) ↔ (¬a ∨ b) := by
  apply Iff.intro
  . case mp =>
    contrapose!
    simp only [imp_self]
  . case mpr =>
    contrapose!
    simp only [imp_self]

-- The hereditariness condition extends from atoms to all formulas
theorem hered_all (M : RMModel) (a b : M.W) (φ : Formula):
(a ⊩ φ) -> (a ≤ᵣ b) -> b ⊩ φ := by
  intros H1 H2
  induction φ
  . case Atom n =>
    exact M.V_her n a b H1 H2
  . case Not φ ih =>
    simp [M.V_not] at *
    sorry
    -- induction φ
    -- . case Atom n =>
    --   simp_all only [M.V_not]
    --   have r : b*ᵣ ≤ᵣ a*ᵣ := M.leq_star a b H2
    --   contrapose! H1
    --   simp_all only [URMModel.nholds, not_not]
    --   exact M.V_her n (b*ᵣ) (a*ᵣ) H1 r
    -- . case Not φ ih' =>
    --   contrapose! ih'
    --   simp [M.V_not, URMModel.nholds, M.star_dneg] at H1 ih'
    --   sorry
    -- . case And φ ψ ih1' ih2' =>
    --   simp_all only [M.V_not, M.V_and, URMModel.nholds, not_and_or]
    --   cases H1
    --   . case inl C =>
    --     apply Or.inl
    --     sorry
    --   . case inr C =>
    --     apply Or.inr
    --     sorry
    -- . case Or φ ψ ih1' ih2' =>
    --   simp_all only [M.V_not, M.V_or, URMModel.nholds, not_or]
    --   apply And.intro
    --   . case left =>
    --     apply ih1'
    --     sorry
    --   . case right =>
    --     sorry
    -- . case Imp φ ψ ih1' ih2' =>
    --   simp_all only [M.V_not, URMModel.nholds]
    --   rw [M.V_imp] at *
    --   sorry
    --   sorry
  . case And φ ψ ih1 ih2 =>
    simp [M.V_and] at *;
    apply And.intro
    . exact ih1 H1.left
    . exact ih2 H1.right
  . case Or φ ψ ih1 ih2 =>
    simp [M.V_or] at *;
    cases H1
    . case inl C =>
      apply Or.inl
      exact ih1 C
    . case inr C =>
      apply Or.inr
      exact ih2 C
  . case Imp φ ψ ih1 ih2 =>
    simp only [M.V_imp φ ψ M.O] at *
    intros b' c'
    exact H1 b' c'


theorem ax1_valid : ⊨ (A →ᵣ A) := by
  intros M w
  simp [M.V_imp A A M.O]
  intros b c


-- Adding Raaa as a frame condition allows us to validate the psudo-modus ponens axiom
theorem PMP (M : RMModel) (A B : Formula) : (∀ (a : M.F.W), M.F.R a a a) -> ⊨ (A ∧ᵣ (A →ᵣ B)) →ᵣ B := by
  sorry


-- The type of proofs of a formula under Hilbert-style RL axioms
inductive Proof : Formula -> Type where
| ax1 {A} : Proof (A →ᵣ A)
| ax2 {A B} : Proof (A ∧ᵣ B →ᵣ A)
| ax3 {A B} : Proof (A ∧ᵣ B →ᵣ B)
| ax4 {A B C} : Proof ((A →ᵣ B) →ᵣ (A →ᵣ C) →ᵣ (A →ᵣ B ∧ᵣ C))
| ax5 {A B} : Proof (A →ᵣ A ∨ᵣ B)
| ax6 {A B} : Proof (B →ᵣ A ∨ᵣ B)
| ax7 {A B C} : Proof ((A →ᵣ C) →ᵣ (B →ᵣ C) →ᵣ (A ∨ᵣ B →ᵣ C))
| ax8 {A B C} : Proof (A ∧ᵣ (B ∨ᵣ C) →ᵣ (A ∧ᵣ B) ∨ᵣ (A ∧ᵣ C))
| ax9 {A} : Proof (¬ᵣ¬ᵣA →ᵣ A)
| MP {A B} : Proof A → Proof (A →ᵣ B) → Proof B
| CI {A B} : Proof A → Proof B → Proof (A ∧ᵣ B)
| DI1 {A B} : Proof (A →ᵣ B) → Proof (C →ᵣ A) → Proof (C →ᵣ B)
| DI2 {A B} : Proof (A →ᵣ B) → Proof (B →ᵣ C) → Proof (A →ᵣ C)
| CO {A B} : Proof (A →ᵣ B) → Proof (¬ᵣB →ᵣ ¬ᵣA)

def ProofOf (A : Formula) := Nonempty (Proof A)

prefix:80 "⊢ᵣ" => ProofOf
