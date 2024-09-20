

import Mathlib.Tactic.Contrapose

inductive Formula : Type where
| Atom : Nat -> Formula
| Not : Formula -> Formula
| And : Formula -> Formula -> Formula
| Or : Formula -> Formula -> Formula
| Imp : Formula -> Formula -> Formula

prefix:80 "¬ᵣ" => Formula.Not
infixr:70 "∧ᵣ" => Formula.And
infixr:65 "∨ᵣ" => Formula.Or
infixr:60 "→ᵣ" => Formula.Imp

-- Routley–Meyer frames
structure RMFrame where
  -- Worlds
  W : Type
  R : W -> W -> W → Prop
  S : W -> W    -- *
  O : W         -- 0
  -- conditions on Routley–Meyer frames
  C1 (a : W) : R O a a
  C2 (a b c : W) : R O a b → R O b c → R O a c
  C3 (a b c d : W) : R O d a -> R a b c -> R d b c
  C4 (a : W) : S (S a) = a
  C5 (a b : W) : R O a b -> R O (S b) (S a)

def Leqr {F : RMFrame} (a b : F.W) : Prop := F.R F.O a b
notation a "≤ᵣ" b => Leqr a b

-- A Routley–Meyer model is a frame along with a valuation function
-- That satisfies certain conditions
structure RMModel where
  F : RMFrame
  -- Valuation function on atoms
  VA : F.W -> Nat -> Prop -- We use a relation instead : V(w, atom) == w ∈ v(atom)
  V : F.W -> Formula -> Prop
  -- Conditions on the valuation function for compound formulas
  V_atom (n : Nat) (w : F.W) : V w (Formula.Atom n) = VA w n
  V_not (φ : Formula) (w : F.W) : V w (¬ᵣφ) = ¬V (F.S w) φ
  V_and (φ ψ : Formula) (w : F.W) : V w (φ ∧ᵣ ψ) = V w φ ∧ V w ψ
  V_or (φ ψ : Formula) (w : F.W) : V w (φ ∨ᵣ ψ) = V w φ ∨ V w ψ
  V_imp (φ ψ : Formula) (a : F.W) : V w (φ →ᵣ ψ) = ∀ (b c : F.W), F.R a b c → V b φ → V c ψ
  --Hereditariness condition on atoms
  V_hered (n : Nat) (a b : F.W) : V a (Formula.Atom n) -> (a ≤ᵣ b) -> V b (Formula.Atom n)

-- Need this helper def for the notation
def valuation (M : RMModel) (w : M.F.W) (φ : Formula) : Prop := M.V w φ
notation M ":" w "⊨" φ => valuation M w φ

def valid (φ : Formula) : Prop := ∀ (M : RMModel) (w : M.F.W), M : w ⊨ φ
notation "⊨" φ => valid φ

-- The hereditariness condition extends from atoms to all formulas
theorem hered_all (M : RMModel) (a b : M.F.W) (φ : Formula):
(M : a ⊨ φ) -> (a ≤ᵣ b) -> M : b ⊨ φ := by
intros H1 H2
induction φ
. case Atom n =>
  exact M.V_hered n a b H1 H2
. case Not φ F =>
  simp [valuation] at *;
  rw [M.V_not φ a] at H1;
  rw [M.V_not φ b]
  contrapose! H1
  sorry





-- Hopefully we can prove hereditariness condition as traditionally presented from our
-- addition of it on entails.










theorem ax1_valid : ⊨ (A →ᵣ A) := by
intros M w
simp [entails]
intros b c Rwb H
sorry


-- Adding Raaa as a frame condition allows us to validate the psudo-modus ponens axiom
theorem PMP (M : RMModel) (A B : Formula) : (∀ (a : M.F.W), M.F.R a a a) -> ⊨ (A ∧ᵣ (A →ᵣ B)) →ᵣ B := by
intros FrameCond M w
simp [entails]
intros b1 c1 Rwb1c1 H1 H2
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
