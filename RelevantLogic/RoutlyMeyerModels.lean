
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Contrapose
import Mathlib.Tactic.Basic
import Aesop

import RelevantLogic.Formula

/-! # Routley–Meyer Models

This file contains definitions for baisc Routley-Meyer Frames
and Models for Relevant Logic, as well as some basic theorems
about them.
-/

/-- Unconditioned Routley–Meyer frames -/
structure URMFrame where
  /-- "Set" of Worlds -/
  W : Type
  /-- Accessibility Relation -/
  R : W -> W -> W → Prop
  /-- Star Function, * -/
  S : W -> W
  /-- Distinguished World, 0 -/
  O : W

-- TODO: This dosen't seem to work in many places
/-- The numeric literal "0" can be coerced into the designated world F.O -/
instance {F : URMFrame} : OfNat F.W 0 := ⟨F.O⟩
example {F : URMFrame} : F.W := 0

/-- The *ᵣ operator maps worlds to worlds -/
def URMFrame.Star {F : URMFrame} (a : F.W) : F.W := F.S a
postfix:80 "*ᵣ"  => URMFrame.Star

/-- The containment relation, w1 ≤ᵣ w2 -/
def URMFrame.Contains {F : URMFrame} (a b : F.W) : Prop := F.R 0 a b
infix:70 " ≤ᵣ " => URMFrame.Contains

def URMFrame.Related {F : URMFrame} (a b c : F.W) : Prop := F.R a b c
notation "Rᵣ" a:max b:max c:max  => URMFrame.Related a b c

/-- Conditioned Routley–Meyer frames -/
structure RMFrame extends URMFrame where
  con_rfl   (a : W)       : a ≤ᵣ a
  con_trans (a b c : W)   : a ≤ᵣ b → b ≤ᵣ c → a ≤ᵣ c
  con_?     (a b c d : W) : d ≤ᵣ a -> Rᵣ a b c -> Rᵣ d b c
  star_star (a : W)       : a*ᵣ*ᵣ = a
  con_star  (a b : W)     : a ≤ᵣ b -> b*ᵣ ≤ᵣ a*ᵣ


lemma RMFrame.eq_imp_con (F : RMFrame) {a b : F.W} :
a = b -> a ≤ᵣ b := by
  intro H
  simp only [H, F.con_rfl b]

lemma RMFrame.eq_imp_con' (F : RMFrame) {a b : F.W} :
a = b -> b ≤ᵣ a := by
  intro H
  simp only [H, F.con_rfl b]

-- lemma RMFrame.con_eq (F : RMFrame) {a b : F.W} :
-- a ≤ᵣ b -> b ≤ᵣ a -> a = b := by
--   sorry

/--
Version of `RMFrame.con_?` that infers worlds from hypotheses
via type unification, very useful for actually proving things.
-/
lemma RMFrame.con_?' (F : RMFrame) {a b c d: F.W} :
d ≤ᵣ a -> F.R a b c -> Rᵣ d b c := by
  intros H1 H2
  exact F.con_? a b c d H1 H2

/-- An Unconditioned Routley–Meyer model
   is a frame along with a valuation function -/
structure URMModel extends RMFrame where
  -- Valuation function
  V : W -> Formula -> Prop

/-- A world `URMFrame.W` w "makes true" a `Formula` ϕ (w ⊩ ϕ) iff its
    the valuation function `URMModel.V` makes true ϕ at w. This is also
    read "ϕ holds at w" or "w forces ϕ" -/
def URMModel.holds {M : URMModel} (w : M.W) (ϕ : Formula) : Prop := M.V w ϕ
infix:50 " ⊩ " => URMModel.holds
def URMModel.nholds {M : URMModel} (w : M.W) (φ : Formula) : Prop := ¬(w ⊩ φ)
infix:50 " ⊮ " => URMModel.nholds

/-- Conditioned Routley–Meyer models -/
structure RMModel extends URMModel where
  -- Basic Conditions
  V_not (φ : Formula)   (w : W) :    (w ⊩ ¬ᵣφ) ↔ (w*ᵣ ⊮ φ)
  V_and (φ ψ : Formula) (w : W) : (w ⊩ φ ∧ᵣ ψ) ↔ (w ⊩ φ) ∧ (w ⊩ ψ)
  V_imp (φ ψ : Formula) (a : W) : (a ⊩ φ →ᵣ ψ) ↔ ∀ b c, (R a b c ∧ b ⊩ φ) → (c ⊩ ψ)
  -- Hereditariness on atoms condition
  V_atomic_heredity (n : Nat) (a b : W) : (a ⊩ n) → (a ≤ᵣ b) → (b ⊩ n)

/-- A `Formula` ϕ is valid (⊨ᴮ ϕ) iff it holds at every world `URMFrame.W`
    in every `RMModel` -/
def valid (ϕ : Formula) : Prop := ∀ (M : RMModel), M.O ⊩ ϕ
prefix:50 "⊨ᴮ " => valid

/-- The hereditariness condition extends from atoms to all formulas -/
theorem RMModel.heredity (M : RMModel) (a b : M.W) (φ : Formula):
(a ⊩ φ) -> (a ≤ᵣ b) -> b ⊩ φ := by
  intros H1 H2
  induction φ generalizing a b
  . case Atom n =>
    exact M.V_atomic_heredity n a b H1 H2
  . case Not φ ih =>
    contrapose! H1
    simp_all only [M.V_not, URMModel.nholds, not_not]
    exact ih (b*ᵣ) (a*ᵣ) H1 (M.con_star a b H2)
  . case And φ ψ ih1 ih2 =>
    simp_all only [M.V_and]
    exact And.intro (ih1 a b H1.left H2) (ih2 a b H1.right H2)
  . case Imp φ ψ _ _ =>
    simp_all only [M.V_imp φ ψ]
    intros w1 w2 C
    exact H1 w1 w2 (And.intro (M.con_? b w1 w2 a H2 C.left) C.right)

/--
The semantics of or lines up as expected with respect to its definition
in terms of not and and
-/
theorem RMModel.V_or (M : RMModel) (φ ψ : Formula) (w : M.W) :
(w ⊩ φ ∨ᵣ ψ) ↔ (w ⊩ φ) ∨ (w ⊩ ψ) := by
  apply Iff.intro
  . case mp =>
    intro H
    simp only [Formula.Or, M.V_not, URMModel.nholds, M.V_and, M.star_star] at H
    exact or_iff_not_and_not.mpr H
  . case mpr =>
    intro H
    simp only [Formula.Or, M.V_not, URMModel.nholds, M.V_and, M.star_star]
    exact or_iff_not_and_not.mp H

/--
We have this theorem but fusion in B is not nice. Actually,
We can't even define fusion in B, probably... We require
it is impossible to prove the nice permuted semantics more
commonly used i.e.
(c ⊩ φ ∘ᵣ ψ) ↔ ∃ a b, M.R a b c ∧ a ⊩ φ ∧ b*ᵣ ⊩ ψ
-/
lemma RModel.V_fusion (M : RMModel) (φ ψ : Formula) (c : M.W) :
(c ⊩ φ ∘ᵣ ψ) ↔ ∃ a b, M.R (c*ᵣ) a b ∧ a ⊩ φ ∧ b*ᵣ ⊩ ψ := by
  simp [Formula.Fusion, M.V_not, URMModel.nholds, M.V_imp, and_imp, not_forall,
    Classical.not_imp, not_not]
