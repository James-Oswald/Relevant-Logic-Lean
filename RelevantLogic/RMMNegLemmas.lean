
import RelevantLogic.RoutlyMeyerModels

/-!
This file contains various lemmas regarding the transforming
`Formula.Not`, `URMFrame.Star`, in the presence of the `URMModel.holds`
relation. Created during the great heredity crisis.
-/

lemma RMMModel.V_ppn_nnp (M : RMModel) (φ : Formula) (w : M.W) :
(w ⊩ ¬ᵣφ) ↔ (w*ᵣ ⊮ φ) :=
  M.V_not φ w

lemma RMModel.V_npn_pnp (M : RMModel) (φ : Formula) (w : M.W) :
(w*ᵣ ⊩ ¬ᵣφ) ↔ (w ⊮ φ) := by
  apply Iff.intro
  . case mp =>
    intro H
    simp [M.V_not, M.star_star] at H
    exact H
  . case mpr =>
    intro H
    simp [M.V_not, M.star_star]
    exact H

lemma RMModel.V_nnn_ppp (M : RMModel) (φ : Formula) (w : M.W) :
(w*ᵣ ⊮ ¬ᵣφ) ↔ (w ⊩ φ) := by
  apply Iff.intro
  . case mp =>
    intro H
    simp [URMModel.nholds, M.V_not, M.star_star] at H
    exact H
  . case mpr =>
    intro H
    simp [URMModel.nholds, M.V_not, M.star_star]
    exact H

lemma RMModel.V_pnn_npp (M : RMModel) (φ : Formula) (w : M.W) :
(w ⊮ ¬ᵣφ) ↔ (w*ᵣ ⊩ φ) := by
  apply Iff.intro
  . case mp =>
    intro H
    simp [URMModel.nholds, M.V_not, M.star_star] at H
    exact H
  . case mpr =>
    intro H
    simp [URMModel.nholds, M.V_not, M.star_star]
    exact H
