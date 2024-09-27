
import Mathlib.Tactic.ByContra
import Aesop

import RelevantLogic.RoutlyMeyerModels
import RelevantLogic.HilbertProofTheory
import RelevantLogic.RMMNegLemmas

lemma id_valid : ⊨ᴮ (ϕ →ᵣ ϕ) :=
  --A fun proof by construction
  λ M => (M.V_imp ϕ ϕ M.O).mpr
    (λ w1 w2 ⟨H1, H2⟩ => M.heredity w1 w2 ϕ H2 H1)

lemma and_elim_left_valid : ⊨ᴮ (A ∧ᵣ B →ᵣ A) := by
  intro M
  simp only [M.V_imp, and_imp]
  intros b c H1 H2
  simp only [M.V_and] at H2
  exact M.heredity b c A H2.left H1

lemma and_elim_right_valid : ⊨ᴮ (A ∧ᵣ B →ᵣ B) := by
  intro M
  simp only [M.V_imp, and_imp]
  intros b c H1 H2
  simp [M.V_and] at H2
  exact M.heredity b c B H2.right H1

lemma and_intro_valid : ⊨ᴮ ((A →ᵣ B) ∧ᵣ (A →ᵣ C) →ᵣ (A →ᵣ B ∧ᵣ C)) := by
  intros M
  simp only [M.V_imp, and_imp, M.V_and]
  intros w1 w2 R012 H1AB H1AC w3 w4 R234 w3A
  have R134 := M.con_?' R012 R234
  apply And.intro
  . case left =>
    exact H1AB w3 w4 R134 w3A
  . case right =>
    exact H1AC w3 w4 R134 w3A

theorem or_intro_left_valid : ⊨ᴮ (A →ᵣ A ∨ᵣ B) := by
  intros M
  simp only [M.V_imp, M.V_or, and_imp]
  intros b c H1 H2
  apply Or.inl
  exact M.heredity b c A H2 H1

theorem or_intro_right_valid : ⊨ᴮ (B →ᵣ A ∨ᵣ B) := by
  intros M
  simp only [M.V_imp, M.V_or, and_imp]
  intros b c H1 H2
  apply Or.inr
  exact M.heredity b c B H2 H1

theorem or_elim_valid : ⊨ᴮ ((A →ᵣ C) ∧ᵣ (B →ᵣ C) →ᵣ (A ∨ᵣ B →ᵣ C)) := by
  intros M
  simp only [M.V_imp, and_imp, M.V_or, M.V_and]
  intros w1 w2 R012 H1AC H1BC w3 w4 R234 w3AoB
  have R134 := M.con_?' R012 R234
  cases w3AoB
  . case inl w3A =>
    exact H1AC w3 w4 R134 w3A
  . case inr w3B =>
    exact H1BC w3 w4 R134 w3B

theorem and_or_valid : ⊨ᴮ (A ∧ᵣ (B ∨ᵣ C) →ᵣ (A ∧ᵣ B) ∨ᵣ (A ∧ᵣ C)) := by
  intro M
  simp only [M.V_imp, M.V_or, M.V_and]
  intros w1 w2 H
  have ⟨R012, w1A, w1Bow1C⟩ := H
  cases w1Bow1C
  . case inl H2 =>
    exact Or.inl (And.intro (M.heredity w1 w2 A w1A R012)
     (M.heredity w1 w2 B H2 R012))
  . case inr H2 =>
    exact Or.inr (And.intro (M.heredity w1 w2 A w1A R012)
     (M.heredity w1 w2 C H2 R012))

theorem dne_valid : ⊨ᴮ (¬ᵣ¬ᵣA →ᵣ A) := by
  intro M
  simp only [M.V_imp, and_imp, M.V_not, M.V_nnn_ppp]
  intros b c H1 H2
  exact M.heredity b c A H2 H1

theorem mp_valid : (⊨ᴮ A) → (⊨ᴮ A →ᵣ B) → (⊨ᴮ B) := by
  intros H1 H2 M
  simp_all only [valid]
  have H1' := H1 M
  have H2' := H2 M
  simp [M.V_imp] at H2'
  exact H2' 0 0 (M.con_rfl 0) H1'

theorem adj_valid : (⊨ᴮ A) → (⊨ᴮ B) → (⊨ᴮ A ∧ᵣ B) := by
  intros H1 H2 M
  simp_all only [valid, M.V_and, and_self]

theorem pre_valid : (⊨ᴮ A →ᵣ B) → (⊨ᴮ (C →ᵣ A) →ᵣ (C →ᵣ B)) := by
  intros H M
  have H0AB := H M
  simp_all only [M.V_imp]
  intros w1 w2 R012_H1CA w3 w4 R234_H3C
  have ⟨R012, H1CA⟩ := R012_H1CA
  have ⟨R234, H3C⟩ := R234_H3C
  clear R012_H1CA R234_H3C
  have R134 := M.con_?' R012 R234
  have w4A := H1CA w3 w4 (And.intro R134 H3C)
  apply H0AB w4 w4
  exact ⟨M.con_rfl w4, w4A⟩

theorem suf_valid : (⊨ᴮ A →ᵣ B) → (⊨ᴮ (B →ᵣ C) →ᵣ (A →ᵣ C)) := by
  intros H M
  have H0AB := H M
  simp_all only [M.V_imp]
  intros w1 w2 R012_H1BC w3 w4 R234_H3A
  have ⟨R012, H1BC⟩ := R012_H1BC
  have ⟨R234, H3A⟩ := R234_H3A
  clear R012_H1BC R234_H3A
  have R134 := M.con_?' R012 R234
  apply H1BC w3 w4
  apply And.intro
  . case left =>
    exact R134
  . case right =>
    apply H0AB w3 w3 ⟨M.con_rfl w3, H3A⟩

theorem rcont_valid : (⊨ᴮ A →ᵣ B) → (⊨ᴮ ¬ᵣB →ᵣ ¬ᵣA) := by
  intros H M
  have H' := H M
  simp_all only [M.V_imp, and_imp, M.V_not]
  intros w1 w2 R012 H1nB
  contrapose! H1nB
  simp_all only [URMModel.nholds, not_not]
  exact H' (w2*ᵣ) (w1*ᵣ) (M.con_star w1 w2 R012) H1nB

theorem RM_sound (ϕ : Formula) : ⊢ᴮ ϕ → ⊨ᴮ ϕ := by
  intros H
  cases H
  . case intro val =>
    induction val
    . case id => exact id_valid
    . case and_elim_left => exact and_elim_left_valid
    . case and_elim_right => exact and_elim_right_valid
    . case and_intro => exact and_intro_valid
    . case or_intro_left => exact or_intro_left_valid
    . case or_intro_right => exact or_intro_right_valid
    . case or_elim => exact or_elim_valid
    . case and_or => exact and_or_valid
    . case dne => exact dne_valid
    . case mp ih1 ih2 => exact mp_valid ih1 ih2
    . case adj ih1 ih2 => exact adj_valid ih1 ih2
    . case pre ih => exact pre_valid ih
    . case suf ih => exact suf_valid ih
    . case rcont ih => exact rcont_valid ih
