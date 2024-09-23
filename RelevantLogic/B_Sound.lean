
import RelevantLogic.RoutlyMeyer

theorem ax1_valid : ⊨ᴮ (A →ᵣ A) := by
  intros M w
  simp [M.V_imp A A M.O]
  intros b c H1 H2
  exact M.her b c A H2 H1

theorem ax2_valid : ⊨ (A ∧ᵣ B →ᵣ A) := by
  intros M w
  simp only [M.V_imp (A ∧ᵣ B) A M.O, and_imp]
  intros b c H1 H2
  simp only [M.V_and] at H2
  exact M.her b c A H2.left H1

theorem ax3_valid : ⊨ (A ∧ᵣ B →ᵣ B) := by
  intros M w
  simp [M.V_imp (A ∧ᵣ B) B M.O]
  intros b c H1 H2
  simp [M.V_and] at H2
  exact M.her b c B H2.right H1

theorem ax4_valid : ⊨ ((A →ᵣ B) →ᵣ (A →ᵣ C) →ᵣ (A →ᵣ B ∧ᵣ C)) := by
  intros M w
  simp only [M.V_imp (A →ᵣ B) ((A →ᵣ C) →ᵣ (A →ᵣ B ∧ᵣ C)) M.O, and_imp]
  intro w1 w2 _ w1AB
  simp only [M.V_imp (A →ᵣ C) (A →ᵣ B ∧ᵣ C) M.O, and_imp]
  intro w3 w4 _ w3AC
  simp only [M.V_imp A (B ∧ᵣ C) M.O, and_imp]
  intro w5 w6 Hw56 w5A
  simp [M.V_imp A B M.O] at w1AB
  simp [M.V_imp A C M.O] at w3AC
  simp [M.V_and]
  apply And.intro
  . case left =>
    apply w1AB w5 w6
    exact Hw56
    exact w5A
  . case right =>
    apply w3AC w5 w6
    exact Hw56
    exact w5A

theorem ax5_valid : ⊨ (A →ᵣ A ∨ᵣ B) := by
  intros M w
  simp [M.V_imp A (A ∨ᵣ B) M.O]
  intros b c H1 H2
  simp [M.V_or]
  apply Or.inl
  exact M.her b c A H2 H1

theorem ax6_valid : ⊨ (B →ᵣ A ∨ᵣ B) := by
  intros M w
  simp [M.V_imp B (A ∨ᵣ B) M.O]
  intros b c H1 H2
  simp [M.V_or]
  apply Or.inr
  exact M.her b c B H2 H1

theorem ax7_valid : ⊨ ((A →ᵣ C) →ᵣ (B →ᵣ C) →ᵣ (A ∨ᵣ B →ᵣ C)) := by
  intros M w
  simp only [M.V_imp (A →ᵣ C) ((B →ᵣ C) →ᵣ (A ∨ᵣ B →ᵣ C)) M.O, and_imp]
  intro w1 w2 _ w1AC
  simp only [M.V_imp (B →ᵣ C) (A ∨ᵣ B →ᵣ C) M.O, and_imp]
  intro w3 w4 _ w3BC
  simp only [M.V_imp (A ∨ᵣ B) C M.O, and_imp]
  intro w5 w6 Hw56 Hw5AB
  simp [M.V_imp A C M.O] at w1AC
  simp [M.V_imp B C M.O] at w3BC
  simp [M.V_or] at Hw5AB
  cases Hw5AB
  . case inl C =>
    apply w1AC w5 w6
    exact Hw56
    exact C
  . case inr C =>
    apply w3BC w5 w6
    exact Hw56
    exact C

theorem ax8_valid : ⊨ (A ∧ᵣ (B ∨ᵣ C) →ᵣ (A ∧ᵣ B) ∨ᵣ (A ∧ᵣ C)) := by
  intros M w
  simp only [M.V_imp (A ∧ᵣ (B ∨ᵣ C)) ((A ∧ᵣ B) ∨ᵣ (A ∧ᵣ C)) M.O, and_imp]
  intro w1 w2 Hw12 w1ABC
  simp only [M.V_and, M.V_or] at w1ABC
  simp only [M.V_or, M.V_and]
  cases w1ABC.right
  . case inl Hw1B =>
    apply Or.inl
    apply And.intro
    . exact M.her w1 w2 A w1ABC.left Hw12
    . exact M.her w1 w2 B Hw1B Hw12
  . case inr Hw1C =>
    apply Or.inr
    apply And.intro
    . exact M.her w1 w2 A w1ABC.left Hw12
    . exact M.her w1 w2 C Hw1C Hw12

theorem ax9_valid : ⊨ (¬ᵣ¬ᵣA →ᵣ A) := by
  intros M w
  simp [M.V_imp (¬ᵣ¬ᵣA) A M.O]
  intros b c H1 H2
  simp [M.V_not, M.V_not''] at H2
  exact M.her b c A H2 H1

theorem mp_valid : (⊨ A) → (⊨ A →ᵣ B) → (⊨ B) := by
  intros H1 H2 M w
  simp_all only [valid]
  simp [M.V_imp A B M.O] at H2
  have H1' := H1 M w
  have H2' := H2 M w
  exact H2' w w (M.leq_symm w) H1'

theorem ci_valid : (⊨ A) → (⊨ B) → (⊨ A ∧ᵣ B) := by
  intros H1 H2 M w
  simp_all only [valid]
  simp [M.V_and]
  apply And.intro
  . exact H1 M w
  . exact H2 M w

theorem di1_valid : (⊨ A →ᵣ B) → (⊨ (C →ᵣ A) →ᵣ (C →ᵣ B)) := by
  intros H1 M w1
  simp_all only [valid]
  simp only [M.V_imp (C →ᵣ A) (C →ᵣ B) M.O, and_imp]
  intros w2 w3 H2 H3
  have H1' := H1 M w2
  simp [M.V_imp A B M.O] at H1'
  simp [M.V_imp C A M.O] at H3
  simp [M.V_imp C B M.O]
  intro w4 w5 H4 H5
  apply H1' w4 w5
  simp_all only
  apply (H3 w1 w4)
  sorry

theorem di2_valid : (⊨ A →ᵣ B) → (⊨ (B →ᵣ C) →ᵣ (A →ᵣ C)) := by
  sorry

theorem co_valid : (⊨ A →ᵣ B) → (⊨ ¬ᵣB →ᵣ ¬ᵣA) := by
  sorry


theorem RM_sound (A : Formula) : ⊢ᵣ A → ⊨ A := by
  intros H
  cases H
  . case intro val =>
    induction val
    . case ax1 => exact ax1_valid
    . case ax2 => exact ax2_valid
    . case ax3 => exact ax3_valid
    . case ax4 => exact ax4_valid
    . case ax5 => exact ax5_valid
    . case ax6 => exact ax6_valid
    . case ax7 => exact ax7_valid
    . case ax8 => exact ax8_valid
    . case ax9 => exact ax9_valid
    . case MP _ _ ih1 ih2 => exact mp_valid (ih1) (ih2)
    . case CI _ _ ih1 ih2 => exact ci_valid (ih1) (ih2)
    . case DI1 _ ih1 => exact di1_valid (ih1)
    . case DI2 _ ih1 => exact di2_valid (ih1)
    . case CO _ ih1 => exact co_valid (ih1)
