
import RelevantLogic.RoutlyMeyerModels
import RelevantLogic.HilbertProofTheory

theorem RM_complete : ⊨ᴮ ϕ → ⊢ᴮ ϕ := by
  contrapose!
  intro H
  simp [valid]
  induction ϕ
  . case Atom n =>
    --Trivial to construct a model where this fails
    sorry
  . case Not ϕ ih =>
    -- "There exists a model where ¬ϕ is does not hold at O"
    -- Can easily construct a model for this
    sorry
  . case And ϕ ψ ih1 ih2 =>
    simp only [adj_bi, not_and_or] at H
    cases H
    . case inl l =>
      have ⟨w, H2⟩ := ih1 l
      exists w
      simp only [w.V_and, not_and]
      intro C
      contradiction
    . case inr r =>
      have ⟨w, H2⟩ := ih2 r
      exists w
      simp only [w.V_and, not_and']
      intro C
      contradiction
  . case Imp ϕ ψ ih1 ih2 =>
    sorry

-- theorem RM_complete : ⊨ᴮ ϕ → ⊢ᴮ ϕ := by
--   intro H
--   simp only [valid] at H
--   induction ϕ
--   . case Atom n =>
