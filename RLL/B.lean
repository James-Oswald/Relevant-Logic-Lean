
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

-- A Routley–Meyer model is a frame along with a valuation function
structure RMModel where
  F : RMFrame
  V : Nat → F.W -> Prop -- We use a relation instead : V(atom, w) == w ∈ v(atom)


def entails (M : RMModel) (a : M.F.W) : Formula -> Prop
| Formula.Atom n => M.V n a
| Formula.Not φ => ¬entails M (M.F.S a) φ
| Formula.And φ ψ => entails M a φ ∧ entails M a ψ
| Formula.Or φ ψ => entails M a φ ∨ entails M a ψ
| Formula.Imp φ ψ => ∀ (b c : M.F.W), M.F.R a b c → entails M b φ → entails M c ψ

notation M ":" w "⊨" φ => entails M w φ

def valid (φ : Formula) : Prop := ∀ (M : RMModel) (w : M.F.W), M : w ⊨ φ

notation "⊨" φ => valid φ


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
