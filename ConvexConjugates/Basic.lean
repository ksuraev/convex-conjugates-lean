import Mathlib.Analysis.InnerProductSpace.Defs

set_option linter.style.header false

local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (f : E → EReal)

/-- The effective domain of `f`. -/
def dom : Set E := {x : E | f x < ⊤ ∧ f x > ⊥}

/-- The epigraph of `f`. -/
def epigraph : Set (E × ℝ) := {p | f p.1 ≤ p.2}

/-- The Fenchel conjugate of `f : E → EReal`. -/
noncomputable def fenchelConjugate (v : E) : EReal :=
  ⨆ x : E, ⟪v, x⟫ - f x

local postfix:max "∗" => fenchelConjugate

def IsProper : Prop := dom f ≠ ∅

-- not great name but will do for now
lemma fenchelConjugate_not_neg_inf (v : E) : IsProper f → f∗ v ≠ ⊥ := by
  intro h
  obtain ⟨x, ht, hb⟩ := Set.nonempty_iff_ne_empty.mpr h
  rw [lt_top_iff_ne_top] at ht
  rw [gt_iff_lt, bot_lt_iff_ne_bot] at hb
  unfold fenchelConjugate
  apply ne_of_gt
  rw [@bot_lt_iSup]
  use x
  rw [EReal.lt_sub_iff_add_lt (Or.inl hb) (Or.inl ht)]
  exact compareOfLessAndEq_eq_lt.mp rfl



theorem fenchel_young (v x : E) (h1 : f x ≠ ⊥) (h2 : f x ≠ ⊤) : ⟪v,x⟫ ≤ f x + f∗ v := by
  have h : f∗ v ≥ ⟪v,x⟫ - f x := by
    exact le_iSup_iff.mpr fun b a ↦ a x
  rw[ge_iff_le] at h
  rw[EReal.sub_le_iff_le_add (Or.inl h1) (Or.inl h2)] at h
  rw[add_comm]
  exact h

#min_imports
