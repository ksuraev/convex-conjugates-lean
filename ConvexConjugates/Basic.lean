import Mathlib.Analysis.InnerProductSpace.Defs

set_option linter.style.header false

/-!
# Convex Conjugates

## TODO
- Replace the definition of `fenchelConjugate` to apply on the dual space of `E`
- Organise things better e.g. structure for EReal function, sections
-/

local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (f : E → EReal)

/-- The Fenchel conjugate of `f : E → EReal`. -/
noncomputable def fenchelConjugate (v : E) : EReal := ⨆ x : E, ⟪v, x⟫ - f x

/-- Notation for the Fenchel conjugate: `f∗`. -/
local postfix:max "∗" => fenchelConjugate

/-- The effective domain of `f`. -/
def dom : Set E := {x : E | f x ≠ ⊤ ∧ f x ≠ ⊥}

/-- The epigraph of `f`. -/
def epi : Set (E × ℝ) := {p | f p.1 ≤ p.2}

/-- A function `f` is proper if its domain is nonempty. -/
def IsProper : Prop := dom f ≠ ∅

/-- If a function `f` is proper, then its Fenchel conjugate is not `-∞`. -/
lemma fenchelConjugate_ne_bot (v : E) : IsProper f → f∗ v ≠ ⊥ := by
  intro h
  obtain ⟨x, ht, hb⟩ := Set.nonempty_iff_ne_empty.mpr h
  have h1 : (f x).toReal = f x := EReal.coe_toReal ht hb
  unfold fenchelConjugate
  apply ne_of_gt
  rw [bot_lt_iSup]
  use x
  rw [← h1]
  exact compareOfLessAndEq_eq_lt.mp rfl

/-- Fenchel-Young inequality for a proper function `f : E → EReal`. -/
theorem fenchel_young (v x : E) (h1 : f x ≠ ⊥) (h2 : IsProper f) : ⟪v,x⟫ ≤ f x + f∗ v := by
  have h3 : f∗ v ≥ ⟪v,x⟫ - f x := by
    exact le_iSup_iff.mpr fun b a ↦ a x
  rw[ge_iff_le] at h3
  rw [EReal.sub_le_iff_le_add (Or.inl h1) (Or.inr (fenchelConjugate_ne_bot f v h2))] at h3
  rw[add_comm]
  exact h3

#min_imports
