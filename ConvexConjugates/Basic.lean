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

local postfix:max "∗" => fenchelConjugate -- https://lean-lang.org/doc/reference/latest/Notations-and-Macros/Custom-Operators/#operators

theorem fenchel_young (v x : E) (h3 : f x ≠ ⊥) (h4 : f x ≠ ⊤) : ⟪v,x⟫ ≤ f x + f∗ v := by
  have h : f∗ v ≥ ⟪v,x⟫ - f x := by
    exact le_iSup_iff.mpr fun b a ↦ a x
  rw[ge_iff_le] at h
  rw[EReal.sub_le_iff_le_add (Or.inl h3) (Or.inl h4)] at h
  rw[add_comm]
  exact h

#min_imports
