import Mathlib.Analysis.InnerProductSpace.Defs

set_option linter.style.header false

local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (f : E → EReal)

/-- The Fenchel conjugate of `f : E → EReal`. -/
noncomputable def fenchelConjugate (v : E) : EReal :=
  ⨆ x : E, ⟪v, x⟫ - f x

/-- The effective domain of `f`. -/
def dom : Set E := {x : E | f x < ⊤}

/-- The epigraph of `f`. -/
def epigraph : Set (E × ℝ) := {p | f p.1 ≤ p.2}
