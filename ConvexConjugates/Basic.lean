import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Data.EReal.Basic

set_option linter.style.header false

open InnerProductSpace

local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {f : E → EReal} {x : E} {s : Set E}

/-- The Fenchel conjugate of `f : E → EReal`. -/
noncomputable def fenchelConjugate (f : E → EReal) (v : E) : EReal :=
  ⨆ x : E, ⟪v, x⟫ - f x

/-- The effective domain of `f`. -/
def dom (f : E → EReal) : Set E := {x : E | f x < ⊤}
