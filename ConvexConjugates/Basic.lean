import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.Basic

set_option linter.style.header false

/-!
# Convex Conjugates

## TODO
- Replace the definition of `fenchelConjugate` to apply on the dual space of `E`
- Organise things better e.g. structure for EReal function, sections
- Figure out naming conventions
-/

local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (f : E → EReal)

-- The effective domain of `f`
def dom : Set E := {x : E | f x ≠ ⊤ ∧ f x ≠ ⊥}

-- A function `f` is proper if its domain is nonempty
def IsProper : Prop := dom f ≠ ∅

-- The Fenchel conjugate of `f : E → EReal`: f∗(v) = sup_{x ∈ E} ⟨v,x⟩-f(x)
noncomputable def fenchelConjugate (v : E) : EReal := ⨆ x : E, ⟪v, x⟫ - f x

-- Notation for the Fenchel conjugate: `f∗`
local postfix:max "∗" => fenchelConjugate

-- If a function `f` is proper, then its Fenchel conjugate is not `-∞`
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

-- Fenchel-Young inequality for a proper function `f : E → EReal`
theorem fenchel_young (v x : E) (h1 : f x ≠ ⊥) (h2 : IsProper f) : ⟪v,x⟫ ≤ f x + f∗ v := by
  have h3 : f∗ v ≥ ⟪v,x⟫ - f x := by
    exact le_iSup_iff.mpr fun b a ↦ a x
  rw[ge_iff_le] at h3
  rw [EReal.sub_le_iff_le_add (Or.inl h1) (Or.inr (fenchelConjugate_ne_bot f v h2))] at h3
  rw[add_comm]
  exact h3

-- The Fenchel biconjugate of `f : E → EReal`: f∗∗(x) = sup_{v ∈ E} ⟨v,x⟩-f∗(v)
noncomputable def fenchelBiconjugate (x : E) : EReal := ⨆ v : E, ⟪v, x⟫ - f∗ v

-- Notation for the Fenchel biconjugate: `f∗∗`
local postfix:max "∗∗" => fenchelBiconjugate

-- The Fenchel biconjugate of a proper function `f : E → EReal` is less than or equal to `f`
-- Assuming we make the same assumptions as in the Fenchel-Young inequality?
theorem fenchelBiconjugate_le (x : E) (h1 : f x ≠ ⊥) (h2 : IsProper f) : f∗∗ x ≤ f x := by
  unfold fenchelBiconjugate
  apply iSup_le
  intro v
  apply EReal.sub_le_of_le_add
  exact fenchel_young f v x h1 h2

-- Based on https://github.com/optsuite/optlib/blob/main/Optlib/Convex/Subgradient.lean
def IsSubgradient (v x : E) : Prop := ∀ y, ⟪v, y - x⟫ ≤ f y - f x

def subdifferential (x : E) : Set E := {v : E | IsSubgradient f v x}

local prefix:max "∂" => subdifferential

theorem mem_subdifferential : IsSubgradient f v x ↔ v ∈ ∂f x := ⟨id, id⟩

-- Helper while trying to figure out this mess
lemma EReal.inner_sub_right' (v x y : E) : (⟪v, y - x⟫ : EReal) = ⟪v, y⟫ - ⟪v, x⟫ := by
  rw [inner_sub_right, EReal.coe_sub]

-- Trying to break it down into something more manageable
theorem some_name (v : E) (x : dom f) (h1 : IsProper f) (h2 : v ∈ ∂f x) : f x + f∗ v ≤ ⟪v,x⟫ := by
  rw[← mem_subdifferential] at h2
  rw[add_comm]
  rw [← EReal.le_sub_iff_add_le (Or.inl x.2.2) (Or.inr (by simp))]
  apply iSup_le
  intro y
  unfold IsSubgradient at h2
  specialize h2 y
  sorry
  -- It seems impossible to move anything around because I think f(y) can be ∞ or -∞.
  -- Probably need to split into cases or I've done something wrong








-- The epigraph of `f`
def epi : Set (E × ℝ) := {p | f p.1 ≤ p.2}

#min_imports
