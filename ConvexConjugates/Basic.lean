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
-- `v` is a subgradient of `f` at `x` if `∀ y, ⟪v, y - x⟫ ≤ f(y) - f(x)`
def IsSubgradient (v x : E) : Prop := ∀ y, ⟪v, y - x⟫ ≤ f y - f x

-- The subdifferential of `f` at `x` is the set of all subgradients of `f` at `x`
def subdifferential (x : E) : Set E := {v : E | IsSubgradient f v x}

-- Notation for the subdifferential: `∂f x`
local prefix:max "∂" => subdifferential

-- `v` is a subgradient of `f` at `x` iff `v` is in the subdifferential of `f` at `x`
theorem mem_subdifferential : IsSubgradient f v x ↔ v ∈ ∂f x := ⟨id, id⟩

-- Helper while trying to figure out this mess
-- The inner product coerced to EReal can be split across subtraction
lemma EReal.inner_sub_right' (v x y : E) : (⟪v, y - x⟫ : EReal) = ⟪v, y⟫ - ⟪v, x⟫ := by
  rw [inner_sub_right, EReal.coe_sub]

-- DRAFT Trying to break it down into something more manageable first
-- h1 is unused
theorem some_name (v : E) (x : dom f) (h1 : IsProper f) (h2 : v ∈ ∂f x) : f x + f∗ v ≤ ⟪v,x⟫ := by
  rw[← mem_subdifferential] at h2
  unfold IsSubgradient at h2
  rw[add_comm]
  -- Move f x to the other side of the inequality since f x ≠ ⊥ and ⟪v,x⟫ ≠ ⊤
  rw [← EReal.le_sub_iff_add_le (Or.inl x.2.2) (Or.inr (EReal.coe_ne_top _))]
  -- Change the goal to a universal quantifier over y ∈ E
  apply iSup_le
  -- Assume y ∈ E is arbitrary. We need to show that ⟪v,y-x⟫ ≤ f y - f x
  intro y
  -- Replace universal quantifier with a specific y
  specialize h2 y
  -- f(y) can be -∞, +∞, or a real number. Split into cases
  by_cases hy : f y = ⊥
  · -- Case 1: f(y) = ⊥
    -- Transform goal to false
    exfalso
    -- ⟪v,y-x⟫ ≤ ⊥ - f x → ⟪v,y-x⟫ ≤ ⊥ → ⟪v, y-x⟫ = ⊥
    rw [hy, EReal.bot_sub, le_bot_iff] at h2
    -- show that ⟪v,y-x⟫ ≠ ⊥
    have h3 : (⟪v,y - x⟫ : EReal) ≠ ⊥ := by
      exact EReal.coe_ne_bot (inner ℝ v (y - ↑x))
    contradiction
  · -- Case 2: f(y) ≠ ⊥
    -- splits into two further cases: f(y) = ⊤ or f(y) ∈ ℝ
    by_cases hy' : f y = ⊤
    · -- Subcase 2.1: f(y) = ⊤
      rw [hy']
      -- ⟪v,y⟫ - ⊤ = ⊥ and ⊥ ≤ ⟪v,x⟫ - f x is always true
      simp only [EReal.sub_top, bot_le]
    · -- Subcase 2.2: f(y) ∈ ℝ
      -- move f y to the other side of the inequality since f y ≠ ⊥ and f y ≠ ⊤
      rw [EReal.sub_le_iff_le_add (Or.inl hy) (Or.inl hy')]
      -- Split the inner product: ⟪v,y-x⟫ = ⟪v,y⟫ - ⟪v,x⟫
      rw [EReal.inner_sub_right'] at h2
      -- move ⟪v,x⟫ to the other side of the inequality and infer that ⟪v,x⟫ ≠ ⊥ and ⟪v,x⟫ ≠ ⊤
      -- Might be clearer to define lemmas ⟪v,x⟫ ≠ ⊥ and ⟪v,x⟫ ≠ ⊤ rather than inferring
      rw [EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _))] at h2
      -- Swap the order of the addition on the right hand side to match the goal
      rw[add_comm] at h2
      -- Just moving things around to make it match h2 (there must be a cleaner way to do it)
      rw[sub_eq_add_neg]
      rw [add_right_comm (↑(inner ℝ v ↑x)) (-f ↑x) (f y)]
      rw [@AddSemigroup.add_assoc]
      exact h2







-- The epigraph of `f`
def epi : Set (E × ℝ) := {p | f p.1 ≤ p.2}

#min_imports
