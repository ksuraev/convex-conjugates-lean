import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.Basic

set_option linter.style.header false
set_option linter.style.longLine false
set_option pp.parens true

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
  -- Assume that the function `f` is proper
  intro h
  -- The Fenchel conjugate, defined as sup_{x∈E} ⟨v,x⟩-f(x)
  unfold fenchelConjugate
  -- Apply the fact that if `x<y` then `x≠y`
  apply ne_of_gt
  -- -∞ < sup_{i} s_i iff ∃ i: -∞ < s_i.
  rw [bot_lt_iSup]
  -- Indeed, since the domain is nonempty there exists x such that f(x)<∞ and f(x)>-∞.
  obtain ⟨x, ht, hb⟩ := Set.nonempty_iff_ne_empty.mpr h
  use x
  -- Since f(x)≠-∞  and f(x)≠+∞, then f(x) is a real number.
  have h1 : (f x).toReal = f x := EReal.coe_toReal ht hb
  rw [← h1]
  -- From Init.Data.Ord.Basic: uses decidable less-than and equality relations to find an `Ordering`
  -- Gives a 'less than' ordering iff x < y - clearly ⊥ < ⟪v,x⟫ - f x, since ⊥ < ⟪v,x⟫ and f x ≠ ⊥
  exact compareOfLessAndEq_eq_lt.mp rfl

-- Fenchel-Young inequality for a proper function `f : E → EReal`
theorem fenchel_young (v x : E) (h1 : f x ≠ ⊥) (h2 : IsProper f) : ⟪v,x⟫ ≤ f x + f∗ v := by
  -- f∗ v = sup_{x ∈ E} ⟨v,x⟩ - f(x) ≥ ⟨v,x⟫ - f(x)
  have h3 : f∗ v ≥ ⟪v,x⟫ - f x := by
    exact le_iSup_iff.mpr fun b a ↦ a x
  rw[ge_iff_le] at h3
  rw [EReal.sub_le_iff_le_add (Or.inl h1) (Or.inr (fenchelConjugate_ne_bot f v h2))] at h3
  rw[add_comm]
  exact h3

-- The Fenchel biconjugate of `f` is the conjugate of the conjugate of `f`
noncomputable def fenchelBiconjugate (x : E) : EReal := f∗∗ x

-- The Fenchel biconjugate of `f` can be expressed as a supremum over `v ∈ E`
lemma fenchelBiconjugate_eq_sup (x : E) : f∗∗ x = ⨆ v, ⟪v, x⟫ - f∗ v := by
  conv in ⟪_,_⟫ =>
   rw [real_inner_comm]
  rfl

-- The Fenchel biconjugate of a proper function `f : E → EReal` is less than or equal to `f`
theorem fenchelBiconjugate_le (x : E) (h1 : f x ≠ ⊥) (h2 : IsProper f) : f∗∗ x ≤ f x := by
  apply iSup_le
  intro v
  apply EReal.sub_le_of_le_add
  rw[real_inner_comm]
  exact fenchel_young f v x h1 h2

/-
`IsSubgradient`, `subdifferential`, and `mem_subdifferential` are based on the definitions in Optlib
https://github.com/optsuite/optlib/blob/main/Optlib/Convex/Subgradient.lean
-/

-- `v` is a subgradient of `f` at `x` if `∀ y, ⟪v, y - x⟫ ≤ f(y) - f(x)`
def IsSubgradient (v x : E) : Prop := ∀ y, ⟪v, y - x⟫ ≤ f y - f x

-- The subdifferential of `f` at `x` is the set of all subgradients of `f` at `x`
def subdifferential (x : E) : Set E := {v : E | IsSubgradient f v x}

-- Notation for the subdifferential: `∂f`
local prefix:max "∂" => subdifferential

-- `v` is a subgradient of `f` at `x` iff `v` is in the subdifferential of `f` at `x`
theorem mem_subdifferential : IsSubgradient f v x ↔ v ∈ ∂f x := ⟨id, id⟩

-- coming up with names is hard
lemma subdifferential_nonempty_f_ne_bot : ∂f x ≠ ∅ → ∀ y : E, f y ≠ ⊥ := by
  intro hsub y fy
  obtain ⟨v, hv⟩ := Set.nonempty_iff_ne_empty.mpr hsub
  specialize hv y
  rw[fy, EReal.bot_sub] at hv
  contradiction

-- inner_sub_right, restated after coercing to EReal
lemma EReal.inner_sub_right' (v x y : E) : (⟪v, y - x⟫ : EReal) = ⟪v, y⟫ - ⟪v, x⟫ := by
  rw [inner_sub_right, EReal.coe_sub]

-- First direction of Fenchel-Young equality
theorem fenchel_young_eq (v : E) (x : dom f) (h : IsProper f) : v ∈ ∂f x → f x + f∗ v = ⟪v,x⟫ := by
  -- Assume `v ∈ ∂f x`
  intro hv
  have h_ne : ∂f x ≠ ∅ := by exact ne_of_mem_of_not_mem' hv fun a ↦ a -- Trying to see if this simplifies things
  -- Split into two inequalities: `f x + f∗ v ≤ ⟪v,x⟫` and `f x + f∗ v ≥ ⟪v,x⟫`
  apply le_antisymm
  · -- Case 1: `f x + f∗ v ≤ ⟪v,x⟫`
    rw[add_comm]
    -- Use `f x ≠ ⊥` and `⟪v,x⟫ ≠ ⊤` to move `f x` to the other side of the inequality
    rw [← EReal.le_sub_iff_add_le (Or.inl x.2.2) (Or.inr (EReal.coe_ne_top ⟪v,x⟫))]
    -- Change the goal to a universal quantifier over y ∈ E
    apply iSup_le
    -- Assume y ∈ E is arbitrary
    intro y
    -- Replace universal quantifier with a specific y giving `hv : ⟪v, y-x⟫ ≤ f y - f x`
    specialize hv y
    have h_fy : f y ≠ ⊥ := by apply subdifferential_nonempty_f_ne_bot f h_ne -- Also trying to see if this simplifies things
    -- Rewrite `⟪v, y-x⟫` as `⟪v,y⟫ - ⟪v,x⟫`
    rw [EReal.inner_sub_right'] at hv
    -- Move f y to the other side of the inequality
    apply EReal.sub_le_of_le_add
    -- Use `⟪v,x⟫ ≠ ⊥` and `⟪v,x⟫ ≠ ⊤` to move `⟪v,x⟫` to the other side of the inequality
    rw [EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot ⟪v,x⟫)) (Or.inl (EReal.coe_ne_top ⟪v,x⟫))] at hv
    -- `f y - f x + ⟪v,x⟫ = ⟪v,x⟫ + (f y - f x)`
    rw[add_comm] at hv
    -- The next 3 can be moved into a single rewrite but just left it as is for now
    -- `-f x + f y = + -f x + f y`
    rw[sub_eq_add_neg]
    -- `+ -f x + f y = f y + -f x`
    rw [add_right_comm]
    -- `f y + -f x = (f y + -f x)`
    rw [add_assoc]
    exact hv
  · -- Case 2: `f x + f∗ v ≥ ⟪v,x⟫`
    -- Use the Fenchel-Young inequality
    exact fenchel_young f v x x.2.2 h



-- The epigraph of `f`
def epi : Set (E × ℝ) := {p | f p.1 ≤ p.2}
#min_imports
