import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Analysis.InnerProductSpace.Basic

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Convex Conjugates

## TODO
- Replace the definition of `fenchelConjugate` to apply on the dual space of `E`
- Organise things better e.g. structure for EReal function, sections
- Figure out naming conventions
- Write proper header for file - overview, key declarations, references
- Discuss whether to redefine the domain as the set of x where f(x) is real
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

-- Notation for the Fenchel conjugate of f: `f∗`
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
  -- Since `f(x)≠-∞` and `f(x)≠+∞`, then `f(x)` is a real number.
  rw[← EReal.coe_toReal ht hb]
  -- From Init.Data.Ord.Basic: uses decidable less-than and equality relations to find an `Ordering`
  -- Gives a 'less than' ordering iff `x < y`. Clearly `⊥ < ⟪v,x⟫ - f x`, since `⊥ < ⟪v,x⟫` and `f x < ⊥`
  exact compareOfLessAndEq_eq_lt.mp rfl

-- Fenchel-Young inequality for a proper function `f : E → EReal`
theorem fenchel_young (v x : E) (h1 : f x ≠ ⊥) (h2 : IsProper f) : ⟪v,x⟫ ≤ f x + f∗ v := by
  -- f∗(v) = sup_{x ∈ E} ⟨v,x⟩ - f(x) ≥ ⟨v,x⟫ - f(x)
  have h3 : f∗ v ≥ ⟪v,x⟫ - f x := by exact le_iSup_iff.mpr fun b a ↦ a x
  -- Write h3 as ⟪v,x⟫ - f(x) ≤ f∗ v
  rw[ge_iff_le] at h3
  -- Since f(x) ≠ -∞ and f∗(v) ≠ -∞, we can add f(x) to both sides of the inequality
  rw [EReal.sub_le_iff_le_add (Or.inl h1) (Or.inr (fenchelConjugate_ne_bot f v h2))] at h3
  -- Commute the addition to get ⟪v,x⟫ ≤ f(x) + f∗ v
  rw[add_comm]
  -- Conclude the proof with the final inequality
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
  -- Write `f∗∗ x` as a supremum over `v ∈ E`
  rw[fenchelBiconjugate_eq_sup]
  -- Since the supremum of `⟪v,x⟫ - f∗ v` over all `v ∈ E` is `≤ f(x)` then `∀ i, ⟪i,x⟫ - f∗ i ≤ f(x)`
  apply iSup_le
  -- Say `v` is an arbitrary element of `E`
  intro v
  -- Move `f∗ v` to the other side of the inequality to get `⟪v,x⟫ ≤ f(x) + f∗ v`
  apply EReal.sub_le_of_le_add
  -- This is exactly the Fenchel-Young inequality
  exact fenchel_young f v x h1 h2

/-
`IsSubgradient`, `subdifferential`, and `mem_subdifferential` are based on the definitions in Optlib
https://github.com/optsuite/optlib/blob/main/Optlib/Convex/Subgradient.lean
-/

-- `v` is a subgradient of `f` at `x` if `∀ y, ⟪v, y⟫ - ⟪v,x⟫ ≤ f(y) - f(x)`
def IsSubgradient (v x : E) : Prop := ∀ y, ⟪v, y⟫ - ⟪v,x⟫ ≤ f y - f x

-- The subdifferential of `f` at `x` is the set of all subgradients of `f` at `x`
def subdifferential (x : E) : Set E := {v : E | IsSubgradient f v x}

-- Notation for the subdifferential: `∂f`
local prefix:max "∂" => subdifferential

-- unused for now
-- `v` is a subgradient of `f` at `x` iff `v` is in the subdifferential of `f` at `x`
-- theorem mem_subdifferential : IsSubgradient f v x ↔ v ∈ ∂f x := ⟨id, id⟩

-- The subdifferential of a proper function `f` at `x` is nonempty if `f(y) ≠ ⊥` for all `y ∈ E`
lemma subdifferential_nonempty_f_ne_bot : ∂f x ≠ ∅ → ∀ y : E, f y ≠ ⊥ := by
  -- Assume that `∂f x ≠ ∅`, `y ∈ E`, and `f y = ⊥`
  intro h_ne y h_fy
  -- Since `∂f x ≠ ∅`, there exists `v ∈ ∂f x`
  obtain ⟨v, hv⟩ := Set.nonempty_iff_ne_empty.mpr h_ne
  -- Write the subgradient inequality using `y`
  specialize hv y
  -- Substitute `f y = ⊥` into the subgradient inequality to get `⟪v,y⟫ - ⟪v,x⟫ ≤ ⊥`
  rw[h_fy, EReal.bot_sub] at hv
  -- Since `⊥ < ⟪v,y⟫ - ⟪v,x⟫`, we have a contradiction
  contradiction


-- The Fenchel-Young equality: `f(x) + f∗(v) = ⟪v,x⟫` iff `f∗(v) = ⟪v,x⟫ - f(x)`
lemma fenchelConjugate_sub_iff_add_eq (v : E) (x : dom f) : f x + f∗ v = ⟪v,x⟫ ↔ f∗ v = ⟪v,x⟫ - f x := by
  -- Split the equivalence into two implications
  apply Iff.intro
  · -- (→) Assume f(x) + f∗(v) = ⟪v,x⟫
    intro h
    -- Rewrite ⟪v,x⟫ as f x + f∗ v to get f∗(v) = f(x) + f∗(v) - f(x)
    rw[← h]
    -- Since f(x) ≠ ⊥ and f(x) ≠ ⊤, f(x) is a real number
    rw[← EReal.coe_toReal x.2.1 x.2.2]
    -- Cancel f(x) to get f∗(v) = f∗(v)
    rw [EReal.add_sub_cancel_left]
  · -- (←) Assume f∗(v) = ⟪v,x⟫ - f(x)
    intro h
    -- Rewrite f∗ v as ⟪v,x⟫ - f x
    rw[h]
    rw[← EReal.coe_toReal x.2.1 x.2.2]
    -- Rewrite the left-hand side using the fact that a + (b - c) = a + b - c
    rw [add_sub]
    -- Cancel f(x) to get ⟪v,x⟫ = ⟪v,x⟫
    rw [EReal.add_sub_cancel_left]


-- If `v` is a subgradient of `f` at `x`, then `f(x) + f∗(v) = ⟪v,x⟫`
theorem fenchel_young_eq.mp (v : E) (x : dom f) (h : IsProper f) : v ∈ ∂f x → f x + f∗ v = ⟪v,x⟫ := by
  -- Assume `v ∈ ∂f x`
  intro hv
  -- Apply the equivalence between `f(x) + f∗(v) = ⟪v,x⟫` and `f∗(v) = ⟪v,x⟫ - f(x)`
  rw[fenchelConjugate_sub_iff_add_eq f v x]
  -- Split into two inequalities: `f∗(v) ≤ ⟪v,x⟫ - f(x)` and `⟪v,x⟫ - f(x) ≤ f∗(v)`
  apply le_antisymm
  · -- Case 1: `f∗(v) ≤ ⟪v,x⟫ - f(x)`
    -- Since the supremum of ⟪v,y⟫ - f(y) over all y ∈ E is ≤ ⟪v,x⟫ - f(x) then ∀ y, ⟪v,y⟫ - f(y) ≤ ⟪v,x⟫ - f(x)
    apply iSup_le
    intro y
    -- Rewrite the subgradient inequality using y
    specialize hv y
    -- Move f(y) to the other side of the inequality
    apply EReal.sub_le_of_le_add
    -- Use `⟪v,x⟫ ≠ ⊥` and `⟪v,x⟫ ≠ ⊤` to move `⟪v,x⟫` to the other side of the inequality
    rw [EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot ⟪v,x⟫)) (Or.inl (EReal.coe_ne_top ⟪v,x⟫))] at hv
    -- Simplify all subtractions to additions of negatives
    simp only [sub_eq_add_neg] at *
    -- Apply associativity and commutativity of addition
    grind => ac
  · -- Case 2: `⟪v,x⟫ - f(x) ≤ f∗(v)`
    -- Use f(x) ≠ ⊥ and f(x) ≠ ⊤ to move f(x) to the other side of the inequality
    rw [(EReal.sub_le_iff_le_add (Or.inl x.2.2) (Or.inl x.2.1))]
    rw[add_comm]
    -- Apply the Fenchel-Young inequality
    exact fenchel_young f v x x.2.2 h


-- If `f(x) + f∗(v) = ⟪v,x⟫`, then `v` is a subgradient of `f` at `x`
theorem fenchel_young_eq.mpr (v : E) (x : dom f) (h : IsProper f) : f x + f∗ v = ⟪v,x⟫ → v ∈ ∂f x := by
  -- Assume f(x) + f∗(v) = ⟪v,x⟫ and y ∈ E in the subgradient inequality
  intro h_eq y
  -- Rewrite the equality `f x + f∗ v = ⟪v,x⟫` as `f∗ v = ⟪v,x⟫ - f x` at h_eq
  rw [fenchelConjugate_sub_iff_add_eq f v x] at h_eq
  -- Add ⟪v,x⟫ to both sides of the subgradient inequality
  rw [EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot ⟪v,x⟫)) (Or.inl (EReal.coe_ne_top ⟪v,x⟫))]
  -- Rewrite to group ⟪v,x⟫ - f(x) together
  rw[sub_eq_add_neg, add_assoc, add_comm (-f x), ← sub_eq_add_neg]
  -- Substitute ⟪v,x⟫ - f(x) = f∗(v)
  rw[← h_eq, add_comm]
  -- Show that f∗(v) ≠ ⊤
  have h_ne_top : f∗ v ≠ ⊤ := by
    -- ⟪v,x⟫ - f(x) ≠ ⊤
    rw [h_eq]
    -- Coerce f(x) to a real number since f(x) ≠ ⊤ and f(x) ≠ ⊥
    rw[← EReal.coe_toReal x.2.1 x.2.2]
    -- A real number is not equal to ⊤
    exact EReal.coe_ne_top (⟪v,x⟫ - (f x).toReal)
  -- Show that f∗(v) ≠ ⊥
  have h_ne_bot : f∗ v ≠ ⊥ := by exact fenchelConjugate_ne_bot f v h
  -- ⟪v,y⟫ - f(y) ≤ sup_{y ∈ E} ⟨v,y⟩ - f(y) = f∗(v)
  have h_le : ⟪v,y⟫ - f y ≤ f∗ v:= by exact le_iSup_iff.mpr fun b a ↦ a y
  -- Add f(y) to both sides of the inequality in h_le to get ⟪v,y⟫ ≤ f∗(v) + f(y)
  rw [EReal.sub_le_iff_le_add (Or.inr h_ne_top) (Or.inr h_ne_bot)] at h_le
  -- Our goal is exactly h_le
  exact h_le

-- The Fenchel-Young equality: `v` is a subgradient of `f` at `x` iff `f(x) + f∗(v) = ⟪v,x⟫`
theorem fenchel_young_eq (v : E) (x : dom f) (h : IsProper f) : v ∈ ∂f x ↔ f x + f∗ v = ⟪v,x⟫ := by
  apply Iff.intro
  · exact fenchel_young_eq.mp f v x h
  · exact fenchel_young_eq.mpr f v x h





-- The epigraph of `f`
def epi : Set (E × ℝ) := {(x,c) | f x ≤ c}
#min_imports
