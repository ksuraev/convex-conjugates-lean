import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.EReal.Inv

set_option linter.style.header false
set_option linter.style.longLine false

/-!
# Convex Conjugates

## TODO
- Replace the definition of `fenchelConjugate` to apply on the dual space of `E`
- Figure out naming conventions
- Write proper header for file - overview, key declarations, references
- Discuss whether to redefine the domain as the set of x where f(x) is real
-/

local notation "⟪" x ", " y "⟫" => @inner ℝ _ _ x y

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable (f : E → EReal)

/-
`IsSubgradient` and `subdifferential` are based on the definitions in Optlib
https://github.com/optsuite/optlib/blob/main/Optlib/Convex/Subgradient.lean
-/

/-- `v` is a subgradient of `f` at `x` if `⟪v, y⟫ - ⟪v, x⟫ ≤ f y - f x` for all `y`. -/
def IsSubgradient (v x : E) : Prop := ∀ y, ⟪v, y⟫ - ⟪v,x⟫ ≤ f y - f x

/-- The subdifferential of `f` at `x` is the set of all subgradients of `f` at `x`. -/
def subdifferential (x : E) : Set E := {v : E | IsSubgradient f v x}

-- Notation for the subdifferential: `∂f`
local prefix:max "∂" => subdifferential

/-- The effective domain of `f` is the set of `x` for which `f x` is finite. -/
def dom : Set E := {x : E | f x ≠ ⊤ ∧ f x ≠ ⊥}

-- The epigraph of `f`
def epi : Set (E × ℝ) := {p : E × ℝ | p.1 ∈ Set.univ ∧ f p.1 ≤ p.2}

/-- A function `f` is proper if its domain is nonempty. -/
def IsProper : Prop := dom f ≠ ∅

/-- The Fenchel conjugate of `f` at `v` is the supremum of `⟪v, x⟫ - f x` over `x`. -/
noncomputable def fenchelConjugate (v : E) : EReal := ⨆ x : E, ⟪v, x⟫ - f x

-- Notation for the Fenchel conjugate of f: `f∗`
local postfix:max "∗" => fenchelConjugate

/-- The Fenchel biconjugate of `f` is the Fenchel conjugate of `f∗`. -/
noncomputable def fenchelBiconjugate (x : E) : EReal := f∗∗ x

/-- If `f` is proper, then its Fenchel conjugate `f∗ v` is not `⊥` for any `v ∈ E`. -/
lemma fenchelConjugate.ne_bot (v : E) : IsProper f → f∗ v ≠ ⊥ := by
  -- Assume that `f` is proper
  intro h
  unfold fenchelConjugate
  -- It suffices to show the supremum is strictly greater than `⊥`
  apply ne_of_gt
  -- `⊥ < ⨆ i, s i` iff `⊥ < s i` for some `i`
  rw [bot_lt_iSup]
  -- Since the domain is nonempty there exists `x` such that `f x ≠ ⊤` and `f x ≠ ⊥`
  obtain ⟨x, h_ne_top, h_ne_bot⟩ := Set.nonempty_iff_ne_empty.mpr h
  use x
  -- Rewrite the finite `EReal` value `f x` as its real coercion
  rw[← EReal.coe_toReal h_ne_top h_ne_bot]
  -- The comparison reduces to `Ordering.lt`, giving the required `⊥ < ⟪v, x⟫ - f x`
  exact compareOfLessAndEq_eq_lt.mp rfl

/-- For a proper function `f` and `x` such that `f x ≠ ⊥`, the Fenchel-Young inequality gives `⟪v, x⟫ ≤ f x + f∗ v`. -/
theorem fenchel_young_inequality (v x : E) (h1 : f x ≠ ⊥) (h2 : IsProper f) : ⟪v,x⟫ ≤ f x + f∗ v := by
  -- From the definition of `f∗`, we have `f∗ v ≥ ⟪v,x⟫ - f x`
  have h3 : f∗ v ≥ ⟪v,x⟫ - f x := by exact le_iSup_iff.mpr fun b a ↦ a x
  -- Rewrite the inequality with `≤`
  rw[ge_iff_le] at h3
  -- Since `f x ≠ ⊥` and `f∗ v ≠ ⊥`, add `f x` to both sides
  rw [EReal.sub_le_iff_le_add (Or.inl h1) (Or.inr (fenchelConjugate.ne_bot f v h2))] at h3
  -- Match the order of the terms using commutativity
  rw[add_comm]
  exact h3

/-- The Fenchel biconjugate of `f` is the supremum of `⟪v, x⟫ - f∗ v` over `v`. -/
lemma fenchelBiconjugate.eq_sup (x : E) : f∗∗ x = ⨆ v : E, ⟪v, x⟫ - f∗ v := by
  unfold fenchelConjugate
  -- Apply symmetry to match the inner-product ordering
  conv in ⟪_,_⟫ =>
   rw [real_inner_comm]

/-- For proper `f` with `f x ≠ ⊥`, the Fenchel biconjugate satisfies `f∗∗ x ≤ f x`. -/
theorem fenchelBiconjugate_le (x : E) (h1 : f x ≠ ⊥) (h2 : IsProper f) : f∗∗ x ≤ f x := by
  -- Write `f∗∗ x` as a supremum over `v ∈ E`
  rw[fenchelBiconjugate.eq_sup]
  -- Since the supremum of `⟪v,x⟫ - f∗ v` over all `v ∈ E` is `≤ f x` then `∀ i, ⟪i,x⟫ - f∗ i ≤ f x`
  apply iSup_le
  -- Suppose `v` is an arbitrary element of `E`
  intro v
  -- Move `f∗ v` to the other side of the inequality to get `⟪v,x⟫ ≤ f x + f∗ v`
  apply EReal.sub_le_of_le_add
  -- `⟪v,x⟫ ≤ f x + f∗ v` is exactly the Fenchel-Young inequality
  exact fenchel_young_inequality f v x h1 h2

/-- The subdifferential of a proper function `f` at `x` is nonempty if `f y ≠ ⊥` for all `y ∈ E`. -/
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

/-- For `x ∈ dom f`, `f x + f∗ v = ⟪v, x⟫` iff `f∗ v = ⟪v, x⟫ - f x`. -/
lemma fenchelConjugate.sub_iff_add_eq (v : E) (x : dom f) : f x + f∗ v = ⟪v,x⟫ ↔ f∗ v = ⟪v,x⟫ - f x := by
  -- Split the equivalence into two implications
  apply Iff.intro
  · -- (→) Assume `f x + f∗ v = ⟪v,x⟫`
    intro h
    -- Rewrite `⟪v,x⟫` as `f x + f∗ v `to get `f∗ v = f x + f∗ v - f x`
    rw[← h]
    -- Since `f x ≠ ⊥` and `f x ≠ ⊤`, `f x` is a real number
    rw[← EReal.coe_toReal x.2.1 x.2.2]
    -- Cancel `f x` to get `f∗ v = f∗ v`
    rw [EReal.add_sub_cancel_left]
  · -- (←) Assume `f∗ v = ⟪v,x⟫ - f x`
    intro h
    -- Rewrite `f∗ v` as `⟪v,x⟫ - f x`
    rw[h]
    rw[← EReal.coe_toReal x.2.1 x.2.2]
    -- Rewrite the left-hand side using the fact that `a + (b - c) = a + b - c`
    rw [add_sub]
    -- Cancel `f x` to get `⟪v,x⟫ = ⟪v,x⟫`
    rw [EReal.add_sub_cancel_left]

/-- If `v` is a subgradient of `f` at `x`, then `f x + f∗ v = ⟪v,x⟫`. -/
theorem fenchel_young_eq.mp (v : E) (x : dom f) (h : IsProper f) : v ∈ ∂f x → f x + f∗ v = ⟪v,x⟫ := by
  -- Assume `v ∈ ∂f x`
  intro hv
  -- Apply the equivalence between `f x + f∗ v = ⟪v,x⟫` and `f∗ v = ⟪v,x⟫ - f x`
  rw[fenchelConjugate.sub_iff_add_eq f v x]
  -- Split into two inequalities: `f∗ v ≤ ⟪v,x⟫ - f x` and `⟪v,x⟫ - f x ≤ f∗ v`
  apply le_antisymm
  · -- Case 1: `f∗ v ≤ ⟪v,x⟫ - f x`
    -- Since the supremum of `⟪v,y⟫ - f y` over all `y ∈ E` is `≤ ⟪v,x⟫ - f x` then `∀ i, ⟪v,i⟫ - f i ≤ ⟪v,x⟫ - f x`
    apply iSup_le
    intro y
    -- Rewrite the subgradient inequality using `y`
    specialize hv y
    -- Add `⟪v,x⟫` to both sides of the subgradient inequality
    rw [EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot ⟪v,x⟫)) (Or.inl (EReal.coe_ne_top ⟪v,x⟫))] at hv
    -- Move `f y` to the other side of the inequality
    apply EReal.sub_le_of_le_add
    -- Rewrite all subtractions to additions of negatives
    simp only [sub_eq_add_neg] at *
    -- Invoke grind with the solver for associative and commutative operators
    grind => ac
  · -- Case 2: `⟪v,x⟫ - f x ≤ f∗ v`
    -- Rearrange the inequality using the fact that `f x` is finite
    rw [(EReal.sub_le_iff_le_add (Or.inl x.2.2) (Or.inl x.2.1)), add_comm]
    -- Close the goal using the Fenchel-Young inequality
    exact fenchel_young_inequality f v x x.2.2 h

/-- If `f x + f∗ v = ⟪v,x⟫`, then `v` is a subgradient of `f` at `x`. -/
theorem fenchel_young_eq.mpr (v : E) (x : dom f) (h : IsProper f) : f x + f∗ v = ⟪v,x⟫ → v ∈ ∂f x := by
  -- Assume `f x + f∗ v = ⟪v,x⟫` and `y ∈ E` in the subgradient inequality
  intro h_eq y
  -- Rewrite the equality `f x + f∗ v = ⟪v,x⟫` as `f∗ v = ⟪v,x⟫ - f x` at h_eq
  rw [fenchelConjugate.sub_iff_add_eq f v x] at h_eq
  -- Add `⟪v,x⟫` to both sides of the subgradient inequality
  rw [EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot ⟪v,x⟫)) (Or.inl (EReal.coe_ne_top ⟪v,x⟫))]
  -- Rewrite to group `⟪v,x⟫ - f x` together
  rw[sub_eq_add_neg, add_assoc, add_comm (-f x), ← sub_eq_add_neg]
  -- Substitute `⟪v,x⟫ - f x = f∗ v`
  rw[← h_eq, add_comm]
  -- Show that `f∗ v ≠ ⊤`
  have h_ne_top : f∗ v ≠ ⊤ := by
    -- `⟪v,x⟫ - f x ≠ ⊤`
    rw [h_eq]
    -- Coerce `f x` to a real number since `f x ≠ ⊤` and `f x ≠ ⊥`
    rw[← EReal.coe_toReal x.2.1 x.2.2]
    -- A real number is not equal to `⊤`
    exact EReal.coe_ne_top (⟪v,x⟫ - (f x).toReal)
  -- Show that `f∗ v ≠ ⊥`
  have h_ne_bot : f∗ v ≠ ⊥ := by exact fenchelConjugate.ne_bot f v h
  -- `⟪v,y⟫ - f y ≤ sup_{y ∈ E} ⟨v,y⟩ - f y = f∗ v`
  have h_le : ⟪v,y⟫ - f y ≤ f∗ v:= by exact le_iSup_iff.mpr fun b a ↦ a y
  -- Add `f y` to both sides of the inequality in h_le to get `⟪v,y⟫ ≤ f∗ v + f y`
  rw [EReal.sub_le_iff_le_add (Or.inr h_ne_top) (Or.inr h_ne_bot)] at h_le
  -- Our goal is exactly h_le
  exact h_le

/-- For proper `f`, `v` is a subgradient of `f` at `x` if and only if the Fenchel-Young equality holds. -/
theorem fenchel_young_eq (v : E) (x : dom f) (h : IsProper f) : v ∈ ∂f x ↔ f x + f∗ v = ⟪v,x⟫ := by
  apply Iff.intro
  · exact fenchel_young_eq.mp f v x h
  · exact fenchel_young_eq.mpr f v x h


-- Convexity of the Fenchel conjugate
/-- For fixed `x ∈ dom f`, `inner f x` is the real-valued function `v ↦ ⟪v, x⟫`. -/
def inner (x : dom f) : E → ℝ := fun v => ⟪v, x⟫

/-- For fixed `x ∈ dom f`, the function `inner f x` is convex. -/
lemma inner.convex (x : dom f) : ConvexOn ℝ Set.univ (inner f x) := by
  -- `flip` fixes `x` in the second argument, giving `v ↦ ⟪v, x⟫`
  exact LinearMap.convexOn ((innerₗ E).flip x) convex_univ

/-- For fixed `x ∈ dom f`, `φ f x` is the real-valued function `v ↦ ⟪v, x⟫ - f x`. -/
def φ (x : dom f) : E → ℝ := fun v => inner f x v - (f x).toReal

/-- For fixed `x ∈ dom f`, `φ f x` is convex. -/
lemma φ.convex (x : dom f) : ConvexOn ℝ Set.univ (φ f x) := by
  have hinner : ConvexOn ℝ Set.univ (inner f x) := by
    exact inner.convex f x
  have h := hinner.add_const (-(f x).toReal)
  exact ConvexOn.congr h fun ⦃x_1⦄ ↦ congrFun rfl

/-- `φ.toEReal f x` is `φ f x` as an `EReal`-valued function. -/
def φ.toEReal (x : dom f) : E → EReal := fun v => (φ f x v : EReal)

/-- For `x ∈ dom f`, coercing `φ f x v` to `EReal` gives `⟪v, x⟫ - f x`. -/
lemma φ.toEReal_eq (x : dom f) : φ.toEReal f x v = ⟪v,x⟫ - f x := by
  -- Since `x ∈ dom f`, `f x` is finite
  rw [← EReal.coe_toReal x.2.1 x.2.2]
  -- Prove the equality using `ac_rfl` for associative and commutative operators
  ac_rfl

/-- If `f` never takes the value `⊥`, then `f∗ v` is the supremum of `φ.toEReal f x v` over `x ∈ dom f`. -/
lemma fenchelConjugate.eq_iSup_dom (h : ∀ x, f x ≠ ⊥) (v : E) : f∗ v = ⨆ x : dom f, φ.toEReal f x v := by
  apply le_antisymm
  · -- (≤) Show that `f∗ v ≤ ⨆ x ∈ dom f, φ.toEReal f x v`
    -- For all `x ∈ E`, `⟪v,x⟫ - f x ≤ ⨆ x, φ.toEReal f x v`
    apply iSup_le
    intro x
    -- Split according to whether `x` belongs to `dom f`
    by_cases hx : x ∈ dom f
    · -- Case 1: `x ∈ dom f`
      -- Let `x` be the element of `dom f`
      let x' : dom f := ⟨x, hx⟩
      -- Rewrite `⟪v, x⟫ - f x` as `φ.toEReal f x' v`
      rw [← φ.toEReal_eq f x']
      -- This is bounded by the supremum over `dom f`
      exact le_iSup (fun y : dom f => φ.toEReal f y v) x'
    · -- Case 2: `x ∉ dom f`
      -- If `x ∉ dom f`, then `f x = ⊤` since `f x ≠ ⊥`
      have htop : f x = ⊤ := by
        -- Assume for contradiction that `f x ≠ ⊤`
        by_contra hne
        -- Then `f x ≠ ⊤` and `f x ≠ ⊥`, so `x ∈ dom f`, contradicting `hx`
        exact hx ⟨hne, h x⟩
      -- Since `f x = ⊤`, then `⟪v, x⟫ - f x = ⊥` and the inequality holds trivially
      simp [htop]
  · -- (≥) Show that `f∗ v ≥ ⨆ x ∈ dom f, φ.toEReal f x v`
    -- For all `x ∈ dom f, φ.toEReal f x v ≤ f∗ v`
    apply iSup_le
    intro x
    -- Rewrite `φ.toEReal f x v` as `⟪v, x⟫ - f x`
    rw [φ.toEReal_eq f x]
    -- This is bounded by the supremum defining `f∗ v`
    exact le_iSup (fun y : E => ⟪v, y⟫ - f y) x

/-- For fixed `x ∈ dom f`, the epigraph of `φ.toEReal f x` is convex. -/
lemma φ.toEReal.epi_convex (x : dom f) : Convex ℝ (epi (φ.toEReal f x)) := by
  simp only [epi, φ.toEReal]
  norm_cast
  exact (φ.convex f x).convex_epigraph

/-- The epigraph of the supremum of `φ.toEReal f x` over `x ∈ dom f` is convex. -/
lemma φ.iSup_epi_convex : Convex ℝ (epi (fun v : E => ⨆ x : dom f, φ.toEReal f x v)) := by
  -- The epigraph of the supremum is the intersection of the epigraphs
  have h_inter : epi (fun v : E => ⨆ x : dom f, φ.toEReal f x v) = ⋂ x : dom f, epi (φ.toEReal f x) := by
    -- `p` is in the epigraph of the supremum iff `p` is in the intersection of the epigraphs
    ext p
    -- Membership in the intersection is equivalent to membership in each epigraph
    simp [epi]
  -- Rewrite epigraph of the supremum as the intersection of epigraphs
  rw[h_inter]
  -- The intersection of convex sets is convex
  apply convex_iInter
  -- Each individual epigraph is convex by `φ.toEReal.epi_convex`
  intro x
  exact φ.toEReal.epi_convex f x

/-- The epigraph of the Fenchel conjugate `f∗` is convex if `f x ≠ ⊥` for all `x`. -/
theorem fenchelConjugate.epi_convex (h : ∀ x, f x ≠ ⊥) : Convex ℝ (epi f∗) := by
  -- `f∗` is the supremum of `φ.toEReal f x` over `x ∈ dom f`
  have hf : f∗ = fun v : E => ⨆ x : dom f, φ.toEReal f x v := by
    -- `f∗ v` is the supremum of `φ.toEReal f x v` over `x ∈ dom f`
    ext v
    -- These two expressions are equal by `fenchelConjugate.eq_iSup_dom`
    rw[fenchelConjugate.eq_iSup_dom f h]
  -- Rewrite the epigraph of `f∗` as the epigraph of the supremum
  rw[hf]
  -- The epigraph of the supremum is convex
  exact φ.iSup_epi_convex f

variable [Semiring 𝕜] [PartialOrder 𝕜] [SMul 𝕜 E] [SMul 𝕜 EReal] [PosSMulMono 𝕜 EReal]
variable {s : Set E}

theorem ConvexOn.isup (hs : Convex 𝕜 s) (g : F → (E → EReal)) (hg : ∀ i, ConvexOn 𝕜 s (g i)) : ConvexOn 𝕜 s (⨆ i, g i) := by
  -- Split the goal into two parts: `s` is convex and `⨆ i, g i` is convex on `s`
  constructor
  · -- `s` is convex by assumption
    exact hs
  · -- `⨆ i, g i` is convex on `s`
    intro x hx y hy a b ha hb hab
    -- `(⨆ i, g i) (a • x + b • y) = ⨆ i, g i (a • x + b • y)`
    rw [iSup_apply]
    -- For all `i`, `g i (a • x + b • y) ≤ a • (⨆ i, g i) x + b • (⨆ i, g i) y`
    rw [iSup_le_iff]
    intro i
    calc
      g i (a • x + b • y) ≤ a • g i x + b • g i y := (hg i).right hx hy ha hb hab
      _ ≤ a • (⨆ i, g i) x + b • (⨆ i, g i) y := by
        -- Show a • g i x ≤ a • (⨆ i, g i) x and b • g i y ≤ b • (⨆ i, g i) y
        apply add_le_add
        · -- a • b₁ ≤ a • b₂ if b₁ ≤ b₂ and a ≥ 0
          refine smul_le_smul_of_nonneg_left ?_ ha
          · rw [iSup_apply]
            exact le_iSup_iff.mpr fun b a ↦ a i
        · -- b • b₁ ≤ b • b₂ if b₁ ≤ b₂ and b ≥ 0
          refine smul_le_smul_of_nonneg_left ?_ hb
          · rw [iSup_apply]
            exact le_iSup_iff.mpr fun b a ↦ a i


#min_imports
