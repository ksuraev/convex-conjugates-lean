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

/-- The effective domain of `f` is the set of `x` for which `f x` is finite. -/
def dom : Set E := {x : E | f x ≠ ⊤ ∧ f x ≠ ⊥}

/-- A function `f` is proper if its domain is nonempty. -/
def IsProper : Prop := dom f ≠ ∅

/-- The Fenchel conjugate of `f` at `v` is the supremum of `⟪v, x⟫ - f x` over `x`. -/
noncomputable def fenchelConjugate (v : E) : EReal := ⨆ x : E, ⟪v, x⟫ - f x

-- Notation for the Fenchel conjugate of f: `f∗`
local postfix:max "∗" => fenchelConjugate

/-- If `f` is proper, then its Fenchel conjugate `f∗ v` is not `⊥` for any `v ∈ E`. -/
lemma fenchelConjugate_ne_bot (v : E) : IsProper f → f∗ v ≠ ⊥ := by
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
theorem fenchel_young (v x : E) (h1 : f x ≠ ⊥) (h2 : IsProper f) : ⟪v,x⟫ ≤ f x + f∗ v := by
  -- From the definition of `f∗`, we have `f∗ v ≥ ⟪v,x⟫ - f x`
  have h3 : f∗ v ≥ ⟪v,x⟫ - f x := by exact le_iSup_iff.mpr fun b a ↦ a x
  -- Rewrite the inequality with `≤`
  rw[ge_iff_le] at h3
  -- Since `f x ≠ ⊥` and `f∗ v ≠ ⊥`, add `f x` to both sides
  rw [EReal.sub_le_iff_le_add (Or.inl h1) (Or.inr (fenchelConjugate_ne_bot f v h2))] at h3
  -- Match the order of the terms using commutativity
  rw[add_comm]
  exact h3

/-- The Fenchel biconjugate of `f` is the Fenchel conjugate of `f∗`. -/
noncomputable def fenchelBiconjugate (x : E) : EReal := f∗∗ x

/-
Note: doing this below also works

unfold fenchelConjugate
simp only [real_inner_comm]

Regular `rw` without `conv` or `simp only` does not work because `rw` cannot rewrite subterms containing bound variables. The inner product is in a "binder".
`conv in` works because we can get inside the binder and rewrite. The simp only works for the same reason
-/
/-- The Fenchel biconjugate of `f` is the supremum of `⟪v, x⟫ - f∗ v` over `v`. -/
lemma fenchelBiconjugate_eq_sup (x : E) : f∗∗ x = ⨆ v : E, ⟪v, x⟫ - f∗ v := by
  unfold fenchelConjugate
  -- Apply symmetry to match the inner-product ordering
  conv in ⟪_,_⟫ =>
   rw [real_inner_comm]

/-- For proper `f` with `f x ≠ ⊥`, the Fenchel biconjugate satisfies `f∗∗ x ≤ f x`. -/
theorem fenchelBiconjugate_le (x : E) (h1 : f x ≠ ⊥) (h2 : IsProper f) : f∗∗ x ≤ f x := by
  -- Write `f∗∗ x` as a supremum over `v ∈ E`
  rw[fenchelBiconjugate_eq_sup]
  -- Since the supremum of `⟪v,x⟫ - f∗ v` over all `v ∈ E` is `≤ f x` then `∀ i, ⟪i,x⟫ - f∗ i ≤ f x`
  apply iSup_le
  -- Suppose `v` is an arbitrary element of `E`
  intro v
  -- Move `f∗ v` to the other side of the inequality to get `⟪v,x⟫ ≤ f x + f∗ v`
  apply EReal.sub_le_of_le_add
  -- `⟪v,x⟫ ≤ f x + f∗ v` is exactly the Fenchel-Young inequality
  exact fenchel_young f v x h1 h2

/-
`IsSubgradient`, `subdifferential`, and `mem_subdifferential` are based on the definitions in Optlib
https://github.com/optsuite/optlib/blob/main/Optlib/Convex/Subgradient.lean
-/

/-- `v` is a subgradient of `f` at `x` if `⟪v, y⟫ - ⟪v, x⟫ ≤ f y - f x` for all `y`. -/
def IsSubgradient (v x : E) : Prop := ∀ y, ⟪v, y⟫ - ⟪v,x⟫ ≤ f y - f x

/-- The subdifferential of `f` at `x` is the set of all subgradients of `f` at `x`. -/
def subdifferential (x : E) : Set E := {v : E | IsSubgradient f v x}

-- Notation for the subdifferential: `∂f`
local prefix:max "∂" => subdifferential

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
lemma fenchelConjugate_sub_iff_add_eq (v : E) (x : dom f) : f x + f∗ v = ⟪v,x⟫ ↔ f∗ v = ⟪v,x⟫ - f x := by
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
  rw[fenchelConjugate_sub_iff_add_eq f v x]
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
    exact fenchel_young f v x x.2.2 h

/-- If `f x + f∗ v = ⟪v,x⟫`, then `v` is a subgradient of `f` at `x`. -/
theorem fenchel_young_eq.mpr (v : E) (x : dom f) (h : IsProper f) : f x + f∗ v = ⟪v,x⟫ → v ∈ ∂f x := by
  -- Assume `f x + f∗ v = ⟪v,x⟫` and `y ∈ E` in the subgradient inequality
  intro h_eq y
  -- Rewrite the equality `f x + f∗ v = ⟪v,x⟫` as `f∗ v = ⟪v,x⟫ - f x` at h_eq
  rw [fenchelConjugate_sub_iff_add_eq f v x] at h_eq
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
  have h_ne_bot : f∗ v ≠ ⊥ := by exact fenchelConjugate_ne_bot f v h
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





-- CONVEXITY
-- innerₗ (mathlib) is the inner product as bilinear map
#check (innerₗ E) -- innerₗ E : E →ₗ[ℝ] E →ₗ[ℝ] ℝ

lemma innerₗ.convex (x : E) : ConvexOn ℝ Set.univ ((innerₗ E) x) := by
  -- convex_univ is the proof that the universal set is convex
  exact LinearMap.convexOn ((innerₗ E) x) convex_univ

-- Using our defs
def inner' (x : dom f) : E → ℝ := fun v => ⟪v, x⟫

lemma inner'.convex (x : dom f) : ConvexOn ℝ Set.univ (inner' f x) := by
  -- .flip flips the arguments of the inner product
  exact LinearMap.convexOn ((innerₗ E).flip x) convex_univ

-- In Easy Path book, they define φₓ: ℝⁿ → ℝ, φₓ(v) = ⟨v, x⟩ - f(x) for x ∈ dom f and v ∈ ℝⁿ
def φ (x : dom f) : E → ℝ := fun v => inner' f x v - (f x).toReal

-- this is convex because it is the sum of a linear function and a constant
lemma φ.convex (x : dom f) : ConvexOn ℝ Set.univ (φ f x) := by
  have hinner : ConvexOn ℝ Set.univ (inner' f x) := by
    exact inner'.convex f x
  have h := hinner.add_const (-(f x).toReal)
  exact ConvexOn.congr h fun ⦃x_1⦄ ↦ congrFun rfl

-- Coercion of φ to an EReal function
def φ.toEReal (x : dom f) : E → EReal := fun v => (φ f x v : EReal)

-- helper
lemma φ.toEReal.eq (x : dom f) : φ.toEReal f x v = ⟪v,x⟫ - f x := by
  -- Since `x ∈ dom f`, `f x` is finite
  rw [← EReal.coe_toReal x.2.1 x.2.2]
  -- Prove the equality using `ac_rfl` for associative and commutative operators
  ac_rfl

-- In line with the book, we need to show f∗ v = ⨆ x ∈ dom f,  φₓ(v) for v ∈ E?
-- Then show that this is convex (the hard part)
lemma fenchelConjugate.eq_iSup_dom (h : ∀ x, f x ≠ ⊥) (v : E) : f∗ v = ⨆ x : dom f, φ.toEReal f x v := by
  apply le_antisymm
  · -- (≤) Show that `f∗ v ≤ ⨆ x ∈ dom f, φ.toEReal f x v`
    -- For all `i ∈ E`, `⟪v,i⟫ - f i ≤ ⨆ x, φ.toEReal f x v`
    apply iSup_le
    -- `x` is an arbitrary element of `E`
    intro x
    -- Split into two cases: `x ∈ dom f` and `x ∉ dom f`
    by_cases hx : x ∈ dom f
    · -- Case 1: `x ∈ dom f`
      -- Let `x` be the element of `dom f`
      let x : dom f := ⟨x, hx⟩
      -- `⟪v, x⟫ - f x` is bounded by the supremum over `dom f`
      have h2 : ⟪v, x⟫ - f x ≤ ⨆ y : dom f, φ.toEReal f y v := by
        rw[← φ.toEReal.eq f x]
        exact le_iSup_iff.mpr fun b a ↦ a x
      exact h2
    · -- Case 2: `x ∉ dom f`
      -- Since `f x ≠ ⊥` for all `x`, then if `x ∉ dom f, f x = ⊤`
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
    -- The supremum over `dom f` is bounded by `f∗ v`
    have h2 : ⟪v, x⟫ - f x ≤ f∗ v := by exact le_iSup_iff.mpr fun b a ↦ a x
    -- Rewrite `φ.toEReal f x v` as `⟪v, x⟫ - f x` and apply the inequality
    rw[φ.toEReal.eq]
    exact le_of_eq_of_le rfl h2

-- No clue how to handle this yet
lemma phi_iSup.convex : ConvexOn ℝ Set.univ (fun v => ⨆ x : dom f, φ f x v) := by
  sorry


-- Trying epigraph route
-- The epigraph of `f`
-- def epi : Set (E × ℝ) := {(x, c) | f x ≤ c}
def epi : Set (E × ℝ) := {p : E × ℝ | p.1 ∈ Set.univ ∧ f p.1 ≤ p.2}

#check (φ.convex f _).convex_epigraph --  (φ.convex f _) : Convex ℝ {p | p.1 ∈ Set.univ ∧ phi f _ p.1 ≤ p.2}


lemma φ.toEReal.epi_convex (x : dom f) : Convex ℝ (epi (φ.toEReal f x)) := by
  simp only [epi, φ.toEReal]
  norm_cast
  exact (φ.convex f x).convex_epigraph

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


theorem fenchelConjugate.convex (h : ∀ x, f x ≠ ⊥) : Convex ℝ (epi f∗) := by
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

-- Leaving for now because I needed to understand the linear mapping stuff
-- variable (β : Type*) [Semiring β] [PartialOrder β] [SMul β E] [SMul β EReal]
-- def IsConvex : Prop := ConvexOn β Set.univ f

-- unused for now
-- `v` is a subgradient of `f` at `x` iff `v` is in the subdifferential of `f` at `x`
-- theorem mem_subdifferential : IsSubgradient f v x ↔ v ∈ ∂f x := ⟨id, id⟩


#min_imports
