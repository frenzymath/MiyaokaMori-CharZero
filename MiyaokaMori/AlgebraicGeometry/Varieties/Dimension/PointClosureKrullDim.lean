import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.CycleGroup
import MiyaokaMori.AlgebraicGeometry.Varieties.Points.PointClosureSubscheme
import MiyaokaMori.AlgebraicGeometry.Divisors.Weil.PrincipalDivisor
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.SchemeDimension
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.Stacks0a21
import MiyaokaMori.AlgebraicGeometry.Varieties.Points.ReducedInducedSubschemeIntegral

/-! # Krull dimension of the closure of a point

(1) A closed immersion preserves the height of points. (2) If a point `w` of `X` has height `d`,
the reduced induced closed subscheme `W_w` on `closure {w}` has topological Krull dimension `d`,
i.e. `(X.pointClosure w).dimension = d`. (3) If `W` is an integral, locally Noetherian,
quasi-compact scheme locally of finite type over a field `k` with `dim W = n + 1`, every principal
cycle `div(f)` on `W` lies in `Z_n(W)` (graded by `Order.height`). (4) The closure of a point of
height `0` contains no point of coheight `1`.

Proof sketch:
1. A closed immersion `f` is a closed embedding, so `f a ≤ f b ↔ a ≤ b` in the specialization
   order; points below `f y` lie in the closed set `range f`, so strict chains below `f y` lift
   bijectively to strict chains below `y`.
2. `dim W_w` is the height of the generic point `⊤` of `W_w` (`Order.height_top_eq_krullDim`; the
   Krull dimension of the specialization order equals the topological Krull dimension,
   `irreducibleSetEquivPoints`), `ι_w(⊤) = w` (`pointClosureι_genericPoint`), then (1).
3. Points in the support of `div(f)` have coheight `1` (`Scheme.ord_eq_zero_of_coheight_neq_one`),
   and Stacks 0A21 (4) (`height_add_coheight_eq_of_locallyOfFiniteType`) gives `height z + 1 = n + 1`.
4. `height w = 0` means `w` is minimal (a closed point); `z' ∈ W_w` with `z' < y` gives
   `ι z' < ι y ≤ w` (the image of `ι` lies in `closure {w}`), contradicting minimality.

Sources: dimension bookkeeping in the notation of Stacks 0A21 (4) and 02QR.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- `ι_w` is a closed immersion (Mathlib's `subschemeι` instance). -/
instance AlgebraicGeometry.Scheme.isClosedImmersion_pointClosureι {X : AlgebraicGeometry.Scheme.{u}}
    (w : X) : AlgebraicGeometry.IsClosedImmersion (X.pointClosureι w) := by
  unfold AlgebraicGeometry.Scheme.pointClosureι
  exact AlgebraicGeometry.IsClosedImmersion.instSubschemeι _

/-- A closed immersion is an order embedding for the specialization order. -/
theorem AlgebraicGeometry.Scheme.Hom.le_iff_of_isClosedImmersion {Y X : AlgebraicGeometry.Scheme.{u}}
    (f : Y ⟶ X) [AlgebraicGeometry.IsClosedImmersion f] (a b : Y) :
    f.base a ≤ f.base b ↔ a ≤ b :=
  f.isClosedEmbedding.isInducing.specializes_iff

theorem AlgebraicGeometry.Scheme.Hom.lt_iff_of_isClosedImmersion {Y X : AlgebraicGeometry.Scheme.{u}}
    (f : Y ⟶ X) [AlgebraicGeometry.IsClosedImmersion f] (a b : Y) :
    f.base a < f.base b ↔ a < b := by
  rw [lt_iff_le_not_ge, lt_iff_le_not_ge, f.le_iff_of_isClosedImmersion, f.le_iff_of_isClosedImmersion]

/-- A closed immersion preserves the height of points. -/
theorem AlgebraicGeometry.Scheme.Hom.height_of_isClosedImmersion {Y X : AlgebraicGeometry.Scheme.{u}}
    (f : Y ⟶ X) [AlgebraicGeometry.IsClosedImmersion f] (y : Y) :
    Order.height (f.base y) = Order.height y := by
  refine le_antisymm ?_ (Order.height_le_height_apply_of_strictMono _
    (fun a b hab => (f.lt_iff_of_isClosedImmersion a b).mpr hab) y)
  refine Order.height_le_iff.mpr fun p hp => ?_
  have hrange : ∀ i, p i ∈ Set.range f.base := fun i => by
    have h1 : p i ≤ f.base y := (p.monotone (Fin.le_last i)).trans hp
    have h2 : p i ∈ closure {f.base y} := (specializes_iff_mem_closure).mp h1
    exact (f.isClosedEmbedding.isClosed_range.closure_subset_iff.mpr
      (Set.singleton_subset_iff.mpr ⟨y, rfl⟩)) h2
  choose g hg using hrange
  let q : LTSeries Y := ⟨p.length, g, fun i => by
    have := p.step i
    rw [← hg, ← hg] at this
    exact (f.lt_iff_of_isClosedImmersion _ _).mp this⟩
  have hq : q.last ≤ y := by
    rw [← f.le_iff_of_isClosedImmersion]
    show f.base (g _) ≤ _
    rw [hg]; exact hp
  exact Order.length_le_height (p := q) hq

/-- The height of the generic point of `W_w` equals the height of `w`. -/
theorem AlgebraicGeometry.Scheme.height_top_pointClosure {X : AlgebraicGeometry.Scheme.{u}} (w : X) :
    Order.height (genericPoint (X.pointClosure w)) = Order.height w := by
  rw [← (X.pointClosureι w).height_of_isClosedImmersion,
    AlgebraicGeometry.Scheme.pointClosureι_genericPoint w]

/-- dim W_w = height w. -/
theorem AlgebraicGeometry.Scheme.topologicalKrullDim_pointClosure {X : AlgebraicGeometry.Scheme.{u}}
    (w : X) {d : ℕ} (hw : Order.height w = (d : ℕ∞)) :
    topologicalKrullDim (X.pointClosure w) = ((d : ℕ) : WithBot ℕ∞) := by
  have hk : Order.krullDim (X.pointClosure w) = topologicalKrullDim (X.pointClosure w) :=
    (Order.krullDim_eq_of_orderIso
      (@irreducibleSetEquivPoints (X.pointClosure w) _ _ _ :
        IrreducibleCloseds (X.pointClosure w) ≃o (X.pointClosure w))).symm
  rw [← hk, ← Order.height_top_eq_krullDim]
  have h1 : Order.height (⊤ : X.pointClosure w) = (d : ℕ∞) := by
    rw [← hw, ← AlgebraicGeometry.Scheme.height_top_pointClosure w]
    rfl
  rw [h1]; rfl

theorem AlgebraicGeometry.Scheme.dimension_pointClosure {X : AlgebraicGeometry.Scheme.{u}}
    (w : X) {d : ℕ} (hw : Order.height w = (d : ℕ∞)) : (X.pointClosure w).dimension = d := by
  unfold AlgebraicGeometry.Scheme.dimension
  rw [AlgebraicGeometry.Scheme.topologicalKrullDim_pointClosure w hw]
  rfl

/-- In an integral scheme `W` locally of finite type over a field with `dim W = n + 1`, a point of
coheight `1` has height `n`. -/
theorem AlgebraicGeometry.Scheme.height_eq_of_coheight_eq_one {k : Type u} [Field k]
    {W : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsIntegral W]
    (π : W ⟶ AlgebraicGeometry.Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType π]
    {n : ℕ} (hdim : topologicalKrullDim W = ((n + 1 : ℕ) : WithBot ℕ∞)) {z : W}
    (hz : Order.coheight z = 1) : Order.height z = (n : ℕ∞) := by
  let _ : W.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) := ⟨π⟩
  have : AlgebraicGeometry.LocallyOfFiniteType (W ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    inferInstanceAs (AlgebraicGeometry.LocallyOfFiniteType π)
  have hadd := AlgebraicGeometry.height_add_coheight_eq_of_locallyOfFiniteType (k := k) W (n + 1) hdim z
  rw [hz] at hadd
  have hne : Order.height z ≠ ⊤ := by
    intro ht; rw [ht] at hadd
    have h' : (⊤ : ℕ∞) = ((n + 1 : ℕ) : ℕ∞) := by exact_mod_cast hadd
    exact ENat.top_ne_natCast _ h'
  lift Order.height z to ℕ using hne with m
  have : m + 1 = n + 1 := by exact_mod_cast hadd
  have : m = n := by omega
  exact_mod_cast this

/-- A principal cycle lies in `Z_{dim W − 1}(W)`. -/
theorem AlgebraicGeometry.Scheme.principalCycle_mem_cycleSubgroup {k : Type u} [Field k]
    {W : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsIntegral W]
    [AlgebraicGeometry.IsLocallyNoetherian W]
    (π : W ⟶ AlgebraicGeometry.Spec (CommRingCat.of k)) [AlgebraicGeometry.LocallyOfFiniteType π]
    {n : ℕ} (hdim : topologicalKrullDim W = ((n + 1 : ℕ) : WithBot ℕ∞)) (f : W.functionFieldˣ) :
    W.principalCycle f ∈ AlgebraicGeometry.cycleSubgroup W n := by
  intro z hz
  rw [AlgebraicGeometry.Scheme.principalCycle_apply] at hz
  have hco : Order.coheight z = 1 := by
    by_contra h
    exact hz (AlgebraicGeometry.Scheme.ord_eq_zero_of_coheight_neq_one h _)
  exact AlgebraicGeometry.Scheme.height_eq_of_coheight_eq_one π hdim hco

/-- The closure of a point of height `0` (a single point) contains no point of coheight `1`. -/
theorem AlgebraicGeometry.Scheme.coheight_ne_one_of_height_eq_zero {X : AlgebraicGeometry.Scheme.{u}}
    {w : X} (hw : Order.height w = 0) (z' : X.pointClosure w) : Order.coheight z' ≠ 1 := by
  intro hco
  have hnotmax : ¬ IsMax z' := by
    rw [← Order.coheight_eq_zero, hco]; exact one_ne_zero
  obtain ⟨y, hy⟩ := not_isMax_iff.mp hnotmax
  have h1 : (X.pointClosureι w).base z' < (X.pointClosureι w).base y :=
    ((X.pointClosureι w).lt_iff_of_isClosedImmersion _ _).mpr hy
  have h2 : (X.pointClosureι w).base y ≤ w := by
    have hle : y ≤ genericPoint (X.pointClosure w) := genericPoint_specializes y
    have := ((X.pointClosureι w).le_iff_of_isClosedImmersion _ _).mpr hle
    rwa [AlgebraicGeometry.Scheme.pointClosureι_genericPoint w] at this
  have hmin : IsMin w := Order.height_eq_zero.mp hw
  exact (hmin.not_lt) (lt_of_lt_of_le h1 h2)

end
