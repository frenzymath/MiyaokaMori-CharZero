import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProperOverField
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.SchemeDimension
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.Stacks0a21
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.DimensionFiniteness

/-! # Dimension drops along a proper closed subscheme

Let `X` be an integral scheme proper over a field `K`, and `w : W → X` a closed immersion with `W`
integral whose image is not all of `X`. Then `W.dimension < X.dimension` (dimensions truncated
to `ℕ`).

Proof:
1. `X` is of finite type over `K` and integral, so `topologicalKrullDim X = d` is a natural number
   (`X` is nonempty, so it is not `⊥`), and `X.dimension = d` (`Scheme.dimension_spec`).
2. Let `η` be the generic point of `W` and `x := w(η)`. A closed immersion preserves the height of
   points (every point below `x` lies in the closed set `range w`), and `dim W = height(η)`
   (`Order.height_top_eq_krullDim`; the Krull dimension of the specialization order on the underlying
   space is the topological Krull dimension), so `dim W = height(x)`.
3. By Stacks Project, Tag 0A21 (4) (`height_add_coheight_eq_of_locallyOfFiniteType`),
   `height(x) + coheight(x) = d`. Since `range w = closure{x} ≠ X`, `x` is not the generic point `ξ`
   of `X`, so `x < ξ` strictly and `coheight(x) ≥ 1`.
4. Hence `dim W = height(x) ≤ d − 1 < d`; `W` is nonempty (integral), so `dim W ≠ ⊥` and is finite,
   and `W.dimension = height(x) < d = X.dimension`.
References: Stacks Project, Tag 0A21 (4); Hartshorne, Exercise II.3.20.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- A closed immersion preserves the height of points. -/
private theorem height_eq_of_isClosedImmersion' {Y X : AlgebraicGeometry.Scheme.{u}}
    (f : Y ⟶ X) [AlgebraicGeometry.IsClosedImmersion f] (y : Y) :
    Order.height (f.base y) = Order.height y := by
  have hiff : ∀ a b : Y, f.base a ≤ f.base b ↔ a ≤ b := fun a b =>
    f.isClosedEmbedding.isInducing.specializes_iff
  have hlt : ∀ a b : Y, f.base a < f.base b ↔ a < b := fun a b => by
    rw [lt_iff_le_not_ge, lt_iff_le_not_ge, hiff, hiff]
  refine le_antisymm ?_ (Order.height_le_height_apply_of_strictMono _ (fun a b hab => (hlt a b).mpr hab) y)
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
    exact (hlt _ _).mp this⟩
  have hq : q.last ≤ y := by
    rw [← hiff]
    show f.base (g _) ≤ _
    rw [hg]; exact hp
  exact Order.length_le_height (p := q) hq

private theorem krullDim_scheme_eq_topologicalKrullDim'' (X : AlgebraicGeometry.Scheme.{u}) :
    Order.krullDim X = topologicalKrullDim X :=
  (Order.krullDim_eq_of_orderIso
    (@irreducibleSetEquivPoints X _ _ _ : IrreducibleCloseds X ≃o X)).symm

theorem AlgebraicGeometry.Scheme.dimension_lt_of_isClosedImmersion_of_range_ne_univ {K : Type u}
    [Field K] {W X : AlgebraicGeometry.Scheme.{u}}
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of K))] (hX : IsProperOver K X)
    [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsIntegral W]
    (w : W ⟶ X) [AlgebraicGeometry.IsClosedImmersion w] (hw : Set.range w.base ≠ Set.univ) :
    W.dimension < X.dimension := by
  have : AlgebraicGeometry.IsProper (X ↘ AlgebraicGeometry.Spec (CommRingCat.of K)) := hX
  have : AlgebraicGeometry.IsOfFiniteType (X ↘ AlgebraicGeometry.Spec (CommRingCat.of K)) := {}
  -- dim X is a natural number d
  let XV : Variety K := { carrier := X }
  have hfin : topologicalKrullDim X ≠ ⊤ := (Variety.topologicalKrullDim_eq_trdeg XV).2
  have hbot : topologicalKrullDim X ≠ ⊥ := by
    rw [← krullDim_scheme_eq_topologicalKrullDim'']
    exact Order.krullDim_ne_bot_iff.mpr inferInstance
  have hdX := X.dimension_spec hbot hfin
  -- x, the image of the generic point of W
  set x : X := w.base (⊤ : W) with hx
  have hadd := AlgebraicGeometry.height_add_coheight_eq_of_locallyOfFiniteType (k := K) X
    X.dimension hdX x
  have hco : Order.coheight x ≠ 0 := by
    intro h0
    have hmax : IsMax x := Order.coheight_eq_zero.mp h0
    have hxt : x ⤳ (⊤ : X) := hmax (le_top : x ≤ ⊤)
    apply hw
    have hcl : IsClosed (Set.range w.base) := w.isClosedEmbedding.isClosed_range
    have htop : (⊤ : X) ∈ Set.range w.base := hxt.mem_closed hcl ⟨⊤, rfl⟩
    rw [Set.eq_univ_iff_forall]
    intro z
    have hz : (⊤ : X) ⤳ z := (le_top : z ≤ ⊤)
    exact hz.mem_closed hcl htop
  have hhW : topologicalKrullDim W = ((Order.height x : ℕ∞) : WithBot ℕ∞) := by
    rw [← krullDim_scheme_eq_topologicalKrullDim'', ← Order.height_top_eq_krullDim, hx,
      height_eq_of_isClosedImmersion' w]
  have hne : Order.height x ≠ ⊤ := by
    intro ht; rw [ht] at hadd; simp at hadd
  have hcne : Order.coheight x ≠ ⊤ := by
    intro ht; rw [ht] at hadd; simp at hadd
  lift Order.height x to ℕ using hne with n hn
  lift Order.coheight x to ℕ using hcne with c hc
  have hsum : n + c = X.dimension := by exact_mod_cast hadd
  have hc0 : c ≠ 0 := by
    intro h; apply hco; simp [h]
  have hWd : W.dimension = n := by
    unfold AlgebraicGeometry.Scheme.dimension
    rw [hhW]; rfl
  omega

end
