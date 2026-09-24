import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.ProjectiveLineIsSmoothProjectiveCurve
import MiyaokaMori.Paper.S3PositiveLine.Realization.FiberPolynomialExtensionDegreeFiberChartMap
import MiyaokaMori.Paper.S3PositiveLine.Realization.FiberPolynomialExtensionDegreeFiberChartRange
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveLineAutToZero
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveLineStdChartRange
import MiyaokaMori.Paper.S4Completion.RuledSurfaceFiberP1
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpaceCanonicallyOver
import MiyaokaMori.AlgebraicGeometry.Morphisms.AffineLineOverCanonicallyOver

/-! # The fiber of the ruled surface over a closed point is `P¹`, compatibly with the standard chart

The fiber of the ruled surface `W = P(O ⊕ L) → C̃` over a closed point `y` is `P¹_k`, and the fiber of
`Tot(L) → C̃` over `y` is `A¹_k`, **compatibly with the standard chart** `stdChart : A¹ → P¹`
(`t ↦ [1 : t]`) and with the `k`-structures.

Source: §2 of the paper (`W = P(O ⊕ L)`, `Tot(L) = W ∖ σ_L`) and the proof of Theorem 4.2 (the
fiber `P¹` in which the fiber of `U ⊆ Tot(L)` is homogenized). Hartshorne II.7 (projective bundles),
Stacks 01OA/01O3 (relative Proj, base change).

**Route.** Instead of redoing the local triviality `W|_V ≅ P¹ × V` with a controlled chart, we use the
*uncontrolled* isomorphism `e₀ : W_y ≅ P¹_k` over `k` that the library already has
(`ruledSurface.fiber_iso_projectiveLine_over`) and repair the chart
afterwards by an automorphism of `P¹`:
1. the fiber inclusion `Tot(L)_y → W_y` is an open immersion whose image is the complement of one
   point `x₀` ; so `j := (Tot(L)_y → W_y) ≫ e₀.hom`
   is an open immersion `Tot(L)_y → P¹_k` with image `P¹ ∖ {q}`, `q = e₀ x₀`; `{q}` is closed since
   its complement is open;
2. a `k`-automorphism `g` of `P¹_k` moves `q` to `0 = [0 : 1]` ;
3. `stdChart : A¹_k → P¹_k` is an open immersion with image `P¹ ∖ {0}` and is a `k`-morphism
   ;
4. two open immersions with the same image are isomorphic over the target
   (Mathlib `IsOpenImmersion.isoOfRangeEq`): `α : Tot(L)_y ≅ A¹_k` with `α.hom ≫ stdChart = j ≫ g.hom`;
   put `e := e₀ ≪≫ g`. The `k`-compatibility of `α` follows from that of `stdChart`, `g`, `e₀`
   and the fiber square (`totalSpaceFiberToRuledFiber_comp_fiberι`, `totalSpaceIncl_comp_π`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- **** (§2.1 of the paper).
See the module docstring for the route.

Setting: `L` a line bundle on the smooth projective curve `C` over `k = k̄`, `p : Tot(L) → C`,
`π_W : W = P(O ⊕ L) → C`, `y` a closed point of `C`. Claim: there are isomorphisms
`α : Tot(L)_y ≅ A¹_k` and `e : W_y ≅ P¹_k` such that `α` is a `k`-morphism
(`α.hom ≫ (A¹_k → Spec k) = (Tot(L)_y → Spec k)`, the latter being
`p.fiberι y ≫ p ≫ (C → Spec k)` through the canonical `Over` instances) and the inclusion of fibers
`Tot(L)_y → W_y` (`totalSpaceFiberToRuledFiber`) becomes `ProjectiveLine.stdChart k : A¹ → P¹`. -/
theorem totalSpace_fiber_chart_ruledFiber_iso_p1 {k : Type u} [Field k] [IsAlgClosed k]
    {C : SmoothProjectiveCurve k} (L : LineBundle C.toVariety)
    (y : C.toScheme) (hy : IsClosed ({y} : Set C.toScheme)) :
    ∃ (α : (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom.fiber y ≅
          AlgebraicGeometry.Scheme.affineLineOver (AlgebraicGeometry.Spec (CommRingCat.of k)))
      (e : (ruledSurface.π L).fiber y ≅ (ProjectiveLine.asSmoothProjectiveCurve k).toScheme),
      α.hom ≫ (AlgebraicGeometry.Scheme.affineLineOver (AlgebraicGeometry.Spec (CommRingCat.of k)) ↘
          AlgebraicGeometry.Spec (CommRingCat.of k)) =
        ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom.fiber y ↘
          AlgebraicGeometry.Spec (CommRingCat.of k)) ∧
      totalSpaceFiberToRuledFiber L y ≫ e.hom = α.hom ≫ ProjectiveLine.stdChart k := by
  -- Step 0: the uncontrolled isomorphism `e₀ : W_y ≅ P¹_k` over `k`
  obtain ⟨e₀, he₀⟩ := ruledSurface.fiber_iso_projectiveLine_over L y hy
  -- Step 1: `j := (Tot(L)_y → W_y) ≫ e₀.hom` is an open immersion with image `P¹ ∖ {q}`
  obtain ⟨x₀, hx₀⟩ := exists_range_totalSpaceFiberToRuledFiber_eq_compl_singleton L y
  have hm : AlgebraicGeometry.IsOpenImmersion (totalSpaceFiberToRuledFiber L y) :=
    totalSpaceFiberToRuledFiber_isOpenImmersion L y
  set j : (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom.fiber y ⟶ ProjectiveLine k :=
    totalSpaceFiberToRuledFiber L y ≫ e₀.hom with hj
  have hj_oi : AlgebraicGeometry.IsOpenImmersion j := inferInstance
  set q : ProjectiveLine k := e₀.hom x₀ with hq
  have hjrange : Set.range j = ({q}ᶜ : Set (ProjectiveLine k)) :=
    AlgebraicGeometry.Scheme.range_comp_iso_hom_eq_compl_singleton _ e₀ x₀ hx₀
  have hq_closed : IsClosed ({q} : Set (ProjectiveLine k)) := by
    have h := j.isOpenEmbedding.isOpen_range.isClosed_compl
    rwa [hjrange, compl_compl] at h
  -- Step 2: move `q` to `0 = [0 : 1]` by a `k`-automorphism
  obtain ⟨g, hg_over, hgq⟩ := ProjectiveLine.exists_aut_over_map_eq_zero q hq_closed
  set j' : (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom.fiber y ⟶ ProjectiveLine k :=
    j ≫ g.hom with hj'
  have hj'_oi : AlgebraicGeometry.IsOpenImmersion j' := inferInstance
  -- Step 3: `j'` and `stdChart` have the same image `P¹ ∖ {0}`
  have hrange_eq : Set.range j' = Set.range (ProjectiveLine.stdChart k) := by
    rw [ProjectiveLine.range_stdChart, ← hgq]
    exact AlgebraicGeometry.Scheme.range_comp_iso_hom_eq_compl_singleton _ g q hjrange
  -- Step 4: the isomorphism `α`
  let α : (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom.fiber y ≅
      AlgebraicGeometry.Scheme.affineLineOver (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq j' (ProjectiveLine.stdChart k) hrange_eq
  have hα : α.hom ≫ ProjectiveLine.stdChart k = j' :=
    AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq_hom_fac j' (ProjectiveLine.stdChart k) hrange_eq
  refine ⟨α, e₀ ≪≫ g, ?_, ?_⟩
  · -- `α` is over `k`
    change α.hom ≫ AlgebraicGeometry.Scheme.affineLineOver.toBase (AlgebraicGeometry.Spec (CommRingCat.of k)) =
      (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom.fiberι y ≫
        ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ≫
          (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))
    have he₀' : e₀.hom ≫ ProjectiveSpace.toSpecBase 1 k =
        (ruledSurface.π L).fiberι y ≫
          (ruledSurface.π L ≫ (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) := he₀
    have h1 : α.hom ≫ ProjectiveLine.stdChart k ≫ ProjectiveSpace.toSpecBase 1 k =
        totalSpaceFiberToRuledFiber L y ≫ e₀.hom ≫ g.hom ≫ ProjectiveSpace.toSpecBase 1 k := by
      rw [← Category.assoc, hα, hj', hj]
      simp only [Category.assoc]
    rw [← ProjectiveLine.stdChart_comp_toSpecBase, h1, hg_over, he₀',
      reassoc_of% (totalSpaceFiberToRuledFiber_comp_fiberι L y),
      reassoc_of% (ruledSurface.totalSpaceIncl_comp_π L)]
  · -- the chart compatibility
    rw [hα, hj', hj, Iso.trans_hom, Category.assoc]

end
