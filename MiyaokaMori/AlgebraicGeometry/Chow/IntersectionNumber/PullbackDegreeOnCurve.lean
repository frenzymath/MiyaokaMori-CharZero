import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Morphisms.ConstantMorphism
import MiyaokaMori.AlgebraicGeometry.Varieties.FunctionField.FunctionFieldExtensionDegree
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.FundamentalClassLemmas
import MiyaokaMori.AlgebraicGeometry.Chow.Pushforward.VarietyCyclePushforward
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.SmoothProjectiveVariety
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ChowGroupDegreePushforward
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.CapDivisorEqFirstChernClass
import MiyaokaMori.AlgebraicGeometry.Chow.Pushforward.ChowPushforward
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.ProjectionFormula
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundlePullback
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.IntegralCurve
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.LineBundleCurveIntersection
import MiyaokaMori.AlgebraicGeometry.Chow.Pushforward.Stacks02r5
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.PointClosureKrullDim
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.IdealSheafCycleEqPushforward
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.FirstChernCapFundamentalCycle
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.PointClosureDimensionTrdeg
import MiyaokaMori.AlgebraicGeometry.Varieties.FunctionField.ResidueFieldBaseTower
import MiyaokaMori.AlgebraicGeometry.Varieties.Points.ReducedPointClosure
import MiyaokaMori.AlgebraicGeometry.Morphisms.ClosedImmersionCycles
-- The following imports are not used by this file; downstream modules reach them through it.
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.TwistInvertibleSufficientlyDivisible
import MiyaokaMori.Paper.S2WeightedJets.Intersection.SplitWeightedAlgebra
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedProjectivizationOfBundle
import MiyaokaMori.AlgebraicGeometry.Modules.RelativelyVeryAmple
import MiyaokaMori.Paper.S2WeightedJets.Ygg.WeightedProjectivization
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.TruncatedJetAlgebra

/-! # Degree of a pulled-back line bundle on an integral curve

The intersection number of a pulled-back line bundle with an integral curve `Γ`: it is `0` when `Φ|_Γ`
is constant; otherwise `Γ` maps onto an integral curve `R` and the intersection number is
`[K(Γ):K(R)] × (L·R)` (§4 of the paper, proof of Lemma 5.1; Stacks 02SU projection
formula + 02R4 pushforward coefficients + 0A21 dimension = transcendence degree).

## Route

1. `LineBundle.inter_pullback`: `(Φ^*L) ⬝ Z = L ⬝ Φ_*Z` for every 1-cycle `Z` on `S`.
   Degree is compatible with proper pushforward (`ChowGroup.degree_chowPushforward`), and the
   projection formula `Φ_*(c₁(Φ^*L) ∩ α) = c₁(L) ∩ Φ_*α` (`chowPushforward_firstChernClass_pullback`)
   is applied directly.
2. `[Γ]` is the one-point cycle at `ι(η)` (`IntegralCurve.fundamentalClass_coe_eq_single`), and the
   pushforward of a one-point cycle is computed by `AlgebraicCycle.properPushforward_single`.
3. Constant case: the image point is closed (proper ⇒ closed map), so its height is `0 ≠ 1`, and
   the pushforward coefficient vanishes (`cyclePushforward_fundamentalClass_eq_zero_of_isConstant`).
4. Nonconstant case: `x := Φ(ι η)` has `dim closure{x} = 1`
   (`IntegralCurve.pointClosureDimension_image_genericPoint_eq_one`: not a closed point, so height ≥ 1;
   `trdeg_k κ(x) ≤ trdeg_k κ(η) = 1` by Stacks 0A21). `R` is the reduced closure of `x`
   (`IntegralCurve.imageCurve`), `g : Γ → R` is the closed-immersion lift (`IntegralCurve.toImageCurve`),
   and `Φ_*[Γ] = R.ι_* g_* [η] = deg(g)·[R]` by `properPushforward_comp` (Stacks 02R5).
-/
set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Projection formula for intersection numbers: `(Φ^*L) ⬝ Z = L ⬝ Φ_* Z`. -/
theorem LineBundle.inter_pullback {k : Type u} [Field k] [IsAlgClosed k] {S X : SmoothProjectiveVariety k}
    (Φ : S.toScheme ⟶ X.toScheme) [Φ.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.IsProper Φ]
    (L : LineBundle X.toVariety) (Z : OneCycle S.toVariety) :
    (Φ ^* L) ⬝ Z = L ⬝ (cyclePushforward Φ 1 Z) := by
  have hΦ : Φ ≫ X.structureMorphism = S.structureMorphism :=
    CategoryTheory.comp_over Φ (AlgebraicGeometry.Spec (CommRingCat.of k))
  let : AlgebraicGeometry.Scheme.Modules.IsLineBundle (X := X.toScheme) L.toModules := by
    refine ⟨fun y ↦ ?_⟩
    exact SheafOfModules.IsLineBundle.locally_trivial (M := L.toModules) y
  change ChowGroup.degree S
      (AlgebraicGeometry.firstChernClass
        ((AlgebraicGeometry.Scheme.Modules.pullback Φ).obj L.toModules) 1
        (AlgebraicGeometry.ChowGroup.mk Z)) =
    ChowGroup.degree X
      (AlgebraicGeometry.firstChernClass L.toModules 1
        (AlgebraicGeometry.ChowGroup.mk (cyclePushforward Φ 1 Z)))
  rw [← ChowGroup.degree_chowPushforward Φ hΦ]
  congr 1
  rw [← chowPushforward_mk_variety Φ 1 Z]
  exact AlgebraicGeometry.chowPushforward_firstChernClass_pullback (k := k) Φ L.toModules 0
    (QuotientAddGroup.mk Z)


open Classical in
/-- Pushforward of a one-point cycle: `f_*(n·[x]) = n·mapCoeff(x)·[f x]`. -/
theorem AlgebraicGeometry.AlgebraicCycle.properPushforward_single {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) [AlgebraicGeometry.IsProper f] (x : X) (n : ℤ) :
    AlgebraicGeometry.AlgebraicCycle.properPushforward f
        (Function.locallyFinsuppWithin.single x n) =
      Function.locallyFinsuppWithin.single (f.base x)
        (n * ((AlgebraicGeometry.AlgebraicCycle.mapCoeff f (Order.height (α := X))
          (Order.height (α := Y)) x : ℕ) : ℤ)) := by
  ext z
  have happ : AlgebraicGeometry.AlgebraicCycle.properPushforward f
      (Function.locallyFinsuppWithin.single x n) z =
      ∑ᶠ y ∈ f.base ⁻¹' {z}, (Function.locallyFinsuppWithin.single x n : X → ℤ) y *
        ((AlgebraicGeometry.AlgebraicCycle.mapCoeff f (Order.height (α := X))
          (Order.height (α := Y)) y : ℕ) : ℤ) := rfl
  rw [happ]
  by_cases hz : z = f.base x
  · subst hz
    rw [finsum_mem_inter_support_eq' _ _ ({x} : Set X)]
    · rw [finsum_mem_singleton]
      simp
    · intro y hy
      have hyx : y = x := by
        by_contra hne
        apply hy
        simp [hne]
      subst hyx
      simp
  · rw [Function.locallyFinsuppWithin.single_apply, if_neg hz]
    apply finsum_mem_eq_zero_of_forall_eq_zero
    intro y hy
    have hfy : f.base y = z := hy
    have hyx : y ≠ x := fun h => hz (by rw [← hfy, h])
    simp [hyx]

private theorem coe_cast_cycleGroup {k : Type u} [Field k] {X : Variety k}
    {i j : ℕ} (h : i = j) (c : CycleGroup X i) :
    ((cast (congrArg (fun n : ℕ => ↥(CycleGroup X n)) h) c : CycleGroup X j) :
      AlgebraicGeometry.AlgebraicCycle X.toScheme ℤ) = c.1 := by
  cases h
  rfl

open Classical in
/-- `[Γ]`, as a cycle on the ambient variety, is the one-point cycle at the image of the generic point. -/
theorem IntegralCurve.fundamentalClass_coe_eq_single {k : Type u} [Field k] {X : Variety k}
    (Γ : IntegralCurve k X.toScheme) :
    (Γ.fundamentalClass : AlgebraicGeometry.AlgebraicCycle X.toScheme ℤ) =
      Function.locallyFinsuppWithin.single (Γ.ι.base (genericPoint Γ.carrier)) (1 : ℤ) := by
  unfold IntegralCurve.fundamentalClass
  rw [coe_cast_cycleGroup Γ.dimension_eq_one]
  exact ClosedSubvariety.fundamentalClass_eq_single Γ.toClosedSubvariety

/-- The value of the graded pushforward is Mathlib's `properPushforward` (weights `Order.height`). -/
theorem cyclePushforward_coe {k : Type u} [Field k] {X Y : Variety k}
    (f : X.toScheme ⟶ Y.toScheme) [AlgebraicGeometry.IsProper f] (i : ℕ) (c : CycleGroup X i) :
    ((cyclePushforward f i c : CycleGroup Y i) : AlgebraicGeometry.AlgebraicCycle Y.toScheme ℤ) =
      AlgebraicGeometry.AlgebraicCycle.properPushforward f c.1 :=
  rfl

open Classical in
/-- The image of the generic point of an integral curve has height 1 in the ambient variety. -/
theorem IntegralCurve.height_image_genericPoint {k : Type u} [Field k] {X : Variety k}
    (Γ : IntegralCurve k X.toScheme) :
    Order.height (Γ.ι.base (genericPoint Γ.carrier)) = (1 : ℕ∞) := by
  have hmem := Γ.fundamentalClass.2
  change ∀ x : X.toScheme, (Γ.fundamentalClass : AlgebraicGeometry.AlgebraicCycle X.toScheme ℤ) x ≠ 0 →
    Order.height x = ((1 : ℕ) : ℕ∞) at hmem
  have := hmem (Γ.ι.base (genericPoint Γ.carrier))
    (by rw [IntegralCurve.fundamentalClass_coe_eq_single]; simp)
  simpa using this

/-- Constant case: `Φ_*[Γ] = 0` when `Φ` contracts `Γ` to a point. -/
theorem cyclePushforward_fundamentalClass_eq_zero_of_isConstant {k : Type u} [Field k]
    {S X : SmoothProjectiveVariety k} (Φ : S.toScheme ⟶ X.toScheme) [AlgebraicGeometry.IsProper Φ]
    (Γ : IntegralCurve k S.toScheme) (h : IsConstantMorphism (Γ.ι ≫ Φ)) :
    cyclePushforward Φ 1 Γ.fundamentalClass = 0 := by
  classical
  apply Subtype.ext
  rw [cyclePushforward_coe, IntegralCurve.fundamentalClass_coe_eq_single,
    AlgebraicGeometry.AlgebraicCycle.properPushforward_single]
  set η := genericPoint Γ.carrier
  set x := Φ.base (Γ.ι.base η) with hxdef
  have hx : ∀ γ : Γ.carrier, (Γ.ι ≫ Φ).base γ = x := by
    obtain ⟨y, hy⟩ := h
    intro γ
    rw [hy γ]
    exact (hy η).symm
  have h1 : Order.height (Γ.ι.base η) = (1 : ℕ∞) := Γ.height_image_genericPoint
  have hcl : IsClosed ({x} : Set X.toScheme) := by
    have hrange : Set.range (Γ.ι ≫ Φ).base = {x} := by
      ext y
      constructor
      · rintro ⟨γ, rfl⟩
        exact hx γ
      · rintro rfl
        exact ⟨η, hx η⟩
    rw [← hrange]
    exact (Γ.ι ≫ Φ).isClosedMap.isClosed_range
  have h0 : Order.height x = 0 := by
    rw [Order.height_eq_zero]
    intro y hy
    have hmem : y ∈ closure ({x} : Set X.toScheme) := specializes_iff_mem_closure.mp hy
    rw [hcl.closure_eq] at hmem
    rw [Set.mem_singleton_iff.mp hmem]
  have hcoeff : AlgebraicGeometry.AlgebraicCycle.mapCoeff Φ (Order.height (α := S.toScheme))
      (Order.height (α := X.toScheme)) (Γ.ι.base η) = 0 := by
    unfold AlgebraicGeometry.AlgebraicCycle.mapCoeff
    rw [if_neg]
    rw [h1, h0]
    exact one_ne_zero
  rw [hcoeff]
  simp
  rfl


/-- If `Φ|_Γ` is not constant, the closure of the image of the generic point of `Γ` is a curve:
`dim closure{Φ(ι η)} = 1`. Lower bound: the image point is not closed (else `Φ|_Γ` would be constant),
so its height is ≥ 1. Upper bound: `dim closure{x} = trdeg_k κ(x) ≤ trdeg_k κ(η) = dim Γ = 1`
(Stacks 0A21, via `MiyaokaMori.PointClosureTrdeg.pointClosureDimension_eq_trdeg`). -/
theorem IntegralCurve.pointClosureDimension_image_genericPoint_eq_one {k : Type u} [Field k]
    {S X : SmoothProjectiveVariety k} (Φ : S.toScheme ⟶ X.toScheme)
    [Φ.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))] [AlgebraicGeometry.IsProper Φ]
    (Γ : IntegralCurve k S.toScheme) (h : ¬ IsConstantMorphism (Γ.ι ≫ Φ)) :
    AlgebraicGeometry.Intersection.pointClosureDimension X.toScheme
      ((Γ.ι ≫ Φ).base (genericPoint Γ.carrier)) = 1 := by
  set f := Γ.ι ≫ Φ with hfdef
  set η := genericPoint Γ.carrier with hηdef
  set x := f.base η with hxdef
  have hirr : IrreducibleSpace Γ.carrier := inferInstance
  -- lower bound: x is not a closed point
  have hnotcl : ¬ IsClosed ({x} : Set X.toScheme) := by
    intro hcl
    apply h
    refine ⟨x, fun γ => ?_⟩
    have hγ : γ ∈ closure ({η} : Set Γ.carrier) := by
      rw [hηdef, genericPoint_closure]
      trivial
    have hmem : f.base γ ∈ closure (f.base '' ({η} : Set Γ.carrier)) :=
      image_closure_subset_closure_image f.base.hom.continuous ⟨γ, hγ, rfl⟩
    rw [Set.image_singleton, hcl.closure_eq] at hmem
    exact hmem
  have hpos : (1 : ℕ∞) ≤ Order.height x := by
    rw [Order.one_le_iff_pos, Order.height_pos]
    intro hmin
    apply hnotcl
    have hcl : closure ({x} : Set X.toScheme) = {x} := by
      apply Set.Subset.antisymm _ subset_closure
      intro y hy
      have hle : y ≤ x := specializes_iff_mem_closure.mpr hy
      have hge : x ≤ y := hmin hle
      exact (Specializes.antisymm hge hle).eq
    exact closure_eq_iff_isClosed.mp hcl
  -- upper bound via transcendence degree
  have hup : AlgebraicGeometry.Intersection.pointClosureDimension X.toScheme x ≤ 1 := by
    let X' : AlgebraicGeometry.Proj.SchemeOver k := ⟨X.toScheme, X.structureMorphism⟩
    let Γ' : AlgebraicGeometry.Proj.SchemeOver k := ⟨Γ.carrier, f ≫ X.structureMorphism⟩
    have hF : f ≫ X'.toBase = Γ'.toBase := rfl
    have : AlgebraicGeometry.LocallyOfFiniteType X'.toBase :=
      inferInstanceAs (AlgebraicGeometry.LocallyOfFiniteType X.structureMorphism)
    have : AlgebraicGeometry.LocallyOfFiniteType Γ'.toBase :=
      inferInstanceAs (AlgebraicGeometry.LocallyOfFiniteType (f ≫ X.structureMorphism))
    have : AlgebraicGeometry.IsIntegral Γ'.scheme := Γ.isIntegral
    let _ : Algebra k (X.toScheme.residueField x) :=
      (AlgebraicGeometry.Intersection.pointBaseMap X'.toBase x).hom.toAlgebra
    let _ : Algebra k (Γ.carrier.residueField η) :=
      (AlgebraicGeometry.Intersection.pointBaseMap Γ'.toBase η).hom.toAlgebra
    have hX := MiyaokaMori.PointClosureTrdeg.pointClosureDimension_eq_trdeg X' x
    have hΓ := MiyaokaMori.PointClosureTrdeg.pointClosureDimension_eq_trdeg Γ' η
    have hΓdim : AlgebraicGeometry.Intersection.pointClosureDimension Γ'.scheme η = 1 := by
      change AlgebraicGeometry.Intersection.pointClosureDimension Γ.carrier (genericPoint Γ.carrier) = 1
      rw [MiyaokaMori.PointClosureTrdeg.genericPoint_pointClosureDimension_eq]
      exact Γ.dim_eq_one
    let φ : X.toScheme.residueField x →ₐ[k] Γ.carrier.residueField η :=
      { toRingHom := (f.residueFieldMap η).hom
        commutes' := fun t => congrArg
          (fun m : CommRingCat.of k ⟶ Γ.carrier.residueField η => m.hom t)
          (AlgebraicGeometry.Intersection.pointBaseMap_residueFieldMap (X := Γ') (Y := X') f hF η) }
    have htr : Algebra.trdeg k (X.toScheme.residueField x) ≤
        Algebra.trdeg k (Γ.carrier.residueField η) :=
      trdeg_le_of_injective φ (f.residueFieldMap η).hom.injective
    have hmono : Cardinal.toENat (Algebra.trdeg k (X.toScheme.residueField x)) ≤
        Cardinal.toENat (Algebra.trdeg k (Γ.carrier.residueField η)) :=
      OrderHomClass.mono Cardinal.toENat htr
    calc AlgebraicGeometry.Intersection.pointClosureDimension X.toScheme x
        = (Cardinal.toENat (Algebra.trdeg k (X.toScheme.residueField x)) : WithBot ℕ∞) := hX
      _ ≤ (Cardinal.toENat (Algebra.trdeg k (Γ.carrier.residueField η)) : WithBot ℕ∞) :=
          WithBot.coe_le_coe.mpr hmono
      _ = AlgebraicGeometry.Intersection.pointClosureDimension Γ'.scheme η := hΓ.symm
      _ = 1 := hΓdim
  rw [AlgebraicGeometry.Intersection.pointClosureDimension_eq_height] at hup ⊢
  have hle : Order.height x ≤ 1 := WithBot.coe_le_one.mp hup
  rw [le_antisymm hle hpos]
  rfl


/-! ## The image curve `R = Φ(Γ)` and the factorization `Γ → R` -/

/-- The reduced closure of `Φ(ι(η))` (η the generic point of Γ), as an integral curve in `X`
(Stacks 01J3 reduced induced structure; dimension 1 by
`IntegralCurve.pointClosureDimension_image_genericPoint_eq_one`). -/
noncomputable def IntegralCurve.imageCurve {k : Type u} [Field k]
    {S X : SmoothProjectiveVariety k} (Φ : S.toScheme ⟶ X.toScheme)
    [Φ.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))] [AlgebraicGeometry.IsProper Φ]
    (Γ : IntegralCurve k S.toScheme) (h : ¬ IsConstantMorphism (Γ.ι ≫ Φ)) :
    IntegralCurve k X.toScheme where
  carrier := AlgebraicGeometry.Intersection.ReducedPointClosure.scheme X.toScheme
    ((Γ.ι ≫ Φ).base (genericPoint Γ.carrier))
  ι := AlgebraicGeometry.Intersection.ReducedPointClosure.inclusion X.toScheme
    ((Γ.ι ≫ Φ).base (genericPoint Γ.carrier))
  isClosedImmersion := AlgebraicGeometry.Intersection.ReducedPointClosure.inclusion_isClosedImmersion _ _
  isIntegral := AlgebraicGeometry.Intersection.ReducedPointClosure.scheme_isIntegral _ _
  -- closed immersion ≫ proper = proper (Mathlib instance)
  isProper := by
    have : AlgebraicGeometry.IsProper (X.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      X.isProper_structureMorphism
    infer_instance
  dim_eq_one := (AlgebraicGeometry.Intersection.ReducedPointClosure.dimension_eq X.toScheme _).trans
    (Γ.pointClosureDimension_image_genericPoint_eq_one Φ h)

theorem IntegralCurve.imageCurve_ι {k : Type u} [Field k]
    {S X : SmoothProjectiveVariety k} (Φ : S.toScheme ⟶ X.toScheme)
    [Φ.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))] [AlgebraicGeometry.IsProper Φ]
    (Γ : IntegralCurve k S.toScheme) (h : ¬ IsConstantMorphism (Γ.ι ≫ Φ)) :
    (Γ.imageCurve Φ h).ι = AlgebraicGeometry.Intersection.ReducedPointClosure.inclusion X.toScheme
      ((Γ.ι ≫ Φ).base (genericPoint Γ.carrier)) := rfl

theorem IntegralCurve.imageCurve_ι_genericPoint {k : Type u} [Field k]
    {S X : SmoothProjectiveVariety k} (Φ : S.toScheme ⟶ X.toScheme)
    [Φ.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))] [AlgebraicGeometry.IsProper Φ]
    (Γ : IntegralCurve k S.toScheme) (h : ¬ IsConstantMorphism (Γ.ι ≫ Φ)) :
    (Γ.imageCurve Φ h).ι.base (genericPoint (Γ.imageCurve Φ h).carrier) =
      (Γ.ι ≫ Φ).base (genericPoint Γ.carrier) := by
  set x := (Γ.ι ≫ Φ).base (genericPoint Γ.carrier)
  have h1 : genericPoint (Γ.imageCurve Φ h).carrier =
      AlgebraicGeometry.Intersection.ReducedPointClosure.generic X.toScheme x :=
    (genericPoint_spec _).eq (AlgebraicGeometry.Intersection.ReducedPointClosure.generic_spec X.toScheme x)
  rw [h1]
  rfl

/-- The kernel of a morphism out of a reduced scheme is a radical ideal sheaf. -/
theorem AlgebraicGeometry.Scheme.Hom.ker_eq_radical_of_isReduced {Y X : AlgebraicGeometry.Scheme.{u}}
    (f : Y ⟶ X) [AlgebraicGeometry.QuasiCompact f] [AlgebraicGeometry.IsReduced Y] :
    f.ker = f.ker.radical := by
  ext U x
  have hr : (f.ker.ideal U).IsRadical := by
    rw [AlgebraicGeometry.Scheme.Hom.ker_apply]
    intro a ha
    obtain ⟨n, hn⟩ := Ideal.mem_radical_iff.mp ha
    rw [RingHom.mem_ker] at hn ⊢
    rw [map_pow] at hn
    exact IsNilpotent.eq_zero ⟨n, hn⟩
  rw [AlgebraicGeometry.Scheme.IdealSheafData.radical_ideal]
  rw [Ideal.radical_eq_iff.mpr hr]

/-- `Γ.ι ≫ Φ` factors through the image curve `R`. -/
theorem IntegralCurve.imageCurve_ker_le {k : Type u} [Field k]
    {S X : SmoothProjectiveVariety k} (Φ : S.toScheme ⟶ X.toScheme)
    [Φ.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))] [AlgebraicGeometry.IsProper Φ]
    (Γ : IntegralCurve k S.toScheme) (h : ¬ IsConstantMorphism (Γ.ι ≫ Φ)) :
    (Γ.imageCurve Φ h).ι.ker ≤ (Γ.ι ≫ Φ).ker := by
  set f := Γ.ι ≫ Φ with hfdef
  set η := genericPoint Γ.carrier with hηdef
  set x := f.base η with hxdef
  have hirr : IrreducibleSpace Γ.carrier := inferInstance
  have hrange : Set.range f.base ⊆ closure ({x} : Set X.toScheme) := by
    rintro _ ⟨γ, rfl⟩
    have hγ : γ ∈ closure ({η} : Set Γ.carrier) := by
      rw [hηdef, genericPoint_closure]
      trivial
    have hmem : f.base γ ∈ closure (f.base '' ({η} : Set Γ.carrier)) :=
      image_closure_subset_closure_image f.base.hom.continuous ⟨γ, hγ, rfl⟩
    rwa [Set.image_singleton] at hmem
  have hsupp : f.ker.support ≤ ⟨closure ({x} : Set X.toScheme), isClosed_closure⟩ := by
    change (f.ker.support : Set X.toScheme) ⊆ closure ({x} : Set X.toScheme)
    rw [f.support_ker]
    exact closure_minimal hrange isClosed_closure
  rw [IntegralCurve.imageCurve_ι]
  change (AlgebraicGeometry.Intersection.ReducedPointClosure.ideal X.toScheme x).subschemeι.ker ≤ f.ker
  rw [AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι]
  calc
    AlgebraicGeometry.Intersection.ReducedPointClosure.ideal X.toScheme x
        = AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal
            ⟨closure ({x} : Set X.toScheme), isClosed_closure⟩ := rfl
    _ ≤ AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal f.ker.support :=
        AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal_antimono hsupp
    _ = f.ker.radical := AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal_support
    _ = f.ker := (f.ker_eq_radical_of_isReduced).symm

/-- The factorization `g : Γ → R` of `Γ.ι ≫ Φ` through the image curve. -/
noncomputable def IntegralCurve.toImageCurve {k : Type u} [Field k]
    {S X : SmoothProjectiveVariety k} (Φ : S.toScheme ⟶ X.toScheme)
    [Φ.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))] [AlgebraicGeometry.IsProper Φ]
    (Γ : IntegralCurve k S.toScheme) (h : ¬ IsConstantMorphism (Γ.ι ≫ Φ)) :
    Γ.carrier ⟶ (Γ.imageCurve Φ h).carrier :=
  AlgebraicGeometry.IsClosedImmersion.lift (Γ.imageCurve Φ h).ι (Γ.ι ≫ Φ) (Γ.imageCurve_ker_le Φ h)

theorem IntegralCurve.toImageCurve_fac {k : Type u} [Field k]
    {S X : SmoothProjectiveVariety k} (Φ : S.toScheme ⟶ X.toScheme)
    [Φ.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))] [AlgebraicGeometry.IsProper Φ]
    (Γ : IntegralCurve k S.toScheme) (h : ¬ IsConstantMorphism (Γ.ι ≫ Φ)) :
    Γ.toImageCurve Φ h ≫ (Γ.imageCurve Φ h).ι = Γ.ι ≫ Φ :=
  AlgebraicGeometry.IsClosedImmersion.lift_fac _ _ _

theorem IntegralCurve.toImageCurve_genericPoint {k : Type u} [Field k]
    {S X : SmoothProjectiveVariety k} (Φ : S.toScheme ⟶ X.toScheme)
    [Φ.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))] [AlgebraicGeometry.IsProper Φ]
    (Γ : IntegralCurve k S.toScheme) (h : ¬ IsConstantMorphism (Γ.ι ≫ Φ)) :
    (Γ.toImageCurve Φ h).base (genericPoint Γ.carrier) = genericPoint (Γ.imageCurve Φ h).carrier := by
  apply (Γ.imageCurve Φ h).ι.isClosedEmbedding.injective
  rw [IntegralCurve.imageCurve_ι_genericPoint]
  change ((Γ.toImageCurve Φ h) ≫ (Γ.imageCurve Φ h).ι).base (genericPoint Γ.carrier) = _
  rw [IntegralCurve.toImageCurve_fac]

/-- `g` is proper (it is a morphism to a closed subscheme with proper composite). -/
theorem IntegralCurve.toImageCurve_isProper {k : Type u} [Field k]
    {S X : SmoothProjectiveVariety k} (Φ : S.toScheme ⟶ X.toScheme)
    [Φ.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))] [AlgebraicGeometry.IsProper Φ]
    (Γ : IntegralCurve k S.toScheme) (h : ¬ IsConstantMorphism (Γ.ι ≫ Φ)) :
    AlgebraicGeometry.IsProper (Γ.toImageCurve Φ h) := by
  have hcomp : AlgebraicGeometry.IsProper (Γ.toImageCurve Φ h ≫ (Γ.imageCurve Φ h).ι) := by
    rw [IntegralCurve.toImageCurve_fac]
    infer_instance
  exact CategoryTheory.MorphismProperty.of_postcomp (W := @AlgebraicGeometry.IsProper)
    (W' := @AlgebraicGeometry.IsSeparated) (Γ.toImageCurve Φ h) (Γ.imageCurve Φ h).ι
    inferInstance hcomp

/-- Heights of generic points of integral curves are 1. -/
theorem IntegralCurve.height_genericPoint {k : Type u} [Field k] {X : AlgebraicGeometry.Scheme.{u}}
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (Γ : IntegralCurve k X) :
    Order.height (genericPoint Γ.carrier) = (1 : ℕ∞) := by
  have := AlgebraicGeometry.height_genericPoint_of_dimension_pos (X := Γ.carrier) (m := 0)
    (by simpa using Γ.carrier_dimension)
  simpa using this

/-- Pushforward congruence in the morphism (the `IsProper` instance depends on it). -/
private theorem properPushforward_congr_hom {A B : AlgebraicGeometry.Scheme.{u}} (g₁ g₂ : A ⟶ B)
    [AlgebraicGeometry.IsProper g₁] [AlgebraicGeometry.IsProper g₂] (h : g₁ = g₂)
    (c : AlgebraicGeometry.AlgebraicCycle A ℤ) :
    AlgebraicGeometry.AlgebraicCycle.properPushforward g₁ c =
      AlgebraicGeometry.AlgebraicCycle.properPushforward g₂ c := by
  subst h
  rfl

open Classical in
/-- Nonconstant case: `Φ_*[Γ] = [K(Γ):K(R)]·[R]` (Stacks 02R4 / Fulton §1.4). -/
theorem cyclePushforward_fundamentalClass_eq_of_not_isConstant {k : Type u} [Field k]
    {S X : SmoothProjectiveVariety k} (Φ : S.toScheme ⟶ X.toScheme)
    [Φ.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))] [AlgebraicGeometry.IsProper Φ]
    (Γ : IntegralCurve k S.toScheme) (h : ¬ IsConstantMorphism (Γ.ι ≫ Φ)) :
    cyclePushforward Φ 1 Γ.fundamentalClass =
      (functionFieldDegree (Γ.toImageCurve Φ h) : ℤ) • (Γ.imageCurve Φ h).fundamentalClass := by
  set g := Γ.toImageCurve Φ h with hg
  have hgproper : AlgebraicGeometry.IsProper g := Γ.toImageCurve_isProper Φ h
  set η := genericPoint Γ.carrier with hηdef
  apply Subtype.ext
  rw [cyclePushforward_coe, IntegralCurve.fundamentalClass_coe_eq_single]
  -- [Γ]_S = ι_*[η]
  have hΓ : Function.locallyFinsuppWithin.single (Γ.ι.base η) (1 : ℤ) =
      AlgebraicGeometry.AlgebraicCycle.properPushforward Γ.ι
        (Function.locallyFinsuppWithin.single η (1 : ℤ)) := by
    rw [AlgebraicGeometry.AlgebraicCycle.properPushforward_single]
    congr 1
    unfold AlgebraicGeometry.AlgebraicCycle.mapCoeff
    rw [if_pos (Γ.ι.height_of_isClosedImmersion η).symm,
      AlgebraicGeometry.Intersection.closedImmersion_residueDegree_eq_one]
    simp
  rw [hΓ, AlgebraicGeometry.AlgebraicCycle.properPushforward_comp,
    properPushforward_congr_hom (Γ.ι ≫ Φ) (g ≫ (Γ.imageCurve Φ h).ι) (Γ.toImageCurve_fac Φ h).symm,
    ← AlgebraicGeometry.AlgebraicCycle.properPushforward_comp,
    AlgebraicGeometry.AlgebraicCycle.properPushforward_single,
    AlgebraicGeometry.AlgebraicCycle.properPushforward_single]
  -- right-hand side
  rw [AddSubgroupClass.coe_zsmul, IntegralCurve.fundamentalClass_coe_eq_single]
  have hgη : g.base η = genericPoint (Γ.imageCurve Φ h).carrier := Γ.toImageCurve_genericPoint Φ h
  have hcoeffR : AlgebraicGeometry.AlgebraicCycle.mapCoeff (Γ.imageCurve Φ h).ι (Order.height (α := (Γ.imageCurve Φ h).carrier))
      (Order.height (α := X.toScheme)) (g.base η) = 1 := by
    unfold AlgebraicGeometry.AlgebraicCycle.mapCoeff
    rw [if_pos ((Γ.imageCurve Φ h).ι.height_of_isClosedImmersion _).symm,
      AlgebraicGeometry.Intersection.closedImmersion_residueDegree_eq_one]
  have hcoeffg : AlgebraicGeometry.AlgebraicCycle.mapCoeff g (Order.height (α := Γ.carrier))
      (Order.height (α := (Γ.imageCurve Φ h).carrier)) η = functionFieldDegree g := by
    unfold AlgebraicGeometry.AlgebraicCycle.mapCoeff
    rw [if_pos]
    · rfl
    · rw [hgη, Γ.height_genericPoint, (Γ.imageCurve Φ h).height_genericPoint]
  rw [hcoeffR, hcoeffg, hgη]
  ext z
  simp only [Function.locallyFinsuppWithin.coe_zsmul, Pi.smul_apply,
    Function.locallyFinsuppWithin.single_apply, smul_eq_mul]
  split_ifs <;> simp

set_option linter.unusedVariables false in
/-- **Weighted degree of a pulled-back line bundle on an integral curve** (§4 of the paper).
If `Φ|_Γ` is constant then `(Φ^*L)·Γ = 0`; otherwise `Φ(Γ)` is an integral curve `R`, `Φ|_Γ`
factors as `g : Γ → R` sending generic point to generic point, and `(Φ^*L)·Γ = [K(Γ):K(R)]·(L·R)`.
Proof: `LineBundle.inter_pullback` (projection formula) followed by the computation of `Φ_*[Γ]` in
`cyclePushforward_fundamentalClass_eq_zero_of_isConstant` / `cyclePushforward_fundamentalClass_eq_of_not_isConstant`. -/
theorem degree_pullback_restrict {k : Type u} [Field k] [IsAlgClosed k] {S X : SmoothProjectiveVariety k}
    (Φ : S.toScheme ⟶ X.toScheme) [Φ.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.IsProper Φ]
    (L : LineBundle X.toVariety) (Γ : IntegralCurve k S.toScheme) :
    (IsConstantMorphism (Γ.ι ≫ Φ) → (Φ ^* L) ⬝ Γ.fundamentalClass = 0)
    ∧ (¬ IsConstantMorphism (Γ.ι ≫ Φ) →
        ∃ (R : IntegralCurve k X.toScheme) (g : Γ.carrier ⟶ R.carrier)
          (hfac : g ≫ R.ι = Γ.ι ≫ Φ)
          (hg : g.base (genericPoint Γ.carrier) = genericPoint R.carrier),
          (Φ ^* L) ⬝ Γ.fundamentalClass
            = (functionFieldDegree g : ℤ) * (L ⬝ R.fundamentalClass)) := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [LineBundle.inter_pullback, cyclePushforward_fundamentalClass_eq_zero_of_isConstant Φ Γ h]
    exact map_zero L.interHom
  · refine ⟨Γ.imageCurve Φ h, Γ.toImageCurve Φ h, Γ.toImageCurve_fac Φ h,
      Γ.toImageCurve_genericPoint Φ h, ?_⟩
    rw [LineBundle.inter_pullback, cyclePushforward_fundamentalClass_eq_of_not_isConstant Φ Γ h]
    change L.interHom _ = _ * L.interHom _
    rw [map_zsmul, zsmul_eq_mul, Int.cast_id]

end
