import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedQcAlgebraPullback
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierDivisorPullback
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.CurveDivisorDegree
import MiyaokaMori.AlgebraicGeometry.Varieties.FunctionField.FunctionFieldExtensionDegree
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.LineBundleDegree
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.Paper.S1Intro.TangentBundlePullback
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.VectorBundleDegree
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundlePullback
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ChowGroupDegree
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ChowDegreeRat
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.IdealSheafToModules
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedPolynomialAlgebraPullback
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ZeroCycleDegreeScheme
import MiyaokaMori.AlgebraicGeometry.Chow.CurveDegreeEqTopSelfIntersection
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.CurveDegreePullbackFinite
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.IntegralCurveDegree
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundlePullback
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.IntegralCurve
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.NefPullback
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.PointDivisor
import MiyaokaMori.AlgebraicGeometry.Morphisms.Stacks02og
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothCurveGeometry
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.CurveModuleDegreePullback
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.LineBundleDegreeEqCartierDivisorDegree
import MiyaokaMori.AlgebraicGeometry.Morphisms.Stacks02nx

/-! # Degree of the pulled-back point class on a horizontal curve

On a horizontal integral closed curve `ι : Γ ↪ Y`, `deg(ι^*π^*O_C(p_0)) = [K(Γ):K(C)]` (`= e_0`; `Γ` may be singular).
This is how `e_0 = deg ρ_0` enters equation (2.11) of Lemma 2.5 of the paper.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem degree_pullback_point_eq_functionFieldDegree {K : Type u} [Field K] [IsAlgClosed K]
    {Y : AlgebraicGeometry.Scheme.{u}} [Y.Over (AlgebraicGeometry.Spec (CommRingCat.of K))]
    {C : SmoothProjectiveCurve K} (π : Y ⟶ C.toScheme)
    [π.IsOver (AlgebraicGeometry.Spec (CommRingCat.of K))]
    (Γ : IntegralCurve K Y) (p₀ : C.toScheme) (hp₀ : IsClosed ({p₀} : Set C.toScheme))
    (hsurj : Function.Surjective (Γ.ι ≫ π).base)
    (hg : (Γ.ι ≫ π).base (genericPoint Γ.carrier) = genericPoint C.toScheme) :
    Γ.degree ((AlgebraicGeometry.Scheme.Modules.pullback π).obj
        (Divisor.ofPoint p₀).lineBundle.toModules)
      = (functionFieldDegree (Γ.ι ≫ π) : ℤ) := by
  let g : Γ.carrier ⟶ C.toScheme := Γ.ι ≫ π
  have hg_g : g.base (genericPoint Γ.carrier) = genericPoint C.toScheme := by
    exact hg
  letI : g.IsOver (AlgebraicGeometry.Spec (CommRingCat.of K)) := by
    constructor
    change (Γ.ι ≫ π) ≫ (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of K)) =
      Γ.carrier ↘ AlgebraicGeometry.Spec (CommRingCat.of K)
    rw [Category.assoc, (inferInstance : π.IsOver
      (AlgebraicGeometry.Spec (CommRingCat.of K))).comp_over]
    rfl
  have hgeneric_residue_finite :
      (g.residueFieldMap (genericPoint Γ.carrier)).hom.Finite := by
    letI : AlgebraicGeometry.IsProper
        (Γ.carrier ↘ AlgebraicGeometry.Spec (CommRingCat.of K)) := Γ.isProperOver
    letI : AlgebraicGeometry.LocallyOfFiniteType
        (Γ.carrier ↘ AlgebraicGeometry.Spec (CommRingCat.of K)) :=
      AlgebraicGeometry.IsProper.toLocallyOfFiniteType
    letI : AlgebraicGeometry.QuasiCompact
        (Γ.carrier ↘ AlgebraicGeometry.Spec (CommRingCat.of K)) := inferInstance
    let ΓV : Variety K :=
      { carrier := Γ.carrier
        integral := inferInstance
        separated := Γ.isProper.toIsSeparated
        finiteType := AlgebraicGeometry.IsOfFiniteType.mk }
    have hdimΓ : ΓV.toScheme.dimension = 1 := Γ.carrier_dimension
    have hdimC : C.toScheme.dimension = 1 := by
      unfold AlgebraicGeometry.Scheme.dimension
      rw [C.dim_one]
      simp
    exact Variety.residueFieldMap_genericPoint_finite_of_dim_eq
      (X := ΓV) (Y := C.toVariety) g hg (hdimΓ.trans hdimC.symm)
  have hfinite_fiber : ∀ y : C.toScheme, (g.base ⁻¹' {y}).Finite := by
    letI : AlgebraicGeometry.IsNoetherian Γ.carrier :=
      AlgebraicGeometry.Intersection.properFieldScheme_isNoetherian
        (Γ.ι ≫ (Y ↘ AlgebraicGeometry.Spec (CommRingCat.of K)))
    intro y
    by_cases hy : IsClosed ({y} : Set C.toScheme)
    · let U : C.toScheme.Opens := ⟨({y} : Set C.toScheme)ᶜ, hy.isOpen_compl⟩
      let V : Γ.carrier.Opens := TopologicalSpace.Opens.comap ⟨g.base, g.continuous⟩ U
      have hgeneric_not_closed : ¬ IsClosed ({genericPoint C.toScheme} : Set C.toScheme) := by
        intro h
        have hone := AlgebraicGeometry.Scheme.closedPoint_coheight_eq_one_of_dimension_one
          C.toScheme C.dim_one (genericPoint C.toScheme) h
        have hzero : Order.coheight (genericPoint C.toScheme) = 0 :=
          Order.coheight_eq_zero.mpr (isMax_top (α := C.toScheme))
        exact one_ne_zero (hone.symm.trans hzero)
      have hgen_ne_y : genericPoint C.toScheme ≠ y := by
        intro h
        apply hgeneric_not_closed
        simpa [h] using hy
      have hVnonempty : Nonempty V := by
        refine ⟨⟨genericPoint Γ.carrier, ?_⟩⟩
        rw [TopologicalSpace.Opens.mem_comap]
        simp only [U]
        intro h
        apply hgen_ne_y
        change g.base (genericPoint Γ.carrier) = y at h
        exact hg ▸ h
      have hfinite := AlgebraicGeometry.Scheme.finite_coheight_one_not_mem V
      refine hfinite.subset ?_
      intro x hx
      have hxnotgen : x ≠ genericPoint Γ.carrier := by
        intro hxgen
        subst x
        apply hgen_ne_y
        change g.base (genericPoint Γ.carrier) = y at hx
        exact hg ▸ hx
      have hco_pos : 0 < Order.coheight x := by
        exact Order.coheight_pos_of_lt_top (lt_of_le_not_ge le_top (by
          intro htop
          apply hxnotgen
          have hle : x ≤ (⊤ : Γ.carrier) := le_top
          have hspec1 : x ⤳ (⊤ : Γ.carrier) :=
            AlgebraicGeometry.Scheme.le_iff_specializes.mp htop
          have hspec2 : (⊤ : Γ.carrier) ⤳ x :=
            AlgebraicGeometry.Scheme.le_iff_specializes.mp hle
          exact (hspec1.antisymm hspec2).eq))
      have hkrull : Order.krullDim Γ.carrier ≤ 1 := by
        rw [← Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := Γ.carrier))]
        exact le_of_eq Γ.dim_eq_one
      have hco_le : Order.coheight x ≤ 1 := by
        exact WithBot.coe_le_coe.mp ((Order.coheight_le_krullDim x).trans hkrull)
      have hco : Order.coheight x = 1 := by
        apply le_antisymm hco_le
        exact Order.one_le_iff_ne_zero.mpr (ne_of_gt hco_pos)
      constructor
      · exact hco
      · change g.base x ∉ ({y} : Set C.toScheme)ᶜ
        exact fun h' => h' hx
    · have hdimCtop : topologicalKrullDim C.toScheme ≤ 1 := by
        rw [C.dim_one]
      have hkrullC : Order.krullDim C.toScheme ≤ 1 := by
        rw [← Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := C.toScheme))]
        exact hdimCtop
      have hco_le : Order.coheight y ≤ 1 := by
        exact WithBot.coe_le_coe.mp ((Order.coheight_le_krullDim y).trans hkrullC)
      have hygen : y = genericPoint C.toScheme := by
        by_cases hzero : Order.coheight y = 0
        · have hmax : IsMax y := Order.coheight_eq_zero.mp hzero
          have hle : y ≤ genericPoint C.toScheme :=
            AlgebraicGeometry.Scheme.le_iff_specializes.mpr (genericPoint_specializes y)
          have hgen_le : genericPoint C.toScheme ≤ y := hmax hle
          have hs1 : y ⤳ genericPoint C.toScheme :=
            AlgebraicGeometry.Scheme.le_iff_specializes.mp hgen_le
          have hs2 : genericPoint C.toScheme ⤳ y := genericPoint_specializes y
          exact (hs1.antisymm hs2).eq
        · have hco : Order.coheight y = 1 := by
            apply le_antisymm hco_le
            exact Order.one_le_iff_ne_zero.mpr hzero
          have hyclosed : IsClosed ({y} : Set C.toScheme) :=
            AlgebraicGeometry.Intersection.isClosed_singleton_of_coheight_eq_one hdimCtop y hco
          exact (hy hyclosed).elim
      letI : AlgebraicGeometry.LocallyOfFiniteType g := by
        have hcomp : g ≫ (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of K)) =
            Γ.carrier ↘ AlgebraicGeometry.Spec (CommRingCat.of K) := by
          exact comp_over g _
        have hsource : AlgebraicGeometry.LocallyOfFiniteType
            (Γ.carrier ↘ AlgebraicGeometry.Spec (CommRingCat.of K)) :=
          Γ.isProper.toLocallyOfFiniteType
        have htarget : AlgebraicGeometry.LocallyOfFiniteType
            (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of K)) :=
          C.isProper.toLocallyOfFiniteType
        letI : AlgebraicGeometry.LocallyOfFiniteType
            (g ≫ (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of K))) := by
          rw [hcomp]
          exact hsource
        exact AlgebraicGeometry.locallyOfFiniteType_of_comp g
          (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of K))
      have hfiber :=
        (AlgebraicGeometry.functionField_finite_iff_generic_fiber g hg).mp
          hgeneric_residue_finite
      rw [hygen]
      have hfiber' : g.base ⁻¹' {genericPoint C.toScheme} =
          {genericPoint Γ.carrier} := by
        simpa [hg_g] using hfiber
      rw [hfiber']
      exact Set.finite_singleton _
  letI : AlgebraicGeometry.LocallyOfFiniteType
      (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of K)) :=
    C.isProper.toLocallyOfFiniteType
  letI : AlgebraicGeometry.IsLocallyNoetherian C.toScheme :=
    AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian
      (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of K))
  letI : AlgebraicGeometry.IsProper (g ≫
      (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of K))) := by
    rw [comp_over g]
    exact Γ.isProperOver
  letI : AlgebraicGeometry.IsSeparated
      (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of K)) := C.isSeparated
  letI : AlgebraicGeometry.IsProper g := AlgebraicGeometry.IsProper.of_comp g
    (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of K))
  letI : AlgebraicGeometry.IsFinite g :=
    AlgebraicGeometry.isFinite_of_isProper_of_finite_fibers g
      hfinite_fiber
  letI : AlgebraicGeometry.IsDominant g := ⟨hsurj.denseRange⟩
  let Y₁ : AlgebraicGeometry.Proj.SchemeOver K :=
    ⟨Y, Y ↘ AlgebraicGeometry.Spec (CommRingCat.of K)⟩
  let X : AlgebraicGeometry.Proj.SchemeOver K :=
    AlgebraicGeometry.Intersection.closedCurveOver Y₁ Γ.ι
  let Y₀ : AlgebraicGeometry.Proj.SchemeOver K :=
    ⟨C.toScheme, C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of K)⟩
  letI : AlgebraicGeometry.IsIntegral X.scheme := Γ.isIntegral
  letI : AlgebraicGeometry.IsIntegral Y₀.scheme := SmoothProjectiveCurve.isIntegral C
  letI : AlgebraicGeometry.IsProper X.toBase := Γ.isProperOver
  letI : AlgebraicGeometry.IsProper Y₀.toBase := C.isProper
  have hgover : g ≫ Y₀.toBase = X.toBase := by
    change g ≫ (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of K)) =
      Γ.ι ≫ (Y ↘ AlgebraicGeometry.Spec (CommRingCat.of K))
    dsimp [g]
    rw [Category.assoc, (inferInstance : π.IsOver
      (AlgebraicGeometry.Spec (CommRingCat.of K))).comp_over]
  -- the instances with the implicit schemes spelled `X.scheme`, `Y₀.scheme`, as the re-keyed
  -- `curveModuleDegree_pullback_finite X Y₀ … g hgover` expects them
  letI : @AlgebraicGeometry.IsFinite X.scheme Y₀.scheme g := by
    change AlgebraicGeometry.IsFinite g
    infer_instance
  letI : @AlgebraicGeometry.IsDominant X.scheme Y₀.scheme g := by
    change AlgebraicGeometry.IsDominant g
    infer_instance
  have hM := AlgebraicGeometry.VectorBundle.isLocallyFreeRank
    (C := C) (Divisor.ofPoint p₀).lineBundle.toVectorBundle
  rw [(Divisor.ofPoint p₀).lineBundle.rank_eq_one] at hM
  have hpull := AlgebraicGeometry.Intersection.curveModuleDegree_pullback_finite X Y₀
    (by change topologicalKrullDim Γ.carrier ≤ 1; rw [Γ.dim_eq_one])
    (by rw [C.dim_one]) g hgover
    (Divisor.ofPoint p₀).lineBundle.toModules hM
    (LineBundle.degree_spec (Divisor.ofPoint p₀).lineBundle)
  let ecomp :
      (AlgebraicGeometry.Scheme.Modules.pullback Γ.ι).obj
          ((AlgebraicGeometry.Scheme.Modules.pullback π).obj
            (Divisor.ofPoint p₀).lineBundle.toModules) ≅
        (AlgebraicGeometry.Scheme.Modules.pullback g).obj
          (Divisor.ofPoint p₀).lineBundle.toModules :=
    (AlgebraicGeometry.Scheme.Modules.pullbackComp Γ.ι π).app
      (Divisor.ofPoint p₀).lineBundle.toModules
  have hpull' :=
    (AlgebraicGeometry.Intersection.curveModuleDegree_iso_iff X
      ((AlgebraicGeometry.Scheme.Modules.pullback Γ.ι).obj
        ((AlgebraicGeometry.Scheme.Modules.pullback π).obj
          (Divisor.ofPoint p₀).lineBundle.toModules))
      ((AlgebraicGeometry.Scheme.Modules.pullback g).obj
        (Divisor.ofPoint p₀).lineBundle.toModules) ecomp
      ((AlgebraicGeometry.Scheme.finiteMapFunctionFieldDegree g : ℤ) *
        LineBundle.degree (Divisor.ofPoint p₀).lineBundle)).mpr hpull
  have hdeg := IntegralCurve.degree_eq_of_hasCurveModuleDegree Γ
    ((AlgebraicGeometry.Scheme.Modules.pullback π).obj
      (Divisor.ofPoint p₀).lineBundle.toModules) hpull'
  have hfmdeg : AlgebraicGeometry.Scheme.finiteMapFunctionFieldDegree g =
      functionFieldDegree g := by
    have hg' : g.base (genericPoint Γ.carrier) = genericPoint C.toScheme := by
      exact hg
    have hff := functionFieldDegree_eq_finrank g hg'
    unfold AlgebraicGeometry.Scheme.finiteMapFunctionFieldDegree
    rw [hff]
    letI : Semiring Γ.carrier.functionField :=
      Field.toSemifield.toDivisionSemiring.toSemiring
    let A1 : Algebra C.toScheme.functionField Γ.carrier.functionField :=
      @AlgebraicGeometry.Scheme.dominantFunctionFieldAlgebra Γ.carrier C.toScheme
        inferInstance inferInstance g inferInstance
    let A2 : Algebra C.toScheme.functionField Γ.carrier.functionField :=
      @RingHom.toAlgebra' _ _ _ (Field.toSemifield.toDivisionSemiring.toSemiring)
        (C.toScheme.functionFieldIsoResidueField.hom ≫
        (C.toScheme.residueFieldCongr hg'.symm).hom ≫
        g.residueFieldMap (genericPoint Γ.carrier) ≫
        Γ.carrier.functionFieldIsoResidueField.inv).hom
        (by intro c x; exact mul_comm _ _)
    have hmap : AlgebraicGeometry.Scheme.dominantFunctionFieldMap g =
        C.toScheme.functionFieldIsoResidueField.hom ≫
          (C.toScheme.residueFieldCongr hg'.symm).hom ≫
          g.residueFieldMap (genericPoint Γ.carrier) ≫
          Γ.carrier.functionFieldIsoResidueField.inv := by
      unfold AlgebraicGeometry.Scheme.dominantFunctionFieldMap
      apply (cancel_mono (Γ.carrier.residue (genericPoint Γ.carrier))).1
      simp only [Category.assoc]
      rw [← AlgebraicGeometry.Scheme.residue_residueFieldMap]
      rw [← Category.assoc]
      rw [← AlgebraicGeometry.Scheme.residue_residueFieldCongr]
      simp [AlgebraicGeometry.Scheme.functionFieldIsoResidueField]
      exact hg'.symm
    have hA : A2 = A1 := by
      apply Algebra.algebra_ext
      intro r
      change ((C.toScheme.functionFieldIsoResidueField.hom ≫
        (C.toScheme.residueFieldCongr hg'.symm).hom ≫
        g.residueFieldMap (genericPoint Γ.carrier) ≫
        Γ.carrier.functionFieldIsoResidueField.inv).hom r) =
        (AlgebraicGeometry.Scheme.dominantFunctionFieldMap g).hom r
      exact congrArg (fun q => q.hom r) hmap.symm
    change @Module.finrank C.toScheme.functionField Γ.carrier.functionField
        Field.toSemifield.toDivisionSemiring.toSemiring
        Field.toSemifield.toDivisionSemiring.toAddCommMonoid
        (@Algebra.toModule C.toScheme.functionField Γ.carrier.functionField
          Field.toSemifield.toCommSemiring
          Field.toSemifield.toDivisionSemiring.toSemiring A1) =
      @Module.finrank C.toScheme.functionField Γ.carrier.functionField
        Field.toSemifield.toDivisionSemiring.toSemiring
        Field.toSemifield.toDivisionSemiring.toAddCommMonoid
        (@Algebra.toModule C.toScheme.functionField Γ.carrier.functionField
          Field.toSemifield.toCommSemiring
          Field.toSemifield.toDivisionSemiring.toSemiring A2)
    rw [hA]
  change Γ.degree ((AlgebraicGeometry.Scheme.Modules.pullback π).obj
      (Divisor.ofPoint p₀).lineBundle.toModules) = _
  rw [hdeg, CartierDivisor.lineBundle_degree C (Divisor.ofPoint p₀),
    Divisor.ofPoint_degree p₀ hp₀]
  norm_num [hfmdeg]
  rfl

end
