import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedQcAlgebraPullback
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.LineBundleDegreeWellDefined
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierDivisorPullback
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.ClosedSubvariety
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.CurveDivisorDegree
import MiyaokaMori.AlgebraicGeometry.Varieties.FunctionField.FunctionFieldExtensionDegree
import MiyaokaMori.AlgebraicGeometry.Varieties.FunctionField.FunctionFieldDegreeComp
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.VarietyLineBundle
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.LineBundleDegree
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.SmoothProjectiveVariety
import MiyaokaMori.Paper.S1Intro.TangentBundlePullback
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.VectorBundleDegree
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundlePullback
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ChowGroupDegree
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ChowDegreeRat
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.AlgebraicGeometry.Varieties.FiniteCover
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.IdealSheafToModules
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.ModulesLineBundleZpow
import MiyaokaMori.Paper.S2WeightedJets.Ygg.PaperYgg
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.RelativeProjTwistQC
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.SufficientlyDivisible
import MiyaokaMori.Paper.S2WeightedJets.Ygg.TautologicalClass
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedPolynomialAlgebraPullback
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ZeroCycleDegreeScheme
import MiyaokaMori.AlgebraicGeometry.Chow.CurveDegreeEqTopSelfIntersection
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.CurveDegreePullbackFinite
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.DegreeOfTensorPower
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.IntegralCurveDegree
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundlePullback
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleTensorPower
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.IntegralCurve
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.NefPullback
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.LocallyFreeRankPullback
import MiyaokaMori.AlgebraicGeometry.Morphisms.ResidueDegreeComposition
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.CurveModuleDegreePullback
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.RationalSectionDegree
import MiyaokaMori.AlgebraicGeometry.Morphisms.IsProjectiveOverIsProper

/-! # The degree relation

Taking degrees in `τ^*B_k ≅ L^{-m}` (`τ = ι∘ν∘η`): `d_L = −deg η·(H_k·Γ)` with `H_k·Γ := deg(ι^*B_k)/m`, and
`e = deg η·e_0` (§3 of the paper, proof of Proposition 3.2).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem degree_relation {K : Type u} [Field K] [IsAlgClosed K]
    {X : SmoothProjectiveVariety K} {C : SmoothProjectiveCurve K}
    (f : C.toScheme ⟶ X.toScheme) [MMSetup f] (κ m : ℕ) (hm0 : 0 < m)
    [Fact ((jetAlgebra f κ).SufficientlyDivisible m)]
    (ρ : FiniteCover K C) (L : LineBundle ρ.source.toVariety)
    (Γ : IntegralCurve K (YGG f κ))
    {Ct₀ : SmoothProjectiveCurve K} (ν : Ct₀.toScheme ⟶ Γ.carrier) [AlgebraicGeometry.IsFinite ν]
    (hνg : ν.base (genericPoint Ct₀.toScheme) = genericPoint Γ.carrier)
    (hνbir : functionFieldDegree ν = 1)
    (η : ρ.source.toScheme ⟶ Ct₀.toScheme) [AlgebraicGeometry.IsFinite η]
    (hηg : η.base (genericPoint ρ.source.toScheme) = genericPoint Ct₀.toScheme)
    (hρ : ρ.hom = η ≫ ν ≫ Γ.ι ≫ YGG.proj f κ)
    (hg₀ : (ν ≫ Γ.ι ≫ YGG.proj f κ).base (genericPoint Ct₀.toScheme) = genericPoint C.toScheme)
    (hiso : Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback (η ≫ ν ≫ Γ.ι)).obj (polarization f κ m)
      ≅ (L.zpow (-(m : ℤ))).toModules)) :
    (L.degree : ℚ) = - (functionFieldDegree η : ℚ) *
        ((Γ.degree (polarization f κ m) : ℚ) / m)
    ∧ functionFieldDegree ρ.hom = functionFieldDegree η *
        functionFieldDegree (ν ≫ Γ.ι ≫ YGG.proj f κ) := by
  constructor
  · let τ : ρ.source.toScheme ⟶ Γ.carrier := η ≫ ν
    let X0 : AlgebraicGeometry.Proj.SchemeOver K :=
      ⟨ρ.source.toScheme, ρ.source.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of K)⟩
    let Yamb : AlgebraicGeometry.Proj.SchemeOver K :=
      ⟨YGG f κ, YGG.proj f κ ≫ (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of K))⟩
    let Y0 := AlgebraicGeometry.Intersection.closedCurveOver Yamb Γ.ι
    let BΓ := (AlgebraicGeometry.Scheme.Modules.pullback Γ.ι).obj (polarization f κ m)
    have hτ : τ ≫ Γ.ι ≫ YGG.proj f κ = ρ.hom := by
      dsimp [τ]
      rw [hρ]
      simp [Category.assoc]
    have hτm : τ ≫ Y0.toBase = X0.toBase := by
      dsimp [X0, Y0, τ]
      change (τ ≫ Γ.ι ≫ YGG.proj f κ) ≫
        (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of K)) = _
      rw [hτ, ρ.isOver]
    letI : AlgebraicGeometry.IsIntegral X0.scheme := by
      change AlgebraicGeometry.IsIntegral ρ.source.toScheme
      exact ρ.source.isIntegral
    letI : AlgebraicGeometry.IsIntegral Y0.scheme := by
      change AlgebraicGeometry.IsIntegral Γ.carrier
      exact Γ.isIntegral
    letI : AlgebraicGeometry.IsProper X0.toBase := by
      change AlgebraicGeometry.IsProper
        (ρ.source.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of K))
      exact IsProjectiveOver.isProper ρ.source.projective
    letI : AlgebraicGeometry.IsProper Y0.toBase := by
      exact Γ.isProper
    have hdomη : AlgebraicGeometry.IsDominant η := by
      constructor
      change Dense (Set.range η.base)
      rw [dense_iff_closure_eq]
      have hgen : genericPoint Ct₀.toScheme ∈ closure (Set.range η.base) := by
        rw [← hηg]
        exact subset_closure ⟨genericPoint ρ.source.toScheme, rfl⟩
      have hm : ({genericPoint Ct₀.toScheme} : Set Ct₀.toScheme) ⊆
          closure (Set.range η.base) := by
        intro z hz
        simpa [Set.mem_singleton_iff.mp hz] using hgen
      apply Set.Subset.antisymm
      · exact Set.subset_univ _
      · intro y hy
        have hy' : y ∈ closure ({genericPoint Ct₀.toScheme} : Set Ct₀.toScheme) := by
          rw [(genericPoint_spec Ct₀.toScheme).def]
          exact hy
        exact (closure_minimal hm isClosed_closure) hy'
    have hdomν : AlgebraicGeometry.IsDominant ν := by
      constructor
      change Dense (Set.range ν.base)
      rw [dense_iff_closure_eq]
      have hgen : genericPoint Γ.carrier ∈ closure (Set.range ν.base) := by
        rw [← hνg]
        exact subset_closure ⟨genericPoint Ct₀.toScheme, rfl⟩
      have hm : ({genericPoint Γ.carrier} : Set Γ.carrier) ⊆
          closure (Set.range ν.base) := by
        intro z hz
        simpa [Set.mem_singleton_iff.mp hz] using hgen
      apply Set.Subset.antisymm
      · exact Set.subset_univ _
      · intro y hy
        have hy' : y ∈ closure ({genericPoint Γ.carrier} : Set Γ.carrier) := by
          rw [(genericPoint_spec Γ.carrier).def]
          exact hy
        exact (closure_minimal hm isClosed_closure) hy'
    letI : AlgebraicGeometry.IsDominant η := hdomη
    letI : AlgebraicGeometry.IsDominant ν := hdomν
    letI : AlgebraicGeometry.IsFinite τ := inferInstance
    letI : AlgebraicGeometry.IsDominant τ := inferInstance
    -- the same instances with the implicit schemes spelled `X0.scheme`, `Y0.scheme`, as the
    -- re-keyed `curveModuleDegree_pullback_finite X0 Y0 … τ hτm` expects them
    letI : @AlgebraicGeometry.IsFinite X0.scheme Y0.scheme τ := by
      change AlgebraicGeometry.IsFinite τ
      infer_instance
    letI : @AlgebraicGeometry.IsDominant X0.scheme Y0.scheme τ := by
      change AlgebraicGeometry.IsDominant τ
      infer_instance
    have hdimX : topologicalKrullDim X0.scheme ≤ 1 := by
      change topologicalKrullDim ρ.source.toScheme ≤ 1
      rw [ρ.source.dim_one]
    have hdimY : topologicalKrullDim Y0.scheme ≤ 1 := by
      change topologicalKrullDim Γ.carrier ≤ 1
      rw [Γ.dim_eq_one]
    have hbaseY : AlgebraicGeometry.Scheme.Modules.IsLocallyFreeRank Yamb (polarization f κ m) 1 :=
      MiyaokaMori.RationalSectionDegree.isLocallyFreeRank_one_of_isLineBundle Yamb
        (polarization f κ m)
    have hBΓ : AlgebraicGeometry.Scheme.Modules.IsLocallyFreeRank Y0 BΓ 1 := by
      change AlgebraicGeometry.Scheme.Modules.IsLocallyFreeRank
        (AlgebraicGeometry.Intersection.closedCurveOver Yamb Γ.ι)
        ((AlgebraicGeometry.Scheme.Modules.pullback Γ.ι).obj (polarization f κ m)) 1
      exact AlgebraicGeometry.Scheme.Modules.isLocallyFreeRank_pullback (X := Yamb) (Y := Y0)
        (L := polarization f κ m) (n := 1) hbaseY Γ.ι
    have hdegΓ := IntegralCurve.degree_spec Γ (polarization f κ m)
    have hpull := AlgebraicGeometry.Intersection.curveModuleDegree_pullback_finite
      X0 Y0 hdimX hdimY τ hτm BΓ hBΓ hdegΓ
    obtain ⟨hiso⟩ := hiso
    have hcomp : τ ≫ Γ.ι = η ≫ ν ≫ Γ.ι := by
      dsimp [τ]
      simp [Category.assoc]
    let ecomp : (AlgebraicGeometry.Scheme.Modules.pullback τ).obj BΓ ≅
        (AlgebraicGeometry.Scheme.Modules.pullback (η ≫ ν ≫ Γ.ι)).obj
          (polarization f κ m) :=
      (AlgebraicGeometry.Scheme.Modules.pullbackComp τ Γ.ι).app
          (polarization f κ m) ≪≫
        (AlgebraicGeometry.Scheme.Modules.pullbackCongr hcomp).app
          (polarization f κ m)
    have hdegPull : AlgebraicGeometry.Intersection.HasCurveModuleDegree X0
        (L.zpow (-(m : ℤ))).toModules
        ((AlgebraicGeometry.Scheme.finiteMapFunctionFieldDegree τ : ℤ) * Γ.degree
          (polarization f κ m)) := by
      exact (AlgebraicGeometry.Intersection.curveModuleDegree_iso_iff X0
        ((AlgebraicGeometry.Scheme.Modules.pullback τ).obj BΓ)
        (L.zpow (-(m : ℤ))).toModules
        (ecomp ≪≫ hiso)
        ((AlgebraicGeometry.Scheme.finiteMapFunctionFieldDegree τ : ℤ) * Γ.degree
          (polarization f κ m))).mp hpull
    have hdegL : (L.zpow (-(m : ℤ))).degree =
        (AlgebraicGeometry.Scheme.finiteMapFunctionFieldDegree τ : ℤ) * Γ.degree
          (polarization f κ m) := by
      apply LineBundle.degree_eq_of_hasCurveModuleDegree (L.zpow (-(m : ℤ)))
      exact hdegPull
    rw [LineBundle.degree_zpow] at hdegL
    have hτdeg : functionFieldDegree τ = functionFieldDegree η := by
      have hcompdeg := functionFieldDegree_comp_of_genericPoint η ν hηg
      dsimp [τ]
      rw [hcompdeg, hνbir]
      simp
    have hfmdeg : AlgebraicGeometry.Scheme.finiteMapFunctionFieldDegree τ = functionFieldDegree τ := by
      have hff := functionFieldDegree_eq_finrank τ
        (AlgebraicGeometry.Scheme.dominantMap_genericPoint τ)
      unfold AlgebraicGeometry.Scheme.finiteMapFunctionFieldDegree
      rw [hff]
      let A1 : Algebra Γ.carrier.functionField ρ.source.toScheme.functionField :=
        @AlgebraicGeometry.Scheme.dominantFunctionFieldAlgebra ρ.source.toScheme Γ.carrier
          inferInstance inferInstance τ inferInstance
      let A2 : Algebra Γ.carrier.functionField ρ.source.toScheme.functionField :=
        ((Γ.carrier.functionFieldIsoResidueField.hom ≫
          (Γ.carrier.residueFieldCongr (AlgebraicGeometry.Scheme.dominantMap_genericPoint τ).symm).hom ≫
          τ.residueFieldMap (genericPoint ρ.source.toScheme) ≫
          ρ.source.toScheme.functionFieldIsoResidueField.inv).hom.toAlgebra)
      have hmap : AlgebraicGeometry.Scheme.dominantFunctionFieldMap τ =
          Γ.carrier.functionFieldIsoResidueField.hom ≫
            (Γ.carrier.residueFieldCongr (AlgebraicGeometry.Scheme.dominantMap_genericPoint τ).symm).hom ≫
            τ.residueFieldMap (genericPoint ρ.source.toScheme) ≫
            ρ.source.toScheme.functionFieldIsoResidueField.inv := by
        unfold AlgebraicGeometry.Scheme.dominantFunctionFieldMap
        apply (cancel_mono (ρ.source.toScheme.residue
          (genericPoint ρ.source.toScheme))).1
        simp only [Category.assoc]
        rw [← AlgebraicGeometry.Scheme.residue_residueFieldMap]
        rw [← Category.assoc]
        rw [← AlgebraicGeometry.Scheme.residue_residueFieldCongr]
        simp [AlgebraicGeometry.Scheme.functionFieldIsoResidueField]
        exact (AlgebraicGeometry.Scheme.dominantMap_genericPoint τ).symm
      have hA : A2 = A1 := by
        apply Algebra.algebra_ext
        intro r
        change ((Γ.carrier.functionFieldIsoResidueField.hom ≫
          (Γ.carrier.residueFieldCongr (AlgebraicGeometry.Scheme.dominantMap_genericPoint τ).symm).hom ≫
          τ.residueFieldMap (genericPoint ρ.source.toScheme) ≫
          ρ.source.toScheme.functionFieldIsoResidueField.inv).hom r) =
          (AlgebraicGeometry.Scheme.dominantFunctionFieldMap τ).hom r
        exact congrArg (fun q => q.hom r) hmap.symm
      let finrankOf : Algebra Γ.carrier.functionField ρ.source.toScheme.functionField → ℕ :=
        fun A => letI := A; Module.finrank Γ.carrier.functionField ρ.source.toScheme.functionField
      have hfin := congrArg finrankOf hA
      exact hfin.symm
    have hInt : (-(m : ℤ)) * L.degree =
        (functionFieldDegree η : ℤ) * Γ.degree (polarization f κ m) := by
      rw [← hτdeg, ← hfmdeg]
      exact hdegL
    have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm0)
    have hQ : (-(m : ℚ)) * (L.degree : ℚ) =
        (functionFieldDegree η : ℚ) * (Γ.degree (polarization f κ m) : ℚ) := by
      exact_mod_cast hInt
    field_simp [hmQ]
    linarith
  · rw [hρ]
    let q : Ct₀.toScheme ⟶ C.toScheme := ν ≫ Γ.ι ≫ YGG.proj f κ
    have hcomp := AlgebraicGeometry.Intersection.residueDegree_comp η q
      (genericPoint ρ.source.toScheme)
    unfold functionFieldDegree at *
    rw [hcomp]
    rw [hηg]
    dsimp [q]
    ring

end
