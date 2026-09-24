import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.RationalSectionDivisorTensor
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.RationalSectionDegree
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.PrincipalDivisorDegreeZero
import MiyaokaMori.Paper.S3PositiveLine.NegativeCurve.ShiftedClassLineBundle
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.IntegralCurveDegree

/-! # The negative slope inequality

From `deg(ι^*M) < 0` and `deg(ι^*π^*O_C(p_0)) = e_0` one gets the slope inequality
`θ = a/b < −deg(ι^*B_k)/(m e_0) = −(H_k·Γ)/e_0` (equation (2.11), Lemma 2.5
of the paper).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

private lemma principal_degree_zero {K : Type u} [Field K]
    {W : AlgebraicGeometry.Scheme.{u}}
    [W.Over (AlgebraicGeometry.Spec (CommRingCat.of K))]
    [AlgebraicGeometry.IsIntegral W]
    [AlgebraicGeometry.IsLocallyNoetherian W]
    (hW : IsProperOver K W) (hdim : SchemeIsOneDimensional W)
    (g : W.functionFieldˣ) :
    AlgebraicGeometry.AlgebraicCycle.degree (k := K) (W.principalCycle g) = 0 := by
  unfold AlgebraicGeometry.AlgebraicCycle.degree
  change (∑ᶠ x : W, W.ord (g : W.functionField) x *
      ((W ↘ AlgebraicGeometry.Spec (CommRingCat.of K)).residueDegree x : ℤ)) = 0
  exact principalDivisor_degree_eq_zero W hdim g

private lemma degree_pullback_unit {K : Type u} [Field K]
    {Y : AlgebraicGeometry.Scheme.{u}}
    [Y.Over (AlgebraicGeometry.Spec (CommRingCat.of K))]
    (Γ : IntegralCurve K Y) :
    Γ.degree (SheafOfModules.unit Y.ringCatSheaf) = 0 := by
  letI : AlgebraicGeometry.IsNoetherian Γ.carrier :=
    AlgebraicGeometry.Intersection.properFieldScheme_isNoetherian
      (Γ.ι ≫ (Y ↘ AlgebraicGeometry.Spec (CommRingCat.of K)))
  let M : Γ.carrier.Modules :=
    (AlgebraicGeometry.Scheme.Modules.pullback Γ.ι).obj
      (SheafOfModules.unit Y.ringCatSheaf)
  letI : M.IsLineBundle :=
    AlgebraicGeometry.Scheme.Modules.IsLineBundle.pullback Γ.ι
      (SheafOfModules.unit Y.ringCatSheaf)
  let e := AlgebraicGeometry.Scheme.Modules.pullbackUnitIso Γ.ι
  obtain ⟨s, hs⟩ := AlgebraicGeometry.Scheme.Modules.exists_stalk_genericPoint_ne_zero M
  obtain ⟨g, hg⟩ := AlgebraicGeometry.Scheme.Modules.rationalSectionDivisor_eq_principalCycle_of_iso_unit
    M e s hs
  rw [Γ.degree_eq_degree_rationalSectionDivisor (SheafOfModules.unit Y.ringCatSheaf) s hs, hg]
  exact principal_degree_zero Γ.isProperOver Γ.dim_eq_one g

private lemma degree_add_cycle {K : Type u} [Field K]
    {W : AlgebraicGeometry.Scheme.{u}}
    [W.Over (AlgebraicGeometry.Spec (CommRingCat.of K))]
    (hW : IsProperOver K W)
    (A B : AlgebraicGeometry.AlgebraicCycle W ℤ)
    (_hA : A ∈ AlgebraicGeometry.cycleSubgroup W 0)
    (_hB : B ∈ AlgebraicGeometry.cycleSubgroup W 0) :
    AlgebraicGeometry.AlgebraicCycle.degree (k := K) (A + B) =
      AlgebraicGeometry.AlgebraicCycle.degree (k := K) A +
        AlgebraicGeometry.AlgebraicCycle.degree (k := K) B := by
  letI : AlgebraicGeometry.IsProper
      (W ↘ AlgebraicGeometry.Spec (CommRingCat.of K)) := hW
  have hA' : (Function.support A).Finite := by
    exact AlgebraicGeometry.Intersection.properCycle_finiteSupport
      (W ↘ AlgebraicGeometry.Spec (CommRingCat.of K)) A
  have hB' : (Function.support B).Finite := by
    exact AlgebraicGeometry.Intersection.properCycle_finiteSupport
      (W ↘ AlgebraicGeometry.Spec (CommRingCat.of K)) B
  have hAdeg : Function.HasFiniteSupport
      (fun x : W => A x * ((W ↘ AlgebraicGeometry.Spec (CommRingCat.of K)).residueDegree x : ℤ)) := by
    exact Function.HasFiniteSupport.mul_left hA' _
  have hBdeg : Function.HasFiniteSupport
      (fun x : W => B x * ((W ↘ AlgebraicGeometry.Spec (CommRingCat.of K)).residueDegree x : ℤ)) := by
    exact Function.HasFiniteSupport.mul_left hB' _
  unfold AlgebraicGeometry.AlgebraicCycle.degree
  change (∑ᶠ x : W, (A x + B x) * ((W ↘ AlgebraicGeometry.Spec (CommRingCat.of K)).residueDegree x : ℤ)) = _
  rw [show (fun x : W => (A x + B x) * ((W ↘ AlgebraicGeometry.Spec (CommRingCat.of K)).residueDegree x : ℤ)) =
        (fun x : W => A x * ((W ↘ AlgebraicGeometry.Spec (CommRingCat.of K)).residueDegree x : ℤ) +
          B x * ((W ↘ AlgebraicGeometry.Spec (CommRingCat.of K)).residueDegree x : ℤ)) by
    funext x; ring]
  exact finsum_add_distrib hAdeg hBdeg

private lemma degree_tensor {K : Type u} [Field K] [IsAlgClosed K]
    {Y : AlgebraicGeometry.Scheme.{u}}
    [Y.Over (AlgebraicGeometry.Spec (CommRingCat.of K))]
    (Γ : IntegralCurve K Y)
    (A B : Y.Modules) [A.IsLineBundle] [B.IsLineBundle]
    [(AlgebraicGeometry.Scheme.Modules.tensor A B).IsLineBundle] :
    Γ.degree (AlgebraicGeometry.Scheme.Modules.tensor A B) =
      Γ.degree A + Γ.degree B := by
  let AΓ := (AlgebraicGeometry.Scheme.Modules.pullback Γ.ι).obj A
  let BΓ := (AlgebraicGeometry.Scheme.Modules.pullback Γ.ι).obj B
  let TΓ := (AlgebraicGeometry.Scheme.Modules.pullback Γ.ι).obj
      (AlgebraicGeometry.Scheme.Modules.tensor A B)
  letI : AΓ.IsLineBundle := AlgebraicGeometry.Scheme.Modules.IsLineBundle.pullback Γ.ι A
  letI : BΓ.IsLineBundle := AlgebraicGeometry.Scheme.Modules.IsLineBundle.pullback Γ.ι B
  letI : TΓ.IsLineBundle := AlgebraicGeometry.Scheme.Modules.IsLineBundle.pullback Γ.ι _
  have hdim : topologicalKrullDim Γ.carrier ≤ 1 := by
    rw [Γ.dim_eq_one]
  have hproper : IsProperOver K Γ.carrier := Γ.isProperOver
  letI : AlgebraicGeometry.IsNoetherian Γ.carrier :=
    AlgebraicGeometry.Intersection.properFieldScheme_isNoetherian
      (Γ.ι ≫ (Y ↘ AlgebraicGeometry.Spec (CommRingCat.of K)))
  obtain ⟨s, hs⟩ := AlgebraicGeometry.Scheme.Modules.exists_stalk_genericPoint_ne_zero AΓ
  obtain ⟨t, ht⟩ := AlgebraicGeometry.Scheme.Modules.exists_stalk_genericPoint_ne_zero BΓ
  have hAeq : AlgebraicGeometry.AlgebraicCycle.degree (k := K)
      (AΓ.rationalSectionDivisor s) = Γ.degree A :=
    (Γ.degree_eq_degree_rationalSectionDivisor A s hs).symm
  have hBeq : AlgebraicGeometry.AlgebraicCycle.degree (k := K)
      (BΓ.rationalSectionDivisor t) = Γ.degree B :=
    (Γ.degree_eq_degree_rationalSectionDivisor B t ht).symm
  obtain ⟨u, hu, hdiv⟩ := AlgebraicGeometry.Scheme.Modules.exists_rationalSectionDivisor_tensor
    AΓ BΓ s t hs ht
  have hiso := (AlgebraicGeometry.Scheme.Modules.pullbackTensorIso Γ.ι A B).symm
  have hTeq : AlgebraicGeometry.AlgebraicCycle.degree (k := K)
      ((AΓ.tensor BΓ).rationalSectionDivisor u) =
      Γ.degree (AlgebraicGeometry.Scheme.Modules.tensor A B) := by
    rw [Γ.degree_eq_topSelfIntersection,
      ← AlgebraicGeometry.topSelfIntersection_congr Γ.carrier Γ.isProperOver _ _ hiso,
      MiyaokaMori.TopSelfIntersectionCurve.topSelfIntersection_eq_degree_rationalSectionDivisor
        Γ.isProperOver Γ.carrier_dimension (AΓ.tensor BΓ) u hu]
  have hAmem := MiyaokaMori.RationalSectionDegree.rationalSectionDivisor_mem_cycleSubgroup_zero
    hproper hdim AΓ s hs
  have hBmem := MiyaokaMori.RationalSectionDegree.rationalSectionDivisor_mem_cycleSubgroup_zero
    hproper hdim BΓ t ht
  have hsum := degree_add_cycle hproper
    (AΓ.rationalSectionDivisor s) (BΓ.rationalSectionDivisor t) hAmem hBmem
  calc
    Γ.degree (AlgebraicGeometry.Scheme.Modules.tensor A B) =
        AlgebraicGeometry.AlgebraicCycle.degree (k := K)
          ((AΓ.tensor BΓ).rationalSectionDivisor u) := hTeq.symm
    _ = AlgebraicGeometry.AlgebraicCycle.degree (k := K)
          (AΓ.rationalSectionDivisor s + BΓ.rationalSectionDivisor t) := by rw [hdiv]
    _ = _ := by rw [hsum, hAeq, hBeq]

private lemma degree_tensorPow {K : Type u} [Field K] [IsAlgClosed K]
    {Y : AlgebraicGeometry.Scheme.{u}}
    [Y.Over (AlgebraicGeometry.Spec (CommRingCat.of K))]
    (Γ : IntegralCurve K Y) (A : Y.Modules) [A.IsLineBundle] :
    ∀ q : ℕ, Γ.degree (AlgebraicGeometry.Scheme.Modules.tensorPow A q) =
      (q : ℤ) * Γ.degree A := by
  intro q
  induction q with
  | zero =>
      change Γ.degree (SheafOfModules.unit Y.ringCatSheaf) = _
      rw [degree_pullback_unit]
      simp
  | succ q ih =>
      change Γ.degree (AlgebraicGeometry.Scheme.Modules.tensor
        (AlgebraicGeometry.Scheme.Modules.tensorPow A q) A) = _
      rw [degree_tensor, ih]
      push_cast
      ring

private lemma shifted_degree {K : Type u} [Field K] [IsAlgClosed K]
    {X : SmoothProjectiveVariety K} {C : SmoothProjectiveCurve K}
    (f : C.toScheme ⟶ X.toScheme) [MMSetup f] (κ m : ℕ)
    [Fact ((jetAlgebra f κ).SufficientlyDivisible m)]
    (p₀ : C.toScheme) (a b e₀ : ℕ)
    (Γ : IntegralCurve K (YGG f κ))
    (hfib : Γ.degree ((AlgebraicGeometry.Scheme.Modules.pullback (YGG.proj f κ)).obj
        (Divisor.ofPoint p₀).lineBundle.toModules) = e₀) :
    Γ.degree (shiftedBundle f κ m p₀ a b) =
      (b : ℤ) * Γ.degree (polarization f κ m) +
        (m * a : ℤ) * e₀ := by
  let P := polarization f κ m
  let Q := (AlgebraicGeometry.Scheme.Modules.pullback (YGG.proj f κ)).obj
      (Divisor.ofPoint p₀).lineBundle.toModules
  letI : P.IsLineBundle := polarization_isLineBundle f κ m
  letI : Q.IsLineBundle := AlgebraicGeometry.Scheme.Modules.IsLineBundle.pullback
    (YGG.proj f κ) _
  have hP := degree_tensorPow Γ P b
  have hQ := degree_tensorPow Γ Q (m * a)
  have hPQ := degree_tensor Γ (AlgebraicGeometry.Scheme.Modules.tensorPow P b)
      (AlgebraicGeometry.Scheme.Modules.tensorPow Q (m * a))
  change Γ.degree (AlgebraicGeometry.Scheme.Modules.tensor
      (AlgebraicGeometry.Scheme.Modules.tensorPow P b)
      (AlgebraicGeometry.Scheme.Modules.tensorPow Q (m * a))) = _
  rw [hPQ, hP, hQ, hfib]
  push_cast
  ring

theorem negative_slope {K : Type u} [Field K] [IsAlgClosed K]
    {X : SmoothProjectiveVariety K} {C : SmoothProjectiveCurve K}
    (f : C.toScheme ⟶ X.toScheme) [MMSetup f] (κ m : ℕ) (hm0 : 0 < m)
    [Fact ((jetAlgebra f κ).SufficientlyDivisible m)]
    (p₀ : C.toScheme) (hp₀ : IsClosed ({p₀} : Set C.toScheme)) (a b e₀ : ℕ) (hb : 0 < b) (he₀ : 0 < e₀)
    (Γ : IntegralCurve K (YGG f κ))
    (hfib : Γ.degree ((AlgebraicGeometry.Scheme.Modules.pullback (YGG.proj f κ)).obj
        (Divisor.ofPoint p₀).lineBundle.toModules) = e₀)
    (hneg : Γ.degree (shiftedBundle f κ m p₀ a b) < 0) :
    (a : ℚ) / b < - (Γ.degree (polarization f κ m) : ℚ) / ((m : ℚ) * e₀) := by
  have hshift := shifted_degree f κ m p₀ a b e₀ Γ hfib
  have hneg' : (b : ℤ) * Γ.degree (polarization f κ m) +
      (m * a : ℤ) * e₀ < 0 := by
    rw [← hshift]
    exact hneg
  have hnegQ : (b : ℚ) * (Γ.degree (polarization f κ m) : ℚ) +
      (m * a : ℚ) * (e₀ : ℚ) < 0 := by
    exact_mod_cast hneg'
  have hbQ : (0 : ℚ) < b := by exact_mod_cast hb
  have hmQ : (0 : ℚ) < m := by exact_mod_cast hm0
  have heQ : (0 : ℚ) < e₀ := by exact_mod_cast he₀
  have hmeQ : (0 : ℚ) < (m : ℚ) * e₀ := mul_pos hmQ heQ
  apply (div_lt_div_iff₀ hbQ hmeQ).2
  nlinarith [hnegQ]

end
