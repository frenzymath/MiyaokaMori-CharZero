import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.PrincipalDivisorDegreeZero
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.RationalSectionDegree
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.RationalSectionDivisorTensor
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.IntegralCurveDegree
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.Stacks01ct

/-! # Additivity of the degree on an integral proper curve

On an integral proper curve, the degree of a line bundle is additive under tensor product and the
structure sheaf has degree zero; hence the `q`-th tensor power has `q` times the degree.

Proof sketch:
1. The divisor of any nonzero rational section of the structure sheaf is principal; principal
   divisors have degree zero, and `IntegralCurve.degree_eq_degree_rationalSectionDivisor` gives
   `deg O = 0`.
2. Choose nonzero rational sections of `A` and `B`; `exists_rationalSectionDivisor_tensor` gives a
   section of `A ⊗ B` whose divisor is the sum.
3. On a proper curve a zero-cycle has finite support, so the degree is compatible with addition of
   cycles; `topSelfIntersection_congr` transports along the pullback and tensor isomorphisms.
4. Induction on `q`, using additivity and `deg O = 0`, gives the tensor-power formula.

Sources: Stacks 02SL, 02RU.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

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

theorem IntegralCurve.degree_unit {K : Type u} [Field K]
    {Y : AlgebraicGeometry.Scheme.{u}}
    [Y.Over (AlgebraicGeometry.Spec (CommRingCat.of K))]
    (Γ : IntegralCurve K Y) :
    Γ.degree (SheafOfModules.unit Y.ringCatSheaf) = 0 := by
  let : AlgebraicGeometry.IsNoetherian Γ.carrier :=
    AlgebraicGeometry.Intersection.properFieldScheme_isNoetherian
      (Γ.ι ≫ (Y ↘ AlgebraicGeometry.Spec (CommRingCat.of K)))
  let M : Γ.carrier.Modules :=
    (AlgebraicGeometry.Scheme.Modules.pullback Γ.ι).obj
      (SheafOfModules.unit Y.ringCatSheaf)
  let : M.IsLineBundle :=
    AlgebraicGeometry.Scheme.Modules.IsLineBundle.pullback Γ.ι
      (SheafOfModules.unit Y.ringCatSheaf)
  let e := AlgebraicGeometry.Scheme.Modules.pullbackUnitIso Γ.ι
  obtain ⟨s, hs⟩ := AlgebraicGeometry.Scheme.Modules.exists_stalk_genericPoint_ne_zero M
  obtain ⟨g, hg⟩ :=
    AlgebraicGeometry.Scheme.Modules.rationalSectionDivisor_eq_principalCycle_of_iso_unit
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
  let : AlgebraicGeometry.IsProper
      (W ↘ AlgebraicGeometry.Spec (CommRingCat.of K)) := hW
  have hA' : (Function.support A).Finite := by
    exact AlgebraicGeometry.Intersection.properCycle_finiteSupport
      (W ↘ AlgebraicGeometry.Spec (CommRingCat.of K)) A
  have hB' : (Function.support B).Finite := by
    exact AlgebraicGeometry.Intersection.properCycle_finiteSupport
      (W ↘ AlgebraicGeometry.Spec (CommRingCat.of K)) B
  have hAdeg : Function.HasFiniteSupport
      (fun x : W => A x *
        ((W ↘ AlgebraicGeometry.Spec (CommRingCat.of K)).residueDegree x : ℤ)) := by
    exact Function.HasFiniteSupport.mul_left hA' _
  have hBdeg : Function.HasFiniteSupport
      (fun x : W => B x *
        ((W ↘ AlgebraicGeometry.Spec (CommRingCat.of K)).residueDegree x : ℤ)) := by
    exact Function.HasFiniteSupport.mul_left hB' _
  unfold AlgebraicGeometry.AlgebraicCycle.degree
  change (∑ᶠ x : W, (A x + B x) *
    ((W ↘ AlgebraicGeometry.Spec (CommRingCat.of K)).residueDegree x : ℤ)) = _
  rw [show (fun x : W => (A x + B x) *
      ((W ↘ AlgebraicGeometry.Spec (CommRingCat.of K)).residueDegree x : ℤ)) =
        (fun x : W => A x *
          ((W ↘ AlgebraicGeometry.Spec (CommRingCat.of K)).residueDegree x : ℤ) +
        B x * ((W ↘ AlgebraicGeometry.Spec (CommRingCat.of K)).residueDegree x : ℤ)) by
    funext x
    ring]
  exact finsum_add_distrib hAdeg hBdeg

theorem IntegralCurve.degree_tensor {K : Type u} [Field K] [IsAlgClosed K]
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
  let : AΓ.IsLineBundle :=
    AlgebraicGeometry.Scheme.Modules.IsLineBundle.pullback Γ.ι A
  let : BΓ.IsLineBundle :=
    AlgebraicGeometry.Scheme.Modules.IsLineBundle.pullback Γ.ι B
  let : TΓ.IsLineBundle :=
    AlgebraicGeometry.Scheme.Modules.IsLineBundle.pullback Γ.ι _
  have hdim : topologicalKrullDim Γ.carrier ≤ 1 := by
    rw [Γ.dim_eq_one]
  have hproper : IsProperOver K Γ.carrier := Γ.isProperOver
  let : AlgebraicGeometry.IsNoetherian Γ.carrier :=
    AlgebraicGeometry.Intersection.properFieldScheme_isNoetherian
      (Γ.ι ≫ (Y ↘ AlgebraicGeometry.Spec (CommRingCat.of K)))
  obtain ⟨s, hs⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_stalk_genericPoint_ne_zero AΓ
  obtain ⟨t, ht⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_stalk_genericPoint_ne_zero BΓ
  have hAeq : AlgebraicGeometry.AlgebraicCycle.degree (k := K)
      (AΓ.rationalSectionDivisor s) = Γ.degree A :=
    (Γ.degree_eq_degree_rationalSectionDivisor A s hs).symm
  have hBeq : AlgebraicGeometry.AlgebraicCycle.degree (k := K)
      (BΓ.rationalSectionDivisor t) = Γ.degree B :=
    (Γ.degree_eq_degree_rationalSectionDivisor B t ht).symm
  obtain ⟨v, hv, hdiv⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_rationalSectionDivisor_tensor
      AΓ BΓ s t hs ht
  have hiso := (AlgebraicGeometry.Scheme.Modules.pullbackTensorIso Γ.ι A B).symm
  have hTeq : AlgebraicGeometry.AlgebraicCycle.degree (k := K)
      ((AΓ.tensor BΓ).rationalSectionDivisor v) =
        Γ.degree (AlgebraicGeometry.Scheme.Modules.tensor A B) := by
    rw [Γ.degree_eq_topSelfIntersection,
      ← AlgebraicGeometry.topSelfIntersection_congr Γ.carrier Γ.isProperOver _ _ hiso,
      MiyaokaMori.TopSelfIntersectionCurve.topSelfIntersection_eq_degree_rationalSectionDivisor
        Γ.isProperOver Γ.carrier_dimension (AΓ.tensor BΓ) v hv]
  have hAmem :=
    MiyaokaMori.RationalSectionDegree.rationalSectionDivisor_mem_cycleSubgroup_zero
      hproper hdim AΓ s hs
  have hBmem :=
    MiyaokaMori.RationalSectionDegree.rationalSectionDivisor_mem_cycleSubgroup_zero
      hproper hdim BΓ t ht
  have hsum := degree_add_cycle hproper
    (AΓ.rationalSectionDivisor s) (BΓ.rationalSectionDivisor t) hAmem hBmem
  calc
    Γ.degree (AlgebraicGeometry.Scheme.Modules.tensor A B) =
        AlgebraicGeometry.AlgebraicCycle.degree (k := K)
          ((AΓ.tensor BΓ).rationalSectionDivisor v) := hTeq.symm
    _ = AlgebraicGeometry.AlgebraicCycle.degree (k := K)
          (AΓ.rationalSectionDivisor s + BΓ.rationalSectionDivisor t) := by rw [hdiv]
    _ = _ := by rw [hsum, hAeq, hBeq]

theorem IntegralCurve.degree_tensorPow {K : Type u} [Field K] [IsAlgClosed K]
    {Y : AlgebraicGeometry.Scheme.{u}}
    [Y.Over (AlgebraicGeometry.Spec (CommRingCat.of K))]
    (Γ : IntegralCurve K Y) (A : Y.Modules) [A.IsLineBundle] (q : ℕ) :
    Γ.degree (AlgebraicGeometry.Scheme.Modules.tensorPow A q) =
      (q : ℤ) * Γ.degree A := by
  induction q with
  | zero =>
      change Γ.degree (SheafOfModules.unit Y.ringCatSheaf) = _
      rw [IntegralCurve.degree_unit]
      simp
  | succ q ih =>
      change Γ.degree (AlgebraicGeometry.Scheme.Modules.tensor
        (AlgebraicGeometry.Scheme.Modules.tensorPow A q) A) = _
      rw [IntegralCurve.degree_tensor, ih]
      push_cast
      ring

end
