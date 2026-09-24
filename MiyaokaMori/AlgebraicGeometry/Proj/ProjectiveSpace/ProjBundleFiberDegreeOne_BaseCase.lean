import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpaceStructureMorphism
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.SerreTwistIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.TopSelfIntersectionIsoInvariant
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.SchemeFundamentalCycle
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ZeroCycleDegreeScheme

/-! # `P^0_K` has degree one

Base case of the induction: `deg [P^0_K] = 1`, i.e. `topSelfIntersection (P^0_K) O(1) = 1`.
`P^0 = D_+(x_0) = Spec (K[x_0]_{(x_0)})` and the degree-`0` localization `K[x_0]_{(x_0)}` is `K`,
so `P^0 ≅ Spec K` over `K`; on `Spec K` the fundamental cycle is one point of residue degree `1`.

Source: Hartshorne II.2 (`Proj` charts), Stacks 01M5; the base case of formula (2.6) of the paper.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace ProjBundleFiberDegreeOne

open AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

/-- `topSelfIntersection` at a known dimension `d` (private copy of the helper in
`ProjBundleFiberDegreeOne_Step`, to keep this module independent). -/
private theorem topSelfIntersection_eq_of_dimension_eq' {k : Type u} [Field k] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))] (hX : IsProperOver k X) [IsLocallyNoetherian X]
    (L : X.Modules) [L.IsLineBundle] {d : ℕ} (hd : X.dimension = d) :
    topSelfIntersection X hX L =
      ChowGroup.degreeOver k X hX (firstChernClass.capPow L d 0
        (cast (congrArg (ChowGroup X) (zero_add d).symm) (X.fundamentalChowClass d))) := by
  subst hd
  rfl

section BaseCase

variable (K : Type u) [Field K]

/-- The coordinate `x_0` of `P^0 = Proj K[x_0]` (a `def`, so that all occurrences are syntactically equal
and instance arguments about it match). -/
def coordZero : MvPolynomial (Fin (0 + 1)) K := MvPolynomial.X 0

/-- `x_0 ∈ K[x_0]` is homogeneous of degree `1`. -/
theorem X_zero_mem_projectiveGrading_one : coordZero K ∈ AlgebraicGeometry.Proj.projectiveGrading K 0 1 :=
  (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_X K 0)

/-- `Spec K` over itself: the structure morphism (`specOverSpec`, `Spec.map (algebraMap K K)`) is the
identity. -/
theorem spec_over_self_eq_id :
    (Spec (CommRingCat.of K) ↘ Spec (CommRingCat.of K)) = 𝟙 (Spec (CommRingCat.of K)) := by
  show Spec.map (CommRingCat.ofHom (algebraMap K K)) = 𝟙 _
  rw [show CommRingCat.ofHom (algebraMap K K) = 𝟙 (CommRingCat.of K) from rfl, Spec.map_id]

/-- `D_+(x_0) = P^0`, so the chart `Spec (K[x_0]_{(x_0)}) → P^0` is an isomorphism. -/
theorem isIso_awayι_zero :
    IsIso (Proj.awayι (AlgebraicGeometry.Proj.projectiveGrading K 0) (coordZero K)
      (X_zero_mem_projectiveGrading_one K) Nat.one_pos) := by
  apply isIso_of_isOpenImmersion_of_opensRange_eq_top
  rw [Proj.opensRange_awayι]
  have h : ⨆ i : Fin 1, Proj.basicOpen (AlgebraicGeometry.Proj.projectiveGrading K 0) (MvPolynomial.X i) = ⊤ :=
    projectiveSpace_iSup_basicOpen_X K 0
  rw [iSup_unique, Fin.default_eq_zero] at h
  exact h

/-- A homogeneous polynomial of degree `n` in one variable is `c · x_0^n`. -/
theorem MvPolynomial.eq_C_mul_X_pow_of_isHomogeneous_fin_one {a : MvPolynomial (Fin 1) K} {n : ℕ}
    (ha : a.IsHomogeneous n) :
    a = MvPolynomial.C (MvPolynomial.coeff (Finsupp.single 0 n) a) * MvPolynomial.X 0 ^ n := by
  classical
  rw [MvPolynomial.X_pow_eq_monomial, MvPolynomial.C_mul_monomial, mul_one]
  ext d
  have hd : d = Finsupp.single 0 (d 0) := Finsupp.ext fun j => by
    rw [Subsingleton.elim j 0]
    simp
  rw [MvPolynomial.coeff_monomial]
  by_cases h : d 0 = n
  · rw [if_pos (by rw [hd, h]), hd, h]
  · have hdeg : d.degree ≠ n := by
      rw [hd, Finsupp.degree_single]
      exact h
    rw [ha.coeff_eq_zero hdeg, if_neg]
    intro heq
    apply h
    have := congrArg (fun f : Fin 1 →₀ ℕ => f 0) heq
    simpa using this.symm

/-- The ring map `K → K[x_0]_{(x_0)}`, `c ↦ c/1`. -/
def fromFieldAway : K →+* HomogeneousLocalization.Away (AlgebraicGeometry.Proj.projectiveGrading K 0) (coordZero K) :=
  (HomogeneousLocalization.fromZeroRingHom (AlgebraicGeometry.Proj.projectiveGrading K 0)
    (Submonoid.powers (coordZero K))).comp
      (algebraMap K (AlgebraicGeometry.Proj.projectiveGrading K 0 0))

/-- The degree-zero localization `K[x_0]_{(x_0)}` is `K`: `fromFieldAway` is bijective (surjective since
every element is `a / x_0^n` with `a = c·x_0^n`). -/
theorem bijective_fromFieldAway : Function.Bijective (fromFieldAway K) := by
  have hpow : Submonoid.powers (coordZero K) ≤ nonZeroDivisors (MvPolynomial (Fin (0 + 1)) K) :=
    powers_le_nonZeroDivisors_of_noZeroDivisors (MvPolynomial.X_ne_zero 0)
  haveI : IsDomain (Localization (Submonoid.powers (coordZero K))) :=
    IsLocalization.isDomain_localization hpow
  haveI : Nontrivial (HomogeneousLocalization.Away (AlgebraicGeometry.Proj.projectiveGrading K 0) (coordZero K)) := by
    refine ⟨⟨1, 0, fun h => ?_⟩⟩
    have := congrArg HomogeneousLocalization.val h
    rw [HomogeneousLocalization.val_one, HomogeneousLocalization.val_zero] at this
    exact one_ne_zero this
  refine ⟨RingHom.injective _, fun z => ?_⟩
  obtain ⟨n, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
    (AlgebraicGeometry.Proj.projectiveGrading K 0) (X_zero_mem_projectiveGrading_one K) z
  have ha' : a.IsHomogeneous n := by
    have := (MvPolynomial.mem_homogeneousSubmodule _ _).mp ha
    simpa using this
  have ha2 := MvPolynomial.eq_C_mul_X_pow_of_isHomogeneous_fin_one K ha'
  refine ⟨MvPolynomial.coeff (Finsupp.single 0 n) a, ?_⟩
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.Away.val_mk]
  show Localization.mk _ 1 = _
  rw [Localization.mk_eq_mk_iff]
  apply Localization.r_of_eq
  show MvPolynomial.X 0 ^ n * (algebraMap K (AlgebraicGeometry.Proj.projectiveGrading K 0 0)
    (MvPolynomial.coeff (Finsupp.single 0 n) a) : MvPolynomial (Fin (0 + 1)) K) = 1 * a
  have hcoe : ((algebraMap K (AlgebraicGeometry.Proj.projectiveGrading K 0 0)
      (MvPolynomial.coeff (Finsupp.single 0 n) a) : AlgebraicGeometry.Proj.projectiveGrading K 0 0) :
        MvPolynomial (Fin (0 + 1)) K) = MvPolynomial.C (MvPolynomial.coeff (Finsupp.single 0 n) a) := rfl
  rw [one_mul, hcoe, mul_comm]
  exact ha2.symm

/-- `P^0_K ≅ Spec K` compatibly with the structure morphisms. -/
theorem exists_iso_spec :
    ∃ e : Spec (CommRingCat.of K) ≅ ProjectiveSpace 0 K,
      e.hom ≫ (ProjectiveSpace 0 K ↘ Spec (CommRingCat.of K)) = 𝟙 _ := by
  let e₁ : CommRingCat.of K ≅ CommRingCat.of (HomogeneousLocalization.Away
      (AlgebraicGeometry.Proj.projectiveGrading K 0) (coordZero K)) :=
    (RingEquiv.ofBijective (fromFieldAway K) (bijective_fromFieldAway K)).toCommRingCatIso
  refine ⟨asIso (Spec.map e₁.inv) ≪≫
    @asIso Scheme.{u} _ _ _ (Proj.awayι (AlgebraicGeometry.Proj.projectiveGrading K 0) (coordZero K)
      (X_zero_mem_projectiveGrading_one K) Nat.one_pos) (isIso_awayι_zero K), ?_⟩
  change (Spec.map e₁.inv ≫ Proj.awayι (AlgebraicGeometry.Proj.projectiveGrading K 0) (coordZero K)
      (X_zero_mem_projectiveGrading_one K) Nat.one_pos) ≫
    (Proj.toSpecZero (AlgebraicGeometry.Proj.projectiveGrading K 0) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K (AlgebraicGeometry.Proj.projectiveGrading K 0 0)))) = 𝟙 _
  rw [Category.assoc, ← Category.assoc (Proj.awayι _ _ _ _), Proj.awayι_toSpecZero,
    ← Spec.map_comp, ← Spec.map_comp]
  have hθ : CommRingCat.ofHom (algebraMap K (AlgebraicGeometry.Proj.projectiveGrading K 0 0)) ≫
      CommRingCat.ofHom (HomogeneousLocalization.fromZeroRingHom (AlgebraicGeometry.Proj.projectiveGrading K 0) _)
        = e₁.hom := by
    ext x
    rfl
  rw [hθ, Iso.hom_inv_id, Spec.map_id]

/-- On `Spec K` over itself, every line bundle has top self-intersection `1`: `dim = 0`, the fundamental
cycle is the unique point with multiplicity `1`, and its residue degree over `K` is `1`. -/
theorem spec_field_topSelfIntersection (hS : IsProperOver K (Spec (CommRingCat.of K)))
    (L₀ : (Spec (CommRingCat.of K)).Modules) [L₀.IsLineBundle] :
    topSelfIntersection (Spec (CommRingCat.of K)) hS L₀ = 1 := by
  classical
  haveI : IsDomain (CommRingCat.of K) := inferInstanceAs (IsDomain K)
  haveI : IsIntegral (Spec (CommRingCat.of K)) := inferInstance
  haveI : IsProper (Spec (CommRingCat.of K) ↘ Spec (CommRingCat.of K)) := hS
  haveI : IsLocallyNoetherian (Spec (CommRingCat.of K)) :=
    LocallyOfFiniteType.isLocallyNoetherian (Spec (CommRingCat.of K) ↘ Spec (CommRingCat.of K))
  have hkrull : topologicalKrullDim (Spec (CommRingCat.of K)) = 0 := by
    rw [show topologicalKrullDim (Spec (CommRingCat.of K)) = topologicalKrullDim (PrimeSpectrum K)
      from rfl, PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, ringKrullDim_eq_zero_of_field]
  have hdim : (Spec (CommRingCat.of K)).dimension = 0 := by
    unfold Scheme.dimension
    rw [hkrull]
    rfl
  have hfc := Scheme.fundamentalCycle_of_isIntegral (Spec (CommRingCat.of K))
    (by rw [hkrull]; decide)
  rw [hdim] at hfc
  rw [topSelfIntersection_eq_of_dimension_eq' _ hS _ hdim]
  show ChowGroup.degreeOver K _ hS
    (ChowGroup.mk ⟨(Spec (CommRingCat.of K)).fundamentalCycle 0, _⟩) = 1
  show AlgebraicCycle.degree (k := K) ((Spec (CommRingCat.of K)).fundamentalCycle 0) = 1
  unfold AlgebraicCycle.degree
  rw [finsum_eq_single _ (genericPoint (Spec (CommRingCat.of K)))]
  · rw [hfc, spec_over_self_eq_id, Scheme.Hom.residueDegree_id]
    simp only [if_true, Nat.cast_one, mul_one]
  · intro x hx
    simp only [hfc, if_neg hx, zero_mul]

end BaseCase

/-- Base case: `deg [P^0_K] = 1`, i.e. `(O_{P^0}(1)^0) = 1`. Transport along `Spec K ≅ P^0`
(`exists_iso_spec`, `topSelfIntersection_eq_of_iso_over`) and compute on `Spec K`
(`spec_field_topSelfIntersection`). -/
theorem projectiveSpace_zero_topSelfIntersection_one (K : Type u) [Field K]
    (hP : IsProperOver K (ProjectiveSpace 0 K)) :
    topSelfIntersection (ProjectiveSpace 0 K) hP (projectiveSpaceTwist K 0 1) = 1 := by
  obtain ⟨e, he⟩ := exists_iso_spec K
  haveI : e.hom.IsOver (Spec (CommRingCat.of K)) := ⟨he.trans (spec_over_self_eq_id K).symm⟩
  have hS : IsProperOver K (Spec (CommRingCat.of K)) := by
    show IsProper (Spec (CommRingCat.of K) ↘ Spec (CommRingCat.of K))
    rw [spec_over_self_eq_id]
    infer_instance
  rw [← topSelfIntersection_eq_of_iso_over e hS hP _
    ((Scheme.Modules.pullback e.hom).obj (projectiveSpaceTwist K 0 1)) ⟨Iso.refl _⟩]
  exact spec_field_topSelfIntersection K hS _

end ProjBundleFiberDegreeOne

end
