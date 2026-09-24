import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Blowup.ReesAlgebraSheaf
import MiyaokaMori.RingTheory.RegularLocalRing.Stacks00no

/-! # Base change of the Rees algebra of a regular local ring to the residue field

For a regular local ring `(A, 𝔪, κ)` with `dim A = d`, the base change of the Rees algebra `⊕ₙ 𝔪ⁿ`
along `A → κ` is the polynomial ring `κ[T₁,…,T_d]` as a graded algebra
(`(⊕ 𝔪ⁿ) ⊗_A κ = ⊕ 𝔪ⁿ/𝔪ⁿ⁺¹ = gr_𝔪 A ≅ κ[T₁,…,T_d]`, Stacks 00NO), in exactly the input form needed
for Stacks 01N2 (`Proj.isPullback_of_isBaseChange`): a graded ring homomorphism `f`, the
irrelevant-ideal condition `hf`, an `A`-algebra map `fR` and `IsBaseChange κ fR`.

References: Stacks 00NO (Algebra, Lemma "lemma-regular-graded") and the sentence
"`(⊕ 𝔪ⁿ) ⊗_A κ = gr_𝔪 A`" in the proof of 0AGQ; the prescribed-point specialization (Lemma 5.1 of the paper).

Proof layout (all helper declarations live in `namespace ReesResidueBaseChange`):
* generic commutative ring `R`, ideal `I`, generators `x : Fin d → R`:
  `reesAeval : R[T] →ₐ[R] reesAlgebra I`, `T_i ↦ x_i X`; the coefficient formula
  `coeff_aeval_monomial_one` (coefficient of `X^n` in `F(xX)` is `F_n(x)`), surjectivity from
  `adjoin_monomial_eq_reesAlgebra`, and `coeff_mem_of_reesAeval_eq_zero` (the use of Stacks 00NO);
* local ring `R`, `𝔪 = span x`: `residueMap : R[T] →ₐ[R] κ[T]` (reduce coefficients),
  `residueRees : reesAlgebra 𝔪 →ₐ[R] κ[T]` (descend `residueMap` through the surjection `reesAeval`),
  gradedness via `Ideal.mem_span_pow_iff_exists_isHomogeneous`, `IsBaseChange` by hand
  (every tensor is `1 ⊗ p`, and `1 ⊗ p = 0` once all coefficients lie in `𝔪`);
* `HomogeneousIdeal.irrelevant_le_map_of_surjective`: a surjective graded ring hom satisfies the
  irrelevant-ideal condition of Stacks 01N2.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
open scoped HomogeneousIdeal
open scoped TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

/-! ## A surjective graded ring hom satisfies the irrelevant-ideal condition -/

/-- If `f : 𝒜 →+*ᵍ ℬ` is surjective then `ℬ₊ ≤ 𝒜₊.map f`: for `b = f a ∈ ℬ₊`, the degree-`0`
component of `f a` is `f a₀ = 0`, so `b = f (a - a₀)` with `a - a₀ ∈ 𝒜₊`. -/
theorem HomogeneousIdeal.irrelevant_le_map_of_surjective {A B σ τ : Type*} [Ring A] [Ring B]
    [SetLike σ A] [SetLike τ B] [AddSubgroupClass σ A] [AddSubmonoidClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ] (f : 𝒜 →+*ᵍ ℬ)
    (hf : Function.Surjective f) : ℬ₊ ≤ 𝒜₊.map f := by
  intro b hb
  obtain ⟨a, rfl⟩ := hf b
  rw [HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply] at hb
  have key : f a = f (a - (DirectSum.decompose 𝒜 a 0 : A)) := by
    rw [map_sub, GradedRingHom.map_directSumDecompose, hb, sub_zero]
  rw [key]
  refine Ideal.mem_map_of_mem _ ?_
  rw [HomogeneousIdeal.mem_iff, HomogeneousIdeal.mem_irrelevant_iff, GradedRing.proj_apply,
    DirectSum.decompose_sub, DirectSum.sub_apply, AddSubgroupClass.coe_sub,
    DirectSum.decompose_of_mem_same 𝒜 (SetLike.coe_mem _), sub_self]

namespace ReesResidueBaseChange

variable {R : Type u} [CommRing R] {d : ℕ}

/-! ## Generic: the presentation `R[T₁,…,T_d] → Rees(I)`, `T_i ↦ x_i X` -/

/-- Coefficient formula: substituting `T_i ↦ x_i X` into `F`, the coefficient of `X^n` is the value
at `x` of the degree-`n` homogeneous component of `F`. -/
theorem coeff_aeval_monomial_one (x : Fin d → R) (F : MvPolynomial (Fin d) R) (n : ℕ) :
    (MvPolynomial.aeval (fun i => Polynomial.monomial 1 (x i)) F).coeff n =
      MvPolynomial.eval x (MvPolynomial.homogeneousComponent n F) := by
  induction F using MvPolynomial.induction_on' with
  | monomial m c =>
    have hprod : (m.prod fun i k => Polynomial.monomial 1 (x i) ^ k) =
        Polynomial.monomial m.degree (m.prod fun i k => x i ^ k) := by
      simp_rw [← Polynomial.C_mul_X_eq_monomial, mul_pow, ← map_pow]
      rw [Finsupp.prod_mul, ← map_finsuppProd]
      simp only [Finsupp.prod_pow]
      rw [Finset.prod_pow_eq_pow_sum, ← Finsupp.degree_eq_sum, Polynomial.C_mul_X_pow_eq_monomial]
    rw [MvPolynomial.aeval_monomial, hprod, Polynomial.algebraMap_eq, Polynomial.C_mul_monomial, Polynomial.coeff_monomial,
      MvPolynomial.homogeneousComponent_of_mem (MvPolynomial.isHomogeneous_monomial c rfl)]
    split_ifs with h1 h2 h2
    · rw [MvPolynomial.eval_monomial]
    · exact absurd h1.symm h2
    · exact absurd h2.symm h1
    · rw [map_zero]
  | add p q hp hq => rw [map_add, Polynomial.coeff_add, map_add, map_add, hp, hq]

/-- A homogeneous `F` of degree `n` is sent to the monomial `F(x) Xⁿ`. -/
theorem aeval_monomial_one_of_isHomogeneous (x : Fin d → R) {F : MvPolynomial (Fin d) R} {n : ℕ}
    (hF : F.IsHomogeneous n) :
    MvPolynomial.aeval (fun i => Polynomial.monomial 1 (x i)) F =
      Polynomial.monomial n (MvPolynomial.eval x F) := by
  ext k
  rw [coeff_aeval_monomial_one, MvPolynomial.homogeneousComponent_of_mem hF,
    Polynomial.coeff_monomial]
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd h1.symm h2
  · exact absurd h2.symm h1
  · rw [map_zero]

variable (I : Ideal R) (x : Fin d → R) (hx : ∀ i, x i ∈ I)

/-- The `R`-algebra map `R[T₁,…,T_d] → Rees(I) = ⊕ Iⁿ Xⁿ`, `T_i ↦ x_i X`. -/
def reesAeval : MvPolynomial (Fin d) R →ₐ[R] reesAlgebra I :=
  MvPolynomial.aeval fun i => ⟨Polynomial.monomial 1 (x i),
    reesAlgebra.monomial_mem.mpr (by rw [pow_one]; exact hx i)⟩

theorem coe_reesAeval (F : MvPolynomial (Fin d) R) :
    ((reesAeval I x hx F : reesAlgebra I) : Polynomial R) =
      MvPolynomial.aeval (fun i => Polynomial.monomial 1 (x i)) F := by
  change (reesAlgebra I).val (reesAeval I x hx F) = _
  rw [reesAeval, ← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  rfl

/-- `Rees(I)` is generated by the degree-one monomials `r X`, `r ∈ I = (x₁,…,x_d)`, each of which is
`∑ cᵢ xᵢ X = (∑ cᵢ Tᵢ)(xX)`. -/
theorem reesAeval_surjective (hspan : Ideal.span (Set.range x) = I) :
    Function.Surjective (reesAeval I x hx) := by
  rintro ⟨q, hq⟩
  have hmem : q ∈ (MvPolynomial.aeval fun i => Polynomial.monomial 1 (x i) :
      MvPolynomial (Fin d) R →ₐ[R] Polynomial R).range := by
    rw [← adjoin_monomial_eq_reesAlgebra] at hq
    refine Algebra.adjoin_le ?_ hq
    rintro _ ⟨r, hr, rfl⟩
    rw [← hspan] at hr
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hr
    refine (AlgHom.mem_range _).mpr ⟨∑ i, c i • MvPolynomial.X i, ?_⟩
    simp only [map_sum, map_smul, MvPolynomial.aeval_X]
  obtain ⟨F, hF⟩ := hmem
  exact ⟨F, Subtype.ext (by rw [coe_reesAeval]; exact hF)⟩

/-- **The use of Stacks 00NO.** If `F(xX) = 0` in `Rees(I)` then every homogeneous component `Fₙ`
satisfies `Fₙ(x) = 0 ∈ Iⁿ⁺¹`, so (by the hypothesis `h3`, i.e. Stacks 00NO for `I = 𝔪`) all
coefficients of every `Fₙ`, hence of `F`, lie in `I`. -/
theorem coeff_mem_of_reesAeval_eq_zero
    (h3 : ∀ (n : ℕ) (F : MvPolynomial (Fin d) R), F.IsHomogeneous n →
      MvPolynomial.eval x F ∈ I ^ (n + 1) → ∀ m, F.coeff m ∈ I)
    {F : MvPolynomial (Fin d) R} (hF : reesAeval I x hx F = 0) (m : Fin d →₀ ℕ) :
    F.coeff m ∈ I := by
  have hcoe : ∀ n, MvPolynomial.eval x (MvPolynomial.homogeneousComponent n F) = 0 := by
    intro n
    rw [← coeff_aeval_monomial_one, ← coe_reesAeval I x hx, hF, Subalgebra.coe_zero,
      Polynomial.coeff_zero]
  have hcomp : ∀ n, (MvPolynomial.homogeneousComponent n F).coeff m ∈ I := fun n =>
    h3 n _ (MvPolynomial.homogeneousComponent_isHomogeneous n F)
      (by rw [hcoe]; exact zero_mem _) m
  have hsum := MvPolynomial.sum_homogeneousComponent F
  rw [← hsum, MvPolynomial.coeff_sum]
  exact Submodule.sum_mem _ fun n _ => hcomp n

/-! ## Local ring: descend to `κ[T₁,…,T_d]` -/

section LocalRing

variable [IsLocalRing R]

/-- `R[T] → κ[T]`, reduce the coefficients modulo `𝔪`. -/
def residueMap : MvPolynomial (Fin d) R →ₐ[R] MvPolynomial (Fin d) (IsLocalRing.ResidueField R) :=
  MvPolynomial.mapAlgHom (Algebra.ofId R (IsLocalRing.ResidueField R))

theorem residueMap_apply (F : MvPolynomial (Fin d) R) :
    residueMap F = MvPolynomial.map (IsLocalRing.residue R) F := rfl

theorem residueMap_eq_zero_iff (F : MvPolynomial (Fin d) R) :
    residueMap F = 0 ↔ ∀ m, F.coeff m ∈ IsLocalRing.maximalIdeal R := by
  rw [residueMap_apply]
  constructor
  · intro h m
    have := congrArg (MvPolynomial.coeff m) h
    rwa [MvPolynomial.coeff_map, MvPolynomial.coeff_zero, IsLocalRing.residue_eq_zero_iff] at this
  · intro h
    ext m
    rw [MvPolynomial.coeff_map, MvPolynomial.coeff_zero, IsLocalRing.residue_eq_zero_iff]
    exact h m

theorem residueMap_surjective : Function.Surjective (residueMap (R := R) (d := d)) :=
  MvPolynomial.map_surjective _ IsLocalRing.residue_surjective

theorem residueMap_isHomogeneous {F : MvPolynomial (Fin d) R} {n : ℕ} (hF : F.IsHomogeneous n) :
    (residueMap F).IsHomogeneous n :=
  hF.map _

variable (x : Fin d → R) (hx : ∀ i, x i ∈ IsLocalRing.maximalIdeal R)
  (hspan : Ideal.span (Set.range x) = IsLocalRing.maximalIdeal R)
  (h3 : ∀ (n : ℕ) (F : MvPolynomial (Fin d) R), F.IsHomogeneous n →
    MvPolynomial.eval x F ∈ IsLocalRing.maximalIdeal R ^ (n + 1) →
    ∀ m, F.coeff m ∈ IsLocalRing.maximalIdeal R)

/-- `residueMap` factors through `R[T] ⧸ ker (reesAeval)` (Stacks 00NO). -/
def residueQuotLift : (MvPolynomial (Fin d) R ⧸ RingHom.ker (reesAeval (IsLocalRing.maximalIdeal R) x hx))
    →ₐ[R] MvPolynomial (Fin d) (IsLocalRing.ResidueField R) :=
  Ideal.Quotient.liftₐ (RingHom.ker (reesAeval (IsLocalRing.maximalIdeal R) x hx))
    (residueMap (R := R) (d := d)) fun F hF =>
      (residueMap_eq_zero_iff F).mpr
        (coeff_mem_of_reesAeval_eq_zero _ x hx h3 (RingHom.mem_ker.mp hF))

/-- `Rees(𝔪) → κ[T]`: `residueMap` descends along the surjection `reesAeval : R[T] → Rees(𝔪)`
because `ker (reesAeval) ≤ ker (residueMap)` (Stacks 00NO). -/
def residueRees : reesAlgebra (IsLocalRing.maximalIdeal R) →ₐ[R]
    MvPolynomial (Fin d) (IsLocalRing.ResidueField R) :=
  (residueQuotLift x hx h3).comp
    (Ideal.quotientKerAlgEquivOfSurjective (reesAeval_surjective _ x hx hspan)).symm.toAlgHom

theorem residueRees_reesAeval (F : MvPolynomial (Fin d) R) :
    residueRees x hx hspan h3 (reesAeval _ x hx F) = residueMap F := by
  show residueQuotLift x hx h3
    ((Ideal.quotientKerAlgEquivOfSurjective (reesAeval_surjective _ x hx hspan)).symm
      (reesAeval _ x hx F)) = _
  rw [Ideal.quotientKerAlgEquivOfSurjective_symm_apply]
  rfl

theorem residueRees_surjective : Function.Surjective (residueRees x hx hspan h3) := by
  intro b
  obtain ⟨F, rfl⟩ := residueMap_surjective (R := R) (d := d) b
  exact ⟨reesAeval _ x hx F, residueRees_reesAeval x hx hspan h3 F⟩

/-- `residueRees` is graded: a degree-`n` element `a Xⁿ` of `Rees(𝔪)`, `a ∈ 𝔪ⁿ = (x)ⁿ`, is
`G(xX)` for a homogeneous `G` of degree `n` (`Ideal.mem_span_pow_iff_exists_isHomogeneous`), so its
image is the homogeneous polynomial `Ḡ`. -/
theorem residueRees_mem {n : ℕ} {p : reesAlgebra (IsLocalRing.maximalIdeal R)}
    (hp : p ∈ Ideal.reesGrading (IsLocalRing.maximalIdeal R) n) :
    residueRees x hx hspan h3 p ∈
      MvPolynomial.homogeneousSubmodule (Fin d) (IsLocalRing.ResidueField R) n := by
  obtain ⟨a, ha⟩ := (MiyaokaMori.RingTheory.ReesAlgebra.mem_grading_iff _ n p).mp hp
  have hamem : a ∈ Ideal.span (Set.range x) ^ n := by
    rw [hspan]
    have := (mem_reesAlgebra_iff _ _).mp p.2 n
    rwa [← ha, Polynomial.coeff_monomial_same] at this
  obtain ⟨G, hG, hGa⟩ := (Ideal.mem_span_pow_iff_exists_isHomogeneous x a).mp hamem
  have hpG : p = reesAeval _ x hx G := by
    apply Subtype.ext
    rw [coe_reesAeval, aeval_monomial_one_of_isHomogeneous x hG, hGa, ha]
  rw [hpG, residueRees_reesAeval]
  exact residueMap_isHomogeneous hG

/-- `residueRees` as a graded ring hom `⊕ 𝔪ⁿ →+*ᵍ κ[T]` (standard grading). -/
def residueReesGraded : Ideal.reesGrading (IsLocalRing.maximalIdeal R) →+*ᵍ
    MvPolynomial.homogeneousSubmodule (Fin d) (IsLocalRing.ResidueField R) :=
  ⟨(residueRees x hx hspan h3).toRingHom, fun hp => residueRees_mem x hx hspan h3 hp⟩

theorem residueReesGraded_apply (p : reesAlgebra (IsLocalRing.maximalIdeal R)) :
    residueReesGraded x hx hspan h3 p = residueRees x hx hspan h3 p := rfl

/-! ### The base-change property -/

/-- Every element of `κ ⊗[R] Rees(𝔪)` is a pure tensor `1 ⊗ p` (since `R → κ` is surjective). -/
theorem exists_one_tmul (t : IsLocalRing.ResidueField R ⊗[R] reesAlgebra (IsLocalRing.maximalIdeal R)) :
    ∃ p, t = 1 ⊗ₜ p := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, (TensorProduct.tmul_zero _ _).symm⟩
  | tmul c p =>
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective c
    refine ⟨a • p, ?_⟩
    rw [← TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one, IsLocalRing.ResidueField.algebraMap_eq]
  | add s t hs ht =>
    obtain ⟨p, rfl⟩ := hs
    obtain ⟨q, rfl⟩ := ht
    exact ⟨p + q, (TensorProduct.tmul_add _ _ _).symm⟩

/-- If `residueRees p = 0` then `1 ⊗ p = 0` in `κ ⊗[R] Rees(𝔪)`: write `p = F(xX)`; all coefficients
of `F` lie in `𝔪` (Stacks 00NO), and `1 ⊗ (c • q) = c̄ ⊗ q = 0` for `c ∈ 𝔪`. -/
theorem one_tmul_eq_zero_of_residueRees_eq_zero (p : reesAlgebra (IsLocalRing.maximalIdeal R))
    (hp : residueRees x hx hspan h3 p = 0) :
    (1 : IsLocalRing.ResidueField R) ⊗ₜ[R] p = 0 := by
  obtain ⟨F, rfl⟩ := reesAeval_surjective _ x hx hspan p
  rw [residueRees_reesAeval, residueMap_eq_zero_iff] at hp
  have hF : reesAeval _ x hx F =
      ∑ v ∈ F.support, F.coeff v • reesAeval _ x hx (MvPolynomial.monomial v 1) := by
    conv_lhs => rw [MvPolynomial.as_sum F]
    rw [map_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [← map_smul, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [hF, TensorProduct.tmul_sum]
  refine Finset.sum_eq_zero fun v _ => ?_
  rw [← TensorProduct.smul_tmul, ← Algebra.algebraMap_eq_smul_one,
    IsLocalRing.ResidueField.algebraMap_eq, (IsLocalRing.residue_eq_zero_iff _).mpr (hp v),
    TensorProduct.zero_tmul]

/-- The `κ`-linear extension `κ ⊗[R] Rees(𝔪) → κ[T]` of `residueRees`. -/
def residueReesLift : IsLocalRing.ResidueField R ⊗[R] reesAlgebra (IsLocalRing.maximalIdeal R)
    →ₗ[IsLocalRing.ResidueField R] MvPolynomial (Fin d) (IsLocalRing.ResidueField R) :=
  (TensorProduct.isBaseChange R (reesAlgebra (IsLocalRing.maximalIdeal R))
    (IsLocalRing.ResidueField R)).lift (residueRees x hx hspan h3).toLinearMap

theorem residueReesLift_one_tmul (p : reesAlgebra (IsLocalRing.maximalIdeal R)) :
    residueReesLift x hx hspan h3 (1 ⊗ₜ p) = residueRees x hx hspan h3 p :=
  IsBaseChange.lift_eq _ _ p

theorem residueReesLift_bijective : Function.Bijective (residueReesLift x hx hspan h3) := by
  constructor
  · intro t₁ t₂ h
    obtain ⟨p₁, rfl⟩ := exists_one_tmul t₁
    obtain ⟨p₂, rfl⟩ := exists_one_tmul t₂
    rw [← sub_eq_zero, ← TensorProduct.tmul_sub]
    apply one_tmul_eq_zero_of_residueRees_eq_zero x hx hspan h3
    rw [map_sub, ← residueReesLift_one_tmul, ← residueReesLift_one_tmul, h, sub_self]
  · intro b
    obtain ⟨p, hp⟩ := residueRees_surjective x hx hspan h3 b
    exact ⟨1 ⊗ₜ p, by rw [residueReesLift_one_tmul, hp]⟩

/-- `κ[T₁,…,T_d] = κ ⊗_R Rees(𝔪)` via `residueRees`. -/
theorem residueRees_isBaseChange :
    IsBaseChange (IsLocalRing.ResidueField R) (residueRees x hx hspan h3).toLinearMap :=
  IsBaseChange.of_equiv (LinearEquiv.ofBijective _ (residueReesLift_bijective x hx hspan h3))
    fun p => residueReesLift_one_tmul x hx hspan h3 p

end LocalRing

end ReesResidueBaseChange

/-- **The base change of the Rees algebra along `A → κ` is a polynomial ring over `κ` (graded form)**.
Let `A` be a regular local ring of dimension `d`, `𝔪` its maximal ideal, `κ = A/𝔪`. Then there are a
graded ring homomorphism `f : ⊕ₙ 𝔪ⁿ →+*ᵍ κ[T₁,…,T_d]` (standard grading `homogeneousSubmodule` on the
right), the irrelevant-ideal condition `hf` (`κ[T]₊ ≤ (Rees)₊.map f`) and an `A`-algebra map
`fR : reesAlgebra 𝔪 →ₐ[A] κ[T₁,…,T_d]`, such that `fR` and `f` are the same map and `fR` is a base
change: `κ ⊗_A (⊕ 𝔪ⁿ) ≅ κ[T₁,…,T_d]` (`IsBaseChange κ fR.toLinearMap`).

Proof (the argument of Stacks 00NO):
1. **`𝔪 = (x₁,…,x_d)` with algebraically independent initial forms**:
   `IsRegularLocalRing.initialForms_algebraicallyIndependent A d hdim` gives `x : Fin d → 𝔪` with
   `Ideal.span (range x) = 𝔪`, such that for every homogeneous `F ∈ A[T]` of degree `n`, `F(x) ∈ 𝔪ⁿ⁺¹`
   implies that all coefficients of `F` lie in `𝔪`.
2. **Presentation of the Rees algebra**:
   `φ := MvPolynomial.aeval (fun i => ⟨Polynomial.monomial 1 (x i), _⟩) : A[T₁..T_d] →ₐ[A] reesAlgebra 𝔪`
   (`x i ∈ 𝔪 = 𝔪^1`, so `monomial 1 (x i) ∈ reesAlgebra 𝔪`, `reesAlgebra.monomial_mem`). `φ` is
   surjective: the Rees algebra is generated by the degree-one monomials `monomial 1 r` (`r ∈ 𝔪`)
   (`adjoin_monomial_eq_reesAlgebra`), and `r = Σ aᵢ xᵢ` gives `monomial 1 r = Σ aᵢ • monomial 1 (x i)`
   in the image of `φ`.
3. **Reduce coefficients**: `ψ := MvPolynomial.map (algebraMap A κ) : A[T] →ₐ[A] κ[T]`
   (`= MvPolynomial.aeval X`), surjective (`MvPolynomial.map_surjective`, `Ideal.Quotient.mk_surjective`),
   with kernel `Ideal.map C 𝔪` (`MvPolynomial.ker_map`).
4. **`ker φ ≤ ker ψ`** (the use of 00NO): let `φ(F) = 0`. Decompose `F = Σₙ Fₙ` by degree
   (`MvPolynomial.sum_homogeneousComponent`). The value of the homogeneous `Fₙ` at `xᵢ·X` is
   `monomial n (Fₙ(x))` (`MvPolynomial.IsHomogeneous` + `aeval` on monomials:
   `∏ (xᵢ X)^{kᵢ} = (∏ xᵢ^{kᵢ}) X^{|k|}`), so `φ(F) = Σₙ monomial n (Fₙ(x)) = 0` ⇒ every
   `Fₙ(x) = 0 ∈ 𝔪ⁿ⁺¹` (compare `Polynomial.coeff`s), and by step 1 all coefficients of `Fₙ` lie in `𝔪`,
   i.e. `ψ(Fₙ) = 0`; summing, `ψ(F) = 0`.
5. **Definition of `fR`**:
   `fR := (Ideal.Quotient.liftₐ (RingHom.ker φ) ψ h4).comp (Ideal.quotientKerAlgEquivOfSurjective hφ).symm`,
   so that `fR ∘ φ = ψ` (`quotientKerAlgEquivOfSurjective_mk` + `Ideal.Quotient.liftₐ_apply`).
6. **`f` is graded**: `p ∈ reesGrading 𝔪 n` means `p = monomial n a` with `a ∈ 𝔪ⁿ`
   (`MiyaokaMori.RingTheory.ReesAlgebra.mem_grading_iff`). `𝔪ⁿ = span (range x)ⁿ = span ((range x)^n)`
   (`Submodule.span_pow`), whose elements are `A`-linear combinations of products of `n` of the `xᵢ`,
   i.e. `a = G(x)` with `G` homogeneous of degree `n`; thus `p = φ(G)` and `fR p = ψ(G)` is homogeneous
   of degree `n` in `κ[T]` (`MvPolynomial.IsHomogeneous.map`). So `f := ⟨fR.toRingHom, map_mem⟩`.
7. **Irrelevant-ideal condition `hf`**: for `b ∈ κ[T]₊`, each positive-degree homogeneous component
   `bₙ = ψ(Gₙ)` with `Gₙ` a coefficient lift of `bₙ` (still homogeneous of degree `n`),
   `φ(Gₙ) ∈ (Rees)ₙ ⊆ (Rees)₊` and `f(φ Gₙ) = bₙ`; summing, `b ∈ (Rees)₊.map f`
   (`HomogeneousIdeal.irrelevant_le` + `Ideal.mem_map_of_mem`).
8. **`IsBaseChange`**: show that `κ ⊗_A Rees → κ[T]` (the `κ`-linear extension of `TensorProduct.lift`,
   i.e. `IsBaseChange.lift`) is bijective:
   - surjective: `fR` is surjective (`fR ∘ φ = ψ` is surjective);
   - injective: `TensorProduct.quotTensorEquivQuotSMul` gives `κ ⊗_A Rees ≃ Rees ⧸ (𝔪 • ⊤)` (`κ = A ⧸ 𝔪`
     definitionally), and the induced map `Rees/𝔪Rees → κ[T]` is injective iff
     `ker fR = 𝔪 • ⊤ = 𝔪.map (algebraMap A Rees)`; from `fR ∘ φ = ψ` and surjectivity of `φ`:
     `ker fR = φ(ker ψ) = φ(Ideal.map C 𝔪) = Ideal.map (φ.comp C) 𝔪 = Ideal.map (algebraMap A Rees) 𝔪`
     (`Ideal.map_map`, `φ ∘ C = algebraMap`).

Edge cases: `d = 0` (`A` is a field, `𝔪 = 0`, `Rees = A`, `κ[T] = κ`, `fR = algebraMap`, `IsBaseChange`
trivially); `d = 1, 2` same proof; `κ` is a field by `IsLocalRing.ResidueField.field`; `Algebra A κ[T]`
and `IsScalarTower A κ κ[T]` are the standard `MvPolynomial` instances.

**Formalized route**: steps 1–6 as above (step 6 via Mathlib's
`Ideal.mem_span_pow_iff_exists_isHomogeneous`, step 4 via the coefficient formula
`ReesResidueBaseChange.coeff_aeval_monomial_one`); step 7 replaced by the general fact that a
*surjective* graded ring hom satisfies the irrelevant-ideal condition
(`HomogeneousIdeal.irrelevant_le_map_of_surjective`); step 8 done by hand instead of through
`quotTensorEquivQuotSMul`: every tensor in `κ ⊗_A Rees` is `1 ⊗ p`, and `1 ⊗ p = 0` whenever `fR p = 0`
(`ReesResidueBaseChange.one_tmul_eq_zero_of_residueRees_eq_zero`). -/
theorem IsRegularLocalRing.exists_reesGrading_maximalIdeal_baseChange_residueField (A : Type u)
    [CommRing A] [IsRegularLocalRing A] (d : ℕ) (hdim : ringKrullDim A = d) :
    ∃ (f : Ideal.reesGrading (IsLocalRing.maximalIdeal A) →+*ᵍ
          MvPolynomial.homogeneousSubmodule (Fin d) (IsLocalRing.ResidueField A))
      (_hf : (MvPolynomial.homogeneousSubmodule (Fin d) (IsLocalRing.ResidueField A))₊ ≤
          (Ideal.reesGrading (IsLocalRing.maximalIdeal A))₊.map f)
      (fR : reesAlgebra (IsLocalRing.maximalIdeal A) →ₐ[A]
          MvPolynomial (Fin d) (IsLocalRing.ResidueField A)),
      (∀ a, fR a = f a) ∧ IsBaseChange (IsLocalRing.ResidueField A) fR.toLinearMap := by
  obtain ⟨x, hx, hspan, h3⟩ := IsRegularLocalRing.initialForms_algebraicallyIndependent A d hdim
  exact ⟨ReesResidueBaseChange.residueReesGraded x hx hspan h3,
    HomogeneousIdeal.irrelevant_le_map_of_surjective _
      (ReesResidueBaseChange.residueRees_surjective x hx hspan h3),
    ReesResidueBaseChange.residueRees x hx hspan h3, fun _ => rfl,
    ReesResidueBaseChange.residueRees_isBaseChange x hx hspan h3⟩

end
