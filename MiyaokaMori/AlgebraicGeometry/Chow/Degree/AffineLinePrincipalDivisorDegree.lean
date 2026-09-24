import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.OrderOfVanishing.PrimeDivisorLocalEquation
import MiyaokaMori.AlgebraicGeometry.Varieties.FunctionField.ResidueDegreeSpecMapGenericPoint
import Mathlib.AlgebraicGeometry.OrderOfVanishing

/-! # Degree of a principal divisor on the affine line

The order-of-vanishing bookkeeping on the affine line `𝔸¹_K = Spec K[X]` over an arbitrary field `K`,
used for the base case of the Stacks 02RU route to the vanishing of the degree of a principal divisor
on `ℙ¹` (Hartshorne II Prop. 6.4(b) with `n = 1`).

* `polyToFunctionField K : K[X] →+* K(𝔸¹)` is Mathlib's `algebraMap` (spelled out because instance search does
  not see through `CommRingCat.of`); `affineLineOver K : Spec K[X] ⟶ Spec K` is the structure morphism;
  `spanPoint K hp` is the closed point `(p)` for `p` irreducible, `originPoint K = (X)`.
* `ord_polyToFunctionField_eq_zero_of_not_mem`: `ord_q f = 0` if `f ∉ q` (`f` is a unit on `D(f) ∋ q`,
  Mathlib `Scheme.ord_of_isUnit`).
* `ord_polyToFunctionField_spanPoint`: `ord_{(p)} p = 1` for `p` irreducible (`p` generates the maximal ideal
  of the DVR `K[X]_{(p)}`; `coheight (p) = 1` from `height (p) = 1`, Krull's principal ideal theorem).
* `residueDegree_affineLineOver_spanPoint`: `[κ((p)) : K] = deg p` (`κ((p)) = K[X]/(p)`, Mathlib
  `finrank_quotient_span_eq_natDegree`).
* `affineLine_finsum_ord_mul_residueDegree`: `Σ_q ord_q(f)·[κ(q):K] = deg f` for `f ≠ 0`, by induction on the
  prime factorization of `f` (`UniqueFactorizationMonoid.induction_on_prime`), with the finiteness of the support
  (`affineLine_finite_support_ord`).
* `affineLine_ord_originPoint`: `ord_{(X)} (reverse f / X^{deg f}) = -deg f` (this is `ord_∞ f` after the change of
  chart `X ↦ 1/X`); `affineLine_residueDegree_originPoint`: `[κ((X)) : K] = 1`.

Source: Hartshorne, Algebraic Geometry, II Prop. 6.4(b) (n = 1), made explicit on the chart `D₊(x₀) = Spec K[t]`;
the identification "degree of the hypersurface `(π)` = `[κ((π)):K] = deg π`" is Mathlib's `AdjoinRoot.powerBasis`.
Edge cases: `f` constant (unit): all `ord` vanish and `deg f = 0`; `K` finite or not algebraically closed: points are
irreducible polynomials, not roots — nothing here assumes algebraic closure.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open AlgebraicGeometry CategoryTheory

noncomputable section

variable (K : Type u) [Field K]

namespace ProjectiveLine

/-- `K[X] → K(Spec K[X])` (Mathlib's `algebraMap`, spelled out because instance search does not see
through `CommRingCat.of`). -/
def polyToFunctionField : Polynomial K →+* (Spec (CommRingCat.of (Polynomial K))).functionField :=
  @algebraMap _ _ _ _ (AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (CommRingCat.of (Polynomial K)))

/-- the structure morphism `Spec K[X] → Spec K` -/
def affineLineOver : Spec (CommRingCat.of (Polynomial K)) ⟶ Spec (CommRingCat.of K) :=
  Spec.map (CommRingCat.ofHom (algebraMap K (Polynomial K)))

/-- the closed point `(p)` of `Spec K[X]` cut out by an irreducible polynomial -/
def spanPoint {p : Polynomial K} (hp : Irreducible p) : Spec (CommRingCat.of (Polynomial K)) :=
  ⟨Ideal.span {p}, (Ideal.span_singleton_prime hp.ne_zero).mpr hp.prime⟩

/-- the point `X = 0` of `Spec K[X]` -/
def originPoint : Spec (CommRingCat.of (Polynomial K)) := spanPoint K Polynomial.irreducible_X

theorem polyToFunctionField_injective : Function.Injective (polyToFunctionField K) := by
  let _ := AlgebraicGeometry.instAlgebraCarrierFunctionFieldSpec (CommRingCat.of (Polynomial K))
  have _ := AlgebraicGeometry.functionField_isFractionRing_of_affine (CommRingCat.of (Polynomial K))
  exact IsFractionRing.injective (CommRingCat.of (Polynomial K))
    (Spec (CommRingCat.of (Polynomial K))).functionField

theorem polyToFunctionField_eq_germ (f : Polynomial K) :
    polyToFunctionField K f =
      (Spec (CommRingCat.of (Polynomial K))).presheaf.germ ⊤ (genericPoint _) trivial
        ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial K))).inv f) := rfl

/-- `ord_q f = 0` when `f ∉ q` (`f` is a unit on the basic open `D(f) ∋ q`). -/
theorem ord_polyToFunctionField_eq_zero_of_not_mem (q : Spec (CommRingCat.of (Polynomial K)))
    {f : Polynomial K} (hf : f ∉ q.asIdeal) :
    (Spec (CommRingCat.of (Polynomial K))).ord (polyToFunctionField K f) q = 0 := by
  have hq : q ∈ (Spec (CommRingCat.of (Polynomial K))).basicOpen
      ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial K))).inv f) := by
    rw [basicOpen_eq_of_affine]
    exact hf
  have : Nonempty ((Spec (CommRingCat.of (Polynomial K))).basicOpen
      ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial K))).inv f)) := ⟨⟨q, hq⟩⟩
  have hres : polyToFunctionField K f =
      (Spec (CommRingCat.of (Polynomial K))).germToFunctionField
        ((Spec (CommRingCat.of (Polynomial K))).basicOpen
          ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial K))).inv f))
        ((Spec (CommRingCat.of (Polynomial K))).presheaf.map (homOfLE le_top).op
          ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial K))).inv f)) := by
    rw [polyToFunctionField_eq_germ]
    exact ((Spec (CommRingCat.of (Polynomial K))).presheaf.germ_res_apply (homOfLE le_top)
      (genericPoint _) _ _).symm
  rw [hres]
  exact Scheme.ord_of_isUnit (U := (Spec (CommRingCat.of (Polynomial K))).basicOpen
      ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial K))).inv f))
    (RingedSpace.isUnit_res_basicOpen (Spec (CommRingCat.of (Polynomial K))).toRingedSpace _) hq

/-- the height of `(p)` in `K[X]` is `1` for `p` irreducible -/
theorem height_span_singleton_eq_one {p : Polynomial K} (hp : Irreducible p) :
    (Ideal.span {p}).height = 1 := by
  have : (Ideal.span {p}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).mpr hp.prime
  have hle : (Ideal.span {p}).height ≤ 1 :=
    Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes (Ideal.span {p}) (Ideal.span {p})
      (by rw [Ideal.minimalPrimes_eq_subsingleton_self]; rfl)
  have hne : (Ideal.span {p}).height ≠ 0 := by
    rw [Ne, Ideal.height_eq_zero_iff_eq_bot, Ideal.span_singleton_eq_bot]
    exact hp.ne_zero
  exact le_antisymm hle (Order.one_le_iff_ne_zero.mpr hne)

theorem coheight_spanPoint {p : Polynomial K} (hp : Irreducible p) :
    Order.coheight (spanPoint K hp) = 1 := by
  rw [← idealHeight_eq_coheight]
  exact height_span_singleton_eq_one K hp

/-- `ord_{(p)} p = 1` for `p` irreducible: `p` generates the maximal ideal of the DVR `K[X]_{(p)}`. -/
theorem ord_polyToFunctionField_spanPoint {p : Polynomial K} (hp : Irreducible p) :
    (Spec (CommRingCat.of (Polynomial K))).ord (polyToFunctionField K p) (spanPoint K hp) = 1 := by
  have : Nonempty ((⊤ : (Spec (CommRingCat.of (Polynomial K))).Opens)) := ⟨⟨spanPoint K hp, trivial⟩⟩
  have : (spanPoint K hp).asIdeal.IsPrime := (spanPoint K hp).isPrime
  let _ : Algebra (Polynomial K) ((Spec (CommRingCat.of (Polynomial K))).presheaf.stalk (spanPoint K hp)) :=
    StructureSheaf.stalkAlgebra (Polynomial K) (spanPoint K hp)
  have : IsLocalization.AtPrime
      ((Spec (CommRingCat.of (Polynomial K))).presheaf.stalk (spanPoint K hp)) (spanPoint K hp).asIdeal :=
    StructureSheaf.IsLocalization.to_stalk (Polynomial K) (spanPoint K hp)
  have : IsDiscreteValuationRing
      ((Spec (CommRingCat.of (Polynomial K))).presheaf.stalk (spanPoint K hp)) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (Polynomial K)
      (P := (spanPoint K hp).asIdeal) (by
        show Ideal.span {p} ≠ ⊥
        rw [Ne, Ideal.span_singleton_eq_bot]; exact hp.ne_zero) _
  have hgen : Ideal.span {(Spec (CommRingCat.of (Polynomial K))).presheaf.germ ⊤ (spanPoint K hp) trivial
      ((Scheme.ΓSpecIso (CommRingCat.of (Polynomial K))).inv p)} =
      IsLocalRing.maximalIdeal ((Spec (CommRingCat.of (Polynomial K))).presheaf.stalk (spanPoint K hp)) := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (spanPoint K hp).asIdeal]
    show Ideal.span {algebraMap (Polynomial K) _ p} = Ideal.map (algebraMap (Polynomial K) _) (Ideal.span {p})
    rw [Ideal.map_span, Set.image_singleton]
  exact Scheme.ord_germToFunctionField_eq_one_of_span_germ_eq_maximalIdeal (V := ⊤) trivial
    (coheight_spanPoint K hp) _ hgen

/-- `[κ((p)) : K] = deg p` for `p` irreducible (`κ((p)) = K[X]/(p)`, basis `1, X, …, X^{deg p - 1}`). -/
theorem residueDegree_affineLineOver_spanPoint {p : Polynomial K} (hp : Irreducible p) :
    (affineLineOver K).residueDegree (spanPoint K hp) = p.natDegree := by
  have hq : (spanPoint K hp).asIdeal.IsPrime := (spanPoint K hp).isPrime
  have hmax : (Ideal.span {p}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp
  rw [affineLineOver, Scheme.Hom.residueDegree_specMap]
  have hJ : ((Spec.map (CommRingCat.ofHom (algebraMap K (Polynomial K)))) (spanPoint K hp)).asIdeal.IsPrime :=
    ((Spec.map (CommRingCat.ofHom (algebraMap K (Polynomial K)))) (spanPoint K hp)).isPrime
  let _ : Algebra ((Spec.map (CommRingCat.ofHom (algebraMap K (Polynomial K)))) (spanPoint K hp)).asIdeal.ResidueField
      (spanPoint K hp).asIdeal.ResidueField :=
    (Ideal.ResidueField.map _ _ (CommRingCat.ofHom (algebraMap K (Polynomial K))).hom rfl).toAlgebra
  change Module.finrank ((Spec.map (CommRingCat.ofHom (algebraMap K (Polynomial K)))) (spanPoint K hp)).asIdeal.ResidueField
    (spanPoint K hp).asIdeal.ResidueField = p.natDegree
  let i : ((Spec.map (CommRingCat.ofHom (algebraMap K (Polynomial K)))) (spanPoint K hp)).asIdeal.ResidueField ≃+* K :=
    (Ideal.algEquivResidueFieldOfField _).symm.toRingEquiv
  let j : (spanPoint K hp).asIdeal.ResidueField ≃+* (Polynomial K ⧸ Ideal.span {p}) :=
    (RingEquiv.ofBijective (algebraMap (Polynomial K ⧸ Ideal.span {p}) (Ideal.span {p}).ResidueField)
      (Ideal.bijective_algebraMap_quotient_residueField _)).symm
  rw [Algebra.finrank_eq_of_equiv_equiv i j ?_]
  · exact finrank_quotient_span_eq_natDegree
  · ext c
    simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom]
    have hi : i (algebraMap K _ c) = c :=
      AlgEquiv.symm_apply_apply (Ideal.algEquivResidueFieldOfField _) c
    rw [hi]
    have h2 : algebraMap _ (spanPoint K hp).asIdeal.ResidueField (algebraMap K
        ((Spec.map (CommRingCat.ofHom (algebraMap K (Polynomial K)))) (spanPoint K hp)).asIdeal.ResidueField c) =
        algebraMap (Polynomial K) (Ideal.span {p}).ResidueField (algebraMap K (Polynomial K) c) :=
      Ideal.ResidueField.map_algebraMap _ _ _ rfl c
    rw [h2, ← Ideal.algebraMap_quotient_residueField_mk]
    exact (RingEquiv.symm_apply_apply (RingEquiv.ofBijective
      (algebraMap (Polynomial K ⧸ Ideal.span {p}) (Ideal.span {p}).ResidueField)
      (Ideal.bijective_algebraMap_quotient_residueField _))
      (Ideal.Quotient.mk _ (algebraMap K (Polynomial K) c))).symm

theorem affineLine_residueDegree_originPoint :
    (affineLineOver K).residueDegree (originPoint K) = 1 := by
  rw [originPoint, residueDegree_affineLineOver_spanPoint, Polynomial.natDegree_X]

theorem ord_polyToFunctionField_of_ne_spanPoint {p : Polynomial K} (hp : Irreducible p)
    (q : Spec (CommRingCat.of (Polynomial K))) (hq : q ≠ spanPoint K hp) :
    (Spec (CommRingCat.of (Polynomial K))).ord (polyToFunctionField K p) q = 0 := by
  apply ord_polyToFunctionField_eq_zero_of_not_mem
  intro hpq
  apply hq
  have hle : Ideal.span {p} ≤ q.asIdeal := (Ideal.span_singleton_le_iff_mem _).mpr hpq
  have hmax : (Ideal.span {p}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp
  exact PrimeSpectrum.ext (hmax.eq_of_le q.isPrime.ne_top hle).symm

theorem polyToFunctionField_ne_zero {f : Polynomial K} (hf : f ≠ 0) : polyToFunctionField K f ≠ 0 :=
  (map_ne_zero_iff _ (polyToFunctionField_injective K)).mpr hf

theorem ord_pow_eq {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] {g : X.functionField}
    (hg : g ≠ 0) (n : ℕ) (x : X) : X.ord (g ^ n) x = n * X.ord g x := by
  induction n with
  | zero => simp [Scheme.ord_one_eq_zero]
  | succ n ih =>
    rw [pow_succ, Scheme.ord_mul (pow_ne_zero _ hg) hg, ih]
    push_cast
    ring

theorem affineLine_ord_originPoint (f : Polynomial K) (hf : f ≠ 0) :
    (Spec (CommRingCat.of (Polynomial K))).ord
        (polyToFunctionField K f.reverse / polyToFunctionField K Polynomial.X ^ f.natDegree)
        (originPoint K) = -(f.natDegree : ℤ) := by
  have h1 : polyToFunctionField K f.reverse ≠ 0 :=
    polyToFunctionField_ne_zero K (Polynomial.reverse_eq_zero.not.mpr hf)
  have h2 : polyToFunctionField K (Polynomial.X : Polynomial K) ≠ 0 :=
    polyToFunctionField_ne_zero K Polynomial.X_ne_zero
  rw [Scheme.ord_div_eq_sub h1 (pow_ne_zero _ h2), ord_pow_eq h2, originPoint,
    ord_polyToFunctionField_spanPoint K Polynomial.irreducible_X,
    ord_polyToFunctionField_eq_zero_of_not_mem]
  · ring
  · show f.reverse ∉ Ideal.span {Polynomial.X}
    rw [Ideal.mem_span_singleton, Polynomial.X_dvd_iff, Polynomial.coeff_zero_reverse]
    exact Polynomial.leadingCoeff_ne_zero.mpr hf

/-- finiteness of the support and the degree formula `Σ_q ord_q(f)·[κ(q):K] = deg f`, by
induction on the prime factorization of `f`. -/
theorem affineLine_finite_support_and_finsum (f : Polynomial K) (hf : f ≠ 0) :
    (Function.support fun q : Spec (CommRingCat.of (Polynomial K)) =>
      (Spec (CommRingCat.of (Polynomial K))).ord (polyToFunctionField K f) q).Finite ∧
    ∑ᶠ q : Spec (CommRingCat.of (Polynomial K)),
      (Spec (CommRingCat.of (Polynomial K))).ord (polyToFunctionField K f) q *
        ((affineLineOver K).residueDegree q : ℤ) = f.natDegree := by
  induction f using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd rfl hf
  | h₂ u hu =>
    have h0 : ∀ q : Spec (CommRingCat.of (Polynomial K)),
        (Spec (CommRingCat.of (Polynomial K))).ord (polyToFunctionField K u) q = 0 := fun q =>
      ord_polyToFunctionField_eq_zero_of_not_mem K q
        (fun h => q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h hu))
    refine ⟨?_, ?_⟩
    · simp [h0]
    · simp [h0, Polynomial.natDegree_eq_zero_of_isUnit hu]
  | h₃ a p ha hp ih =>
    have hp' : Irreducible p := hp.irreducible
    obtain ⟨hfin, hsum⟩ := ih ha
    have hpa : ∀ q : Spec (CommRingCat.of (Polynomial K)),
        (Spec (CommRingCat.of (Polynomial K))).ord (polyToFunctionField K (p * a)) q =
          (Spec (CommRingCat.of (Polynomial K))).ord (polyToFunctionField K p) q +
            (Spec (CommRingCat.of (Polynomial K))).ord (polyToFunctionField K a) q := by
      intro q
      rw [map_mul, Scheme.ord_mul (polyToFunctionField_ne_zero K hp'.ne_zero)
        (polyToFunctionField_ne_zero K ha)]
    have hfinp : (Function.support fun q : Spec (CommRingCat.of (Polynomial K)) =>
        (Spec (CommRingCat.of (Polynomial K))).ord (polyToFunctionField K p) q).Finite := by
      refine (Set.finite_singleton (spanPoint K hp')).subset ?_
      intro q hq
      by_contra h
      exact hq (ord_polyToFunctionField_of_ne_spanPoint K hp' q h)
    refine ⟨?_, ?_⟩
    · refine (hfinp.union hfin).subset ?_
      intro q hq
      rw [Function.mem_support, hpa] at hq
      by_contra h
      simp only [Set.mem_union, Function.mem_support, not_or, not_not] at h
      exact hq (by rw [h.1, h.2, add_zero])
    · have hfinp' : (Function.support fun q : Spec (CommRingCat.of (Polynomial K)) =>
          (Spec (CommRingCat.of (Polynomial K))).ord (polyToFunctionField K p) q *
            ((affineLineOver K).residueDegree q : ℤ)).Finite :=
        hfinp.subset (Function.support_mul_subset_left _ _)
      have hfin' : (Function.support fun q : Spec (CommRingCat.of (Polynomial K)) =>
          (Spec (CommRingCat.of (Polynomial K))).ord (polyToFunctionField K a) q *
            ((affineLineOver K).residueDegree q : ℤ)).Finite :=
        hfin.subset (Function.support_mul_subset_left _ _)
      rw [finsum_congr (fun q => by rw [hpa q, add_mul]), finsum_add_distrib hfinp' hfin', hsum,
        finsum_eq_single _ (spanPoint K hp')
          (fun q hq => by rw [ord_polyToFunctionField_of_ne_spanPoint K hp' q hq, zero_mul]),
        ord_polyToFunctionField_spanPoint, residueDegree_affineLineOver_spanPoint,
        Polynomial.natDegree_mul hp'.ne_zero ha]
      push_cast
      ring

theorem affineLine_finite_support_ord (f : Polynomial K) (hf : f ≠ 0) :
    (Function.support fun q : Spec (CommRingCat.of (Polynomial K)) =>
      (Spec (CommRingCat.of (Polynomial K))).ord (polyToFunctionField K f) q).Finite :=
  (affineLine_finite_support_and_finsum K f hf).1

theorem affineLine_finsum_ord_mul_residueDegree (f : Polynomial K) (hf : f ≠ 0) :
    ∑ᶠ q : Spec (CommRingCat.of (Polynomial K)),
      (Spec (CommRingCat.of (Polynomial K))).ord (polyToFunctionField K f) q *
        ((affineLineOver K).residueDegree q : ℤ) = f.natDegree :=
  (affineLine_finite_support_and_finsum K f hf).2

end ProjectiveLine

end
