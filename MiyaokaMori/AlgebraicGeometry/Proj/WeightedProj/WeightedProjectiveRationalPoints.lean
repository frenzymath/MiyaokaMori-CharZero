import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveBundle.ProjectiveBundleUniversalProperty
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjQC
import MiyaokaMori.AlgebraicGeometry.Morphisms.SchemeOverBase
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedGradedAlgebra
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveTupleFrameChange

/-! # Rational points of weighted projective space

The `K`-points of the weighted projective space `P_k(w)` (morphisms `Spec K → P(w)` over `k`,
`KPoint`) and their base change along field extensions; a nonzero tuple `v` gives a `K`-point via
the universal property of `Proj` for global sections (`pointOfTuple` / `kPointOfTuple`), well
defined modulo weighted scaling `(v_i) ~ (c^{w_i} v_i)` (`rationalPointToPoint`). This map is in
general not injective (at points with nontrivial stabilizer, different classes give the same
`K`-point); the reverse direction "`K`-point ↦ class of tuples" is not provided.

This is the "weighted projective point over `k(C̃_0)`" in the proof of the affine lift after finite
base change (Lemma 3.1) of the paper. Reference: Dolgachev, *Weighted projective
varieties*, §1.2.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

private theorem eval₂Hom_weighted_scale {k K : Type u} [CommSemiring k] [CommSemiring K]
    {σ : Type v} (c : k →+* K) (w : σ → ℕ) (p : σ → K) (a : Kˣ)
    {F : MvPolynomial σ k} {d : ℕ} (hF : F.IsWeightedHomogeneous w d) :
    MvPolynomial.eval₂Hom c (fun i ↦ (a : K) ^ w i * p i) F =
      (a : K) ^ d * MvPolynomial.eval₂Hom c p F := by
  induction hF using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add F G hF hG ihF ihG => simp only [map_add, ihF, ihG, mul_add]
  | monomial m b hm =>
    rw [MvPolynomial.eval₂Hom_monomial]
    have hdegree : (∑ i ∈ m.support, m i * w i) = d := by
      simpa [Finsupp.weight_apply, Finsupp.sum, smul_eq_mul] using hm
    have hprod : (∏ i ∈ m.support, ((a : K) ^ w i) ^ m i) = (a : K) ^ d := by
      calc
        (∏ i ∈ m.support, ((a : K) ^ w i) ^ m i) =
            ∏ i ∈ m.support, (a : K) ^ (w i * m i) := by
          apply Finset.prod_congr rfl
          intro i hi
          rw [← pow_mul]
        _ = (a : K) ^ (∑ i ∈ m.support, w i * m i) :=
          Finset.prod_pow_eq_pow_sum _ _ _
        _ = (a : K) ^ d := by rw [show (∑ i ∈ m.support, w i * m i) = d by
          simpa [mul_comm] using hdegree]
    simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib]
    rw [hprod]
    simp only [MvPolynomial.eval₂Hom_monomial, Finsupp.prod]
    ac_rfl

/- The `K`-points of `P(w)` are the morphisms `Spec K ⟶ P(w)` over `k` (`KPoint`). A nonzero tuple
   gives a `K`-point (`pointOfTuple`, the universal property of `Proj` for global sections), well
   defined modulo weighted scaling (`rationalPointToPoint`). The reverse direction "`K`-point ↦ class
   of tuples" is not provided: it is not canonical in general (not injective at points with
   nontrivial stabilizer), and the paper does not need it — it passes directly to a finite extension
   via `[u] ↦ [u^q]` and states the conclusion as an equality of `pointOfTuple`s. -/

/-- The weighted scaling relation on nonzero tuples: `v ~ v'` iff `v'_i = c^{w_i} v_i` for a unit `c`. -/
def weightedProjectiveSpace.scalingSetoid (K : Type u) [Field K] {σ : Type u} (w : σ → ℕ) :
    Setoid {v : σ → K // v ≠ 0} where
  r v v' := ∃ c : Kˣ, ∀ i, (v' : σ → K) i = (c : K) ^ w i * (v : σ → K) i
  iseqv := ⟨fun v => ⟨1, by simp⟩, fun ⟨c, h⟩ => ⟨c⁻¹, by intro i; simp [h]⟩,
    fun ⟨c, h⟩ ⟨c', h'⟩ => ⟨c' * c, by intro i; simp [h, h', mul_pow, mul_assoc]⟩⟩

/-- Nonzero tuples modulo weighted scaling. -/
def weightedProjectiveSpace.RationalPoint (K : Type u) [Field K] {σ : Type u} (w : σ → ℕ)
    (hw : ∀ i, 0 < w i) : Type u :=
  Quotient (weightedProjectiveSpace.scalingSetoid K w)

/-- The `K`-points of `P(w)`: morphisms `Spec K ⟶ P_k(w)` over `k` (the `k`-algebra structure of `K`
gives `Spec K → Spec k`). -/

def weightedProjectiveSpace.KPoint (k : Type u) [Field k] {σ : Type u} (w : σ → ℕ)
    (hw : ∀ i, 0 < w i) (K : Type u) [Field K] [Algebra k K] : Type u :=
  { x : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ weightedProjectiveSpace k w hw //
      x ≫ (weightedProjectiveSpace k w hw ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
        = AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k K)) }

/-- Base change of a `K`-point along a field extension `K → K'`: composition with
`Spec K' → Spec K`. -/

def weightedProjectiveSpace.KPoint.baseChange {k : Type u} [Field k] {σ : Type u} {w : σ → ℕ}
    {hw : ∀ i, 0 < w i} {K : Type u} [Field K] [Algebra k K]
    (x : weightedProjectiveSpace.KPoint k w hw K) (K' : Type u) [Field K'] [Algebra k K']
    [Algebra K K'] [IsScalarTower k K K'] : weightedProjectiveSpace.KPoint k w hw K' :=
  ⟨AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap K K')) ≫ x.1, by
    rw [CategoryTheory.Category.assoc, x.2, ← AlgebraicGeometry.Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← IsScalarTower.algebraMap_eq]⟩

/- The `K`-point of a tuple `v`: the ring map `k[x] → K`, `x_i ↦ v_i` (`aeval v`), sends the
   irrelevant ideal to the unit ideal (`v ≠ 0` and all weights positive), so Mathlib's
   `Proj.fromOfGlobalSections` gives `Spec K → Proj k[x]^{(w)}`. -/

/-- The irrelevant ideal `(x_i)` generates the unit ideal under `aeval v`: some `v_i ≠ 0`, and `x_i`
has positive weight (so it lies in the irrelevant ideal), hence the image contains the unit `v_i`. -/
theorem weightedProjectiveSpace.map_irrelevant_eq_top (k : Type u) [Field k] {σ : Type u}
    (w : σ → ℕ) (hw : ∀ i, 0 < w i) (K : Type u) [Field K] [Algebra k K] (v : {v : σ → K // v ≠ 0}) :
    letI := MvPolynomial.weightedGradedAlgebra (R := k) w
    Ideal.map
        ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom.comp
          (MvPolynomial.aeval (v : σ → K)).toRingHom)
        (HomogeneousIdeal.irrelevant (MvPolynomial.weightedHomogeneousSubmodule k w)).toIdeal = ⊤ := by
  classical
  dsimp
  letI := MvPolynomial.weightedGradedAlgebra (R := k) w
  obtain ⟨i, hi⟩ : ∃ i, (v : σ → K) i ≠ 0 := by
    by_contra h
    apply v.property
    funext i
    exact not_ne_iff.mp (fun hi' ↦ h ⟨i, hi'⟩)
  let s : K →+* _ :=
    (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  have hmem0 : MvPolynomial.X i ∈
      HomogeneousIdeal.irrelevant (MvPolynomial.weightedHomogeneousSubmodule k w) :=
    HomogeneousIdeal.mem_irrelevant_of_mem (MvPolynomial.weightedHomogeneousSubmodule k w)
      (hw i) (by
        rw [MvPolynomial.mem_weightedHomogeneousSubmodule]
        exact MvPolynomial.isWeightedHomogeneous_X k (fun j ↦ w j) i)
  have hX : MvPolynomial.X i ∈
      (HomogeneousIdeal.irrelevant (MvPolynomial.weightedHomogeneousSubmodule k w)).toIdeal := hmem0
  refine Ideal.eq_top_of_isUnit_mem _
    (Ideal.mem_map_of_mem
      ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom.comp
        (MvPolynomial.aeval (v : σ → K)).toRingHom) hX) ?_
  change IsUnit (s ((MvPolynomial.aeval (v : σ → K)) (MvPolynomial.X i)))
  rw [MvPolynomial.aeval_X]
  exact (isUnit_iff_ne_zero.mpr hi).map s

/-- The `K`-point `Spec K ⟶ P_k(w)` of a nonzero tuple `v`. -/
noncomputable def weightedProjectiveSpace.pointOfTuple (k : Type u) [Field k] {σ : Type u}
    (w : σ → ℕ) (hw : ∀ i, 0 < w i) (K : Type u) [Field K] [Algebra k K] (v : {v : σ → K // v ≠ 0}) :
    AlgebraicGeometry.Spec (CommRingCat.of K) ⟶ weightedProjectiveSpace k w hw :=
  letI := MvPolynomial.weightedGradedAlgebra (R := k) w
  AlgebraicGeometry.Proj.fromOfGlobalSections (MvPolynomial.weightedHomogeneousSubmodule k w)
    ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom.comp
      (MvPolynomial.aeval (v : σ → K)).toRingHom)
    (weightedProjectiveSpace.map_irrelevant_eq_top k w hw K v)

/-- `aeval v` is a `k`-algebra homomorphism, so `pointOfTuple` is a morphism over `k`. -/

theorem weightedProjectiveSpace.pointOfTuple_over (k : Type u) [Field k] {σ : Type u}
    (w : σ → ℕ) (hw : ∀ i, 0 < w i) (K : Type u) [Field K] [Algebra k K] (v : {v : σ → K // v ≠ 0}) :
      weightedProjectiveSpace.pointOfTuple k w hw K v ≫
        (weightedProjectiveSpace k w hw ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
      = AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap k K)) := by
  letI : GradedRing (MvPolynomial.weightedHomogeneousSubmodule k w) :=
    MvPolynomial.weightedGradedAlgebra (R := k) w
  change AlgebraicGeometry.Proj.fromOfGlobalSections
      (MvPolynomial.weightedHomogeneousSubmodule k w) _ _ ≫
    (AlgebraicGeometry.Proj.toSpecZero (MvPolynomial.weightedHomogeneousSubmodule k w) ≫
      AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom
          (algebraMap k (MvPolynomial.weightedHomogeneousSubmodule k w 0)))) = _
  rw [← Category.assoc, AlgebraicGeometry.Proj.fromOfGlobalSections_toSpecZero,
    Category.assoc, ← AlgebraicGeometry.Spec.map_comp, ← CommRingCat.ofHom_comp]
  have heval :
      (((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom.comp
          (MvPolynomial.aeval (v : σ → K)).toRingHom).comp
            (algebraMap (MvPolynomial.weightedHomogeneousSubmodule k w 0)
              (MvPolynomial σ k))).comp
        (algebraMap k (MvPolynomial.weightedHomogeneousSubmodule k w 0)) =
      (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom.comp
        (algebraMap k K) := by
    ext c
    simp
  rw [heval, CommRingCat.ofHom_comp, AlgebraicGeometry.Spec.map_comp, ← Category.assoc,
    CommRingCat.ofHom_hom, AlgebraicGeometry.toSpecΓ_SpecMap_ΓSpecIso_inv,
    Category.id_comp]

/-- The `K`-point of a nonzero tuple, as an element of `KPoint`. -/

noncomputable def weightedProjectiveSpace.kPointOfTuple (k : Type u) [Field k] {σ : Type u}
    (w : σ → ℕ) (hw : ∀ i, 0 < w i) (K : Type u) [Field K] [Algebra k K] (v : {v : σ → K // v ≠ 0}) :
    weightedProjectiveSpace.KPoint k w hw K :=
  ⟨weightedProjectiveSpace.pointOfTuple k w hw K v, weightedProjectiveSpace.pointOfTuple_over k w hw K v⟩

/- Well defined on the quotient: independent of the representative (a weighted scaling `c`
   multiplies numerator and denominator of a degree-zero fraction `a/x_i^n` by `c^{n w_i}`). The map
   is in general not injective: on `P(1,2)` the tuples `(0,1)` and `(0,2)` give the same `K`-point,
   but are equivalent only when `2` is a square in `K` (stabilizer `μ_2`). -/

/-- Independence of the representative: a weighted scaling `c` multiplies numerator and denominator
of a degree-zero fraction `a/x_i^n` by `c^{n w_i}`. -/
theorem weightedProjectiveSpace.kPointOfTuple_congr (k : Type u) [Field k] {σ : Type u}
    (w : σ → ℕ) (hw : ∀ i, 0 < w i) (K : Type u) [Field K] [Algebra k K]
    (a b : {v : σ → K // v ≠ 0}) (h : (weightedProjectiveSpace.scalingSetoid K w).r a b) :
    weightedProjectiveSpace.kPointOfTuple k w hw K a = weightedProjectiveSpace.kPointOfTuple k w hw K b := by
  obtain ⟨c, hc⟩ := h
  let s : K →+* Γ(AlgebraicGeometry.Spec (CommRingCat.of K), ⊤) :=
    (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  let u : Γ(AlgebraicGeometry.Spec (CommRingCat.of K), ⊤)ˣ := Units.map s.toMonoidHom c
  have hscale : ∀ (d : ℕ) (x : MvPolynomial σ k),
      x ∈ MvPolynomial.weightedHomogeneousSubmodule k w d →
        ((s.comp (MvPolynomial.eval₂Hom (algebraMap k K)
          (b : σ → K))) x) = (u : Γ(AlgebraicGeometry.Spec (CommRingCat.of K), ⊤)) ^ d *
          ((s.comp (MvPolynomial.eval₂Hom (algebraMap k K)
            (a : σ → K))) x) := by
    intro d x hx
    change s (MvPolynomial.eval₂Hom (algebraMap k K) (b : σ → K) x) =
      (u : Γ(AlgebraicGeometry.Spec (CommRingCat.of K), ⊤)) ^ d *
        s (MvPolynomial.eval₂Hom (algebraMap k K) (a : σ → K) x)
    have hba : (b : σ → K) = fun i ↦ (c : K) ^ w i * (a : σ → K) i := by
      exact funext hc
    rw [hba, eval₂Hom_weighted_scale (algebraMap k K) w (a : σ → K) c
      ((MvPolynomial.mem_weightedHomogeneousSubmodule k w d x).mp hx),
      map_mul, map_pow]
    rfl
  letI := MvPolynomial.weightedGradedAlgebra (R := k) w
  have ha : (HomogeneousIdeal.irrelevant (MvPolynomial.weightedHomogeneousSubmodule k w)).toIdeal.map
      (s.comp (MvPolynomial.eval₂Hom (algebraMap k K) (a : σ → K))) = ⊤ := by
    exact weightedProjectiveSpace.map_irrelevant_eq_top k w hw K a
  have hmap := AlgebraicGeometry.Proj.ProjectiveTupleFrameChange.fromOfGlobalSections_unit_scale
    (MvPolynomial.weightedHomogeneousSubmodule k w)
    (s.comp (MvPolynomial.eval₂Hom (algebraMap k K) (a : σ → K)))
    (s.comp (MvPolynomial.eval₂Hom (algebraMap k K) (b : σ → K))) u hscale ha
  unfold weightedProjectiveSpace.kPointOfTuple
  apply Subtype.ext
  unfold weightedProjectiveSpace.pointOfTuple
  exact hmap.symm

noncomputable def weightedProjectiveSpace.rationalPointToPoint (k : Type u) [Field k] {σ : Type u}
    (w : σ → ℕ) (hw : ∀ i, 0 < w i) (K : Type u) [Field K] [Algebra k K] :
    weightedProjectiveSpace.RationalPoint K w hw → weightedProjectiveSpace.KPoint k w hw K :=
  Quotient.lift (weightedProjectiveSpace.kPointOfTuple k w hw K)
    (weightedProjectiveSpace.kPointOfTuple_congr k w hw K)

end
