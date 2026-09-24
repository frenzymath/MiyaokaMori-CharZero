import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedProjectiveRationalPoints
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedToOrdinaryProj

/-! # Affine lift of a generic weighted point

The affine lift of a general weighted point: for a `K`-point `x` of `P_k(w)`, take a closed point in the fibre of
the finite surjection `[u] ↦ [u^q]` over `x`, pass to the finite residue field extension `K'`, represent it by a
nonzero ordinary projective tuple `a`, and raise each coordinate to its weight: the `K'`-point given by the tuple
`(a_i^{w_i})` is the base change of `x` to `K'` (§3 of the paper).

## Proof (the "fibre point" is taken algebraically)

Write `𝒜 = k[x]` with weights `w`, `ℬ = k[u]` with weights `1`, `ψ : 𝒜 → ℬ`, `x_j ↦ u_j^{w_j}`
(`weightedPowerGradedHom`), `A_i = 𝒜_(x_i)`, `B_i = ℬ_(u_i^{w_i})` the degree-`0` chart rings and
`wp = weightedPowerAwayMap : A_i → B_i` (finite, injective; `Spec wp` is surjective).

1. The unique point of `Spec K` lands in some chart `D₊(x_i)` (`iSup_basicOpen_eq_top`), so
   `x = Spec φ ≫ awayι 𝒜 x_i` for a ring map `φ : A_i → K` (`IsOpenImmersion.lift`, `Spec.preimage`);
   `x` being a `k`-morphism means `φ ∘ (k → A_i) = algebraMap k K`.
2. The scheme-theoretic fibre of `Spec wp` over `Spec φ` is `Spec (K ⊗[A_i] B_i)` (`pullbackSpecIso`);
   it is nonempty because surjectivity is stable under base change, so `R := K ⊗[A_i] B_i ≠ 0`, and
   `R` is a finite `K`-module (`Module.Finite.base_change`). Take a maximal ideal `m` of `R` and
   `K' := R ⧸ m`: a field, finite over `K`, with `ψ' : B_i → K'` satisfying `ψ' ∘ wp = (K → K') ∘ φ`
   (this is the residue field of a closed point of the fibre `P^N ×_{P(w)} Spec K`).
3. The coordinates `a_j := ψ' (u_j u_i^{w_i-1} / u_i^{w_i}) ∈ K'` (so `a_i = 1`, `a ≠ 0`). Every
   `g / (u_i^{w_i})^n ∈ B_i` (`g` of degree `n w_i`) equals `g(r)` for the ratio elements
   `r_j = u_j u_i^{w_i-1} / u_i^{w_i}` (`SpecMap_chartEval_awayι`'s helper `hcore`: checked in
   `k[u]_(u_i^{w_i})` after multiplying by the unit `u_i^{n w_i}`, using that `g` is homogeneous).
   Hence `ψ' ∘ wp` sends `f / x_i^n` to `f(a^w)` (`c := a^w`, `c_i = 1`), i.e. `ψ' ∘ wp` is the
   "evaluation at `c`" chart map `chartEval (aeval c) i`.
4. `Spec (chartEval (aeval c)) ≫ awayι 𝒜 x_i = pointOfTuple k w hw K' c` (`SpecMap_chartEval_awayι`,
   the weighted version of `ProjectiveSpaceOverChart.chartMap_ι`: unfold Mathlib's
   `fromOfGlobalSections` on the chart `D(e x_i) = Spec K'`). Therefore
   `pointOfTuple k w hw K' (a^w) = Spec (ψ' ∘ wp) ≫ awayι = Spec ((K → K') ∘ φ) ≫ awayι
    = Spec (K → K') ≫ x = (x.baseChange K').1`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
-- `letI` (not `let`) is needed: it inlines the graded-ring instance so that terms match the
-- statements syntactically (a `let`-bound instance fvar breaks `rw`).
set_option linter.style.haveILetI false

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry TensorProduct

noncomputable section

namespace AffineLiftGenericPoint

open MvPolynomial WeightedToOrdinaryProj

variable (k : Type u) [Field k] {σ : Type u} (w : σ → ℕ)

/-- Weighted scaling of an evaluation: for `F` weighted homogeneous of degree `d`,
`F (a^{w_i} p_i) = a^d F (p)` (copy of the private lemma of `WeightedProjectiveRationalPoints`). -/
theorem eval₂Hom_weighted_scale {R : Type v} [CommRing R] (c : k →+* R) (p : σ → R) (a : Rˣ)
    {F : MvPolynomial σ k} {d : ℕ} (hF : F.IsWeightedHomogeneous w d) :
    MvPolynomial.eval₂Hom c (fun i ↦ (a : R) ^ w i * p i) F =
      (a : R) ^ d * MvPolynomial.eval₂Hom c p F := by
  induction hF using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add F G hF hG ihF ihG => simp only [map_add, ihF, ihG, mul_add]
  | monomial m b hm =>
    rw [MvPolynomial.eval₂Hom_monomial]
    have hdegree : (∑ i ∈ m.support, m i * w i) = d := by
      simpa [Finsupp.weight_apply, Finsupp.sum, smul_eq_mul] using hm
    have hprod : (∏ i ∈ m.support, ((a : R) ^ w i) ^ m i) = (a : R) ^ d := by
      calc
        (∏ i ∈ m.support, ((a : R) ^ w i) ^ m i) =
            ∏ i ∈ m.support, (a : R) ^ (w i * m i) := by
          apply Finset.prod_congr rfl
          intro i hi
          rw [← pow_mul]
        _ = (a : R) ^ (∑ i ∈ m.support, w i * m i) :=
          Finset.prod_pow_eq_pow_sum _ _ _
        _ = (a : R) ^ d := by rw [show (∑ i ∈ m.support, w i * m i) = d by
          simpa [mul_comm] using hdegree]
    simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib]
    rw [hprod]
    simp only [MvPolynomial.eval₂Hom_monomial, Finsupp.prod]
    ac_rfl

/-- Unweighted scaling: for `F` homogeneous of degree `d` (all weights `1`),
`F (p_i a) = a^d F (p)`. -/
theorem eval₂Hom_scale_one {R : Type v} [CommRing R] (c : k →+* R) (p : σ → R) (a : Rˣ)
    {F : MvPolynomial σ k} {d : ℕ} (hF : F.IsWeightedHomogeneous (fun _ : σ => 1) d) :
    MvPolynomial.eval₂Hom c (fun i ↦ p i * (a : R)) F =
      (a : R) ^ d * MvPolynomial.eval₂Hom c p F := by
  have h := eval₂Hom_weighted_scale k (fun _ : σ => 1) c p a hF
  simpa only [pow_one, mul_comm] using h

/-- Evaluation of the chart ring `k[x]_(x_i)` (degree-`0` fractions `f / x_i^n`) at a point `e` of the
polynomial ring with `e (x_i)` invertible: `f / x_i^n ↦ e f · e(x_i)^{-n}`
(`IsLocalization.Away.lift` composed with `val`). -/
def chartEval {R : Type u} [CommRing R] (e : MvPolynomial σ k →+* R) (i : σ)
    (hi : IsUnit (e (X i))) :
    letI := MvPolynomial.weightedGradedAlgebra (R := k) w
    HomogeneousLocalization.Away (weightedHomogeneousSubmodule k w) (X i) →+* R :=
  letI := MvPolynomial.weightedGradedAlgebra (R := k) w
  (IsLocalization.Away.lift (S := Localization.Away (X (R := k) i)) (X i) hi).comp
    (algebraMap (HomogeneousLocalization.Away (weightedHomogeneousSubmodule k w) (X i))
      (Localization.Away (X i)))

variable (hw : ∀ i, 0 < w i)

/-- **Chart form of `Proj.fromOfGlobalSections`** (weighted version of
`ProjectiveSpaceOverChart.chartMap_ι`): if `e (x_i)` is a unit on `T`, then the canonical
morphism `T → P(w)` given by `e : k[x] → Γ(T, ⊤)` factors through the chart `D₊(x_i) = Spec k[x]_(x_i)`
as `T → Spec Γ(T, ⊤) → Spec k[x]_(x_i) → P(w)`, the middle map being `Spec` of `chartEval`.

Proof: `fromOfGlobalSections` restricted to `D(e x_i) = T` is `toBasicOpenOfGlobalSections`
(`fromOfGlobalSections_resLE`), which is by definition `T ∣_ D(e x_i) → Spec (Γ(T,⊤)_(e x_i)) →
Spec k[x]_(x_i)`, the last map being `Spec` of `IsLocalization.map e ∘ val`; since `e x_i` is a unit,
`Γ(T,⊤) → Γ(T,⊤)_(e x_i)` is an isomorphism with inverse `lift`, and `lift ∘ map e = Away.lift e`. -/
theorem SpecMap_chartEval_awayι (T : AlgebraicGeometry.Scheme.{u})
    (e : MvPolynomial σ k →+* Γ(T, ⊤))
    (he : letI := MvPolynomial.weightedGradedAlgebra (R := k) w
      (HomogeneousIdeal.irrelevant (weightedHomogeneousSubmodule k w)).toIdeal.map e = ⊤)
    (i : σ) (hi : IsUnit (e (X i))) :
    letI := MvPolynomial.weightedGradedAlgebra (R := k) w
    T.toSpecΓ ≫ AlgebraicGeometry.Spec.map (CommRingCat.ofHom (chartEval k w e i hi)) ≫
        AlgebraicGeometry.Proj.awayι (weightedHomogeneousSubmodule k w) (X i) (X_mem k w i) (hw i) =
      AlgebraicGeometry.Proj.fromOfGlobalSections (weightedHomogeneousSubmodule k w) e he := by
  letI := MvPolynomial.weightedGradedAlgebra (R := k) w
  let t : MvPolynomial σ k := X i
  let x : Γ(T, ⊤) := e t
  let L : (T.basicOpen x).toScheme ⟶ AlgebraicGeometry.Spec (.of (Localization.Away x)) :=
    (T.isoOfEq (T.toSpecΓ_preimage_basicOpen x)).inv ≫
      T.toSpecΓ ∣_ PrimeSpectrum.basicOpen x ≫ (AlgebraicGeometry.basicOpenIsoSpecAway x).hom
  let m : Localization.Away t →+* Localization.Away x :=
    IsLocalization.map (M := Submonoid.powers t) (T := Submonoid.powers x)
      (Localization.Away x) e (by
        intro b hb
        obtain ⟨d, rfl⟩ := hb
        exact ⟨d, (map_pow e t d).symm⟩)
  let l : Localization.Away x →+* Γ(T, ⊤) :=
    IsLocalization.Away.lift x (show IsUnit ((RingHom.id Γ(T, ⊤)) x) from hi)
  let a : Localization.Away t →+* Γ(T, ⊤) := IsLocalization.Away.lift t hi
  have hl : l.comp (algebraMap Γ(T, ⊤) (Localization.Away x)) = RingHom.id _ :=
    IsLocalization.Away.lift_comp x _
  have hm : l.comp m = a := by
    apply IsLocalization.ringHom_ext (M := Submonoid.powers t)
    refine RingHom.ext fun b ↦ ?_
    change l (m (algebraMap _ _ b)) = a (algebraMap _ _ b)
    simp only [m, IsLocalization.map_eq, l, a, IsLocalization.Away.lift_eq, RingHom.id_apply]
  have key : ∀ (V : (AlgebraicGeometry.Spec Γ(T, ⊤)).Opens) (hV : T.toSpecΓ ⁻¹ᵁ V = T.basicOpen x),
      (T.isoOfEq hV).inv ≫ T.toSpecΓ ∣_ V ≫ V.ι = (T.basicOpen x).ι ≫ T.toSpecΓ := by
    intro V hV
    rw [AlgebraicGeometry.morphismRestrict_ι, ← Category.assoc, AlgebraicGeometry.Scheme.isoOfEq_inv_ι]
  have hL : L = (T.basicOpen x).ι ≫ T.toSpecΓ ≫ AlgebraicGeometry.Spec.map (CommRingCat.ofHom l) := by
    apply (cancel_mono (AlgebraicGeometry.Spec.map
      (CommRingCat.ofHom (algebraMap Γ(T, ⊤) (Localization.Away x))))).mp
    simp only [L, Category.assoc, AlgebraicGeometry.basicOpenIsoSpecAway_hom_SpecMap,
      ← AlgebraicGeometry.Spec.map_comp, ← CommRingCat.ofHom_comp, hl, CommRingCat.ofHom_id,
      AlgebraicGeometry.Spec.map_id]
    exact (key _ (T.toSpecΓ_preimage_basicOpen x)).trans (Category.comp_id _).symm
  let chartMapT : T ⟶ (AlgebraicGeometry.Proj.basicOpen (weightedHomogeneousSubmodule k w) t).toScheme :=
    T.toSpecΓ ≫ AlgebraicGeometry.Spec.map (CommRingCat.ofHom (chartEval k w e i hi)) ≫
      (AlgebraicGeometry.Proj.basicOpenIsoSpec (weightedHomogeneousSubmodule k w) t (X_mem k w i)
        (hw i)).inv
  have hlocal :
      AlgebraicGeometry.Proj.toBasicOpenOfGlobalSections (weightedHomogeneousSubmodule k w) e rfl
          (hw i) (X_mem k w i) =
        (T.basicOpen x).ι ≫ chartMapT := by
    change L ≫ AlgebraicGeometry.Spec.map (CommRingCat.ofHom
      (m.comp (algebraMap
        (HomogeneousLocalization.Away (weightedHomogeneousSubmodule k w) t) (Localization.Away t)))) ≫
        (AlgebraicGeometry.Proj.basicOpenIsoSpec (weightedHomogeneousSubmodule k w) t
          (X_mem k w i) (hw i)).inv = _
    rw [hL]
    simp only [chartMapT, chartEval, Category.assoc, ← AlgebraicGeometry.Spec.map_comp_assoc,
      ← CommRingCat.ofHom_comp, ← RingHom.comp_assoc, hm, a, t]
  have htop : T.basicOpen x = ⊤ := T.basicOpen_of_isUnit hi
  have : IsIso (T.basicOpen x).ι := by
    rw [htop]
    change IsIso T.topIso.hom
    infer_instance
  apply (cancel_epi (T.basicOpen x).ι).mp
  rw [← AlgebraicGeometry.Proj.basicOpenIsoSpec_inv_ι]
  change (T.basicOpen x).ι ≫ (chartMapT ≫
    (AlgebraicGeometry.Proj.basicOpen (weightedHomogeneousSubmodule k w) t).ι) = _
  rw [← Category.assoc, ← hlocal,
    ← AlgebraicGeometry.Proj.fromOfGlobalSections_resLE (weightedHomogeneousSubmodule k w) e he (hw i)
      (X_mem k w i)]
  exact AlgebraicGeometry.Scheme.Hom.resLE_comp_ι _ _

/-- The `K'`-point of a nonzero tuple `c` with `c_i ≠ 0` factors through the chart `D₊(x_i)` as
`Spec` of the evaluation map `chartEval (aeval c) i` (`f / x_i^n ↦ f(c) / c_i^n`). -/
theorem SpecMap_chartEval_awayι_eq_pointOfTuple (K' : Type u) [Field K'] [Algebra k K']
    (c : {v : σ → K' // v ≠ 0}) (i : σ) (hi : IsUnit ((aeval (c : σ → K')).toRingHom (X i))) :
    letI := MvPolynomial.weightedGradedAlgebra (R := k) w
    AlgebraicGeometry.Spec.map (CommRingCat.ofHom (chartEval k w (aeval (c : σ → K')).toRingHom i hi)) ≫
        AlgebraicGeometry.Proj.awayι (weightedHomogeneousSubmodule k w) (X i) (X_mem k w i) (hw i) =
      weightedProjectiveSpace.pointOfTuple k w hw K' c := by
  letI := MvPolynomial.weightedGradedAlgebra (R := k) w
  let e : MvPolynomial σ k →+* Γ(AlgebraicGeometry.Spec (CommRingCat.of K'), ⊤) :=
    (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of K')).inv.hom.comp
      (aeval (c : σ → K')).toRingHom
  have hi' : IsUnit (e (X i)) := hi.map (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of K')).inv.hom
  have hhi : (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of K')).hom.hom.comp
      (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of K')).inv.hom = RingHom.id _ := by
    ext a
    simp
  have hchart : (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of K')).hom.hom.comp
      (chartEval k w e i hi') = chartEval k w (aeval (c : σ → K')).toRingHom i hi := by
    unfold chartEval
    rw [← RingHom.comp_assoc]
    congr 1
    apply IsLocalization.ringHom_ext (M := Submonoid.powers (X (R := k) i))
    rw [RingHom.comp_assoc, IsLocalization.Away.lift_comp, IsLocalization.Away.lift_comp]
    change (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of K')).hom.hom.comp
      ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of K')).inv.hom.comp
        (aeval (c : σ → K')).toRingHom) = _
    rw [← RingHom.comp_assoc, hhi, RingHom.id_comp]
  unfold weightedProjectiveSpace.pointOfTuple
  rw [← SpecMap_chartEval_awayι k w hw (AlgebraicGeometry.Spec (CommRingCat.of K')) e
    (weightedProjectiveSpace.map_irrelevant_eq_top k w hw K' c) i hi',
    ← AlgebraicGeometry.SpecMap_ΓSpecIso_hom, ← AlgebraicGeometry.Spec.map_comp_assoc,
    ← CommRingCat.ofHom_hom (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of K')).hom,
    ← CommRingCat.ofHom_comp, hchart]

/-- **Algebraic fibre of a finite surjective ring map over a field-valued point.** Let `wp : A → B` be
finite with `Spec wp` surjective and `φ : A → K` a point of `Spec A` with values in a field `K`. Then there
is a finite field extension `K'/K` and a ring map `ψ : B → K'` with `ψ ∘ wp = (K → K') ∘ φ`
(`K'` is the residue field of a closed point of the fibre `Spec B ×_{Spec A} Spec K`).

Proof: `R := K ⊗[A] B` is a finite `K`-module (`Module.Finite.base_change`); `Spec R` is the pullback
`Spec K ×_{Spec A} Spec B` (`pullbackSpecIso`), whose projection to `Spec K` is surjective (surjectivity is
stable under base change), so `Spec R ≠ ∅` and `R ≠ 0`. Take a maximal ideal `m` of `R` and
`K' := R ⧸ m`, `ψ := (R → K') ∘ (b ↦ 1 ⊗ b)`; then `ψ (wp a) = [1 ⊗ wp a] = [φ a ⊗ 1] = (K → K') (φ a)`. -/
theorem exists_finite_field_extension_of_finite_surjective {A B K : Type u} [CommRing A] [CommRing B]
    [Field K] (φ : A →+* K) (wp : A →+* B) (hfin : wp.Finite)
    (hsurj : AlgebraicGeometry.Surjective (AlgebraicGeometry.Spec.map (CommRingCat.ofHom wp))) :
    ∃ (K' : Type u) (_ : Field K') (_ : Algebra K K') (_ : Module.Finite K K') (ψ : B →+* K'),
      ψ.comp wp = (algebraMap K K').comp φ := by
  classical
  letI : Algebra A K := φ.toAlgebra
  letI : Algebra A B := wp.toAlgebra
  haveI hfinAB : Module.Finite A B := hfin
  haveI hfinR : Module.Finite K (K ⊗[A] B) := inferInstance
  haveI hsurj' : AlgebraicGeometry.Surjective
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap A B))) := hsurj
  obtain ⟨y, -⟩ := (inferInstance : AlgebraicGeometry.Surjective
    (pullback.fst (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap A K)))
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap A B))))).surj
        (IsLocalRing.closedPoint K)
  let q : PrimeSpectrum (K ⊗[A] B) := (AlgebraicGeometry.pullbackSpecIso A K B).hom.base y
  haveI : Nontrivial (K ⊗[A] B) := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    exact q.isPrime.ne_top (Subsingleton.elim _ _)
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (K ⊗[A] B)
  haveI := hm
  letI : Field (K ⊗[A] B ⧸ m) := Ideal.Quotient.field m
  refine ⟨K ⊗[A] B ⧸ m, inferInstance, inferInstance,
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ K m).toLinearMap (Ideal.Quotient.mkₐ_surjective K m),
    (Ideal.Quotient.mk m).comp (Algebra.TensorProduct.includeRight (R := A) (A := K) (B := B)).toRingHom,
    ?_⟩
  refine RingHom.ext fun a => ?_
  change Ideal.Quotient.mk m (Algebra.TensorProduct.includeRight (R := A) (A := K) (B := B)
    (algebraMap A B a)) = algebraMap K (K ⊗[A] B ⧸ m) (algebraMap A K a)
  change _ = Ideal.Quotient.mk m (algebraMap K (K ⊗[A] B) (algebraMap A K a))
  congr 1
  simp only [AlgHom.commutes, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
    RingHom.id_apply]

end AffineLiftGenericPoint

open AffineLiftGenericPoint WeightedToOrdinaryProj MvPolynomial in
/- The `K`-point route: `x` is a `K`-point of `P(w)` (a `k`-morphism `Spec K ⟶ P(w)`). The fibre of the finite
   surjection `[u] ↦ [u^{w}]` over `x` is nonempty and finite; take a closed point of it, pass to its finite residue
   field extension `K'`, represent it by a nonzero ordinary projective tuple `a`, and raise each coordinate to its
   weight: the `K'`-point given by the tuple `(a_i^{w_i})` (`pointOfTuple`) is the base change of `x` to `K'`. -/
theorem exists_affine_lift_of_weighted_point {k : Type u} [Field k] {K : Type u} [Field K] [Algebra k K]
    {σ : Type u} [Fintype σ] (w : σ → ℕ) (hw : ∀ i, 0 < w i)
    (x : weightedProjectiveSpace.KPoint k w hw K) :
    ∃ (K' : Type u) (_ : Field K') (_ : Algebra K K') (_ : Algebra k K') (_ : IsScalarTower k K K')
      (_ : Module.Finite K K') (a : σ → K') (ha : a ≠ 0),
      weightedProjectiveSpace.pointOfTuple k w hw K'
          ⟨fun i => a i ^ w i, fun h => ha (funext fun i =>
            (pow_eq_zero_iff (Nat.pos_iff_ne_zero.mp (hw i))).mp (congrFun h i))⟩
        = (x.baseChange K').1 := by
  classical
  letI := MvPolynomial.weightedGradedAlgebra (R := k) w
  letI := MvPolynomial.weightedGradedAlgebra (R := k) (fun _ : σ => 1)
  -- Step 1: the unique point of `Spec K` lands in a chart `D₊(x_i)`.
  let x1 : AlgebraicGeometry.Spec (CommRingCat.of K) ⟶
    AlgebraicGeometry.Proj (MvPolynomial.weightedHomogeneousSubmodule k w) := x.1
  let pt : AlgebraicGeometry.Spec (CommRingCat.of K) := IsLocalRing.closedPoint K
  have hcover : ⨆ i, AlgebraicGeometry.Proj.basicOpen (MvPolynomial.weightedHomogeneousSubmodule k w)
      (MvPolynomial.X i) = ⊤ :=
    AlgebraicGeometry.Proj.iSup_basicOpen_eq_top _ MvPolynomial.X (irrelevant_le_span_X' k w)
  have hmem : (x1.base pt : AlgebraicGeometry.Proj (MvPolynomial.weightedHomogeneousSubmodule k w)) ∈
      (⊤ : (AlgebraicGeometry.Proj (MvPolynomial.weightedHomogeneousSubmodule k w)).Opens) := trivial
  rw [← hcover] at hmem
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hmem
  -- Step 2: lift `x` through the open immersion `awayι`.
  set ι := AlgebraicGeometry.Proj.awayι (MvPolynomial.weightedHomogeneousSubmodule k w)
    (MvPolynomial.X i) (X_mem k w i) (hw i) with hι
  have hrange : Set.range x1.base ⊆ Set.range ι.base := by
    rintro _ ⟨p, rfl⟩
    have hp : p = pt := Subsingleton.elim _ _
    rw [hp]
    rw [← AlgebraicGeometry.Proj.opensRange_awayι (MvPolynomial.weightedHomogeneousSubmodule k w)
      (MvPolynomial.X i) (X_mem k w i) (hw i)] at hi
    exact hi
  let φ' := AlgebraicGeometry.IsOpenImmersion.lift ι x1 hrange
  have hφ' : φ' ≫ ι = x1 := AlgebraicGeometry.IsOpenImmersion.lift_fac ι x1 hrange
  let φ : HomogeneousLocalization.Away (MvPolynomial.weightedHomogeneousSubmodule k w)
      (MvPolynomial.X i) →+* K :=
    (AlgebraicGeometry.Spec.preimage φ').hom
  have hφ : AlgebraicGeometry.Spec.map (CommRingCat.ofHom φ) = φ' := by
    simp [φ]
  -- `φ` is a `k`-algebra map (from `x.2`).
  have hφk : (φ.comp (HomogeneousLocalization.fromZeroRingHom
      (MvPolynomial.weightedHomogeneousSubmodule k w) (Submonoid.powers (MvPolynomial.X i)))).comp
        (algebraMap k (MvPolynomial.weightedHomogeneousSubmodule k w 0)) = algebraMap k K := by
    have h1 : x.1 ≫ (weightedProjectiveSpace k w hw ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom φ) ≫
          (ι ≫ (AlgebraicGeometry.Proj.toSpecZero (MvPolynomial.weightedHomogeneousSubmodule k w) ≫
            AlgebraicGeometry.Spec.map (CommRingCat.ofHom
              (algebraMap k (MvPolynomial.weightedHomogeneousSubmodule k w 0))))) := by
      rw [hφ, ← Category.assoc, hφ']; rfl
    have hx := x.2
    rw [h1, hι, AlgebraicGeometry.Proj.awayι_toSpecZero_assoc, ← AlgebraicGeometry.Spec.map_comp,
      ← AlgebraicGeometry.Spec.map_comp] at hx
    have h2 := AlgebraicGeometry.Spec.map_injective hx
    have h3 := congrArg CommRingCat.Hom.hom h2
    simpa using h3
  -- Step 3/4: a finite field extension `K'/K` and `ψ : B → K'` with `ψ ∘ wp = (K → K') ∘ φ`
  -- (the residue field of a closed point of the fibre of `Spec wp` over `Spec φ`).
  let B := HomogeneousLocalization.Away (MvPolynomial.weightedHomogeneousSubmodule k (fun _ : σ => 1))
    (weightedPowerGradedHom k w (MvPolynomial.X i))
  let wp : HomogeneousLocalization.Away (MvPolynomial.weightedHomogeneousSubmodule k w)
      (MvPolynomial.X i) →+* B := weightedPowerAwayMap k w hw i
  obtain ⟨K', instK', instKK', hfin, ψ, hψφ⟩ := exists_finite_field_extension_of_finite_surjective φ wp
    (weightedPowerAwayMap_finite_injective k w hw i).1 (spec_weightedPowerAwayMap_surjective k w hw i)
  let ιK : K →+* K' := algebraMap K K'
  letI algk : Algebra k K' := (ιK.comp (algebraMap k K)).toAlgebra
  haveI : IsScalarTower k K K' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  -- Step 5: the tuple `b_j = ψ (u_j u_i^{w_i-1} / u_i^{w_i})`.
  have hψX : weightedPowerGradedHom k w (MvPolynomial.X i) ∈
      MvPolynomial.weightedHomogeneousSubmodule k (fun _ : σ => 1) (w i) := psiX_mem k w i
  have hf : weightedPowerGradedHom k w (MvPolynomial.X i) = MvPolynomial.X i ^ w i :=
    weightedPowerGradedHom_X k w i
  have hrmem : ∀ j : σ, (MvPolynomial.X j * MvPolynomial.X i ^ (w i - 1) : MvPolynomial σ k) ∈
      MvPolynomial.weightedHomogeneousSubmodule k (fun _ : σ => 1) (1 • w i) := by
    intro j
    rw [MvPolynomial.mem_weightedHomogeneousSubmodule]
    have h := (MvPolynomial.isWeightedHomogeneous_X k (fun _ : σ => 1) j).mul
      ((MvPolynomial.isWeightedHomogeneous_X k (fun _ : σ => 1) i).pow (w i - 1))
    have hdeg : (fun _ : σ => 1) j + (w i - 1) • (fun _ : σ => 1) i = 1 • w i := by
      have := hw i
      show 1 + (w i - 1) * 1 = 1 * w i
      omega
    rw [hdeg] at h
    exact h
  let r : σ → B := fun j => HomogeneousLocalization.Away.mk
    (MvPolynomial.weightedHomogeneousSubmodule k (fun _ : σ => 1)) hψX 1
    (MvPolynomial.X j * MvPolynomial.X i ^ (w i - 1)) (hrmem j)
  let b : σ → K' := fun j => ψ (r j)
  have hri : r i = 1 := by
    apply HomogeneousLocalization.val_injective
    rw [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.val_one, Localization.mk_eq_mk',
      eq_comm, IsLocalization.eq_mk'_iff_mul_eq, one_mul]
    congr 1
    dsimp only
    rw [hf, pow_one, ← pow_succ', Nat.sub_add_cancel (hw i)]
  have hbi : b i = 1 := by
    simp only [b, hri, map_one]
  have hb : b ≠ 0 := fun h => by
    have := congrFun h i
    rw [hbi] at this
    exact one_ne_zero this
  -- Step 6: every element `g / (u_i^{w_i})^n` of `B` is `g (r)`.
  let F₀ : k →+* B := (HomogeneousLocalization.fromZeroRingHom
    (MvPolynomial.weightedHomogeneousSubmodule k (fun _ : σ => 1))
    (Submonoid.powers (weightedPowerGradedHom k w (MvPolynomial.X i)))).comp
    (algebraMap k (MvPolynomial.weightedHomogeneousSubmodule k (fun _ : σ => 1) 0))
  let Loc := Localization.Away (weightedPowerGradedHom k w (MvPolynomial.X i))
  have hF₀ : (algebraMap B Loc).comp F₀ = (algebraMap (MvPolynomial σ k) Loc).comp MvPolynomial.C := by
    refine RingHom.ext fun a => ?_
    simp only [RingHom.comp_apply, F₀]
    change (HomogeneousLocalization.mk _).val = _
    rw [HomogeneousLocalization.val_mk]
    simp only [Localization.mk_eq_mk', SetLike.GradeZero.coe_algebraMap, MvPolynomial.algebraMap_eq]
    exact IsLocalization.mk'_one _ _
  have hu : IsUnit (algebraMap (MvPolynomial σ k) Loc (MvPolynomial.X i)) := by
    have h := IsLocalization.Away.algebraMap_isUnit (S := Loc)
      (weightedPowerGradedHom k w (MvPolynomial.X i))
    have h2 := congrArg (algebraMap (MvPolynomial σ k) Loc) hf
    rw [map_pow] at h2
    rw [h2] at h
    exact (isUnit_pow_iff (hw i).ne').mp h
  let u : Locˣ := hu.unit
  have hval_r : ∀ j, (r j).val = algebraMap (MvPolynomial σ k) Loc (MvPolynomial.X j) * (u⁻¹ : Locˣ) := by
    intro j
    rw [Units.eq_mul_inv_iff_mul_eq, IsUnit.unit_spec, HomogeneousLocalization.Away.val_mk,
      Localization.mk_eq_mk', ← IsLocalization.mk'_one (M := Submonoid.powers
        (weightedPowerGradedHom k w (MvPolynomial.X i))) Loc (MvPolynomial.X i),
      ← IsLocalization.mk'_mul, IsLocalization.mk'_eq_iff_eq_mul]
    simp only [mul_one]
    change (algebraMap (MvPolynomial σ k) Loc) _ =
      (algebraMap (MvPolynomial σ k) Loc) _ * (algebraMap (MvPolynomial σ k) Loc) _
    rw [← map_mul]
    congr 1
    rw [hf, pow_one, mul_assoc, ← pow_succ, Nat.sub_add_cancel (hw i)]
  have hcore : ∀ (n : ℕ) (g : MvPolynomial σ k)
      (hg : g ∈ MvPolynomial.weightedHomogeneousSubmodule k (fun _ : σ => 1) (n • w i)),
      HomogeneousLocalization.Away.mk (MvPolynomial.weightedHomogeneousSubmodule k (fun _ : σ => 1))
        hψX n g hg = MvPolynomial.eval₂Hom F₀ r g := by
    intro n g hg
    apply HomogeneousLocalization.val_injective
    rw [HomogeneousLocalization.Away.val_mk, ← HomogeneousLocalization.algebraMap_apply,
      MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_comp_left, ← MvPolynomial.coe_eval₂Hom, hF₀]
    have hval : (algebraMap B Loc ∘ r) = fun j => algebraMap (MvPolynomial σ k) Loc (MvPolynomial.X j) *
        (u⁻¹ : Locˣ) := by
      funext j
      exact hval_r j
    rw [hval, eval₂Hom_scale_one k _ _ u⁻¹ ((MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).mp hg)]
    have heta : MvPolynomial.eval₂Hom ((algebraMap (MvPolynomial σ k) Loc).comp MvPolynomial.C)
        (fun j => algebraMap (MvPolynomial σ k) Loc (MvPolynomial.X j)) g =
        algebraMap (MvPolynomial σ k) Loc g := by
      rw [MvPolynomial.coe_eval₂Hom]
      change MvPolynomial.eval₂ ((algebraMap (MvPolynomial σ k) Loc).comp MvPolynomial.C)
        ((algebraMap (MvPolynomial σ k) Loc) ∘ MvPolynomial.X) g = _
      rw [← MvPolynomial.eval₂_comp_left, MvPolynomial.eval₂_eta]
    rw [heta]
    -- multiply both sides by the unit `u^(n w_i) = algebraMap ((u_i^{w_i})^n)`
    apply (Units.mul_left_inj (u ^ (n * w i))).mp
    have hupow : ((u ^ (n * w i) : Locˣ) : Loc) = algebraMap (MvPolynomial σ k) Loc
        (weightedPowerGradedHom k w (MvPolynomial.X i) ^ n) := by
      rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec, ← map_pow]
      congr 1
      rw [hf, ← pow_mul, mul_comm]
    have hR' : ((u⁻¹ : Locˣ) : Loc) ^ (n • w i) * algebraMap (MvPolynomial σ k) Loc g *
        ((u ^ (n * w i) : Locˣ) : Loc) = algebraMap (MvPolynomial σ k) Loc g := by
      rw [smul_eq_mul, mul_comm _ (algebraMap (MvPolynomial σ k) Loc g), mul_assoc,
        ← Units.val_pow_eq_pow_val, ← Units.val_mul, inv_pow, inv_mul_cancel, Units.val_one, mul_one]
    have hL' : ∀ hd : weightedPowerGradedHom k w (MvPolynomial.X i) ^ n ∈
        Submonoid.powers (weightedPowerGradedHom k w (MvPolynomial.X i)),
        Localization.mk g ⟨weightedPowerGradedHom k w (MvPolynomial.X i) ^ n, hd⟩ *
          ((u ^ (n * w i) : Locˣ) : Loc) = algebraMap (MvPolynomial σ k) Loc g := by
      intro hd
      rw [hupow, Localization.mk_eq_mk']
      exact IsLocalization.mk'_spec _ _ _
    rw [hR', hL']
  -- Step 7: `ψ ∘ wp` is the evaluation at `c = b^w` on the chart ring `A`.
  let c : σ → K' := fun j => b j ^ w j
  have hci : c i = 1 := by simp only [c, hbi, one_pow]
  have hcne : c ≠ 0 := fun h => by
    have := congrFun h i
    rw [hci] at this
    exact one_ne_zero this
  have hcunit : IsUnit ((aeval (R := k) c).toRingHom (MvPolynomial.X i)) := by
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.aeval_X, hci, isUnit_one]
  have hψw : ∀ g : MvPolynomial σ k, weightedPowerGradedHom k w g =
      aeval (R := k) (fun j : σ => (MvPolynomial.X j : MvPolynomial σ k) ^ w j) g := fun _ => rfl
  have h1 : wp.comp ((HomogeneousLocalization.fromZeroRingHom
      (MvPolynomial.weightedHomogeneousSubmodule k w) (Submonoid.powers (MvPolynomial.X i))).comp
        (algebraMap k (MvPolynomial.weightedHomogeneousSubmodule k w 0))) = F₀ := by
    refine RingHom.ext fun a => ?_
    apply HomogeneousLocalization.val_injective
    simp only [RingHom.comp_apply, F₀, wp, weightedPowerAwayMap]
    change (HomogeneousLocalization.map _ _ (HomogeneousLocalization.mk _)).val =
      (HomogeneousLocalization.mk _).val
    rw [HomogeneousLocalization.map_mk, HomogeneousLocalization.val_mk, HomogeneousLocalization.val_mk]
    simp only [Localization.mk_eq_mk', SetLike.GradeZero.coe_algebraMap, MvPolynomial.algebraMap_eq,
      hψw, MvPolynomial.aeval_C]
    congr 1
    refine Subtype.ext ?_
    simp only [SetLike.GradeZero.coe_one, map_one]
  have hψk : ψ.comp F₀ = algebraMap k K' := by
    rw [← h1, ← RingHom.comp_assoc, hψφ, RingHom.comp_assoc, ← RingHom.comp_assoc _ _ φ, hφk]
    rfl
  have hkey : ψ.comp wp = chartEval k w (aeval (R := k) c).toRingHom i hcunit := by
    refine RingHom.ext fun z => ?_
    obtain ⟨n, g, hg, rfl⟩ := HomogeneousLocalization.Away.mk_surjective
      (MvPolynomial.weightedHomogeneousSubmodule k w) (X_mem k w i) z
    -- left-hand side
    have hL : (ψ.comp wp) (HomogeneousLocalization.Away.mk
        (MvPolynomial.weightedHomogeneousSubmodule k w) (X_mem k w i) n g hg) = aeval (R := k) c g := by
      rw [RingHom.comp_apply]
      change ψ (HomogeneousLocalization.Away.map (weightedPowerGradedHom k w) (MvPolynomial.X i)
        (HomogeneousLocalization.Away.mk (MvPolynomial.weightedHomogeneousSubmodule k w)
          (X_mem k w i) n g hg)) = _
      rw [HomogeneousLocalization.Away.map_mk, hcore, MvPolynomial.coe_eval₂Hom,
        MvPolynomial.eval₂_comp_left, ← MvPolynomial.coe_eval₂Hom, hψk]
      change (MvPolynomial.eval₂Hom (algebraMap k K') (⇑ψ ∘ r))
        ((aeval (R := k) fun j : σ => (MvPolynomial.X j : MvPolynomial σ k) ^ w j) g) = _
      rw [← MvPolynomial.aeval_eq_eval₂Hom]
      change (aeval (R := k) b) ((aeval (R := k) fun j : σ => (MvPolynomial.X j : MvPolynomial σ k) ^ w j) g) = _
      rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
      simp only [map_pow, MvPolynomial.aeval_X, c]
    -- right-hand side
    have hR : chartEval k w (aeval (R := k) c).toRingHom i hcunit (HomogeneousLocalization.Away.mk
        (MvPolynomial.weightedHomogeneousSubmodule k w) (X_mem k w i) n g hg) = aeval (R := k) c g := by
      simp only [chartEval, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
        HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk']
      have h1 : IsLocalization.Away.lift (MvPolynomial.X i) hcunit
          (algebraMap (MvPolynomial σ k) (Localization.Away (MvPolynomial.X (R := k) i))
            (MvPolynomial.X i ^ n)) = 1 := by
        rw [IsLocalization.Away.lift_eq]
        simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_pow, MvPolynomial.aeval_X, hci, one_pow]
      calc IsLocalization.Away.lift (MvPolynomial.X i) hcunit
            (IsLocalization.mk' (Localization.Away (MvPolynomial.X (R := k) i)) g
              ⟨MvPolynomial.X i ^ n, Submonoid.pow_mem _ (Submonoid.mem_powers _) n⟩)
          = IsLocalization.Away.lift (MvPolynomial.X i) hcunit
            (IsLocalization.mk' (Localization.Away (MvPolynomial.X (R := k) i)) g
              ⟨MvPolynomial.X i ^ n, Submonoid.pow_mem _ (Submonoid.mem_powers _) n⟩) *
            IsLocalization.Away.lift (MvPolynomial.X i) hcunit
              (algebraMap (MvPolynomial σ k) (Localization.Away (MvPolynomial.X (R := k) i))
                (MvPolynomial.X i ^ n)) := by rw [h1, mul_one]
        _ = IsLocalization.Away.lift (MvPolynomial.X i) hcunit
            (algebraMap (MvPolynomial σ k) (Localization.Away (MvPolynomial.X (R := k) i)) g) := by
          rw [← map_mul, IsLocalization.mk'_spec]
        _ = aeval (R := k) c g := IsLocalization.Away.lift_eq _ _ _
    rw [hL, hR]
  -- Step 8: assemble.
  have hfinal : AlgebraicGeometry.Spec.map (CommRingCat.ofHom (ιK.comp φ)) ≫ ι =
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom ιK) ≫ x1 := by
    rw [CommRingCat.ofHom_comp, AlgebraicGeometry.Spec.map_comp, Category.assoc, hφ, hφ']
  refine ⟨K', inferInstance, inferInstance, algk, inferInstance, hfin, b, hb, ?_⟩
  rw [← SpecMap_chartEval_awayι_eq_pointOfTuple k w hw K' ⟨c, hcne⟩ i hcunit, ← hkey, hψφ]
  exact hfinal

end
