import MiyaokaMori.Prelude
import MiyaokaMori.RingTheory.WeightedAwayDegreeOneVariable
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedGradedAlgebra
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.Stacks01my

/-! # The power map on a coordinate chart is finite and injective

The power map `[u] ↦ [u^w]` from ordinary to weighted projective space is, on a coordinate chart,
the finite injective ring homomorphism `k[x]^{(w)}_(x_i) → k[x]^{(1)}_(x_i^{w_i})` (`k[x]` is
finitely generated as a module over `k[x_0^{w_0}, …]` by the monomials `x^a` with `a_j < w_j`, and
this passes to the degree-zero homogeneous localizations). This is the finite surjective map from
ordinary to weighted projective space (Dolgachev, *Weighted projective varieties*, §1.2.2) used in
the proof of the Veronese polarization lemma and of the affine lift after finite base change in the
paper.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The power map preserves degrees: a polynomial homogeneous of degree `i` for the weights `w` is
sent to a polynomial homogeneous of degree `i` for the weights `1` (monomial by monomial:
`x^e ↦ Π u_j^{w_j e_j}` has total degree `Σ w_j e_j = i`; `IsWeightedHomogeneous.sum`/`.prod`/`.pow`). -/
theorem weightedPowerGradedHom.map_mem_aux (k : Type u) [Field k] {σ : Type u} [Fintype σ] (w : σ → ℕ)
    {i : ℕ} {x : MvPolynomial σ k} (hx : x ∈ MvPolynomial.weightedHomogeneousSubmodule k w i) :
    (MvPolynomial.aeval (R := k) (fun j : σ => (MvPolynomial.X j : MvPolynomial σ k) ^ w j)).toRingHom x ∈
      MvPolynomial.weightedHomogeneousSubmodule k (fun _ : σ => 1) i := by
  have hx' : x.IsWeightedHomogeneous w i := hx
  change MvPolynomial.IsWeightedHomogeneous (fun _ : σ => 1)
    (MvPolynomial.aeval (fun j : σ => (MvPolynomial.X j : MvPolynomial σ k) ^ w j) x) i
  conv => arg 2; rw [MvPolynomial.as_sum x]
  rw [map_sum]
  refine MvPolynomial.IsWeightedHomogeneous.sum _ _ _ fun d hd => ?_
  rw [MvPolynomial.aeval_monomial, MvPolynomial.algebraMap_eq]
  have hdeg : Finsupp.weight w d = i := hx' (MvPolynomial.mem_support_iff.mp hd)
  have hprod : MvPolynomial.IsWeightedHomogeneous (fun _ : σ => 1)
      (d.prod fun j e => ((MvPolynomial.X j : MvPolynomial σ k) ^ w j) ^ e)
      (∑ j ∈ d.support, d j * w j) := by
    unfold Finsupp.prod
    refine MvPolynomial.IsWeightedHomogeneous.prod d.support _ (fun j => d j * w j) fun j _ => ?_
    have h1 : MvPolynomial.IsWeightedHomogeneous (fun _ : σ => 1)
        ((MvPolynomial.X j : MvPolynomial σ k) ^ w j) (w j) := by
      have := (MvPolynomial.isWeightedHomogeneous_X k (fun _ : σ => 1) j).pow (w j)
      rwa [smul_eq_mul, mul_one] at this
    simpa using h1.pow (d j)
  have hsum : ∑ j ∈ d.support, d j * w j = i := by
    rw [← hdeg, Finsupp.weight_apply, Finsupp.sum]
    rfl
  rw [hsum] at hprod
  exact hprod.C_mul _

/-- The graded ring homomorphism `ψ_w : k[x]` (weights `w`) `→ k[u]` (weights `1`), `x_j ↦ u_j^{w_j}`:
a variable of weight `w_j` goes to a monomial of degree `w_j`. -/

noncomputable def weightedPowerGradedHom (k : Type u) [Field k] {σ : Type u} [Fintype σ] (w : σ → ℕ) :
    letI := MvPolynomial.weightedGradedAlgebra (R := k) w
    letI := MvPolynomial.weightedGradedAlgebra (R := k) (fun _ : σ => 1)
    MvPolynomial.weightedHomogeneousSubmodule k w →+*ᵍ
      MvPolynomial.weightedHomogeneousSubmodule k (fun _ : σ => 1) :=
  letI := MvPolynomial.weightedGradedAlgebra (R := k) w
  letI := MvPolynomial.weightedGradedAlgebra (R := k) (fun _ : σ => 1)
  { toRingHom := (MvPolynomial.aeval (R := k)
      (fun j : σ => (MvPolynomial.X j : MvPolynomial σ k) ^ w j)).toRingHom
    map_mem := fun {i} {x} hx => weightedPowerGradedHom.map_mem_aux k w hx }

/-- The value of `ψ_w` on a variable: `x_j ↦ u_j^{w_j}`. -/

theorem weightedPowerGradedHom_X (k : Type u) [Field k] {σ : Type u} [Fintype σ] (w : σ → ℕ) (j : σ) :
    letI := MvPolynomial.weightedGradedAlgebra (R := k) w
    letI := MvPolynomial.weightedGradedAlgebra (R := k) (fun _ : σ => 1)
    weightedPowerGradedHom k w (MvPolynomial.X j) = (MvPolynomial.X j : MvPolynomial σ k) ^ w j :=
  MvPolynomial.aeval_X _ _

/-- The ring map on a chart: `Away.map ψ_w (x_i) : k[x]^{(w)}_(x_i) → k[u]_(ψ_w x_i) = k[u]_(u_i^{w_i})`. -/

noncomputable def weightedPowerAwayMap (k : Type u) [Field k] {σ : Type u} [Fintype σ] (w : σ → ℕ)
    (hw : ∀ i, 0 < w i) (i : σ) :
    letI := MvPolynomial.weightedGradedAlgebra (R := k) w
    letI := MvPolynomial.weightedGradedAlgebra (R := k) (fun _ : σ => 1)
    HomogeneousLocalization.Away (MvPolynomial.weightedHomogeneousSubmodule k w) (MvPolynomial.X i) →+*
      HomogeneousLocalization.Away (MvPolynomial.weightedHomogeneousSubmodule k (fun _ : σ => 1))
        (weightedPowerGradedHom k w (MvPolynomial.X i)) :=
  letI := MvPolynomial.weightedGradedAlgebra (R := k) w
  letI := MvPolynomial.weightedGradedAlgebra (R := k) (fun _ : σ => 1)
  HomogeneousLocalization.Away.map (weightedPowerGradedHom k w) (MvPolynomial.X i)

/-! ## Helper lemmas for `weightedPowerAwayMap_finite_injective`

Route (standard argument): with `ψ = ψ_w : k[x] → k[u]`, `x_j ↦ u_j^{w_j}`,
the chart map `φ = Away.map ψ (x_i) : k[x]^{(w)}_(x_i) → k[u]_(u_i^{w_i})` is
* **injective**: `ψ` is injective (it sends the monomial `x^e` to the monomial `u^{(w_j e_j)}`, and
  `e ↦ (w_j e_j)_j` is injective for positive weights), `k[u]` is a domain and `u_i^{w_i} ≠ 0`, so the
  induced map on localizations is injective, and `val` embeds the degree-`0` parts;
* **finite type**: `k[u]_(u_i^{w_i})` is of finite type over `ℬ 0 = k` (Mathlib
  `HomogeneousLocalization.Away.finiteType`), and `φ` composed with `k → k[x]^{(w)}_(x_i)` is that
  structure map, so `φ` is of finite type (`RingHom.FiniteType.of_comp_finiteType`);
* **integral**: `k[u]_(u_i^{w_i})` is generated over `ℬ 0` by monomial fractions
  `u^a / (u_i^{w_i})^n` (Mathlib `HomogeneousLocalization.Away.adjoin_mk_prod_pow_eq_top`); with
  `W = ∏ w_j` the `W`-th power of such a fraction is `φ (x^{a'} / x_i^{nW})`, `a'_j = (W/w_j) a_j`,
  so each generator is integral, hence everything is (`Algebra.adjoin_induction`);
* integral + finite type ⇒ finite (`RingHom.IsIntegral.to_finite`). -/

namespace WeightedPowerChartFinite

open MvPolynomial

variable (k : Type u) [Field k] {σ : Type u} [Fintype σ] (w : σ → ℕ)

/-- ψ on a monomial: `x^e ↦ x^{(w_j e_j)_j}`. -/
theorem psi_monomial (e : σ →₀ ℕ) (c : k) :
    MvPolynomial.aeval (fun j : σ => (X j : MvPolynomial σ k) ^ w j) (monomial e c) =
      monomial (Finsupp.equivFunOnFinite.symm fun j => w j * e j) c := by
  rw [aeval_monomial, monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _), algebraMap_eq]
  simp [pow_mul]

theorem psi_injective (hw : ∀ j, 0 < w j) :
    Function.Injective (MvPolynomial.aeval (fun j : σ => (X j : MvPolynomial σ k) ^ w j) :
      MvPolynomial σ k → MvPolynomial σ k) := by
  classical
  set sc : (σ →₀ ℕ) → (σ →₀ ℕ) := fun e => Finsupp.equivFunOnFinite.symm fun j => w j * e j
    with hsc
  have hsc_inj : Function.Injective sc := by
    intro e₁ e₂ h
    ext j
    have h' := congrArg (fun f : σ → ℕ => f j) (Finsupp.equivFunOnFinite.symm.injective h)
    exact Nat.eq_of_mul_eq_mul_left (hw j) h'
  rw [injective_iff_map_eq_zero]
  intro f hf
  ext e
  rw [coeff_zero]
  have key : coeff (sc e) (aeval (fun j : σ => (X j : MvPolynomial σ k) ^ w j) f) = coeff e f := by
    conv_lhs => rw [as_sum f, map_sum, coeff_sum]
    simp_rw [psi_monomial, coeff_monomial]
    have hcongr : ∀ e' ∈ f.support,
        (if sc e' = sc e then coeff e' f else 0) = if e' = e then coeff e' f else 0 :=
      fun e' _ => by simp only [hsc_inj.eq_iff]
    rw [Finset.sum_congr rfl hcongr, Finset.sum_ite_eq' f.support e]
    split_ifs with h
    · rfl
    · exact (MvPolynomial.notMem_support_iff.mp h).symm
  rw [← key, hf, coeff_zero]

omit [Fintype σ] in
/-- A weight-`1` homogeneous polynomial of degree `0` is a constant. -/
theorem eq_C_of_mem_degZero {p : MvPolynomial σ k}
    (hp : p ∈ weightedHomogeneousSubmodule k (fun _ : σ => 1) 0) : p = C (coeff 0 p) :=
  calc p = weightedHomogeneousComponent (fun _ : σ => 1) 0 p :=
        (IsWeightedHomogeneous.weightedHomogeneousComponent_same hp).symm
    _ = C (coeff 0 p) := weightedHomogeneousComponent_zero _ (fun _ => one_ne_zero)


omit [Fintype σ] in
/-- `k[u]` is generated over `ℬ 0` by the variables. -/
theorem adjoin_range_X_degZero :
    letI := MvPolynomial.weightedGradedAlgebra (R := k) (fun _ : σ => 1)
    Algebra.adjoin (MvPolynomial.weightedHomogeneousSubmodule k (fun _ : σ => 1) 0)
      (Set.range (X : σ → MvPolynomial σ k)) = ⊤ := by
  letI := MvPolynomial.weightedGradedAlgebra (R := k) (fun _ : σ => 1)
  rw [eq_top_iff]
  intro p hp
  clear hp
  induction p using MvPolynomial.induction_on with
  | C c =>
    have : (C c : MvPolynomial σ k) =
        algebraMap (MvPolynomial.weightedHomogeneousSubmodule k (fun _ : σ => 1) 0) _
          (algebraMap k _ c) := by
      simp [SetLike.GradeZero.coe_algebraMap, algebraMap_eq]
    rw [this]
    exact Subalgebra.algebraMap_mem _ _
  | add p q hp hq => exact add_mem hp hq
  | mul_X p j hp => exact mul_mem hp (Algebra.subset_adjoin ⟨j, rfl⟩)

/-- `k[u]` is of finite type over `ℬ 0`. -/
theorem finiteType_degZero :
    letI := MvPolynomial.weightedGradedAlgebra (R := k) (fun _ : σ => 1)
    Algebra.FiniteType (MvPolynomial.weightedHomogeneousSubmodule k (fun _ : σ => 1) 0)
      (MvPolynomial σ k) := by
  letI := MvPolynomial.weightedGradedAlgebra (R := k) (fun _ : σ => 1)
  rw [← RingHom.finiteType_algebraMap]
  apply RingHom.FiniteType.of_comp_finiteType (f := algebraMap k
    (MvPolynomial.weightedHomogeneousSubmodule k (fun _ : σ => 1) 0))
  have : (algebraMap (MvPolynomial.weightedHomogeneousSubmodule k (fun _ : σ => 1) 0)
      (MvPolynomial σ k)).comp (algebraMap k _) = algebraMap k (MvPolynomial σ k) := by
    ext c
    simp [SetLike.GradeZero.coe_algebraMap]
  rw [this, RingHom.finiteType_algebraMap]
  infer_instance

section Away

variable (hw : ∀ i, 0 < w i) (i : σ)

omit [Fintype σ] in
theorem X_mem_deg : (X i : MvPolynomial σ k) ∈ weightedHomogeneousSubmodule k w (w i) :=
  isWeightedHomogeneous_X k w i

theorem psiX_mem_deg :
    letI := MvPolynomial.weightedGradedAlgebra (R := k) w
    letI := MvPolynomial.weightedGradedAlgebra (R := k) (fun _ : σ => 1)
    weightedPowerGradedHom k w (X i) ∈ weightedHomogeneousSubmodule k (fun _ : σ => 1) (w i) := by
  letI := MvPolynomial.weightedGradedAlgebra (R := k) w
  letI := MvPolynomial.weightedGradedAlgebra (R := k) (fun _ : σ => 1)
  rw [weightedPowerGradedHom_X]
  have := (isWeightedHomogeneous_X k (fun _ : σ => 1) i).pow (w i)
  rwa [smul_eq_mul, mul_one] at this

/-- `ψ` fixes constants: `ψ (C c) = C c`. -/
theorem psi_C (c : k) :
    letI := MvPolynomial.weightedGradedAlgebra (R := k) w
    letI := MvPolynomial.weightedGradedAlgebra (R := k) (fun _ : σ => 1)
    weightedPowerGradedHom k w (C c) = C c :=
  (MvPolynomial.aeval_C _ _).trans (DFunLike.congr_fun (MvPolynomial.algebraMap_eq k σ) c)

theorem awayMap_injective :
    letI := MvPolynomial.weightedGradedAlgebra (R := k) w
    letI := MvPolynomial.weightedGradedAlgebra (R := k) (fun _ : σ => 1)
    Function.Injective (weightedPowerAwayMap k w hw i) := by
  letI := MvPolynomial.weightedGradedAlgebra (R := k) w
  letI := MvPolynomial.weightedGradedAlgebra (R := k) (fun _ : σ => 1)
  set ψ := weightedPowerGradedHom k w with hψ
  have hle : Submonoid.powers (X i : MvPolynomial σ k) ≤
      (Submonoid.powers (ψ (X i))).comap ψ := by
    rintro _ ⟨n, rfl⟩
    exact ⟨n, by simp⟩
  have hle' : Submonoid.powers (X i : MvPolynomial σ k) ≤
      (Submonoid.powers (ψ (X i))).comap ψ.toRingHom := hle
  have hval : ∀ z, (weightedPowerAwayMap k w hw i z).val =
      IsLocalization.map (Localization (Submonoid.powers (ψ (X i)))) ψ.toRingHom hle' z.val := by
    intro z
    obtain ⟨c, rfl⟩ := HomogeneousLocalization.mk_surjective z
    show (HomogeneousLocalization.map ψ hle (HomogeneousLocalization.mk c)).val = _
    rw [HomogeneousLocalization.map_mk, HomogeneousLocalization.val_mk,
      HomogeneousLocalization.val_mk, Localization.mk_eq_mk', Localization.mk_eq_mk',
      IsLocalization.map_mk']
    rfl
  have hinj : Function.Injective
      (IsLocalization.map (S := Localization (Submonoid.powers (X i : MvPolynomial σ k)))
        (Localization (Submonoid.powers (ψ (X i)))) ψ.toRingHom hle') := by
    refine IsLocalization.map_injective_of_injective'
      (Rₘ := Localization (Submonoid.powers (X i : MvPolynomial σ k)))
      (Submonoid.powers (X i : MvPolynomial σ k)) (MvPolynomial σ k)
      (Localization (Submonoid.powers (ψ (X i)))) hle' ?_ ?_
    · rintro ⟨n, hn⟩
      have hn' : (X i : MvPolynomial σ k) ^ (w i * n) = 0 := by
        rw [pow_mul]
        exact (weightedPowerGradedHom_X k w i ▸ hn :)
      exact pow_ne_zero _ (X_ne_zero _) hn'
    · exact psi_injective k w hw
  intro z₁ z₂ h
  apply HomogeneousLocalization.val_injective
  apply hinj
  rw [← hval, ← hval, h]


/-- The chart map commutes with the structure maps from `k` (through the degree-`0` parts). -/
theorem awayMap_fromZero_algebraMap (c : k) :
    letI := MvPolynomial.weightedGradedAlgebra (R := k) w
    letI := MvPolynomial.weightedGradedAlgebra (R := k) (fun _ : σ => 1)
    weightedPowerAwayMap k w hw i
        (HomogeneousLocalization.fromZeroRingHom (weightedHomogeneousSubmodule k w)
          (Submonoid.powers (X i))
          ⟨C c, isWeightedHomogeneous_C w c⟩) =
      HomogeneousLocalization.fromZeroRingHom (weightedHomogeneousSubmodule k (fun _ : σ => 1))
        (Submonoid.powers (weightedPowerGradedHom k w (X i)))
        ⟨C c, isWeightedHomogeneous_C _ c⟩ := by
  letI := MvPolynomial.weightedGradedAlgebra (R := k) w
  letI := MvPolynomial.weightedGradedAlgebra (R := k) (fun _ : σ => 1)
  have hle : Submonoid.powers (X i : MvPolynomial σ k) ≤
      (Submonoid.powers (weightedPowerGradedHom k w (X i))).comap (weightedPowerGradedHom k w) := by
    rintro _ ⟨n, rfl⟩
    exact ⟨n, by simp⟩
  apply HomogeneousLocalization.val_injective
  show (HomogeneousLocalization.map (weightedPowerGradedHom k w) hle
    (HomogeneousLocalization.mk _)).val = (HomogeneousLocalization.mk _).val
  rw [HomogeneousLocalization.map_mk, HomogeneousLocalization.val_mk,
    HomogeneousLocalization.val_mk]
  simp [psi_C]

/-- The chart map is of finite type. -/
theorem awayMap_finiteType :
    letI := MvPolynomial.weightedGradedAlgebra (R := k) w
    letI := MvPolynomial.weightedGradedAlgebra (R := k) (fun _ : σ => 1)
    (weightedPowerAwayMap k w hw i).FiniteType := by
  letI := MvPolynomial.weightedGradedAlgebra (R := k) w
  letI := MvPolynomial.weightedGradedAlgebra (R := k) (fun _ : σ => 1)
  apply RingHom.FiniteType.of_comp_finiteType
    (f := (HomogeneousLocalization.fromZeroRingHom (weightedHomogeneousSubmodule k w)
      (Submonoid.powers (X i))).comp (algebraMap k (weightedHomogeneousSubmodule k w 0)))
  have heq : (weightedPowerAwayMap k w hw i).comp
      ((HomogeneousLocalization.fromZeroRingHom (weightedHomogeneousSubmodule k w)
        (Submonoid.powers (X i))).comp (algebraMap k (weightedHomogeneousSubmodule k w 0))) =
      (HomogeneousLocalization.fromZeroRingHom (weightedHomogeneousSubmodule k (fun _ : σ => 1))
        (Submonoid.powers (weightedPowerGradedHom k w (X i)))).comp
        (algebraMap k (weightedHomogeneousSubmodule k (fun _ : σ => 1) 0)) := by
    have hk : ∀ c : k, algebraMap k (weightedHomogeneousSubmodule k w 0) c =
        ⟨C c, isWeightedHomogeneous_C w c⟩ :=
      fun c => Subtype.ext (by rw [SetLike.GradeZero.coe_algebraMap, MvPolynomial.algebraMap_eq])
    have hk1 : ∀ c : k, algebraMap k (weightedHomogeneousSubmodule k (fun _ : σ => 1) 0) c =
        ⟨C c, isWeightedHomogeneous_C _ c⟩ :=
      fun c => Subtype.ext (by rw [SetLike.GradeZero.coe_algebraMap, MvPolynomial.algebraMap_eq])
    refine RingHom.ext fun c => ?_
    simp only [RingHom.comp_apply, hk, hk1]
    exact awayMap_fromZero_algebraMap k w hw i c
  rw [heq]
  refine RingHom.FiniteType.comp ?_ (RingHom.FiniteType.of_surjective _ ?_)
  · haveI := finiteType_degZero k (σ := σ)
    exact RingHom.finiteType_algebraMap.mpr
      (HomogeneousLocalization.Away.finiteType _ _ (psiX_mem_deg k w i))
  · rintro ⟨p, hp⟩
    refine ⟨coeff 0 p, Subtype.ext ?_⟩
    rw [SetLike.GradeZero.coe_algebraMap, MvPolynomial.algebraMap_eq]
    exact (eq_C_of_mem_degZero k hp).symm

/-- A monomial fraction `u^a / (u_i^{w_i})^n` is integral over `k[x]^{(w)}_(x_i)`: its
`W`-th power (`W = ∏ w_j`) is the image of `x^{a'} / x_i^{nW}` with `a'_j = (W / w_j) a_j`. -/
theorem isIntegral_mk_prod_pow (n : ℕ) (a : σ → ℕ)
    (hx : ∏ j, (X j : MvPolynomial σ k) ^ a j ∈
      weightedHomogeneousSubmodule k (fun _ : σ => 1) (n • w i)) :
    letI := MvPolynomial.weightedGradedAlgebra (R := k) w
    letI := MvPolynomial.weightedGradedAlgebra (R := k) (fun _ : σ => 1)
    letI := (weightedPowerAwayMap k w hw i).toAlgebra
    IsIntegral (HomogeneousLocalization.Away (weightedHomogeneousSubmodule k w) (X i))
      (HomogeneousLocalization.Away.mk (weightedHomogeneousSubmodule k (fun _ : σ => 1))
        (psiX_mem_deg k w i) n (∏ j, (X j : MvPolynomial σ k) ^ a j) hx) := by
  letI := MvPolynomial.weightedGradedAlgebra (R := k) w
  letI := MvPolynomial.weightedGradedAlgebra (R := k) (fun _ : σ => 1)
  letI := (weightedPowerAwayMap k w hw i).toAlgebra
  set W : ℕ := ∏ j, w j with hW
  have hWpos : 0 < W := Finset.prod_pos fun j _ => hw j
  have hdvd : ∀ j, w j ∣ W := fun j => Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
  -- degree of the numerator: ∑ a_j = n * w_i
  have hdeg : ∑ j, a j = n * w i := by
    have h1 := hx
    rw [mem_weightedHomogeneousSubmodule] at h1
    have h2 : (∏ j, (X j : MvPolynomial σ k) ^ a j) ∈
        weightedHomogeneousSubmodule k (fun _ : σ => 1) (∑ j, a j • (1 : ℕ)) :=
      SetLike.prod_pow_mem_graded _ _ _ _ fun j _ => isWeightedHomogeneous_X k _ j
    have hne : (∏ j, (X j : MvPolynomial σ k) ^ a j) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun j _ => pow_ne_zero _ (X_ne_zero _)
    have := DirectSum.degree_eq_of_mem_mem (weightedHomogeneousSubmodule k (fun _ : σ => 1))
      h2 hx hne
    simpa [smul_eq_mul] using this
  -- the preimage numerator
  set a' : σ → ℕ := fun j => W / w j * a j with ha'
  have hx' : ∏ j, (X j : MvPolynomial σ k) ^ a' j ∈
      weightedHomogeneousSubmodule k w ((n * W) • w i) := by
    have h2 : (∏ j, (X j : MvPolynomial σ k) ^ a' j) ∈
        weightedHomogeneousSubmodule k w (∑ j, a' j • w j) :=
      SetLike.prod_pow_mem_graded _ _ _ _ fun j _ => isWeightedHomogeneous_X k w j
    convert h2 using 2
    simp only [smul_eq_mul, ha']
    calc n * W * w i = W * (n * w i) := by ring
      _ = W * ∑ j, a j := by rw [hdeg]
      _ = ∑ j, W * a j := by rw [Finset.mul_sum]
      _ = ∑ j, W / w j * a j * w j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [mul_right_comm, Nat.div_mul_cancel (hdvd j)]
  have hpow : (HomogeneousLocalization.Away.mk (weightedHomogeneousSubmodule k (fun _ : σ => 1))
      (psiX_mem_deg k w i) n (∏ j, (X j : MvPolynomial σ k) ^ a j) hx) ^ W =
      algebraMap _ _ (HomogeneousLocalization.Away.mk (weightedHomogeneousSubmodule k w)
        (X_mem_deg k w i) (n * W) (∏ j, (X j : MvPolynomial σ k) ^ a' j) hx') := by
    rw [RingHom.algebraMap_toAlgebra]
    apply HomogeneousLocalization.val_injective
    unfold weightedPowerAwayMap
    rw [HomogeneousLocalization.Away.map_mk, HomogeneousLocalization.val_pow,
      HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk,
      Localization.mk_pow]
    congr 1
    · rw [map_prod, ← Finset.prod_pow]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [map_pow, weightedPowerGradedHom_X, ← pow_mul, ← pow_mul, ha']
      congr 1
      rw [← mul_assoc, Nat.mul_div_cancel' (hdvd j), mul_comm]
    · exact Subtype.ext (pow_mul _ _ _).symm
  exact IsIntegral.of_pow hWpos (hpow ▸ isIntegral_algebraMap)


/-- The chart map is integral: `k[u]_(u_i^{w_i})` is generated over `ℬ 0 = k` by monomial
fractions, each of which is integral (`isIntegral_mk_prod_pow`). -/
theorem awayMap_isIntegral :
    letI := MvPolynomial.weightedGradedAlgebra (R := k) w
    letI := MvPolynomial.weightedGradedAlgebra (R := k) (fun _ : σ => 1)
    (weightedPowerAwayMap k w hw i).IsIntegral := by
  letI := MvPolynomial.weightedGradedAlgebra (R := k) w
  letI := MvPolynomial.weightedGradedAlgebra (R := k) (fun _ : σ => 1)
  letI := (weightedPowerAwayMap k w hw i).toAlgebra
  intro z
  change IsIntegral (HomogeneousLocalization.Away (weightedHomogeneousSubmodule k w) (X i)) z
  have htop := HomogeneousLocalization.Away.adjoin_mk_prod_pow_eq_top (psiX_mem_deg k w i) σ X
    (adjoin_range_X_degZero k) (fun _ => 1) (fun j => isWeightedHomogeneous_X k _ j)
  have hz : z ∈ (⊤ : Subalgebra (weightedHomogeneousSubmodule k (fun _ : σ => 1) 0) _) :=
    Algebra.mem_top
  rw [← htop] at hz
  refine Algebra.adjoin_induction ?_ ?_ ?_ ?_ hz
  · rintro _ ⟨n, a, hai, -, rfl⟩
    exact isIntegral_mk_prod_pow k w hw i n a _
  · rintro ⟨p, hp⟩
    have hp' : (⟨p, hp⟩ : weightedHomogeneousSubmodule k (fun _ : σ => 1) 0) =
        ⟨C (coeff 0 p), isWeightedHomogeneous_C _ _⟩ :=
      Subtype.ext (eq_C_of_mem_degZero k hp)
    rw [hp', HomogeneousLocalization.algebraMap_eq, ← awayMap_fromZero_algebraMap k w hw i]
    exact isIntegral_algebraMap
  · intro x y _ _ hx hy
    exact hx.add hy
  · intro x y _ _ hx hy
    exact hx.mul hy

end Away

end WeightedPowerChartFinite

theorem weightedPowerAwayMap_finite_injective (k : Type u) [Field k] {σ : Type u} [Fintype σ]
    (w : σ → ℕ) (hw : ∀ i, 0 < w i) (i : σ) :
    letI := MvPolynomial.weightedGradedAlgebra (R := k) w
    letI := MvPolynomial.weightedGradedAlgebra (R := k) (fun _ : σ => 1)
    (weightedPowerAwayMap k w hw i).Finite ∧ Function.Injective (weightedPowerAwayMap k w hw i) := by
  letI := MvPolynomial.weightedGradedAlgebra (R := k) w
  letI := MvPolynomial.weightedGradedAlgebra (R := k) (fun _ : σ => 1)
  exact ⟨RingHom.IsIntegral.to_finite (WeightedPowerChartFinite.awayMap_isIntegral k w hw i)
      (WeightedPowerChartFinite.awayMap_finiteType k w hw i),
    WeightedPowerChartFinite.awayMap_injective k w hw i⟩

/-- `g : P^{|σ|-1} → P(w)` is the power map `[u] ↦ [u^w]`: `U(ψ_w)` is the whole space and `g` is the
morphism `r_{ψ_w}` of Stacks 01MY. -/

def InducedByPowerMap {k : Type u} [Field k] {σ : Type u} [Fintype σ] {w : σ → ℕ} {hw : ∀ i, 0 < w i}
    (g : weightedProjectiveSpace k (fun _ : σ => 1) (fun _ => Nat.one_pos) ⟶ weightedProjectiveSpace k w hw) : Prop :=
  letI := MvPolynomial.weightedGradedAlgebra (R := k) w
  letI := MvPolynomial.weightedGradedAlgebra (R := k) (fun _ : σ => 1)
  ∃ h : AlgebraicGeometry.Proj.mapDomain (weightedPowerGradedHom k w) = ⊤,
    g = (AlgebraicGeometry.Scheme.topIso _).inv ≫ (AlgebraicGeometry.Scheme.isoOfEq _ h.symm).hom ≫
      AlgebraicGeometry.Proj.mapOfGradedHom (weightedPowerGradedHom k w)

end
