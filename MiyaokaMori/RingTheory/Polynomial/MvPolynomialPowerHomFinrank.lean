import MiyaokaMori.Prelude

/-! # Rank of a polynomial ring over the image of a power map

`k[z]` is a free module of rank `∏ⱼ wⱼ` over `k[y]` via the power map `θ : yⱼ ↦ zⱼ^{wⱼ}`
(all `wⱼ > 0`), with basis the monomials `z^a`, `0 ≤ aⱼ < wⱼ`.

Statement (`MvPolynomial.PowerHom.finrank_eq`). Let `k` be a nontrivial commutative ring, `τ` a finite
type with decidable equality, `w : τ → ℕ` with `w j > 0`, and `θ = powerHom k w : k[τ] →+* k[τ]`,
`X j ↦ X j ^ w j`. Let `R` be a commutative ring which is an algebra over which `k[τ]` is a module, and
`eR : k[τ] ≃+* R` a ring isomorphism with `algebraMap R k[τ] ∘ eR = θ`. Then
`Module.finrank R k[τ] = ∏ j, w j`.

Proof (division with remainder on exponents). Every exponent vector `e : τ →₀ ℕ` is uniquely
`e = a + w * q` with `aⱼ = eⱼ mod wⱼ < wⱼ` and `qⱼ = eⱼ div wⱼ` (`expEquiv`, a bijection
`(τ →₀ ℕ) ≃ (∏ⱼ Fin wⱼ) × (τ →₀ ℕ)`). On monomials `θ (monomial q c) = monomial (w * q) c`
(`powerHom_monomial`), so `θ(r) · z^a = ∑_q coeff_q(r) z^{a + w q}` and
`coeff_{a₀ + w q₀} (θ(r) · z^a) = [a = a₀] · coeff_{q₀} r` (`coeff_powerHom_mul_monomial`).
Hence for the `R`-linear map `L : (ι →₀ R) → k[τ]`, `single a r ↦ r • z^a` (`Finsupp.linearCombination`),
`coeff_{a₀ + w q₀} (L x) = coeff_{q₀} (eR⁻¹ (x a₀))` (`coeff_linearCombination`): `L` is injective
(all coefficients of `eR⁻¹ (x a₀)` vanish) and surjective (`monomial e c = L (single a (eR (monomial q c)))`
for `(a, q) = expEquiv e`; sums by additivity). So `z^a` (`a ∈ ∏ⱼ Fin wⱼ`) is an `R`-basis
(`Basis.ofRepr`), and `Module.finrank_eq_card_basis` with `Fintype.card_pi` gives `∏ j, w j`.

The abstract `R` (instead of `R = k[τ]` with `θ.toAlgebra`) avoids two competing `Module k[τ] k[τ]`
instances; in the application `R` is the chart ring `k[x]^{(w)}_{(x_{i₀})}` and `eR` its dehomogenisation.

Edge cases: `τ` empty: `k[τ] ≅ k`, `ι` is a singleton, rank `1 = ∏_∅`; some `wⱼ = 1`: `Fin 1`, that
variable contributes a single basis monomial `zⱼ^0`.

Source: the degree `∏ wᵢ` of the weighted power map (Lemma 2.2 of the paper; standard
multivariate division with remainder). Used for the rank of the weighted power map on a chart
(`WeightedPowerAwayMapFinrank`); also gives finite generation by the same monomials.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false

universe u v

noncomputable section

namespace MvPolynomial.PowerHom

open MvPolynomial

variable (k : Type u) [CommRing k] {τ : Type u} [Fintype τ] [DecidableEq τ] (w : τ → ℕ)

/-- The power map `θ : k[τ] →+* k[τ]`, `X j ↦ X j ^ w j`. -/
def powerHom : MvPolynomial τ k →+* MvPolynomial τ k :=
  (aeval (R := k) fun j => (X j : MvPolynomial τ k) ^ w j).toRingHom

@[simp] lemma powerHom_X (j : τ) : powerHom k w (X j) = X j ^ w j := by
  simp [powerHom]

@[simp] lemma powerHom_C (c : k) : powerHom k w (C c) = C c := by
  simp [powerHom, algebraMap_eq]

/-- Index of the monomial basis: exponent vectors `a` with `a j < w j`. -/
abbrev Idx : Type u := ∀ j : τ, Fin (w j)

/-- `a` as an exponent vector. -/
def idxExp (a : Idx w) : τ →₀ ℕ := Finsupp.equivFunOnFinite.symm fun j => (a j : ℕ)

/-- `q ↦ w * q` pointwise. -/
def scaleExp (q : τ →₀ ℕ) : τ →₀ ℕ := Finsupp.equivFunOnFinite.symm fun j => w j * q j

@[simp] lemma idxExp_apply (a : Idx w) (j : τ) : idxExp w a j = a j := rfl

@[simp] lemma scaleExp_apply (q : τ →₀ ℕ) (j : τ) : scaleExp w q j = w j * q j := rfl

/-- `θ (monomial q c) = monomial (w * q) c`. -/
lemma powerHom_monomial (q : τ →₀ ℕ) (c : k) :
    powerHom k w (monomial q c) = monomial (scaleExp w q) c := by
  rw [powerHom, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, aeval_monomial, monomial_eq,
    Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Finsupp.prod_fintype _ _ (fun _ => pow_zero _),
    algebraMap_eq]
  simp only [scaleExp_apply, pow_mul]

variable (hw : ∀ j, 0 < w j)

/-- Division with remainder on exponents: `e ↦ (e mod w, e div w)`, inverse `(a, q) ↦ a + w * q`. -/
def expEquiv : (τ →₀ ℕ) ≃ Idx w × (τ →₀ ℕ) where
  toFun e := (fun j => ⟨e j % w j, Nat.mod_lt _ (hw j)⟩,
    Finsupp.equivFunOnFinite.symm fun j => e j / w j)
  invFun p := idxExp w p.1 + scaleExp w p.2
  left_inv e := by
    ext j
    simp only [Finsupp.coe_add, Pi.add_apply, idxExp_apply, scaleExp_apply,
      Finsupp.coe_equivFunOnFinite_symm]
    exact Nat.mod_add_div _ _
  right_inv p := by
    obtain ⟨a, q⟩ := p
    refine Prod.ext (funext fun j => Fin.ext ?_) (Finsupp.ext fun j => ?_)
    · simp only [Finsupp.coe_add, Pi.add_apply, idxExp_apply, scaleExp_apply]
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (a j).2]
    · simp only [Finsupp.coe_add, Pi.add_apply, idxExp_apply, scaleExp_apply,
        Finsupp.coe_equivFunOnFinite_symm]
      rw [Nat.add_mul_div_left _ _ (hw j), Nat.div_eq_of_lt (a j).2, zero_add]

lemma expEquiv_symm_apply (a : Idx w) (q : τ →₀ ℕ) :
    (expEquiv w hw).symm (a, q) = idxExp w a + scaleExp w q := rfl

/-- `coeff_e (θ(r) · z^a) = [a = (e mod w)] · coeff_{e div w} r`. -/
lemma coeff_powerHom_mul_monomial (r : MvPolynomial τ k) (a : Idx w) (e : τ →₀ ℕ) :
    coeff e (powerHom k w r * monomial (idxExp w a) 1) =
      if (expEquiv w hw e).1 = a then coeff (expEquiv w hw e).2 r else 0 := by
  induction r using MvPolynomial.induction_on' with
  | monomial q c =>
    rw [powerHom_monomial, monomial_mul, mul_one, coeff_monomial, coeff_monomial]
    have key : scaleExp w q + idxExp w a = e ↔
        (expEquiv w hw e).1 = a ∧ q = (expEquiv w hw e).2 := by
      rw [add_comm, ← expEquiv_symm_apply w hw, Equiv.symm_apply_eq, Prod.ext_iff]
      exact ⟨fun ⟨h1, h2⟩ => ⟨h1.symm, h2⟩, fun ⟨h1, h2⟩ => ⟨h1.symm, h2⟩⟩
    simp only [key]
    by_cases h1 : (expEquiv w hw e).1 = a <;> by_cases h2 : q = (expEquiv w hw e).2 <;>
      simp [h1, h2]
  | add p q hp hq =>
    rw [map_add, add_mul, coeff_add, hp, hq]
    split_ifs <;> simp

/-! ## The basis over an abstract base ring `R ≃ k[τ]` acting through `θ` -/

variable {R : Type v} [CommRing R] [Algebra R (MvPolynomial τ k)]

/-- The basis vectors `z^a`, `a ∈ ∏ⱼ Fin wⱼ`. -/
def basisVec (a : Idx w) : MvPolynomial τ k := monomial (idxExp w a) 1

variable (eR : MvPolynomial τ k ≃+* R)

lemma smul_eq (h : (algebraMap R (MvPolynomial τ k)).comp eR.toRingHom = powerHom k w)
    (r s : MvPolynomial τ k) : eR r • s = powerHom k w r * s := by
  rw [Algebra.smul_def, ← h]; rfl

/-- `coeff_{a + w q} (∑_b x_b • z^b) = coeff_q (eR⁻¹ (x a))`. -/
lemma coeff_linearCombination (h : (algebraMap R (MvPolynomial τ k)).comp eR.toRingHom = powerHom k w)
    (x : Idx w →₀ R) (a : Idx w) (q : τ →₀ ℕ) :
    coeff ((expEquiv w hw).symm (a, q)) (Finsupp.linearCombination R (basisVec k w) x) =
      coeff q (eR.symm (x a)) := by
  rw [Finsupp.linearCombination_apply, Finsupp.sum, coeff_sum]
  have this : ∀ b ∈ x.support,
      coeff ((expEquiv w hw).symm (a, q)) (x b • basisVec k w b) =
        if a = b then coeff q (eR.symm (x b)) else 0 := by
    intro b _
    rw [← eR.apply_symm_apply (x b), smul_eq k w eR h, basisVec,
      coeff_powerHom_mul_monomial k w hw, Equiv.apply_symm_apply, eR.symm_apply_apply]
  rw [Finset.sum_congr rfl this, Finset.sum_ite_eq]
  split_ifs with hmem
  · rfl
  · rw [Finsupp.notMem_support_iff.mp hmem, map_zero, coeff_zero]

include hw eR in
lemma linearCombination_injective
    (h : (algebraMap R (MvPolynomial τ k)).comp eR.toRingHom = powerHom k w) :
    Function.Injective (Finsupp.linearCombination R (basisVec k w)) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  refine Finsupp.ext fun a => ?_
  rw [Finsupp.zero_apply]
  apply eR.symm.injective
  rw [map_zero]
  refine MvPolynomial.ext _ _ fun q => ?_
  rw [coeff_zero, ← coeff_linearCombination k w hw eR h x a q, hx, coeff_zero]

include hw eR in
lemma linearCombination_surjective
    (h : (algebraMap R (MvPolynomial τ k)).comp eR.toRingHom = powerHom k w) :
    Function.Surjective (Finsupp.linearCombination R (basisVec k w)) := by
  intro s
  induction s using MvPolynomial.induction_on' with
  | monomial e c =>
    refine ⟨Finsupp.single (expEquiv w hw e).1 (eR (monomial (expEquiv w hw e).2 c)), ?_⟩
    rw [Finsupp.linearCombination_single, smul_eq k w eR h, basisVec, powerHom_monomial,
      monomial_mul, mul_one, add_comm, ← expEquiv_symm_apply w hw, Equiv.symm_apply_apply]
  | add p q hp hq =>
    obtain ⟨x, rfl⟩ := hp
    obtain ⟨y, rfl⟩ := hq
    exact ⟨x + y, map_add _ _ _⟩

/-- The monomials `z^a`, `0 ≤ aⱼ < wⱼ`, form an `R`-basis of `k[τ]`. -/
def basis (hw : ∀ j, 0 < w j) (h : (algebraMap R (MvPolynomial τ k)).comp eR.toRingHom = powerHom k w) :
    Module.Basis (Idx w) R (MvPolynomial τ k) :=
  Module.Basis.ofRepr (LinearEquiv.ofBijective (Finsupp.linearCombination R (basisVec k w))
    ⟨linearCombination_injective k w hw eR h, linearCombination_surjective k w hw eR h⟩).symm

include hw eR in
/-- **Rank of the power map**: `k[τ]` has rank `∏ j, w j` over `R ≃ k[τ]` acting through
`θ : X j ↦ X j ^ w j`. -/
theorem finrank_eq [Nontrivial k]
    (h : (algebraMap R (MvPolynomial τ k)).comp eR.toRingHom = powerHom k w) :
    Module.finrank R (MvPolynomial τ k) = ∏ j, w j := by
  have : Nontrivial R := eR.symm.toEquiv.nontrivial
  rw [Module.finrank_eq_card_basis (basis k w eR hw h), Fintype.card_pi]
  simp only [Fintype.card_fin]

end MvPolynomial.PowerHom

end
