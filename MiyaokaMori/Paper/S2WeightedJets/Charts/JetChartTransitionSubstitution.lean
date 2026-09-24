import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S2WeightedJets.Charts.JetSubstitutionCoefficient

/-! # The transition between jet charts is substitution

If two étale chart coordinate systems `h`, `h'` satisfy `h'_i ≡ Φ(X_i)(h) (mod I^{k+1})`, then for
every based `k`-jet `γ` the `h'`-coefficients are obtained from the `h`-coefficients by
substituting into `Φ` and taking the coefficient of `t^q`:
`x'_{i,q} = jetSubstitutionCoeff Φ i q (x)` (eq. (2.7) of the paper).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Coefficients below `k + 1` are unchanged by reduction modulo `X ^ (k + 1)`. -/
theorem jetChartTransition_coeff_modByMonic_X_pow {W : Type u} [CommRing W] (k : ℕ)
    (p : Polynomial W) (q : ℕ) (hq : q ≤ k) :
    (p %ₘ ((Polynomial.X : Polynomial W) ^ (k + 1))).coeff q = p.coeff q := by
  conv_rhs => rw [← Polynomial.modByMonic_add_div p (Polynomial.X ^ (k + 1))]
  rw [Polynomial.coeff_add, Polynomial.coeff_X_pow_mul', if_neg (by omega), add_zero]

/-- The standard representative of an element of `W[t]/(t^{k+1})` is the sum of its
monomials of degree `≤ k`. -/
theorem jetChartTransition_modByMonicHom_eq_sum {W : Type u} [CommRing W] (k : ℕ)
    (x : MiyaokaMori.Jet.TruncatedJetRing W k) :
    AdjoinRoot.modByMonicHom (Polynomial.monic_X_pow (k + 1)) x =
      ∑ j : Fin (k + 1), Polynomial.monomial (j : ℕ)
        ((AdjoinRoot.modByMonicHom (Polynomial.monic_X_pow (k + 1)) x).coeff j) := by
  induction x using AdjoinRoot.induction_on with
  | ih p =>
    rw [AdjoinRoot.modByMonicHom_mk]
    exact (Polynomial.sum_modByMonic_coeff (Polynomial.monic_X_pow (k + 1))
      (Polynomial.degree_X_pow_le (k + 1))).symm

/-- If the constant coefficient vanishes, the representative is the sum of the monomials
of degree `1, …, k`, indexed by `Fin k`. -/
theorem jetChartTransition_modByMonicHom_eq_sum_succ {W : Type u} [CommRing W] (k : ℕ)
    (x : MiyaokaMori.Jet.TruncatedJetRing W k)
    (h0 : (AdjoinRoot.modByMonicHom (Polynomial.monic_X_pow (k + 1)) x).coeff 0 = 0) :
    AdjoinRoot.modByMonicHom (Polynomial.monic_X_pow (k + 1)) x =
      ∑ j : Fin k, Polynomial.monomial ((j : ℕ) + 1)
        ((AdjoinRoot.modByMonicHom (Polynomial.monic_X_pow (k + 1)) x).coeff ((j : ℕ) + 1)) := by
  conv_lhs => rw [jetChartTransition_modByMonicHom_eq_sum k x]
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero, Fin.val_succ, h0, map_zero, zero_add]

/-- A based jet (constant coefficient of every element of `I` vanishes) kills `I ^ (k + 1)`. -/
theorem jetChartTransition_map_pow_eq_zero {A B W : Type u} [CommRing A] [CommRing B] [CommRing W]
    [Algebra A B] [Algebra A W] (I : Ideal B) (k : ℕ)
    (γ : B →ₐ[A] MiyaokaMori.Jet.TruncatedJetRing W k)
    (hγ : ∀ b ∈ I, (AdjoinRoot.modByMonicHom (Polynomial.monic_X_pow (k + 1)) (γ b)).coeff 0 = 0)
    (b : B) (hb : b ∈ I ^ (k + 1)) : γ b = 0 := by
  set f : Polynomial W := Polynomial.X ^ (k + 1) with hf
  have hg : f.Monic := Polynomial.monic_X_pow (k + 1)
  set J : Ideal (MiyaokaMori.Jet.TruncatedJetRing W k) := Ideal.span {AdjoinRoot.root f} with hJ
  have hIJ : ∀ b ∈ I, γ b ∈ J := by
    intro b hb
    have h0 := hγ b hb
    obtain ⟨r, hr⟩ := Polynomial.X_dvd_iff.mpr h0
    rw [hJ, Ideal.mem_span_singleton, ← AdjoinRoot.mk_leftInverse hg (γ b), hr, map_mul,
      AdjoinRoot.mk_X]
    exact Dvd.intro _ rfl
  have hroot : (AdjoinRoot.root f) ^ (k + 1) = 0 := by
    rw [← AdjoinRoot.mk_X, ← map_pow, ← hf, AdjoinRoot.mk_self]
  have hJpow : J ^ (k + 1) = ⊥ := by
    rw [hJ, Ideal.span_singleton_pow, hroot, Ideal.span_singleton_eq_bot]
  have hmap : Ideal.map γ (I ^ (k + 1)) ≤ ⊥ := by
    rw [Ideal.map_pow, ← hJpow]
    exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.mpr hIJ) _
  exact (Ideal.mem_bot).mp (hmap (Ideal.mem_map_of_mem γ hb))

/-- Substituting polynomials divisible by `t` into the truncation of `φ` at level `m ≥ q`
gives the same `t^q`-coefficient as substituting into the truncation at level `q`:
every monomial with some exponent `> q` contributes a multiple of `t^{q+1}`. -/
theorem jetChartTransition_coeff_aeval_trunc' {A W : Type u} [CommRing A] [CommRing W]
    [Algebra A W] (n : ℕ) (a : Fin (n + 1) → Polynomial W) (ha : ∀ j, (a j).coeff 0 = 0)
    (φ : MvPowerSeries (Fin (n + 1)) A) (q m : ℕ) (hqm : q ≤ m) :
    (MvPolynomial.aeval a
        (MvPowerSeries.trunc' A (Finsupp.equivFunOnFinite.symm fun _ => m) φ)).coeff q =
      (MvPolynomial.aeval a
        (MvPowerSeries.trunc' A (Finsupp.equivFunOnFinite.symm fun _ => q) φ)).coeff q := by
  have hX : ∀ j, (Polynomial.X : Polynomial W) ∣ a j := fun j => Polynomial.X_dvd_iff.mpr (ha j)
  show (MvPolynomial.aeval a (MvPowerSeries.truncFinset A (Finset.Iic _) φ)).coeff q =
    (MvPolynomial.aeval a (MvPowerSeries.truncFinset A (Finset.Iic _) φ)).coeff q
  rw [MvPowerSeries.truncFinset_apply, MvPowerSeries.truncFinset_apply, map_sum, map_sum,
    Polynomial.finsetSum_coeff, Polynomial.finsetSum_coeff]
  symm
  apply Finset.sum_subset
  · apply Finset.Iic_subset_Iic.mpr
    rw [Finsupp.le_def]
    intro j
    simp only [Finsupp.coe_equivFunOnFinite_symm]
    exact hqm
  · intro e _ he
    rw [Finset.mem_Iic, Finsupp.le_iff] at he
    push_neg at he
    obtain ⟨j, hj, hje⟩ := he
    simp only [Finsupp.coe_equivFunOnFinite_symm] at hje
    rw [MvPolynomial.aeval_monomial]
    have hdvd : (Polynomial.X : Polynomial W) ^ (q + 1) ∣
        algebraMap A (Polynomial W) (MvPowerSeries.coeff e φ) * e.prod fun i k => a i ^ k := by
      apply Dvd.dvd.mul_left
      refine dvd_trans ?_ (Finset.dvd_prod_of_mem (fun i => a i ^ e i) hj)
      exact dvd_trans (pow_dvd_pow _ hje) (pow_dvd_pow_of_dvd (hX j) _)
    exact Polynomial.X_pow_dvd_iff.mp hdvd q (Nat.lt_succ_self q)

/-- The origin section sends every coordinate to `0`. -/
theorem jetChartTransition_baseCoordinate_origin {A : Type u} [CommRing A] (n : ℕ)
    (j : Fin (n + 1)) :
    MiyaokaMori.BasedAffineJet.baseCoordinate (jetOriginSection (R := A) n) j = 0 := by
  simp [MiyaokaMori.BasedAffineJet.baseCoordinate, jetOriginSection]

/-- **Jet chart transition is substitution** (eq. (2.7) of the paper).
Let `h, h' : Fin (n+1) → B` be two families of chart coordinates, all `h j`
lying in the ideal `I`, and let `Φ` be a formal coordinate change with
`h' i ≡ (trunc_k Φ(X_i))(h) (mod I^(k+1))`. For any `A`-algebra map
`γ : B → W[t]/(t^(k+1))` whose values on `I` have zero constant term (a jet based at the
section `V(I)`), the `t^q`-coefficient of `γ (h' i)` (`1 ≤ q ≤ k`) is the polynomial
`jetSubstitutionCoeff n k Φ i q` evaluated at the coefficients `x_{j,p} = [t^(p+1)] γ (h j)`.

Proof. (1) `γ` sends `I` into `(t)`, hence `I^(k+1)` into `(t)^(k+1) = 0`
(`jetChartTransition_map_pow_eq_zero`), so `γ (h' i) = γ (T_k(h)) = T_k(γ h)` where
`T_k = trunc_k Φ(X_i)`. (2) Writing `γ (h j) = mk (a j)` with `a j` the standard representative,
`T_k(γ h) = mk (T_k(a))`, and reduction mod `t^(k+1)` does not change coefficients `≤ k`
(`jetChartTransition_coeff_modByMonic_X_pow`). (3) Since every `a j` is divisible by `t`,
monomials of `Φ(X_i)` with some exponent `> q` contribute a multiple of `t^(q+1)`, so the
`t^q`-coefficient of `T_k(a)` equals that of `T_q(a)` (`jetChartTransition_coeff_aeval_trunc'`).
(4) `jetSubstitutionCoeff` is the `t^q`-coefficient of `T_q` evaluated at the universal
coordinate series `Σ_p X_{j,p} t^(p+1)` (origin section, constant term `0`); specializing
`X_{j,p} ↦ [t^(p+1)] a j` turns the universal series into `a j`
(`jetChartTransition_modByMonicHom_eq_sum_succ`), which gives the right-hand side.
The hypothesis `1 ≤ q` is not needed for the identity (it also holds for `q = 0`). -/
theorem jetChart_transition_substitution {A B W : Type u} [CommRing A] [CommRing B] [CommRing W]
    [Algebra A B] [Algebra A W] (I : Ideal B) (n k : ℕ) (h h' : Fin (n + 1) → B)
    (hhI : ∀ i, h i ∈ I)
    (Φ : MvPowerSeries (Fin (n + 1)) A ≃ₐ[A] MvPowerSeries (Fin (n + 1)) A)
    (hrel : ∀ i, h' i - MvPolynomial.aeval h
        (MvPowerSeries.trunc' A (Finsupp.equivFunOnFinite.symm fun _ => k) (Φ (MvPowerSeries.X i)))
        ∈ I ^ (k + 1))
    (γ : B →ₐ[A] MiyaokaMori.Jet.TruncatedJetRing W k)
    (hγ : ∀ b ∈ I, (AdjoinRoot.modByMonicHom (Polynomial.monic_X_pow (k + 1)) (γ b)).coeff 0 = 0)
    (i : Fin (n + 1)) (q : ℕ) (hq : 1 ≤ q ∧ q ≤ k) :
    (AdjoinRoot.modByMonicHom (Polynomial.monic_X_pow (k + 1)) (γ (h' i))).coeff q =
      MvPolynomial.aeval
        (fun jp : Fin (n + 1) × Fin k =>
          (AdjoinRoot.modByMonicHom (Polynomial.monic_X_pow (k + 1)) (γ (h jp.1))).coeff ((jp.2 : ℕ) + 1))
        (jetSubstitutionCoeff n k Φ i q) := by
  -- the coefficient polynomials of the jet in the chart `h`
  set a : Fin (n + 1) → Polynomial W :=
    fun j => AdjoinRoot.modByMonicHom (Polynomial.monic_X_pow (k + 1)) (γ (h j)) with ha_def
  have ha0 : ∀ j, (a j).coeff 0 = 0 := fun j => hγ (h j) (hhI j)
  have hmk_a : ∀ j, γ (h j) = AdjoinRoot.mk (Polynomial.X ^ (k + 1)) (a j) := fun j =>
    (AdjoinRoot.mk_leftInverse (Polynomial.monic_X_pow (k + 1)) (γ (h j))).symm
  -- `mk` commutes with substitution
  have hmk : ∀ T : MvPolynomial (Fin (n + 1)) A,
      MvPolynomial.aeval (fun j => AdjoinRoot.mk (Polynomial.X ^ (k + 1)) (a j)) T =
        AdjoinRoot.mk (Polynomial.X ^ (k + 1)) (MvPolynomial.aeval a T) := by
    intro T
    rw [MvPolynomial.map_aeval, MvPolynomial.aeval_eq_eval₂Hom]
    rfl
  -- Steps 1+2: `γ (h' i)` is the substitution of `γ ∘ h` into the truncated series
  set Tk := MvPowerSeries.trunc' A (Finsupp.equivFunOnFinite.symm fun _ => k)
    (Φ (MvPowerSeries.X i)) with hTk
  have h1 : γ (h' i) = AdjoinRoot.mk (Polynomial.X ^ (k + 1)) (MvPolynomial.aeval a Tk) := by
    have := jetChartTransition_map_pow_eq_zero I k γ hγ _ (hrel i)
    rw [map_sub, sub_eq_zero] at this
    rw [this, MvPolynomial.comp_aeval_apply]
    simp only [hmk_a]
    exact hmk Tk
  -- Step 3: the left side is the `t^q` coefficient of the polynomial substitution
  rw [h1, AdjoinRoot.modByMonicHom_mk, jetChartTransition_coeff_modByMonic_X_pow k _ q hq.2,
    jetChartTransition_coeff_aeval_trunc' n a ha0 _ q k hq.2]
  -- Right side: unfold `jetSubstitutionCoeff`, push `aeval x` through the coefficient
  show _ = MvPolynomial.aeval (fun jp : Fin (n + 1) × Fin k => (a jp.1).coeff ((jp.2 : ℕ) + 1))
    (jetSubstitutionCoeff n k Φ i q)
  set x : Fin (n + 1) × Fin k → W := fun jp => (a jp.1).coeff ((jp.2 : ℕ) + 1) with hx
  unfold jetSubstitutionCoeff MiyaokaMori.BasedAffineJet.universalEvaluation
  have hcoeff : ∀ P : Polynomial (MvPolynomial (Fin (n + 1) × Fin k) A),
      MvPolynomial.aeval x (P.coeff q) = (Polynomial.mapAlgHom (MvPolynomial.aeval x) P).coeff q := by
    intro P
    rw [Polynomial.coe_mapAlgHom]
    exact (Polynomial.coeff_map _ _).symm
  rw [hcoeff, MvPolynomial.comp_aeval_apply]
  -- the universal coordinate series specializes to `a j`
  have hU : (fun j : Fin (n + 1) => Polynomial.mapAlgHom (MvPolynomial.aeval x)
      (MiyaokaMori.BasedAffineJet.universalCoordinate (jetOriginSection (R := A) n) k j)) = a := by
    funext j
    rw [MiyaokaMori.BasedAffineJet.universalCoordinate, jetChartTransition_baseCoordinate_origin (A := A) n j,
      map_add, map_sum]
    simp only [Polynomial.coe_mapAlgHom, Polynomial.map_monomial, AlgHom.coe_toRingHom,
      MvPolynomial.aeval_X, map_zero, zero_add]
    exact (jetChartTransition_modByMonicHom_eq_sum_succ k (γ (h j)) (ha0 j)).symm
  rw [hU]

end
