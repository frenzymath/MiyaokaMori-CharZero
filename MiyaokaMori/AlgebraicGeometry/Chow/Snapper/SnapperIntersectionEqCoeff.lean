import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S2WeightedJets.Jets.BasedJetAlgebra
import MiyaokaMori.AlgebraicGeometry.Cohomology.EulerCharacteristic.EulerCharacteristic
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensor
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProperOverField
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.SchemeDimension
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.VarietyDimension
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedSymGenerator
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleTensor
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.Stacks01ct
import MiyaokaMori.AlgebraicGeometry.Chow.Snapper.Stacks0bem
import MiyaokaMori.AlgebraicGeometry.Chow.Snapper.Stacks0bep

/-! # The Snapper intersection number is the coefficient of `n_1⋯n_d`

`AlgebraicGeometry.snapperIntersection_eq_coeff`: the bridge between `snapperIntersection` (the `d`-fold
mixed difference at the origin) and the original definition of Stacks 0BEP (the coefficient of the
monomial `n_1⋯n_d` in the numerical polynomial). -/

set_option autoImplicit false
set_option maxHeartbeats 400000
universe u v w u' v'
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
noncomputable section

/- Characterization (well-definedness): if `P` is a numerical polynomial of total degree `≤ d` giving
   `χ(X, L_1^{n_1} ⊗ ⋯ ⊗ L_d^{n_d})` on `ℤ^d` (0BEM), then `snapperIntersection` is the coefficient of the
   monomial `n_1⋯n_d` in `P` (the original definition of Stacks 0BEP). -/

section MixedDifference

/-- Product of powers of indicator functions: `∏_{i} (1_{i∈t})^{u i} = ∏_{i ∉ t} 0^{u i}` (with the
convention `0^0 = 1`). -/
private theorem prod_indicator_pow {d : ℕ} (u : Fin d →₀ ℕ) (t : Finset (Fin d)) :
    (∏ i : Fin d, (if i ∈ t then (1 : ℚ) else 0) ^ u i)
      = ∏ i ∈ Finset.univ \ t, (0 : ℚ) ^ u i := by
  classical
  rw [← Finset.prod_sdiff (Finset.subset_univ t)]
  have h1 : (∏ i ∈ t, (if i ∈ t then (1 : ℚ) else 0) ^ u i) = 1 :=
    Finset.prod_eq_one fun i hi => by rw [if_pos hi, one_pow]
  have h2 : (∏ i ∈ Finset.univ \ t, (if i ∈ t then (1 : ℚ) else 0) ^ u i)
      = ∏ i ∈ Finset.univ \ t, (0 : ℚ) ^ u i :=
    Finset.prod_congr rfl fun i hi => by rw [if_neg (Finset.mem_sdiff.mp hi).2]
  rw [h1, h2, mul_one]

/-- The mixed difference applied to a monomial `X^u`:
`∑_{S ⊆ {1..d}} (-1)^{d-|S|} ∏_i (1_{i∈S})^{u i} = ∏_i (1 - 0^{u i})`.
This is `Finset.prod_add` expanded with `f i = 1`, `g i = -0^{u i}`. -/
private theorem alternating_sum_indicator_prod {d : ℕ} (u : Fin d →₀ ℕ) :
    (∑ S : Finset (Fin d), (-1 : ℚ) ^ (d - S.card) *
        ∏ i : Fin d, (if i ∈ S then (1 : ℚ) else 0) ^ u i)
      = ∏ i : Fin d, (1 - (0 : ℚ) ^ u i) := by
  classical
  have key := Finset.prod_add (fun _ : Fin d => (1 : ℚ)) (fun i => -((0 : ℚ) ^ u i)) Finset.univ
  rw [Finset.powerset_univ] at key
  have hl : (∏ i : Fin d, ((1 : ℚ) + -((0 : ℚ) ^ u i))) = ∏ i : Fin d, (1 - (0 : ℚ) ^ u i) :=
    Finset.prod_congr rfl fun i _ => by ring
  have hr : ∀ t : Finset (Fin d),
      ((∏ _i ∈ t, (1 : ℚ)) * ∏ i ∈ Finset.univ \ t, -((0 : ℚ) ^ u i))
        = (-1 : ℚ) ^ (d - t.card) * ∏ i : Fin d, (if i ∈ t then (1 : ℚ) else 0) ^ u i := by
    intro t
    have hsplit : (∏ i ∈ Finset.univ \ t, -((0 : ℚ) ^ u i))
        = (∏ _i ∈ Finset.univ \ t, (-1 : ℚ)) * ∏ i ∈ Finset.univ \ t, (0 : ℚ) ^ u i := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun i _ => by ring
    rw [Finset.prod_const_one, one_mul, prod_indicator_pow, hsplit, Finset.prod_const,
      Finset.card_univ_sdiff, Fintype.card_fin]
  rw [← hl, key]
  exact Finset.sum_congr rfl fun t _ => (hr t).symm

/-- Main lemma (pure `MvPolynomial` algebra): for a polynomial of total degree `≤ d`, the `d`-fold mixed
difference at the origin `Δ_1⋯Δ_d P = ∑_S (-1)^{d-|S|} P(1_S)` is exactly the coefficient of the monomial
`n_1⋯n_d`.

Proof: expand `P(1_S)` by `eval_eq'` as `∑_{u ∈ supp P} coeff u P · ∏_i (1_{i∈S})^{u i}`, exchange the
sums, and reduce the inner sum over `S` to `∏_i (1 - 0^{u i})` by `alternating_sum_indicator_prod`; this
is `1` if and only if all `u i ≠ 0`, and `0` otherwise. Only the `u` with full support remain; for such
`u`, `∑_i u i ≥ d`, while the total degree condition gives `∑_i u i ≤ d`, hence `u i = 1` for all `i`,
i.e. `u = ∑ i, single i 1`. -/
private theorem mixed_difference_eq_coeff {d : ℕ} (P : MvPolynomial (Fin d) ℚ)
    (hP : P.totalDegree ≤ d) :
    (∑ S : Finset (Fin d), (-1 : ℚ) ^ (d - S.card) *
        MvPolynomial.eval (fun i => if i ∈ S then (1 : ℚ) else 0) P)
      = MvPolynomial.coeff (∑ i, Finsupp.single i 1) P := by
  classical
  set v : Fin d →₀ ℕ := ∑ i, Finsupp.single i 1 with hvdef
  have hvapp : ∀ j : Fin d, v j = 1 := by
    intro j
    simp [hvdef, Finset.sum_apply', Finsupp.single_apply]
  have hexp : (∑ S : Finset (Fin d), (-1 : ℚ) ^ (d - S.card) *
        MvPolynomial.eval (fun i => if i ∈ S then (1 : ℚ) else 0) P)
      = ∑ u ∈ P.support, P.coeff u * ∏ i : Fin d, (1 - (0 : ℚ) ^ u i) := by
    calc (∑ S : Finset (Fin d), (-1 : ℚ) ^ (d - S.card) *
            MvPolynomial.eval (fun i => if i ∈ S then (1 : ℚ) else 0) P)
        = ∑ S : Finset (Fin d), ∑ u ∈ P.support, P.coeff u *
            ((-1 : ℚ) ^ (d - S.card) *
              ∏ i : Fin d, (if i ∈ S then (1 : ℚ) else 0) ^ u i) := by
          refine Finset.sum_congr rfl fun S _ => ?_
          rw [MvPolynomial.eval_eq', Finset.mul_sum]
          exact Finset.sum_congr rfl fun u _ => by ring
      _ = ∑ u ∈ P.support, ∑ S : Finset (Fin d), P.coeff u *
            ((-1 : ℚ) ^ (d - S.card) *
              ∏ i : Fin d, (if i ∈ S then (1 : ℚ) else 0) ^ u i) := Finset.sum_comm
      _ = ∑ u ∈ P.support, P.coeff u * ∏ i : Fin d, (1 - (0 : ℚ) ^ u i) := by
          refine Finset.sum_congr rfl fun u _ => ?_
          rw [← Finset.mul_sum, alternating_sum_indicator_prod]
  have hone : ∀ w : Fin d →₀ ℕ, (∀ i, w i ≠ 0) →
      (∏ i : Fin d, (1 - (0 : ℚ) ^ w i)) = 1 :=
    fun w hw => Finset.prod_eq_one fun i _ => by rw [zero_pow (hw i), sub_zero]
  have hzero : ∀ (w : Fin d →₀ ℕ) (j : Fin d), w j = 0 →
      (∏ i : Fin d, (1 - (0 : ℚ) ^ w i)) = 0 :=
    fun w j hj => Finset.prod_eq_zero (Finset.mem_univ j) (by rw [hj, pow_zero, sub_self])
  have hstep : (∑ u ∈ P.support, P.coeff u * ∏ i : Fin d, (1 - (0 : ℚ) ^ u i))
      = P.coeff v * ∏ i : Fin d, (1 - (0 : ℚ) ^ v i) := by
    refine Finset.sum_eq_single v ?_ ?_
    · intro u hu hne
      by_cases h : ∀ i, u i ≠ 0
      · exfalso
        refine hne ?_
        have hsupp : u.support = (Finset.univ : Finset (Fin d)) := by
          ext i
          simp only [Finsupp.mem_support_iff, Finset.mem_univ, iff_true]
          exact h i
        have hle : (∑ i : Fin d, u i) ≤ d := by
          have h1 := le_trans (MvPolynomial.le_totalDegree hu) hP
          rwa [Finsupp.sum, hsupp] at h1
        have hcst : (∑ _i : Fin d, (1 : ℕ)) = d := by simp
        have hge : (∑ _i : Fin d, (1 : ℕ)) ≤ ∑ i : Fin d, u i :=
          Finset.sum_le_sum fun i _ => Nat.one_le_iff_ne_zero.mpr (h i)
        have heq : (∑ _i : Fin d, (1 : ℕ)) = ∑ i : Fin d, u i := by omega
        have hall := (Finset.sum_eq_sum_iff_of_le
          (fun i (_ : i ∈ (Finset.univ : Finset (Fin d))) =>
            Nat.one_le_iff_ne_zero.mpr (h i))).mp heq
        refine Finsupp.ext fun i => ?_
        rw [hvapp i]
        exact (hall i (Finset.mem_univ i)).symm
      · push_neg at h
        obtain ⟨j, hj⟩ := h
        rw [hzero u j hj, mul_zero]
    · intro hv
      have : P.coeff v = 0 := by
        by_contra hc
        exact hv (MvPolynomial.mem_support_iff.mpr hc)
      rw [this, zero_mul]
  rw [hexp, hstep, hone v (fun i => by rw [hvapp i]; exact one_ne_zero), mul_one]

end MixedDifference

theorem AlgebraicGeometry.snapperIntersection_eq_coeff {k : Type u} [Field k]
    (X : AlgebraicGeometry.Scheme.{u})
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (hX : IsProperOver k X)
    {d : ℕ} (hd : X.dimension = d) (L : Fin d → X.Modules) [∀ i, (L i).IsLineBundle]
    (P : MvPolynomial (Fin d) ℚ) (hP : P.totalDegree ≤ d)
    (hPχ : ∀ n : Fin d → ℤ,
      (AlgebraicGeometry.sheafEulerCharacteristic (k := k) X
          ((List.finRange d).foldl (fun (G : X.Modules) (i : Fin d) => G.tensor (L i ^ n i))
            (SheafOfModules.unit X.ringCatSheaf)) : ℚ)
        = MvPolynomial.eval (fun i => (n i : ℚ)) P) :
    AlgebraicGeometry.snapperIntersection X hX hd L = MvPolynomial.coeff (∑ i, Finsupp.single i 1) P := by
  classical
  rw [AlgebraicGeometry.snapperIntersection, ← mixed_difference_eq_coeff P hP]
  refine Finset.sum_congr rfl fun S _ => ?_
  congr 1
  rw [hPχ (fun i => if i ∈ S then (1 : ℤ) else 0)]
  have hfun : (fun i : Fin d => (((if i ∈ S then (1 : ℤ) else 0) : ℤ) : ℚ))
      = fun i : Fin d => if i ∈ S then (1 : ℚ) else 0 := by
    funext i
    split <;> norm_num
  rw [hfun]

end
