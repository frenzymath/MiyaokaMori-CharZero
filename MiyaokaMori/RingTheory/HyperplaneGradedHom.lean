import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpace
import Mathlib.Algebra.MvPolynomial.Division

/-! # The hyperplane of projective space, part 1: the graded surjection `K[x_0..x_{m+1}] → K[y_0..y_m]`

The graded `K`-algebra map `φ = killLast : x_i ↦ y_i` (`i ≤ m`, via `Fin.castSucc`), `x_{m+1} ↦ 0`
(`MvPolynomial.aeval (Fin.snoc X 0)`), its graded section `includeVars = rename Fin.castSucc`, and the
kernel computation: `φ p = 0 ⇒ x_{m+1} ∣ p` (with a homogeneous quotient), hence
`ker (A_{(x_i)} → B_{(φ x_i)}) = (x_{m+1}/x_i)` on the chart `D_+(x_i)` (`ker_awayMap_eq`).
Pure algebra; no schemes. Source: Stacks 01MZ / Hartshorne II Ex. 3.12(a).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open MvPolynomial HomogeneousLocalization
open scoped HomogeneousIdeal

noncomputable section

namespace ProjBundleFiberDegreeOne

attribute [local instance] MvPolynomial.gradedAlgebra

variable (K : Type u) [Field K] (m : ℕ)

/-- `x_i ↦ y_i` (`i ≤ m`), `x_{m+1} ↦ 0`. -/
def killLast : MvPolynomial (Fin (m + 2)) K →ₐ[K] MvPolynomial (Fin (m + 1)) K :=
  aeval (Fin.snoc (α := fun _ => MvPolynomial (Fin (m + 1)) K) X 0)

/-- `y_i ↦ x_i`: a section of `killLast`. -/
def includeVars : MvPolynomial (Fin (m + 1)) K →ₐ[K] MvPolynomial (Fin (m + 2)) K :=
  rename Fin.castSucc

theorem killLast_X_castSucc (j : Fin (m + 1)) : killLast K m (X j.castSucc) = X j := by
  simp [killLast]

theorem killLast_X_last : killLast K m (X (Fin.last (m + 1))) = 0 := by
  simp [killLast]

theorem killLast_includeVars (p : MvPolynomial (Fin (m + 1)) K) :
    killLast K m (includeVars K m p) = p := by
  simp only [killLast, includeVars, aeval_rename]
  have : (Fin.snoc (α := fun _ => MvPolynomial (Fin (m + 1)) K) X 0 ∘ Fin.castSucc) = X := by
    funext j; simp
  rw [this]; exact aeval_X_left_apply p

theorem killLast_surjective : Function.Surjective (killLast K m) :=
  fun p => ⟨includeVars K m p, killLast_includeVars K m p⟩

theorem includeVars_mem {n : ℕ} {p : MvPolynomial (Fin (m + 1)) K}
    (hp : p ∈ AlgebraicGeometry.Proj.projectiveGrading K m n) :
    includeVars K m p ∈ AlgebraicGeometry.Proj.projectiveGrading K (m + 1) n := by
  change p.IsHomogeneous n at hp
  exact hp.rename_isHomogeneous

theorem killLast_mem {n : ℕ} {p : MvPolynomial (Fin (m + 2)) K}
    (hp : p ∈ AlgebraicGeometry.Proj.projectiveGrading K (m + 1) n) :
    killLast K m p ∈ AlgebraicGeometry.Proj.projectiveGrading K m n := by
  change p.IsHomogeneous n at hp
  change MvPolynomial.IsHomogeneous (aeval (Fin.snoc (α := fun _ => MvPolynomial (Fin (m + 1)) K) X 0) p) n
  have h := hp.aeval (Fin.snoc (α := fun _ => MvPolynomial (Fin (m + 1)) K) X 0) (n := 1) fun i => by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.snoc_last]; exact isHomogeneous_zero _ _ _
    · simp only [Fin.snoc_castSucc]; exact isHomogeneous_X K j
  simpa only [one_mul] using h

/-- The graded ring homomorphism `K[x_0..x_{m+1}] → K[y_0..y_m]` killing `x_{m+1}`. -/
def hyperplaneGradedHom : AlgebraicGeometry.Proj.projectiveGrading K (m + 1) →+*ᵍ AlgebraicGeometry.Proj.projectiveGrading K m where
  toRingHom := (killLast K m).toRingHom
  map_mem hp := killLast_mem K m hp

theorem hyperplaneGradedHom_apply (p : MvPolynomial (Fin (m + 2)) K) :
    hyperplaneGradedHom K m p = killLast K m p := rfl

theorem hyperplaneGradedHom_X_castSucc (j : Fin (m + 1)) :
    hyperplaneGradedHom K m (X j.castSucc) = X j := killLast_X_castSucc K m j

theorem hyperplaneGradedHom_X_last : hyperplaneGradedHom K m (X (Fin.last (m + 1))) = 0 :=
  killLast_X_last K m

theorem hyperplaneGradedHom_surjective_degree :
    ∀ n, 0 < n → ∀ y ∈ AlgebraicGeometry.Proj.projectiveGrading K m n,
      ∃ x ∈ AlgebraicGeometry.Proj.projectiveGrading K (m + 1) n, hyperplaneGradedHom K m x = y :=
  fun _ _ y hy => ⟨includeVars K m y, includeVars_mem K m hy, killLast_includeVars K m y⟩

theorem irrelevant_le_map_hyperplaneGradedHom :
    (AlgebraicGeometry.Proj.projectiveGrading K m)₊ ≤ (AlgebraicGeometry.Proj.projectiveGrading K (m + 1))₊.map (hyperplaneGradedHom K m) := by
  apply (HomogeneousIdeal.irrelevant_le _).mpr
  intro n hn p hp
  change p ∈ Ideal.map (hyperplaneGradedHom K m).toRingHom
    (HomogeneousIdeal.irrelevant (AlgebraicGeometry.Proj.projectiveGrading K (m + 1))).toIdeal
  rw [← killLast_includeVars K m p]
  exact Ideal.mem_map_of_mem _
    (HomogeneousIdeal.mem_irrelevant_of_mem _ hn (includeVars_mem K m hp))

/-! ### The kernel of `killLast` is `(x_{m+1})` -/

theorem X_last_dvd_sub_includeVars_killLast (p : MvPolynomial (Fin (m + 2)) K) :
    X (Fin.last (m + 1)) ∣ p - includeVars K m (killLast K m p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [killLast, includeVars]
  | add p q hp hq =>
    have := dvd_add hp hq
    rw [map_add, map_add]
    convert this using 1; ring
  | mul_X p i hp =>
    have h2 : X (Fin.last (m + 1)) ∣ X i - includeVars K m (killLast K m (X i)) := by
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [killLast_X_last, map_zero, sub_zero]
      · rw [killLast_X_castSucc]; simp [includeVars]
    rw [map_mul, map_mul]
    have : p * X i - includeVars K m (killLast K m p) * includeVars K m (killLast K m (X i)) =
        (p - includeVars K m (killLast K m p)) * X i +
          includeVars K m (killLast K m p) * (X i - includeVars K m (killLast K m (X i))) := by ring
    rw [this]
    exact dvd_add (hp.mul_right _) (dvd_mul_of_dvd_right h2 _)

theorem X_last_dvd_of_killLast_eq_zero {p : MvPolynomial (Fin (m + 2)) K} (hp : killLast K m p = 0) :
    X (Fin.last (m + 1)) ∣ p := by
  have := X_last_dvd_sub_includeVars_killLast K m p
  rwa [hp, map_zero, sub_zero] at this

/-- A homogeneous multiple of `x_{m+1}` has a homogeneous quotient (of degree one less). -/
theorem exists_homogeneous_eq_X_last_mul {n : ℕ} {p : MvPolynomial (Fin (m + 2)) K}
    (hp : p ∈ AlgebraicGeometry.Proj.projectiveGrading K (m + 1) n) (hdvd : X (Fin.last (m + 1)) ∣ p) :
    ∃ q ∈ AlgebraicGeometry.Proj.projectiveGrading K (m + 1) (n - 1), p = X (Fin.last (m + 1)) * q := by
  refine ⟨p.divMonomial (Finsupp.single (Fin.last (m + 1)) 1), ?_, ?_⟩
  · change p.IsHomogeneous n at hp
    intro d hd
    rw [coeff_divMonomial] at hd
    have := hp hd
    rw [map_add, Finsupp.weight_single, Pi.one_apply, smul_eq_mul, mul_one] at this
    omega
  · have h0 := X_dvd_iff_modMonomial_eq_zero.mp hdvd
    have := divMonomial_add_modMonomial_single p (Fin.last (m + 1))
    rw [h0, add_zero] at this
    exact this.symm

/-! ### The kernel of `A_{(x_i)} → B_{(φ x_i)}` -/

theorem X_mem_one (i : Fin (m + 2)) : X i ∈ AlgebraicGeometry.Proj.projectiveGrading K (m + 1) 1 :=
  isHomogeneous_X K i

/-- The chart coordinate `x_{m+1}/x_i ∈ A_{(x_i)}`. -/
def coordFraction (i : Fin (m + 2)) : Away (AlgebraicGeometry.Proj.projectiveGrading K (m + 1)) (X i) :=
  Away.mk _ (X_mem_one K m i) 1 (X (Fin.last (m + 1))) (by simpa using X_mem_one K m (Fin.last (m + 1)))

theorem awayMap_coordFraction (i : Fin (m + 2)) :
    Away.map (hyperplaneGradedHom K m) (X i) (coordFraction K m i) = 0 := by
  rw [coordFraction, Away.map_mk]
  apply HomogeneousLocalization.val_injective
  rw [Away.val_mk, HomogeneousLocalization.val_zero, hyperplaneGradedHom_X_last]
  exact Localization.mk_zero _

/-- **The kernel on the chart `D_+(x_i)`** is the principal ideal `(x_{m+1}/x_i)`. -/
theorem ker_awayMap_eq (i : Fin (m + 2)) :
    RingHom.ker (Away.map (hyperplaneGradedHom K m) (X i)) = Ideal.span {coordFraction K m i} := by
  apply le_antisymm
  · intro z hz
    obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective _ (X_mem_one K m i) z
    rw [RingHom.mem_ker, Away.map_mk] at hz
    have hz' := congrArg HomogeneousLocalization.val hz
    rw [Away.val_mk, HomogeneousLocalization.val_zero, Localization.mk_eq_mk',
      IsLocalization.mk'_eq_zero_iff] at hz'
    obtain ⟨⟨c, k, rfl⟩, hc⟩ := hz'
    simp only at hc
    -- `φ (x_i^(k+1) * a) = 0`
    have hker : killLast K m (X i ^ (k + 1) * a) = 0 := by
      rw [map_mul, map_pow, pow_succ, mul_assoc, mul_comm (killLast K m (X i)), ← mul_assoc]
      simp only [hyperplaneGradedHom_apply] at hc
      rw [hc, zero_mul]
    have hmem : X i ^ (k + 1) * a ∈ AlgebraicGeometry.Proj.projectiveGrading K (m + 1) (n + (k + 1)) := by
      have h1 := SetLike.mul_mem_graded (SetLike.pow_mem_graded (k + 1) (X_mem_one K m i)) ha
      have e : (k + 1) • 1 + n • 1 = n + (k + 1) := by simp [add_comm]
      rw [e] at h1
      exact h1
    obtain ⟨q, hq, hEq⟩ := exists_homogeneous_eq_X_last_mul K m hmem (X_last_dvd_of_killLast_eq_zero K m hker)
    have e : n + (k + 1) - 1 = n + k := by omega
    rw [e] at hq
    refine Ideal.mem_span_singleton.mpr ⟨Away.mk _ (X_mem_one K m i) (n + k) q (by simpa using hq), ?_⟩
    apply HomogeneousLocalization.val_injective
    rw [HomogeneousLocalization.val_mul, coordFraction, Away.val_mk, Away.val_mk, Away.val_mk,
      Localization.mk_mul, Localization.mk_eq_mk_iff]
    apply Localization.r_of_eq
    change X i ^ 1 * X i ^ (n + k) * a = X i ^ n * (X (Fin.last (m + 1)) * q)
    rw [← hEq]; ring
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    exact awayMap_coordFraction K m i

end ProjBundleFiberDegreeOne

end
