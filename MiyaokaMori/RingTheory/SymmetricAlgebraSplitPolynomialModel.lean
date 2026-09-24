import MiyaokaMori.Prelude
import MiyaokaMori.RingTheory.GradedRing.SymmetricAlgebraGrading

/-! # The symmetric algebra of a split module `R·T ⊕ N` as a polynomial ring

**The symmetric algebra of `R·T ⊕ N` is the polynomial ring `Sym(N)[X]`** (pure commutative algebra; Bourbaki
Algebra III §6 no. 6, Prop. 9: `Sym(M ⊕ N) = Sym(M) ⊗ Sym(N)`, with `Sym(R) = R[X]`).

The shared algebraic core of the affineness of the total space of a line bundle over the base
(`toProjBundle_awayMap_bijective`, `mem_range_lSection_of_not_mem_basicOpen_oCoordinate`,
`zeroSection_toProjBundle_pieces`): there `M = Γ(W, (O ⊕ L)^∨) = R·T ⊕ Γ(W, L^∨)` with `T` the `O`-coordinate,
`Sym_R M = A(W)` (`symGradedAlgebra.symLiftHom_bijective`) and `Sym_R N = Sym(L^∨)(W) = Γ(p⁻¹W, O_Tot)`.

## Data
A `ModuleSplitting R M N` is a splitting `M = R·T ⊕ N`: linear maps `pr : M → R`, `q : M → N`, `s : N → M`, an element
`T : M`, with `pr T = 1`, `q T = 0`, `q ∘ s = id`, `pr ∘ s = 0` and `m = pr m • T + s (q m)` for all `m`.

## Statements
* `toPoly : Sym_R M →ₐ[R] (Sym_R N)[X]`, `ι m ↦ C (ι (q m)) + pr m • X` (universal property of `Sym`);
* `ofPoly : (Sym_R N)[X] →ₐ[R] Sym_R M`, `X ↦ ι T`, `C (ι n) ↦ ι (s n)` (`Polynomial.eval₂AlgHom` of `Sym.lift (ι ∘ s)`);
* they are inverse to each other (`ofPoly_toPoly`, `toPoly_ofPoly`: check on generators, `SymmetricAlgebra.algHom_ext`
  and `Polynomial.algHom_ext'`), giving the algebra isomorphism `toPolyEquiv`;
* **gradedness** (`toPoly_mem_of_mem_symmetricPiece`): `toPoly` sends the standard degree-`k` piece
  `symmetricPiece R M k = (range ι)^k` into the polynomials `p` with `p.coeff j ∈ symmetricPiece R N (k - j)` and
  `p.coeff j = 0` for `j > k` (`IsHomogPoly k`), by `Submodule.pow_induction_on_left'` (multiplying by
  `toPoly (ι m) = C (ι (q m)) + pr m • X` raises the degree by one);
* **evaluation at `X = 1`**: `evalOne := eval 1 ∘ toPoly : Sym_R M →+* Sym_R N` is surjective
  (`evalOne_surjective`: `C b` is hit by `ofPoly (C b)`) and injective on every `symmetricPiece R M k`
  (`eq_zero_of_mem_symmetricPiece_of_evalOne_eq_zero`: a polynomial in `IsHomogPoly k` whose coefficients sum to zero
  is zero, because its coefficients are homogeneous of pairwise distinct degrees `k - j` in the graded ring `Sym_R N`;
  `IsHomogPoly.eq_zero_of_eval_one_eq_zero`).
* `ringHom_ext_of_algebraMap_of_ι`: two ring homomorphisms out of `Sym_R M` agreeing on `algebraMap` and on `ι` are equal
  (`SymmetricAlgebra.induction`).

Edge cases: `R = 0` (everything is the zero ring); `N = 0` (`Sym_R M = R[X]`); `M = R·T` (`N = 0`, `q = 0`, `s = 0`).
The hypotheses of `ModuleSplitting` are exactly those satisfied by the projections/inclusions of a biproduct
`R ⊕ N`; no finiteness or freeness is assumed. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w

open Polynomial

noncomputable section

namespace SymmetricAlgebra

/-- A splitting `M = R·T ⊕ N` of an `R`-module, given by the projections `pr : M → R`, `q : M → N`, the element
`T = (1, 0)` and the inclusion `s : N → M`. -/
structure ModuleSplitting (R : Type u) (M : Type v) (N : Type w) [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] where
  /-- the `R`-coordinate -/
  pr : M →ₗ[R] R
  /-- the projection to `N` -/
  q : M →ₗ[R] N
  /-- the element `(1, 0)` -/
  T : M
  /-- the inclusion of `N` -/
  s : N →ₗ[R] M
  pr_T : pr T = 1
  q_T : q T = 0
  q_s : ∀ n, q (s n) = n
  pr_s : ∀ n, pr (s n) = 0
  eq_smul_add : ∀ m, m = pr m • T + s (q m)

namespace ModuleSplitting

variable {R : Type u} {M : Type v} {N : Type w} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] (D : ModuleSplitting R M N)

/-- The `R`-linear map `M → (Sym_R N)[X]`, `m ↦ C (ι (q m)) + pr m • X`. -/
def toPolyLinear : M →ₗ[R] (SymmetricAlgebra R N)[X] where
  toFun m := Polynomial.C (SymmetricAlgebra.ι R N (D.q m)) + D.pr m • (Polynomial.X : (SymmetricAlgebra R N)[X])
  map_add' m m' := by
    rw [map_add, map_add, map_add, map_add, add_smul]
    abel
  map_smul' r m := by
    rw [RingHom.id_apply, LinearMap.map_smul, LinearMap.map_smul, LinearMap.map_smul, smul_eq_mul, mul_smul,
      smul_add, Polynomial.smul_C]

theorem toPolyLinear_apply (m : M) :
    D.toPolyLinear m =
      Polynomial.C (SymmetricAlgebra.ι R N (D.q m)) + D.pr m • (Polynomial.X : (SymmetricAlgebra R N)[X]) := rfl

/-- `toPoly : Sym_R M → (Sym_R N)[X]`, `ι m ↦ C (ι (q m)) + pr m • X`. -/
def toPoly : SymmetricAlgebra R M →ₐ[R] (SymmetricAlgebra R N)[X] :=
  SymmetricAlgebra.lift D.toPolyLinear

theorem toPoly_ι (m : M) :
    D.toPoly (SymmetricAlgebra.ι R M m) =
      Polynomial.C (SymmetricAlgebra.ι R N (D.q m)) + D.pr m • (Polynomial.X : (SymmetricAlgebra R N)[X]) :=
  SymmetricAlgebra.lift_ι_apply _ m

theorem toPoly_algebraMap (r : R) :
    D.toPoly (algebraMap R (SymmetricAlgebra R M) r) = Polynomial.C (algebraMap R (SymmetricAlgebra R N) r) :=
  D.toPoly.commutes r

/-- `Sym_R N → Sym_R M`, `ι n ↦ ι (s n)`. -/
def ofPolyCoeff : SymmetricAlgebra R N →ₐ[R] SymmetricAlgebra R M :=
  SymmetricAlgebra.lift ((SymmetricAlgebra.ι R M).comp D.s)

theorem ofPolyCoeff_ι (n : N) : D.ofPolyCoeff (SymmetricAlgebra.ι R N n) = SymmetricAlgebra.ι R M (D.s n) :=
  SymmetricAlgebra.lift_ι_apply _ n

/-- `ofPoly : (Sym_R N)[X] → Sym_R M`, `X ↦ ι T`, `C (ι n) ↦ ι (s n)`. -/
def ofPoly : (SymmetricAlgebra R N)[X] →ₐ[R] SymmetricAlgebra R M :=
  Polynomial.eval₂AlgHom D.ofPolyCoeff (SymmetricAlgebra.ι R M D.T) (fun _ => Commute.all _ _)

theorem ofPoly_apply (p : (SymmetricAlgebra R N)[X]) :
    D.ofPoly p = p.eval₂ (D.ofPolyCoeff : SymmetricAlgebra R N →+* SymmetricAlgebra R M)
      (SymmetricAlgebra.ι R M D.T) := rfl

theorem ofPoly_C (b : SymmetricAlgebra R N) : D.ofPoly (Polynomial.C b) = D.ofPolyCoeff b := by
  rw [ofPoly_apply, Polynomial.eval₂_C]
  rfl

theorem ofPoly_X : D.ofPoly Polynomial.X = SymmetricAlgebra.ι R M D.T := by
  rw [ofPoly_apply, Polynomial.eval₂_X]

theorem ofPoly_toPoly : D.ofPoly.comp D.toPoly = AlgHom.id R (SymmetricAlgebra R M) := by
  refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun m => ?_)
  show D.ofPoly (D.toPoly (SymmetricAlgebra.ι R M m)) = SymmetricAlgebra.ι R M m
  rw [toPoly_ι, map_add, map_smul, ofPoly_C, ofPoly_X, ofPolyCoeff_ι, ← map_smul, ← map_add,
    add_comm, ← D.eq_smul_add m]

theorem toPoly_ofPoly : D.toPoly.comp D.ofPoly = AlgHom.id R (SymmetricAlgebra R N)[X] := by
  refine Polynomial.algHom_ext' ?_ ?_
  · refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun n => ?_)
    show D.toPoly (D.ofPoly (Polynomial.C (SymmetricAlgebra.ι R N n))) = Polynomial.C (SymmetricAlgebra.ι R N n)
    rw [ofPoly_C, ofPolyCoeff_ι, toPoly_ι, D.q_s, D.pr_s, zero_smul, add_zero]
  · show D.toPoly (D.ofPoly Polynomial.X) = Polynomial.X
    rw [ofPoly_X, toPoly_ι, D.q_T, D.pr_T, one_smul, map_zero, map_zero, zero_add]

/-- **`Sym_R M ≅ (Sym_R N)[X]`** as `R`-algebras. -/
def toPolyEquiv : SymmetricAlgebra R M ≃ₐ[R] (SymmetricAlgebra R N)[X] :=
  AlgEquiv.ofAlgHom D.toPoly D.ofPoly D.toPoly_ofPoly D.ofPoly_toPoly

theorem toPolyEquiv_apply (a : SymmetricAlgebra R M) : D.toPolyEquiv a = D.toPoly a := rfl

theorem toPolyEquiv_symm_apply (p : (SymmetricAlgebra R N)[X]) : D.toPolyEquiv.symm p = D.ofPoly p := rfl

theorem toPoly_injective : Function.Injective D.toPoly := D.toPolyEquiv.injective

/-- Two ring homomorphisms out of `Sym_R M` agreeing on `algebraMap` and on `ι` are equal. -/
theorem ringHom_ext_of_algebraMap_of_ι {C : Type*} [Semiring C] {f g : SymmetricAlgebra R M →+* C}
    (h0 : ∀ r, f (algebraMap R _ r) = g (algebraMap R _ r)) (h1 : ∀ m, f (SymmetricAlgebra.ι R M m) = g (SymmetricAlgebra.ι R M m)) :
    f = g := by
  refine RingHom.ext fun a => ?_
  induction a using SymmetricAlgebra.induction with
  | algebraMap r => exact h0 r
  | ι m => exact h1 m
  | mul a b ha hb => rw [map_mul, map_mul, ha, hb]
  | add a b ha hb => rw [map_add, map_add, ha, hb]

/-! ## Gradedness -/

/-- A polynomial over the graded ring `Sym_R N` is *homogeneous of total degree `k`* (with `X` in degree one) if its
`j`-th coefficient lies in the degree-`(k - j)` piece and vanishes for `j > k`. -/
def IsHomogPoly (k : ℕ) (p : (SymmetricAlgebra R N)[X]) : Prop :=
  ∀ j, p.coeff j ∈ MiyaokaMori.RingTheory.RuledSurfaceAlgebra.symmetricPiece R N (k - j) ∧ (k < j → p.coeff j = 0)

omit D in
theorem IsHomogPoly.add {k : ℕ} {p p' : (SymmetricAlgebra R N)[X]} (hp : IsHomogPoly k p) (hp' : IsHomogPoly k p') :
    IsHomogPoly k (p + p') := fun j => by
  rw [Polynomial.coeff_add]
  exact ⟨add_mem (hp j).1 (hp' j).1, fun hj => by rw [(hp j).2 hj, (hp' j).2 hj, add_zero]⟩

omit D in
theorem IsHomogPoly.smul {k : ℕ} (r : R) {p : (SymmetricAlgebra R N)[X]} (hp : IsHomogPoly k p) :
    IsHomogPoly k (r • p) := fun j => by
  rw [Polynomial.coeff_smul]
  exact ⟨Submodule.smul_mem _ r (hp j).1, fun hj => by rw [(hp j).2 hj, smul_zero]⟩

omit D in
theorem IsHomogPoly.C_algebraMap (r : R) : IsHomogPoly 0 (Polynomial.C (algebraMap R (SymmetricAlgebra R N) r)) := by
  intro j
  rw [Polynomial.coeff_C]
  split_ifs with hj
  · subst hj
    exact ⟨MiyaokaMori.RingTheory.RuledSurfaceAlgebra.symmetric_algebraMap_mem R N r, fun h => absurd h (lt_irrefl 0)⟩
  · exact ⟨zero_mem _, fun _ => rfl⟩

omit D in
theorem IsHomogPoly.X_mul {k : ℕ} {p : (SymmetricAlgebra R N)[X]} (hp : IsHomogPoly k p) :
    IsHomogPoly (k + 1) (Polynomial.X * p) := by
  intro j
  cases j with
  | zero =>
    rw [Polynomial.coeff_X_mul_zero]
    exact ⟨zero_mem _, fun _ => rfl⟩
  | succ j =>
    rw [Polynomial.coeff_X_mul]
    refine ⟨?_, fun hj => (hp j).2 (Nat.lt_of_succ_lt_succ hj)⟩
    have : k + 1 - (j + 1) = k - j := Nat.add_sub_add_right k 1 j
    rw [this]
    exact (hp j).1

omit D in
theorem IsHomogPoly.C_ι_mul {k : ℕ} (n : N) {p : (SymmetricAlgebra R N)[X]} (hp : IsHomogPoly k p) :
    IsHomogPoly (k + 1) (Polynomial.C (SymmetricAlgebra.ι R N n) * p) := by
  intro j
  rw [Polynomial.coeff_C_mul]
  refine ⟨?_, fun hj => by rw [(hp j).2 (lt_of_le_of_lt (Nat.le_succ k) hj), mul_zero]⟩
  by_cases hj : j ≤ k
  · have h1 := SetLike.mul_mem_graded (MiyaokaMori.RingTheory.RuledSurfaceAlgebra.symmetric_ι_mem R N n) (hp j).1
    have : 1 + (k - j) = k + 1 - j := by omega
    rwa [this] at h1
  · rw [(hp j).2 (lt_of_not_ge hj), mul_zero]
    exact zero_mem _

/-- **`toPoly` respects the gradings**: the standard degree-`k` piece of `Sym_R M` goes to polynomials homogeneous of
total degree `k`. -/
theorem toPoly_mem_of_mem_symmetricPiece {k : ℕ} {a : SymmetricAlgebra R M}
    (ha : a ∈ MiyaokaMori.RingTheory.RuledSurfaceAlgebra.symmetricPiece R M k) : IsHomogPoly k (D.toPoly a) := by
  change a ∈ (LinearMap.range (SymmetricAlgebra.ι R M)) ^ k at ha
  induction ha using Submodule.pow_induction_on_left' with
  | algebraMap r =>
    rw [toPoly_algebraMap]
    exact IsHomogPoly.C_algebraMap r
  | add x y i _ _ hx hy =>
    rw [map_add]
    exact hx.add hy
  | mem_mul m hm i x _ hx =>
    obtain ⟨m, rfl⟩ := hm
    rw [map_mul, toPoly_ι, add_mul, smul_mul_assoc]
    exact (hx.C_ι_mul (D.q m)).add ((hx.X_mul).smul (D.pr m))

omit D in
/-- A polynomial homogeneous of total degree `k` whose coefficients sum to zero is zero (the coefficients are
homogeneous of pairwise distinct degrees `k - j` in the graded ring `Sym_R N`). -/
theorem IsHomogPoly.eq_zero_of_eval_one_eq_zero {k : ℕ} {p : (SymmetricAlgebra R N)[X]} (hp : IsHomogPoly k p)
    (h : p.eval 1 = 0) : p = 0 := by
  classical
  set ℳ := MiyaokaMori.RingTheory.RuledSurfaceAlgebra.symmetricPiece R N with hℳ
  have hdeg : p.natDegree < k + 1 :=
    Nat.lt_succ_of_le (Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun j hj => (hp j).2 hj)
  rw [Polynomial.eval_eq_sum_range' hdeg] at h
  simp only [one_pow, mul_one] at h
  -- extract the coefficient of index `j₀ ≤ k` by decomposing in degree `k - j₀`
  have hcoeff : ∀ j₀, j₀ ≤ k → p.coeff j₀ = 0 := by
    intro j₀ hj₀
    have h1 := congrArg (fun b => (DirectSum.decompose ℳ b (k - j₀) : SymmetricAlgebra R N)) h
    simp only [DirectSum.decompose_zero, DirectSum.zero_apply, ZeroMemClass.coe_zero] at h1
    rw [DirectSum.decompose_sum, DirectSum.sum_apply, AddSubmonoidClass.coe_finsetSum] at h1
    rw [Finset.sum_eq_single j₀ (fun j _ hj => ?_) (fun hj => absurd (Finset.mem_range.mpr (Nat.lt_succ_of_le hj₀)) hj)] at h1
    · rwa [DirectSum.decompose_of_mem_same ℳ (hp j₀).1] at h1
    · by_cases hjk : j ≤ k
      · exact DirectSum.decompose_of_mem_ne ℳ (hp j).1 (fun e => hj (by omega))
      · rw [(hp j).2 (lt_of_not_ge hjk), DirectSum.decompose_zero, DirectSum.zero_apply, ZeroMemClass.coe_zero]
  refine Polynomial.ext fun j => ?_
  rw [Polynomial.coeff_zero]
  by_cases hj : j ≤ k
  · exact hcoeff j hj
  · exact (hp j).2 (lt_of_not_ge hj)

/-! ## Evaluation at `X = 1` -/

/-- `evalOne : Sym_R M → Sym_R N`, `a ↦ (toPoly a).eval 1`; on generators `ι m ↦ ι (q m) + algebraMap (pr m)`. -/
def evalOne : SymmetricAlgebra R M →+* SymmetricAlgebra R N :=
  (Polynomial.evalRingHom (1 : SymmetricAlgebra R N)).comp D.toPoly.toRingHom

theorem evalOne_apply (a : SymmetricAlgebra R M) : D.evalOne a = (D.toPoly a).eval 1 := rfl

theorem evalOne_ι (m : M) :
    D.evalOne (SymmetricAlgebra.ι R M m) = SymmetricAlgebra.ι R N (D.q m) + algebraMap R (SymmetricAlgebra R N) (D.pr m) := by
  rw [evalOne_apply, toPoly_ι, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_smul, Polynomial.eval_X,
    Algebra.smul_def, mul_one]

theorem evalOne_algebraMap (r : R) :
    D.evalOne (algebraMap R (SymmetricAlgebra R M) r) = algebraMap R (SymmetricAlgebra R N) r := by
  rw [evalOne_apply, toPoly_algebraMap, Polynomial.eval_C]

theorem evalOne_ι_T : D.evalOne (SymmetricAlgebra.ι R M D.T) = 1 := by
  rw [evalOne_ι, D.q_T, D.pr_T, map_zero, map_one, zero_add]

theorem evalOne_ι_s (n : N) : D.evalOne (SymmetricAlgebra.ι R M (D.s n)) = SymmetricAlgebra.ι R N n := by
  rw [evalOne_ι, D.q_s, D.pr_s, map_zero, add_zero]

/-- `evalOne` is surjective (`C b` is `toPoly (ofPoly (C b))`). -/
theorem evalOne_surjective : Function.Surjective D.evalOne := by
  intro b
  refine ⟨D.ofPoly (Polynomial.C b), ?_⟩
  rw [evalOne_apply]
  have : D.toPoly (D.ofPoly (Polynomial.C b)) = Polynomial.C b :=
    congrArg (fun F : (SymmetricAlgebra R N)[X] →ₐ[R] (SymmetricAlgebra R N)[X] => F (Polynomial.C b)) D.toPoly_ofPoly
  rw [this, Polynomial.eval_C]

/-- `evalOne` is injective on every standard homogeneous piece of `Sym_R M`. -/
theorem eq_zero_of_mem_symmetricPiece_of_evalOne_eq_zero {k : ℕ} {a : SymmetricAlgebra R M}
    (ha : a ∈ MiyaokaMori.RingTheory.RuledSurfaceAlgebra.symmetricPiece R M k) (h : D.evalOne a = 0) : a = 0 := by
  have hp : D.toPoly a = 0 := (D.toPoly_mem_of_mem_symmetricPiece ha).eq_zero_of_eval_one_eq_zero h
  exact D.toPoly_injective (hp.trans (map_zero _).symm)

end ModuleSplitting

end SymmetricAlgebra

end
