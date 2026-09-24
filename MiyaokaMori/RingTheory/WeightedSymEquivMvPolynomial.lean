import MiyaokaMori.RingTheory.GradedRing.WeightedSymGrading
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-! # The weighted symmetric algebra of free modules as a weighted polynomial ring

Pure algebra (no geometry): if each `W q` has a basis `b q : Basis (κ q) R (W q)`, then
`Sym_R(⨁_q W_q) ≃ₐ[R] MvPolynomial (Σ q, κ q) R` (Mathlib `SymmetricAlgebra.equivMvPolynomial` applied to the
direct-sum basis `DFinsupp.basis b`), and under this isomorphism the weighted piece `WeightedSym.piece w m`
is exactly the set of weighted-homogeneous polynomials of degree `m` for the weight `⟨q, i⟩ ↦ w q`.

Sources: Mathlib `SymmetricAlgebra.equivMvPolynomial`, `DFinsupp.basis`; the grading comparison is the
standard "monomials of weight m" computation (§2 of the paper: the local basis of the `m`-th piece
is the set of monomials of weight `m`). Used for the local structure of the weighted symmetric
algebra and reusable for the atlas of `weightedSymAffineAlgebra`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u v w' x

open DirectSum

noncomputable section

namespace WeightedSym

variable {R : Type u} [CommRing R] {ι : Type v} [DecidableEq ι] [Fintype ι]
  {W : ι → Type w'} [∀ q, AddCommGroup (W q)] [∀ q, Module R (W q)]
  {κ : ι → Type x} (b : ∀ q, Module.Basis (κ q) R (W q))

/-- The basis of `⨁_q W_q` obtained from bases of the summands (Mathlib `DFinsupp.basis`; `DirectSum` is
`DFinsupp` by definition). -/
def directSumBasis : Module.Basis (Σ q, κ q) R (⨁ q, W q) := DFinsupp.basis b

/-- `Sym_R(⨁_q W_q) ≃ₐ[R] R[X_{q,i}]`, sending the generator `gen q (b q i)` to `X ⟨q, i⟩`. -/
def equivMvPolynomial : SymmetricAlgebra R (⨁ q, W q) ≃ₐ[R] MvPolynomial (Σ q, κ q) R :=
  SymmetricAlgebra.equivMvPolynomial (directSumBasis b)

theorem directSumBasis_apply (q : ι) (i : κ q) :
    directSumBasis b ⟨q, i⟩ = DirectSum.lof R ι W q (b q i) := by
  show (DFinsupp.basis b) ⟨q, i⟩ = DirectSum.lof R ι W q (b q i)
  rw [DFinsupp.basis, Module.Basis.coe_ofRepr]
  simp only [LinearEquiv.trans_symm, LinearEquiv.symm_symm, LinearEquiv.trans_apply]
  rw [DirectSum.lof_eq_of]
  show (DFinsupp.mapRange.linearEquiv fun i => (b i).repr).symm
      (sigmaFinsuppLequivDFinsupp R (Finsupp.single ⟨q, i⟩ 1)) = DFinsupp.single q (b q i)
  rw [DFinsupp.mapRange.linearEquiv_symm]
  show DFinsupp.mapRange (fun i => (b i).repr.symm) (fun i => map_zero _)
      (sigmaFinsuppEquivDFinsupp (Finsupp.single ⟨q, i⟩ 1)) = DFinsupp.single q (b q i)
  rw [sigmaFinsuppEquivDFinsupp_single, DFinsupp.mapRange_single, Module.Basis.repr_symm_single_one]

theorem equivMvPolynomial_gen_basis (q : ι) (i : κ q) :
    equivMvPolynomial b (gen R W q (b q i)) = MvPolynomial.X ⟨q, i⟩ := by
  show equivMvPolynomial b (SymmetricAlgebra.ι R (⨁ p, W p) (DirectSum.lof R ι W q (b q i))) = _
  rw [← directSumBasis_apply b q i]
  exact SymmetricAlgebra.equivMvPolynomial_ι_apply (directSumBasis b) ⟨q, i⟩

theorem equivMvPolynomial_symm_X (q : ι) (i : κ q) :
    (equivMvPolynomial b).symm (MvPolynomial.X ⟨q, i⟩) = gen R W q (b q i) := by
  rw [← equivMvPolynomial_gen_basis b q i, AlgEquiv.symm_apply_apply]

/-- **Weighted pieces = weighted-homogeneous polynomials.** -/
theorem mem_piece_iff_isWeightedHomogeneous (w : ι → ℕ) (m : ℕ) (a : SymmetricAlgebra R (⨁ q, W q)) :
    a ∈ piece R W w m ↔
      (equivMvPolynomial b a).IsWeightedHomogeneous (fun p : Σ q, κ q => w p.1) m := by
  set w' : (Σ q, κ q) → ℕ := fun p => w p.1 with hw'
  set e := equivMvPolynomial b with he
  constructor
  · -- `piece ≤ comap e (weightedHomogeneousSubmodule)` by the induction principle
    intro ha
    let Q : ℕ → Submodule R (SymmetricAlgebra R (⨁ q, W q)) := fun n =>
      (MvPolynomial.weightedHomogeneousSubmodule R w' n).comap e.toLinearMap
    have hQ : ∀ n x, x ∈ Q n ↔ (e x).IsWeightedHomogeneous w' n := fun n x =>
      MvPolynomial.mem_weightedHomogeneousSubmodule R w' n (e x)
    have h1 : (1 : SymmetricAlgebra R (⨁ q, W q)) ∈ Q 0 := by
      rw [hQ, map_one]; exact MvPolynomial.isWeightedHomogeneous_one R w'
    have hmul : ∀ i j, Q i * Q j ≤ Q (i + j) := fun i j =>
      Submodule.mul_le.mpr fun x hx y hy => by
        rw [hQ] at hx hy ⊢; rw [map_mul]; exact hx.mul hy
    have hgen : ∀ q, genSpan R W q ≤ Q (w q) := by
      intro q
      have hspan : genSpan R W q = Submodule.span R (Set.range fun i : κ q => gen R W q (b q i)) := by
        rw [genSpan, LinearMap.range_eq_map, ← (b q).span_eq, Submodule.map_span, ← Set.range_comp]
        rfl
      rw [hspan, Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      show gen R W q (b q i) ∈ Q (w q)
      rw [hQ, equivMvPolynomial_gen_basis]
      exact MvPolynomial.isWeightedHomogeneous_X R w' ⟨q, i⟩
    exact (hQ m a).mp (piece_le_of_gen h1 hmul hgen m ha)
  · -- every weighted-homogeneous polynomial of degree `m` comes from `piece m`
    intro ha
    suffices key : ∀ (p : MvPolynomial (Σ q, κ q) R), p.IsWeightedHomogeneous w' m →
        e.symm p ∈ piece R W w m by
      have := key (e a) ha
      rwa [AlgEquiv.symm_apply_apply] at this
    intro p hp
    induction hp using MvPolynomial.IsWeightedHomogeneous.induction_on with
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add p q _ _ ihp ihq => rw [map_add]; exact Submodule.add_mem _ ihp ihq
    | monomial d c hd =>
      rw [MvPolynomial.monomial_eq, map_mul, ← MvPolynomial.algebraMap_eq, AlgEquiv.commutes,
        ← Algebra.smul_def]
      refine Submodule.smul_mem _ c ?_
      rw [Finsupp.prod, map_prod]
      simp only [map_pow]
      have hd' : m = ∑ p ∈ d.support, d p • w p.1 := by
        rw [← hd, Finsupp.weight_apply, Finsupp.sum]
      rw [hd']
      refine SetLike.prod_pow_mem_graded (piece R W w) (fun p : Σ q, κ q => w p.1)
        (fun p => e.symm (MvPolynomial.X p)) (fun p => d p) ?_
      rintro ⟨q, i⟩ -
      rw [equivMvPolynomial_symm_X]
      exact gen_mem_piece w q (b q i)

end WeightedSym

end
