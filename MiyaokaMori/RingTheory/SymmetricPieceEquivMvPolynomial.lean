import MiyaokaMori.RingTheory.GradedRing.SymmetricAlgebraGrading
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-! # The graded pieces of the symmetric algebra of a free module as homogeneous polynomials

Pure algebra (no geometry): if `M` has a basis `b : Basis κ R M`, then under Mathlib's
`SymmetricAlgebra.equivMvPolynomial b : Sym_R M ≃ₐ[R] MvPolynomial κ R` the standard degree-`m` piece
`MiyaokaMori.RingTheory.RuledSurfaceAlgebra.symmetricPiece R M m = (range ι)^m` is exactly the set of homogeneous
polynomials of degree `m`, phrased as weighted-homogeneous for the constant weight `1` (the form the
`WeightedPolynomialAtlas` wants).

Source: Bourbaki Algebra III §6 no. 6 (the symmetric algebra of a free module is the polynomial algebra,
`Sym^m` = homogeneous polynomials of degree `m`); Mathlib `SymmetricAlgebra.equivMvPolynomial`.
Unweighted analogue of `WeightedSym.mem_piece_iff_isWeightedHomogeneous` (module
`WeightedSymEquivMvPolynomial`), same proof.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u v x

noncomputable section

namespace MiyaokaMori.RingTheory.RuledSurfaceAlgebra

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M]
  {κ : Type x} (b : Module.Basis κ R M)

/-- The image of a degree-one generator is a homogeneous polynomial of degree `1`. -/
theorem equivMvPolynomial_ι_isWeightedHomogeneous (v : M) :
    (SymmetricAlgebra.equivMvPolynomial b (SymmetricAlgebra.ι R M v)).IsWeightedHomogeneous
      (fun _ : κ => 1) 1 := by
  set w' : κ → ℕ := fun _ => 1 with hw'
  have hv : v ∈ Submodule.span R (Set.range b) := by rw [b.span_eq]; exact Submodule.mem_top
  have hle : Submodule.span R (Set.range b) ≤
      (MvPolynomial.weightedHomogeneousSubmodule R w' 1).comap
        ((SymmetricAlgebra.equivMvPolynomial b).toLinearMap ∘ₗ SymmetricAlgebra.ι R M) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    show (SymmetricAlgebra.equivMvPolynomial b (SymmetricAlgebra.ι R M (b i))).IsWeightedHomogeneous w' 1
    rw [SymmetricAlgebra.equivMvPolynomial_ι_apply]
    exact MvPolynomial.isWeightedHomogeneous_X R w' i
  exact (MvPolynomial.mem_weightedHomogeneousSubmodule R w' 1 _).mp (hle hv)

/-- **Standard pieces = homogeneous polynomials.** `a ∈ Sym^m M` iff its image in `R[X_κ]` is
(weighted-, for the constant weight `1`) homogeneous of degree `m`. -/
theorem mem_symmetricPiece_iff_isWeightedHomogeneous (m : ℕ) (a : SymmetricAlgebra R M) :
    a ∈ symmetricPiece R M m ↔
      (SymmetricAlgebra.equivMvPolynomial b a).IsWeightedHomogeneous (fun _ : κ => 1) m := by
  set w' : κ → ℕ := fun _ => 1 with hw'
  set e := SymmetricAlgebra.equivMvPolynomial b with he
  constructor
  · intro ha
    change a ∈ (LinearMap.range (SymmetricAlgebra.ι R M)) ^ m at ha
    induction ha using Submodule.pow_induction_on_left' with
    | algebraMap r =>
      rw [AlgEquiv.commutes, MvPolynomial.algebraMap_eq]
      exact MvPolynomial.isWeightedHomogeneous_C w' r
    | add x y n _ _ ihx ihy =>
      rw [map_add]; exact ihx.add ihy
    | mem_mul x hx n y _ ih =>
      obtain ⟨v, rfl⟩ := hx
      rw [map_mul]
      have := (equivMvPolynomial_ι_isWeightedHomogeneous b v).mul ih
      rwa [add_comm] at this
  · intro ha
    suffices key : ∀ (p : MvPolynomial κ R), p.IsWeightedHomogeneous w' m →
        e.symm p ∈ symmetricPiece R M m by
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
      have hd' : m = ∑ p ∈ d.support, d p • w' p := by
        rw [← hd, Finsupp.weight_apply, Finsupp.sum]
      rw [hd']
      refine SetLike.prod_pow_mem_graded (symmetricPiece R M) w'
        (fun p => e.symm (MvPolynomial.X p)) (fun p => d p) ?_
      intro i _
      rw [he, SymmetricAlgebra.equivMvPolynomial_symm_X]
      exact symmetric_ι_mem R M (b i)

end MiyaokaMori.RingTheory.RuledSurfaceAlgebra

end
