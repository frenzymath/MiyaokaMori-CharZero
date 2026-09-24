import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import Mathlib.RingTheory.GradedAlgebra.Basic

/-!
# The natural grading on the actual symmetric algebra

The degree `n` part is the `n`-th power of the image of the canonical linear map into
`SymmetricAlgebra R M`. The symmetric algebra universal property sends each generator to
degree one in the direct sum of these submodules. Induction on submodule powers proves
that this map and the canonical summation map are inverse, giving the actual grading.

This is the algebraic grading needed for the construction `Proj Sym (O ⊕ L∨) = P_lines (O ⊕ L)`
(the ruled surface of the paper). It does not construct a sheaf, relative Proj, a ruling, or its zero section.

The direct-sum proof follows Mathlib's `TensorAlgebra.Grading` construction, with the
universal property of the commutative symmetric algebra and the corresponding actual
commutative direct-sum algebra. No grading is assumed as input.
-/

noncomputable section

open scoped DirectSum

namespace MiyaokaMori.RingTheory.RuledSurfaceAlgebra

universe u v w

variable (R : Type u) (M : Type v) [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- The actual homogeneous submodule of degree `n` in the symmetric algebra. -/
def symmetricPiece (n : ℕ) : Submodule R (SymmetricAlgebra R M) :=
  (LinearMap.range (SymmetricAlgebra.ι R M)) ^ n

/-- Multiplication adds degrees because these submodules are powers of the generator image. -/
instance symmetricPiece_gradedMonoid : SetLike.GradedMonoid (symmetricPiece R M) :=
  Submodule.nat_power_gradedMonoid (LinearMap.range (SymmetricAlgebra.ι R M))

/-- Each canonical module generator belongs to the degree-one part. -/
theorem symmetric_ι_mem (m : M) : SymmetricAlgebra.ι R M m ∈ symmetricPiece R M 1 := by
  simpa only [symmetricPiece, pow_one] using LinearMap.mem_range_self (SymmetricAlgebra.ι R M) m

/-- Each actual coefficient belongs to the degree-zero part. -/
theorem symmetric_algebraMap_mem (r : R) :
    algebraMap R (SymmetricAlgebra R M) r ∈ symmetricPiece R M 0 := by
  simpa only [symmetricPiece, pow_zero] using
    (Submodule.algebraMap_mem r : algebraMap R (SymmetricAlgebra R M) r ∈ (1 : Submodule R _))

/-- The canonical generator map with its image placed in degree one of the direct sum. -/
def symmetricGradedInclusion : M →ₗ[R] ⨁ n : ℕ, symmetricPiece R M n :=
  DirectSum.lof R ℕ (fun n ↦ ↥(symmetricPiece R M n)) 1 ∘ₗ
    (SymmetricAlgebra.ι R M).codRestrict _ (symmetric_ι_mem R M)

/-- Evaluation of the generator map in the direct sum. -/
theorem symmetricGradedInclusion_apply (m : M) :
    symmetricGradedInclusion R M m =
      DirectSum.of (fun n : ℕ ↦ ↥(symmetricPiece R M n)) 1
        ⟨SymmetricAlgebra.ι R M m, symmetric_ι_mem R M m⟩ := rfl

/-- The symmetric algebra universal property produces the homogeneous decomposition map. -/
def symmetricDecomposition :
    SymmetricAlgebra R M →ₐ[R] ⨁ n : ℕ, symmetricPiece R M n :=
  SymmetricAlgebra.lift (symmetricGradedInclusion R M)

/-- A homogeneous element is sent to precisely its degree in the direct sum. -/
theorem symmetricDecomposition_on_piece (n : ℕ) (x : symmetricPiece R M n) :
    symmetricDecomposition R M (x : SymmetricAlgebra R M) =
      DirectSum.of (fun n : ℕ ↦ ↥(symmetricPiece R M n)) n x := by
  obtain ⟨x, hx⟩ := x
  change x ∈ (LinearMap.range (SymmetricAlgebra.ι R M)) ^ n at hx
  dsimp only [Subtype.coe_mk, DirectSum.lof_eq_of]
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap r =>
    rw [AlgHom.commutes, DirectSum.algebraMap_apply]
    rfl
  | add x y n hx hy ihx ihy =>
    rw [map_add, ihx, ihy, ← map_add]
    rfl
  | mem_mul m hm n x hx ih =>
    obtain ⟨m, rfl⟩ := hm
    rw [map_mul, ih, symmetricDecomposition, SymmetricAlgebra.lift_ι_apply,
      symmetricGradedInclusion_apply, DirectSum.of_mul_of]
    exact DirectSum.of_eq_of_gradedMonoid_eq (Sigma.subtype_ext (add_comm _ _) rfl)

/-- The natural-number grading of the same symmetric algebra, with an actual decomposition. -/
instance symmetricGrading : GradedAlgebra (symmetricPiece R M) :=
  GradedAlgebra.ofAlgHom _ (symmetricDecomposition R M)
    (by
      apply SymmetricAlgebra.algHom_ext
      ext m
      show (DirectSum.coeAlgHom (symmetricPiece R M))
          (symmetricDecomposition R M (SymmetricAlgebra.ι R M m)) =
        SymmetricAlgebra.ι R M m
      rw [symmetricDecomposition, SymmetricAlgebra.lift_ι_apply,
        symmetricGradedInclusion_apply, DirectSum.coeAlgHom_of])
    (symmetricDecomposition_on_piece R M)

/-- The decomposition places a canonical module generator entirely in degree one. -/
@[simp]
theorem symmetricDecomposition_ι (m : M) :
    symmetricDecomposition R M (SymmetricAlgebra.ι R M m) =
      DirectSum.of (fun n : ℕ ↦ ↥(symmetricPiece R M n)) 1
        ⟨SymmetricAlgebra.ι R M m, symmetric_ι_mem R M m⟩ :=
  symmetricDecomposition_on_piece R M 1 ⟨_, symmetric_ι_mem R M m⟩

/-- The decomposition places an actual coefficient entirely in degree zero. -/
@[simp]
theorem symmetricDecomposition_algebraMap (r : R) :
    symmetricDecomposition R M (algebraMap R (SymmetricAlgebra R M) r) =
      DirectSum.of (fun n : ℕ ↦ ↥(symmetricPiece R M n)) 0
        ⟨algebraMap R (SymmetricAlgebra R M) r, symmetric_algebraMap_mem R M r⟩ :=
  symmetricDecomposition_on_piece R M 0 ⟨_, symmetric_algebraMap_mem R M r⟩

variable {R M} {N : Type w} [AddCommMonoid N] [Module R N]

/-- The actual symmetric-algebra map induced by a linear map preserves every degree.

The map is written as the existing universal lift, without introducing a second functor. -/
theorem symmetric_lift_linearMap_mem (f : M →ₗ[R] N) {n : ℕ}
    {x : SymmetricAlgebra R M} (hx : x ∈ symmetricPiece R M n) :
    SymmetricAlgebra.lift ((SymmetricAlgebra.ι R N).comp f) x ∈ symmetricPiece R N n := by
  change x ∈ (LinearMap.range (SymmetricAlgebra.ι R M)) ^ n at hx
  induction hx using Submodule.pow_induction_on_left' with
  | algebraMap r =>
    rw [AlgHom.commutes]
    exact symmetric_algebraMap_mem R N r
  | add x y n hx hy ihx ihy =>
    rw [map_add]
    exact (symmetricPiece R N n).add_mem ihx ihy
  | mem_mul m hm n x hx ih =>
    obtain ⟨m, rfl⟩ := hm
    rw [map_mul, SymmetricAlgebra.lift_ι_apply, LinearMap.comp_apply]
    change _ ∈ (LinearMap.range (SymmetricAlgebra.ι R N)) ^ n.succ
    rw [pow_succ']
    exact Submodule.mul_mem_mul (LinearMap.mem_range_self _ (f m)) ih

end MiyaokaMori.RingTheory.RuledSurfaceAlgebra
