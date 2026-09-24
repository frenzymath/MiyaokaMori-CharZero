import MiyaokaMori.Prelude

/-! # Ring homomorphisms out of a graded algebra given by monomials

(Auxiliary to the weight components of a local jet, §3 of the paper.)

Let `A = ⊕_i 𝒜 i` be a graded commutative ring (`GradedAlgebra 𝒜`), `ψ : A →+* R` a ring map and
`M : ι → R` a "monomial family": `M 0 = 1`, `M (i + j) = M i * M j`. Then `z ↦ ψ z * M i` for `z ∈ 𝒜 i`
extends (uniquely) to a ring homomorphism `A →+* R` (`GradedAlgebra.monomialHom`), namely
`DirectSum.toSemiring` on the decomposition. This is the map "`Φ₂ : y ↦ Σ_n φ(y_n) · 𝔪^n`",
with `M n = 𝔪^n` the powers of the tautological linear function of a frame.
-/
set_option autoImplicit false

universe u v w

noncomputable section

namespace GradedAlgebra

variable {ι : Type u} [AddMonoid ι] [DecidableEq ι] {S : Type v} {A : Type w} [CommSemiring S]
  [CommRing A] [Algebra S A] (𝒜 : ι → Submodule S A) [GradedAlgebra 𝒜]
  {R : Type*} [CommRing R] (ψ : A →+* R) (M : ι → R) (hM0 : M 0 = 1)
  (hMadd : ∀ i j : ι, M (i + j) = M i * M j)

/-- The additive map `𝒜 i → R`, `z ↦ ψ z * M i`. -/
def monomialPiece (i : ι) : 𝒜 i →+ R :=
  (AddMonoidHom.mulRight (M i)).comp (ψ.toAddMonoidHom.comp (𝒜 i).subtype.toAddMonoidHom)

theorem monomialPiece_apply (i : ι) (z : 𝒜 i) : monomialPiece 𝒜 ψ M i z = ψ z * M i := rfl

/-- **The monomial ring homomorphism** `A →+* R`, `z ↦ ψ z * M i` on `𝒜 i` (`DirectSum.toSemiring`
along `DirectSum.decomposeRingEquiv`; unit: `SetLike.coe_gOne`, multiplicativity: `SetLike.coe_gMul`
and `hMadd`). -/
def monomialHom : A →+* R :=
  (DirectSum.toSemiring (fun i => monomialPiece 𝒜 ψ M i)
    (by rw [monomialPiece_apply, SetLike.coe_gOne, map_one, hM0, one_mul])
    (fun ai aj => by
      rw [monomialPiece_apply, monomialPiece_apply, monomialPiece_apply, SetLike.coe_gMul, map_mul, hMadd]
      ring)).comp (DirectSum.decomposeRingEquiv 𝒜).toRingHom

theorem monomialHom_of_mem {i : ι} {z : A} (hz : z ∈ 𝒜 i) :
    monomialHom 𝒜 ψ M hM0 hMadd z = ψ z * M i := by
  unfold monomialHom
  rw [RingHom.comp_apply]
  have h : (DirectSum.decomposeRingEquiv 𝒜).toRingHom z = DirectSum.of (fun i => ↥(𝒜 i)) i ⟨z, hz⟩ :=
    DirectSum.decompose_of_mem 𝒜 hz
  rw [h, DirectSum.toSemiring_of]
  rfl

end GradedAlgebra

end
