import MiyaokaMori.Prelude
import Mathlib.RingTheory.Length

/-! # Transport of the length of a quotient along a ring isomorphism

Transport of the length of `R ⧸ I` along a ring isomorphism: for a bijective ring homomorphism
`φ : R → S`, `length_R (R ⧸ I) = length_S (S ⧸ I·S)`. Used to compare the terms of the length sums
of Stacks 0AHH/0AGT on `Bl_x W` and on the local model `Bl_𝔪 Spec O_{W,x}`
(`exists_pointBlowup_improve`).

Source: the lattice of submodules is transported by the semilinear equivalence `R ⧸ I → S ⧸ φ(I)`
(`Submodule.orderIsoMapComapOfBijective`), and length is the Krull dimension of that lattice
(Mathlib `Module.length`, cf. `Module.length_eq_of_surjective`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

noncomputable section

/-- `length_R (R ⧸ I) = length_S (S ⧸ I.map φ)` for a bijective ring homomorphism `φ : R →+* S`. -/
theorem Module.length_quotient_eq_of_bijective {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (φ : R →+* S) (hφ : Function.Bijective φ) (I : Ideal R) :
    Module.length R (R ⧸ I) = Module.length S (S ⧸ I.map φ) := by
  let e : R ⧸ I ≃+* S ⧸ I.map φ :=
    Ideal.quotientEquiv I (I.map φ) (RingEquiv.ofBijective φ hφ) rfl
  let ψ : R ⧸ I →+* S ⧸ I.map φ := e
  have : RingHomSurjective ψ := ⟨e.surjective⟩
  have h1 : Module.length R (R ⧸ I) = Module.length (R ⧸ I) (R ⧸ I) :=
    Module.length_eq_of_surjective (by
      rw [Ideal.Quotient.algebraMap_eq]
      exact Ideal.Quotient.mk_surjective)
  have h2 : Module.length S (S ⧸ I.map φ) = Module.length (S ⧸ I.map φ) (S ⧸ I.map φ) :=
    Module.length_eq_of_surjective (by
      rw [Ideal.Quotient.algebraMap_eq]
      exact Ideal.Quotient.mk_surjective)
  rw [h1, h2, Module.length, Module.length, WithBot.unbot_inj,
    Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComapOfBijective ψ.toSemilinearMap
      e.bijective)]

end
