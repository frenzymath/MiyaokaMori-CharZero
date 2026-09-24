import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.Polynomial.AlgebraMap

/-! # Polynomial rings from symmetric algebras

Pure algebra (Mathlib only), used for the frame coordinate on `Tot(L)`
(`totalSpace_exists_coordinate_of_isFrame`).

* `Polynomial.aeval_bijective_of_isSymmetricAlgebra`: if `A` is the symmetric algebra of a free `R`-module
  of rank one with basis vector `m` (`IsSymmetricAlgebra f`, `b : Basis Unit R M`), then
  `Polynomial.aeval (f (b ())) : R[X] →ₐ[R] A` is bijective, i.e. `A = R[f m]` is a polynomial ring on
  the degree-one generator. (Mathlib has `SymmetricAlgebra.equivMvPolynomial`, `IsSymmetricAlgebra.equiv`
  and `MvPolynomial.uniqueAlgEquiv`; this lemma composes them and records the variable.)
* `Polynomial.aeval_bijective_of_algEquiv`: bijectivity of `aeval a` is transported along an algebra
  isomorphism `e : A ≃ₐ[R] B` to `aeval (e a)`.
-/

set_option autoImplicit false

universe u v w

open Polynomial

namespace Polynomial

variable {R : Type u} {M : Type v} {A : Type w} [CommRing R] [AddCommGroup M] [Module R M]
  [CommRing A] [Algebra R A]

/-- **A symmetric algebra of a free rank-one module is a polynomial ring on the generator.**
Source: Bourbaki, Algebra III §6 no. 6 (the symmetric algebra of a free module is the polynomial algebra
on a basis); in Mathlib, `SymmetricAlgebra.equivMvPolynomial` and `MvPolynomial.uniqueAlgEquiv`.

Proof. `F := uniqueAlgEquiv ∘ h.lift (constr b X) : A →ₐ[R] R[X]` is bijective (`h.lift g` is
`SymmetricAlgebra.lift g ∘ h.equiv.symm`, and `SymmetricAlgebra.lift (constr b X)` is bijective by
`IsSymmetricAlgebra.mvPolynomial`). `F (f (b ())) = X`, so `F ∘ aeval (f (b ())) = id` by
`Polynomial.algHom_ext`; hence `aeval (f (b ()))` is the inverse of the bijection `F`. -/
theorem aeval_bijective_of_isSymmetricAlgebra {f : M →ₗ[R] A} (h : IsSymmetricAlgebra f)
    (b : Module.Basis Unit R M) :
    Function.Bijective (Polynomial.aeval (f (b ())) : R[X] →ₐ[R] A) := by
  have hb : Function.Bijective (SymmetricAlgebra.lift (Module.Basis.constr b R
      (MvPolynomial.X : Unit → MvPolynomial Unit R))) :=
    SymmetricAlgebra.IsSymmetricAlgebra.mvPolynomial Unit b
  let G : A →ₐ[R] MvPolynomial Unit R :=
    h.lift (Module.Basis.constr b R (MvPolynomial.X : Unit → MvPolynomial Unit R))
  have hG : Function.Bijective G := hb.comp h.equiv.symm.bijective
  let F : A →ₐ[R] R[X] := (MvPolynomial.uniqueAlgEquiv R Unit).toAlgHom.comp G
  have hF : Function.Bijective F := (MvPolynomial.uniqueAlgEquiv R Unit).bijective.comp hG
  have hFa : F.comp (Polynomial.aeval (f (b ()))) = AlgHom.id R R[X] := by
    apply Polynomial.algHom_ext
    simp [F, G]
  have key : ∀ p : R[X], F (Polynomial.aeval (f (b ())) p) = p := fun p =>
    congrArg (fun φ : R[X] →ₐ[R] R[X] => φ p) hFa
  refine ⟨fun p q hpq => ?_, fun a => ⟨F a, hF.1 (key (F a))⟩⟩
  rw [← key p, ← key q, hpq]

/-- Bijectivity of `aeval a` transports along an algebra isomorphism. -/
theorem aeval_bijective_of_algEquiv {B : Type*} [CommRing B] [Algebra R B] (e : A ≃ₐ[R] B) {a : A}
    (h : Function.Bijective (Polynomial.aeval a : R[X] →ₐ[R] A)) :
    Function.Bijective (Polynomial.aeval (e a) : R[X] →ₐ[R] B) := by
  have he : (Polynomial.aeval (e a) : R[X] →ₐ[R] B) = e.toAlgHom.comp (Polynomial.aeval a) := by
    apply Polynomial.algHom_ext
    simp
  rw [he]
  exact e.bijective.comp h

end Polynomial
