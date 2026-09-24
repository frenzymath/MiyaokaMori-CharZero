import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic

/-!
# Algebraic inputs for the characteristic-zero version

The setting is Theorem 1.1 of the paper and the beginning of its §2.
The field is a parameter throughout. Algebraic closedness and characteristic zero
are hypotheses of the main theorem, rather than prerequisites for these objects.

This file provides the base-field bundle `Base`, schemes over a field (`SchemeOver`, with their
rational points) and the standard grading `projectiveGrading` of the polynomial ring `k[X_0, …, X_n]`
by total degree, whose `Proj` is `P^n_k`.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Proj

variable (k : Type u) [Field k]

/-- The base scheme of the specified field. -/
abbrev Base : Scheme.{u} := Spec (CommRingCat.of k)

/-- A scheme with its specified structure morphism to the base field. -/
structure SchemeOver where
  scheme : Scheme.{u}
  toBase : scheme ⟶ Base k

variable {k}

/-- Rational points as sections of the specified structure morphism. -/
def SchemeOver.rationalPoints (X : SchemeOver k) :=
  {p : Base k ⟶ X.scheme // p ≫ X.toBase = 𝟙 (Base k)}

attribute [local instance] MvPolynomial.gradedAlgebra

variable (k)

/-- The standard total-degree grading on the homogeneous coordinate ring. -/
abbrev projectiveGrading (n : ℕ) :=
  MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k

end AlgebraicGeometry.Proj
