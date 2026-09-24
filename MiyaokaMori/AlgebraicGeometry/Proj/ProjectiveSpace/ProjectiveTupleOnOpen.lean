import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.SchemeOverResidue
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpace

/-!
# Projective realization on a genuine nonvanishing open

The polynomial realization step first projectivizes a tuple on an open
neighbourhood of the zero section.  This file records that interface over an
arbitrary field without constructing a line-bundle total space or repeating
the local polynomial exactness argument.  The open is an actual
`Scheme.Opens`, the coordinates are actual sections, and the no-common-zero
condition is the irrelevant-ideal condition used by `Proj.fromOfGlobalSections`.

The resulting morphism is the canonical morphism supplied by Mathlib.  A
pointed variant records an actual factorization of a chosen section through
this open; it does not encode a conclusion about the complement or a
resolution of a rational map.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry.Proj

universe u

variable {k : Type u} [Field k]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- A homogeneous coordinate tuple on an actual open subscheme. -/
structure ProjectiveTupleOnOpen (X : Scheme.{u}) where
  U : X.Opens
  dimension : ℕ
  coefficients : k →+* Γ(U.toScheme, ⊤)
  coordinates : Fin (dimension + 1) → Γ(U.toScheme, ⊤)
  no_common_zero :
    (HomogeneousIdeal.irrelevant (projectiveGrading k dimension)).toIdeal.map
        (MvPolynomial.eval₂Hom coefficients coordinates) = ⊤

namespace ProjectiveTupleOnOpen

variable {X : Scheme.{u}} (D : ProjectiveTupleOnOpen (k := k) X)

/-- The actual polynomial evaluation map determined by the coordinate tuple. -/
def coordinateMap : MvPolynomial (Fin (D.dimension + 1)) k →+* Γ(D.U.toScheme, ⊤) :=
  MvPolynomial.eval₂Hom D.coefficients D.coordinates

@[simp] theorem coordinateMap_apply_X (i : Fin (D.dimension + 1)) :
    D.coordinateMap (MvPolynomial.X i) = D.coordinates i := by
  simp [coordinateMap]

@[simp] theorem coordinateMap_apply_C (c : k) :
    D.coordinateMap (MvPolynomial.C c) = D.coefficients c := by
  simp [coordinateMap]

/-- The actual Proj morphism defined on the nonvanishing open. -/
def projectiveMap : D.U.toScheme ⟶ Proj (projectiveGrading k D.dimension) :=
  Proj.fromOfGlobalSections (projectiveGrading k D.dimension) D.coordinateMap
    (by simpa [coordinateMap] using D.no_common_zero)

/-- The base morphism induced by the scalar map on the open subscheme. -/
def baseMap : D.U.toScheme ⟶ Base k :=
  D.U.toScheme.toSpecΓ ≫ Spec.map (CommRingCat.ofHom D.coefficients)

theorem projectiveMap_over_base :
    D.projectiveMap ≫ (ProjectiveSpace D.dimension k ↘ Spec (CommRingCat.of k)) = D.baseMap := by
  change D.projectiveMap ≫ (Proj.toSpecZero (projectiveGrading k D.dimension) ≫
    Spec.map (CommRingCat.ofHom (algebraMap k ((projectiveGrading k D.dimension) 0)))) = _
  rw [← Category.assoc, projectiveMap, Proj.fromOfGlobalSections_toSpecZero,
    Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have heval : ((D.coordinateMap).comp
      (algebraMap ((projectiveGrading k D.dimension) 0)
        (MvPolynomial (Fin (D.dimension + 1)) k))).comp
        (algebraMap k ((projectiveGrading k D.dimension) 0)) = D.coefficients := by
    ext c
    simp [coordinateMap]
  rw [heval]
  rfl

/-- The chart where one coordinate is nonzero is exactly its concrete basic
open on `U`, so the tuple supplies the same cover used by the Proj gluing. -/
theorem projectiveMap_preimage_basicOpen_X (i : Fin (D.dimension + 1)) :
    D.projectiveMap ⁻¹ᵁ Proj.basicOpen (projectiveGrading k D.dimension) (MvPolynomial.X i) =
      D.U.toScheme.basicOpen (D.coordinates i) := by
  change
    (Proj.fromOfGlobalSections (projectiveGrading k D.dimension) D.coordinateMap _ ⁻¹ᵁ
      Proj.basicOpen (projectiveGrading k D.dimension) (MvPolynomial.X i)) = _
  rw [Proj.fromOfGlobalSections_preimage_basicOpen
    (𝒜 := projectiveGrading k D.dimension) (f := D.coordinateMap)
    (n := 1) (r := MvPolynomial.X i)]
  · simp [coordinateMap]
  · exact Nat.zero_lt_one
  · exact MvPolynomial.isHomogeneous_X k i

end ProjectiveTupleOnOpen

/-- A tuple neighbourhood with an actual section through its open. -/
structure PointedProjectiveTupleOnOpen (X : Scheme.{u}) where
  tuple : ProjectiveTupleOnOpen (k := k) X
  Z : Scheme.{u}
  zero : Z ⟶ tuple.U.toScheme
  ambientZero : Z ⟶ X
  zero_factor : zero ≫ tuple.U.ι = ambientZero

namespace PointedProjectiveTupleOnOpen

variable {X : Scheme.{u}} (D : PointedProjectiveTupleOnOpen (k := k) X)

/-- Evaluate the projective map on the actual section factor. -/
def zeroProjectiveMap : D.Z ⟶ Proj (projectiveGrading k D.tuple.dimension) :=
  D.zero ≫ D.tuple.projectiveMap

@[simp] theorem zeroProjectiveMap_def :
    D.zeroProjectiveMap = D.zero ≫ D.tuple.projectiveMap :=
  rfl

end PointedProjectiveTupleOnOpen

end AlgebraicGeometry.Proj
