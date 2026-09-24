import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.AlgebraicCycles
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.Ideal.Quotient.Nilpotent

/-!
# The reduced closed subscheme supported on the closure of a point

The vanishing ideal of a closed subset gives its reduced induced scheme structure.
Its affine charts are quotients by radical vanishing ideals, so they are reduced.
For the closure of a point, the underlying space is irreducible and the original
point supplies an explicit generic point. The inclusion has exactly this closure
as its image.

When the closure has topological Krull dimension one, this construction supplies
the carrier and inclusion of an integral curve (`IntegralCurve.ofClosedSubvariety` of
`ClosedSubvariety.ofPoint`). It requires no Noetherian, finite-type, field, or
properness hypothesis.

Sources: Stacks Project, Tag 01J3 (`schemes.tex`, reduced-closed-subscheme), and
Tag 02QR (`chow.tex`, cycles and cycles-pointwise). The dimension in this file is
the existing `pointClosureDimension`; no comparison with a delta-dimension is used.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Intersection.ReducedPointClosure

/-- Quotienting by the vanishing ideal of a closed subset gives a reduced scheme. -/
theorem vanishingIdeal_subscheme_isReduced {X : Scheme.{u}} (Z : Closeds X) :
    IsReduced (Scheme.IdealSheafData.vanishingIdeal Z).subscheme := by
  let I : X.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal Z
  change IsReduced I.subscheme
  apply (IsReduced.iff_of_openCover I.subscheme I.subschemeCover.openCover).2
  change ∀ U : X.affineOpens, IsReduced (Spec (CommRingCat.of (Γ(X, U.1) ⧸ I.ideal U)))
  intro U
  let : _root_.IsReduced (Γ(X, U.1) ⧸ I.ideal U) :=
    (Ideal.isRadical_iff_quotient_reduced (I.ideal U)).mp <| by
      change (PrimeSpectrum.vanishingIdeal (U.2.fromSpec ⁻¹' (Z : Set X))).IsRadical
      exact PrimeSpectrum.isRadical_vanishingIdeal _
  infer_instance

/-- The vanishing ideal sheaf of the actual closure of `x`. -/
def ideal (X : Scheme.{u}) (x : X) : X.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal ⟨closure ({x} : Set X), isClosed_closure⟩

/-- The support set is stored directly by Mathlib's vanishing-ideal constructor. -/
@[simp]
theorem ideal_support (X : Scheme.{u}) (x : X) :
    ((ideal X x).support : Set X) = closure ({x} : Set X) := rfl

/-- The reduced induced scheme structure on the closure of `x`. -/
def scheme (X : Scheme.{u}) (x : X) : Scheme.{u} :=
  (ideal X x).subscheme

/-- The actual inclusion of the reduced point closure. -/
def inclusion (X : Scheme.{u}) (x : X) : scheme X x ⟶ X :=
  (ideal X x).subschemeι

instance inclusion_isClosedImmersion (X : Scheme.{u}) (x : X) :
    IsClosedImmersion (inclusion X x) := by
  exact inferInstanceAs (IsClosedImmersion (ideal X x).subschemeι)

instance scheme_isReduced (X : Scheme.{u}) (x : X) : IsReduced (scheme X x) :=
  vanishingIdeal_subscheme_isReduced ⟨closure ({x} : Set X), isClosed_closure⟩

instance scheme_irreducibleSpace (X : Scheme.{u}) (x : X) :
    IrreducibleSpace (scheme X x) := by
  change IrreducibleSpace (closure ({x} : Set X))
  exact Subtype.irreducibleSpace isIrreducible_singleton.closure

instance scheme_isIntegral (X : Scheme.{u}) (x : X) : IsIntegral (scheme X x) :=
  isIntegral_of_irreducibleSpace_of_isReduced (scheme X x)

/-- The original point, viewed as a point of its reduced closure. -/
def generic (X : Scheme.{u}) (x : X) : scheme X x :=
  ⟨x, subset_closure (by simp)⟩

/-- The original point is generic in its reduced closure. -/
theorem generic_spec (X : Scheme.{u}) (x : X) :
    IsGenericPoint (generic X x) (Set.univ : Set (scheme X x)) := by
  change closure ({⟨x, subset_closure (by simp)⟩} : Set (closure ({x} : Set X))) = Set.univ
  rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image, Set.image_singleton]
  ext y
  exact ⟨fun _ ↦ Set.mem_univ y, fun _ ↦ y.property⟩

/-- The inclusion sends the chosen generic point to the original point. -/
@[simp]
theorem inclusion_generic (X : Scheme.{u}) (x : X) :
    inclusion X x (generic X x) = x := rfl

/-- The image of the actual closed immersion is precisely the point closure. -/
theorem range_inclusion (X : Scheme.{u}) (x : X) :
    Set.range (inclusion X x) = closure ({x} : Set X) := by
  change Set.range (ideal X x).subschemeι = closure ({x} : Set X)
  rw [Scheme.IdealSheafData.range_subschemeι, ideal_support]

/-- The scheme has the topology of the closure `closure {x}`, whose Krull dimension is
`pointClosureDimension X x` (`pointClosureDimension_eq_topologicalKrullDim_closure`). -/
theorem dimension_eq (X : Scheme.{u}) (x : X) :
    topologicalKrullDim (scheme X x) = pointClosureDimension X x :=
  (pointClosureDimension_eq_topologicalKrullDim_closure X x).symm

end AlgebraicGeometry.Intersection.ReducedPointClosure
