import MiyaokaMori.AlgebraicGeometry.Blowup.SurfaceBlowup

/-!
# Blowing up an invertible ideal is an isomorphism

The identity morphism satisfies the actual geometric blowup universal property precisely
when the given ideal is invertible. Uniqueness of the blowup then identifies any blowup of
that same ideal with the identity over its original base scheme.

This is Stacks Tag 0807. It supplies the Cartier-centre step for the strict-transform
argument in the proof of Corollary 4.3 of the paper (§4). Identifying the
strict transform with the blowup of the original curve is Tag 080E.
-/

open AlgebraicGeometry CategoryTheory

namespace MiyaokaMori.Statement

universe u

/-- The identity is a blowup of the given ideal exactly when the ideal is invertible. -/
theorem isBlowup_id_iff {X : Scheme.{u}} (I : X.IdealSheafData) :
    IsBlowup I (𝟙 X) ↔ IsInvertibleIdeal I := by
  constructor
  · intro h
    simpa using h.1
  · intro h
    refine ⟨by simpa using h, ?_⟩
    intro T f _
    refine ⟨f, by simp, ?_⟩
    intro g hg
    simpa using hg

/-- Every actual blowup of an invertible ideal is an isomorphism over the original scheme. -/
theorem IsBlowup.isIso_of_isInvertibleIdeal
    {X B : Scheme.{u}} {I : X.IdealSheafData} {b : B ⟶ X}
    (hb : IsBlowup I b) (hI : IsInvertibleIdeal I) : IsIso b := by
  obtain ⟨e, he⟩ := hb.exists_iso ((isBlowup_id_iff I).mpr hI)
  have he' : e.hom = b := by simpa using he
  rw [← he']
  infer_instance

end MiyaokaMori.Statement
