import MiyaokaMori.AlgebraicGeometry.Blowup.BlowupOpenIdeal

/-!
# Blowups over opens on which the centre ideal is the unit ideal

The actual blowup universal property supplies an inverse to the restricted
structural morphism over any open on which the centre ideal becomes the unit
ideal. The construction uses the pullback square of the same open restriction;
it neither replaces the blowup nor assumes the isomorphism being proved.

This is the single-step input for the point-blowup sequence in the resolution
argument of Corollary 4.3 of the paper (§4). Its mathematical source
is Stacks Project, Tags 02OS (part 1) and 0806 (the universal property).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace MiyaokaMori.Statement

universe u

/-- A blowup is an isomorphism over every open on which its centre ideal is the
unit ideal. The inverse is obtained from the blowup's universal property and the
actual open-restriction pullback square. -/
theorem IsBlowup.isIsoOverOpen_of_comap_eq_top
    {X B : Scheme.{u}} {I : X.IdealSheafData} {b : B ⟶ X}
    (hb : IsBlowup I b) (U : X.Opens) (hIU : I.comap U.ι = ⊤) :
    IsIsoOverOpen b U := by
  have hU : IsInvertibleIdeal (I.comap U.ι) := by
    rw [hIU]
    exact isInvertibleIdeal_top U.toScheme
  obtain ⟨j, hj, _⟩ := hb.2 U.toScheme U.ι hU
  obtain ⟨l, hl_restrict, hl_ι⟩ :=
    (isPullback_morphismRestrict b U).exists_lift (𝟙 U.toScheme) j
      (by simpa only [Category.id_comp] using hj.symm)
  have hV : IsInvertibleIdeal (I.comap (morphismRestrict b U ≫ U.ι)) := by
    rw [Scheme.IdealSheafData.comap_comp, hIU, Scheme.IdealSheafData.comap_top]
    exact isInvertibleIdeal_top (b ⁻¹ᵁ U).toScheme
  change IsIso (morphismRestrict b U)
  refine ⟨⟨l, ?_, hl_restrict⟩⟩
  apply (cancel_mono (b ⁻¹ᵁ U).ι).1
  rw [Category.assoc, hl_ι, Category.id_comp]
  exact (hb.2 (b ⁻¹ᵁ U).toScheme (morphismRestrict b U ≫ U.ι) hV).unique
    (by rw [Category.assoc, hj]) (morphismRestrict_ι b U).symm

end MiyaokaMori.Statement
