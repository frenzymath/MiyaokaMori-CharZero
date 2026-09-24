import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.IdealSheafComapIdealEqMap
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.IdealSheafStalkIdealBasic
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.IdealSheafStalkIdealEqMapGerm

/-! # Pullback of an ideal sheaf to `Spec O_{X,x}`

The pullback of a quasi-coherent ideal sheaf `I` along the canonical morphism
`Spec O_{X,x} → X` is the ideal sheaf of the stalk ideal `I_x` (transported to
`Γ(Spec O_{X,x})` by `ΓSpecIso`). This is the analogue for arbitrary `I` of
`pointBlowup.vanishingIdeal_comap_fromSpecStalk` and identifies the centre and the ideal in the
local model of the blow-up improvement step of Stacks 0AHH (Stacks 0AGT applied to
`A = O_{W,x}`, `I := I_x`).

Source: Stacks 01HR / 01J7 (`Spec O_{X,x} → X` and its global sections); Mathlib
`Scheme.fromSpecStalk_app`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.IdealSheafData

/-- `I.comap (Spec O_{X,x} → X) = ofIdealTop (I_x)`.

Proof: `Spec O_{X,x}` is affine, so it suffices to compare global sections (`ext_of_isAffine`).
Choose an affine open `U ∋ x`; the whole `Spec O_{X,x}` maps into `U` (`range_fromSpecStalk`:
its points are the generizations of `x`), so `(I.comap g)(⊤) = I(U)` extended along
`g.appLE U ⊤` (`comap_ideal_eq_map_appLE`), and `g.app U = germ ≫ ΓSpecIso.inv ≫ res`
(`fromSpecStalk_app`) with `I(U)·O_{X,x} = I_x` (`stalkIdeal_eq_map_germ`). -/
theorem comap_fromSpecStalk {X : AlgebraicGeometry.Scheme.{u}} (I : X.IdealSheafData) (x : X) :
    I.comap (X.fromSpecStalk x) =
      ofIdealTop ((I.stalkIdeal x).map (AlgebraicGeometry.Scheme.ΓSpecIso (X.presheaf.stalk x)).inv.hom) := by
  obtain ⟨U, hxU⟩ := X.exists_affineOpens_mem x
  have hle : (⊤ : (AlgebraicGeometry.Spec (X.presheaf.stalk x)).Opens) ≤ (X.fromSpecStalk x) ⁻¹ᵁ U.1 := by
    intro s _
    show X.fromSpecStalk x s ∈ U.1
    have hs : X.fromSpecStalk x s ∈ Set.range (X.fromSpecStalk x) := Set.mem_range_self s
    rw [AlgebraicGeometry.Scheme.range_fromSpecStalk] at hs
    exact (hs : X.fromSpecStalk x s ⤳ x).mem_open U.1.2 hxU
  have happ : (X.fromSpecStalk x).appLE U.1 ⊤ hle =
      X.presheaf.germ U.1 x hxU ≫ (AlgebraicGeometry.Scheme.ΓSpecIso (X.presheaf.stalk x)).inv ≫
        (AlgebraicGeometry.Spec (X.presheaf.stalk x)).presheaf.map (homOfLE le_top).op := by
    rw [AlgebraicGeometry.Scheme.Hom.appLE, AlgebraicGeometry.Scheme.fromSpecStalk_app hxU]
    simp only [Category.assoc, ← Functor.map_comp, ← op_comp, homOfLE_comp]
  apply ext_of_isAffine
  rw [comap_ideal_eq_map_appLE I (X.fromSpecStalk x) U ⟨⊤, AlgebraicGeometry.isAffineOpen_top _⟩ hle,
    happ, ofIdealTop_ideal, stalkIdeal_eq_map_germ I x U hxU, Ideal.map_map, Ideal.map_map,
    CommRingCat.hom_comp, CommRingCat.hom_comp]

/-- `comap_fromSpecStalk` with the stalk written as `CommRingCat.of ↑(O_{X,x})`, the spelling used by
Stacks 0AGT (`blowup_regularLocalRing_dimTwo_improve`); definitionally the same statement. -/
theorem comap_fromSpecStalk_of {X : AlgebraicGeometry.Scheme.{u}} (I : X.IdealSheafData) (x : X) :
    I.comap (X.fromSpecStalk x) =
      ofIdealTop ((I.stalkIdeal x).map
        (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of (X.presheaf.stalk x))).inv.hom) :=
  comap_fromSpecStalk I x

end AlgebraicGeometry.Scheme.IdealSheafData

end
