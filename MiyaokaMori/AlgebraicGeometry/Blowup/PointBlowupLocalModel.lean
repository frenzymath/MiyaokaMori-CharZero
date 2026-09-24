import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Surfaces.PointBlowupSurface
import MiyaokaMori.AlgebraicGeometry.Blowup.Stacks0805
import MiyaokaMori.AlgebraicGeometry.Morphisms.Stacks0ahhBlowupImproveStalkIso
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.Stacks0ahhBlowupImproveComapFromSpecStalk

/-! # The local model of a point blowup at the centre

The local model of the point blowup `π : Bl_x W → W` of a smooth projective surface at a closed
point `x`: for `g : Spec O_{W,x} → W` (flat, `flat_fromSpecStalk`) the blowup `X := Bl_{J₀} Spec O_{W,x}`
of the pulled-back centre `J₀ = (vanishingIdeal {x}).comap g` is `Bl_x W ×_W Spec O_{W,x}`
(Stacks 0805, `blowup_flatBaseChange`), and the projection `q : X → Bl_x W` satisfies
`q ≫ π = b ≫ g`, hits every point of `π⁻¹(x)`, and induces isomorphisms on stalks (it is a flat
preimmersion: both properties are stable under base change and composition,
`isIso_stalkMap_of_flat_of_isPreimmersion`).

The centre `J₀` is a variable with `J₀ = (vanishingIdeal {x}).comap g`, so that the statement can be
instantiated with the centre `ofIdealTop (𝔪·Γ(Spec O_{W,x}))` used by Stacks 0AGT
(`pointBlowup.vanishingIdeal_comap_fromSpecStalk`).

Used by `exists_pointBlowup_improve` (steps 1, 5, 6). Source: Stacks 0805, 01J7, 00HT.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The local model `q : Bl_{J₀} Spec O_{W,x} → Bl_x W`: `q ≫ π = b ≫ g`; the pullbacks along `q` of
`I·O_{W'}` and of the exceptional ideal `E = (vanishingIdeal {x})·O_{W'}` are `I_x·O_X` and
`J₀·O_X` (spelled as in Stacks 0AGT); and every point of `π⁻¹(x)` is `q y'` for some `y'` at which
`q` is an isomorphism on stalks. -/
theorem pointBlowup.exists_localModel {k : Type u} [Field k] [PerfectField k]
    (W : SmoothProjectiveSurface k) (x : W.toScheme) (hx : IsClosed ({x} : Set W.toScheme))
    (J₀ : (AlgebraicGeometry.Spec (W.toScheme.presheaf.stalk x)).IdealSheafData)
    (hJ₀ : J₀ = (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩).comap
      (W.toScheme.fromSpecStalk x)) :
    ∃ q : (AlgebraicGeometry.Scheme.blowup J₀).left ⟶ (pointBlowup W x hx).toScheme,
      q ≫ pointBlowup.π W x hx =
        (AlgebraicGeometry.Scheme.blowup J₀).hom ≫ W.toScheme.fromSpecStalk x ∧
      (∀ I : W.toScheme.IdealSheafData, (I.comap (pointBlowup.π W x hx)).comap q =
        (AlgebraicGeometry.Scheme.IdealSheafData.ofIdealTop ((I.stalkIdeal x).map
          (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of (W.toScheme.presheaf.stalk x))).inv.hom)).comap
          (AlgebraicGeometry.Scheme.blowup J₀).hom) ∧
      ((AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩).comap
          (pointBlowup.π W x hx)).comap q = J₀.comap (AlgebraicGeometry.Scheme.blowup J₀).hom ∧
      ∀ y : (pointBlowup W x hx).toScheme, pointBlowup.π W x hx y = x →
        ∃ y' : (AlgebraicGeometry.Scheme.blowup J₀).left, q y' = y ∧ IsIso (q.stalkMap y') := by
  subst hJ₀
  have : AlgebraicGeometry.Flat (W.toScheme.fromSpecStalk x) :=
    AlgebraicGeometry.Scheme.flat_fromSpecStalk _ _
  obtain ⟨e, he⟩ := AlgebraicGeometry.Scheme.blowup_flatBaseChange (W.toScheme.fromSpecStalk x)
    (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩)
  obtain ⟨q₀, hq₀def⟩ : ∃ q₀ : (AlgebraicGeometry.Scheme.blowup
      ((AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩).comap (W.toScheme.fromSpecStalk x))).left ⟶
      (AlgebraicGeometry.Scheme.blowup (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩)).left,
      q₀ = e.hom ≫ pullback.snd (W.toScheme.fromSpecStalk x)
        (AlgebraicGeometry.Scheme.blowup (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩)).hom := ⟨_, rfl⟩
  have hq₀ : ∀ y', IsIso (q₀.stalkMap y') := by
    intro y'
    rw [hq₀def]
    exact AlgebraicGeometry.Scheme.Hom.isIso_stalkMap_of_flat_of_isPreimmersion _ _
  have hqπ₀ : q₀ ≫ (AlgebraicGeometry.Scheme.blowup (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩)).hom =
      (AlgebraicGeometry.Scheme.blowup
        ((AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩).comap (W.toScheme.fromSpecStalk x))).hom ≫ W.toScheme.fromSpecStalk x := by
    rw [hq₀def, Category.assoc, ← pullback.condition, ← Category.assoc, he]
  have hI' : ∀ I : W.toScheme.IdealSheafData,
      (I.comap (AlgebraicGeometry.Scheme.blowup (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩)).hom).comap q₀ =
        (AlgebraicGeometry.Scheme.IdealSheafData.ofIdealTop ((I.stalkIdeal x).map
          (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of (W.toScheme.presheaf.stalk x))).inv.hom)).comap
          (AlgebraicGeometry.Scheme.blowup
            ((AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩).comap (W.toScheme.fromSpecStalk x))).hom := by
    intro I
    rw [← AlgebraicGeometry.Scheme.IdealSheafData.comap_comp, hqπ₀,
      AlgebraicGeometry.Scheme.IdealSheafData.comap_comp,
      AlgebraicGeometry.Scheme.IdealSheafData.comap_fromSpecStalk_of I x]
  have hV' : ((AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩).comap (AlgebraicGeometry.Scheme.blowup (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩)).hom).comap q₀ =
      ((AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩).comap (W.toScheme.fromSpecStalk x)).comap
        (AlgebraicGeometry.Scheme.blowup
          ((AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩).comap (W.toScheme.fromSpecStalk x))).hom := by
    rw [← AlgebraicGeometry.Scheme.IdealSheafData.comap_comp, hqπ₀,
      AlgebraicGeometry.Scheme.IdealSheafData.comap_comp]
  refine ⟨q₀, hqπ₀, hI', hV', ?_⟩
  intro y hy
  obtain ⟨z, -, hz2⟩ := AlgebraicGeometry.Scheme.Pullback.exists_preimage_pullback
    (f := W.toScheme.fromSpecStalk x)
    (g := (AlgebraicGeometry.Scheme.blowup (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩)).hom)
    (IsLocalRing.closedPoint _) y (by rw [AlgebraicGeometry.Scheme.fromSpecStalk_closedPoint]; exact hy.symm)
  refine ⟨e.inv z, ?_, hq₀ _⟩
  have h1 : q₀ (e.inv z) = pullback.snd (W.toScheme.fromSpecStalk x)
      (AlgebraicGeometry.Scheme.blowup (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩)).hom z := by
    rw [hq₀def, AlgebraicGeometry.Scheme.Hom.comp_apply,
      ← AlgebraicGeometry.Scheme.Hom.comp_apply e.inv e.hom, Iso.inv_hom_id]
    rfl
  exact h1.trans hz2

/-- `pointBlowup.vanishingIdeal_comap_fromSpecStalk` with the stalk written as
`CommRingCat.of ↑(O_{W,x})`, the spelling used by Stacks 0AGT; definitionally the same statement. -/
theorem pointBlowup.vanishingIdeal_comap_fromSpecStalk_of {k : Type u} [Field k] [PerfectField k]
    (W : SmoothProjectiveSurface k) (x : W.toScheme) (hx : IsClosed ({x} : Set W.toScheme)) :
    (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩).comap
        (W.toScheme.fromSpecStalk x) =
      AlgebraicGeometry.Scheme.IdealSheafData.ofIdealTop
        ((IsLocalRing.maximalIdeal (W.toScheme.presheaf.stalk x)).map
          (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of (W.toScheme.presheaf.stalk x))).inv.hom) :=
  pointBlowup.vanishingIdeal_comap_fromSpecStalk W x hx

end
