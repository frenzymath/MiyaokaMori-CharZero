import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Blowup.SurfaceBlowup
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.VanishingIdealSingletonEqPointIdeal
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.AlgebraicGeometry.Blowup.BlowupTower
import MiyaokaMori.AlgebraicGeometry.Blowup.BlowupTowerAvoiding
import MiyaokaMori.AlgebraicGeometry.Varieties.Surfaces.PointBlowupSurface
import MiyaokaMori.AlgebraicGeometry.Blowup.Stacks0806IsBlowup
import MiyaokaMori.AlgebraicGeometry.Blowup.Stacks0809

/-! # Composition and pullback lemmas for point-blowup towers

Bookkeeping lemmas on point-blowup towers used by the assembly of Stacks 0AHH
(`exists_pointBlowupTower_invertible`): a tower composed with a tower is a tower; the centre condition
(`IsPointBlowupSequenceOver`) is stable under composition and along one point blowup; and an
effective Cartier divisor pulls back along a tower to an effective Cartier divisor
(Stacks 0809 applied step by step).

Source: Stacks 0AHH proof (steps 6–7: "β := β₂ ∘ β₁ is a sequence of blowups in closed points
lying over T; the pullback of an effective Cartier divisor under a blowup is an effective Cartier
divisor"); the tower is the one in the proof of Corollary 4.3 of the paper (§4).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- A tower on top of a tower is a tower (induction on the upper tower, `Category.assoc`). -/
theorem IsBlowupTower.comp {k : Type u} [Field k] [PerfectField k]
    {S W' W : SmoothProjectiveSurface k} {β₂ : S.toScheme ⟶ W'.toScheme}
    (hβ₂ : IsBlowupTower β₂) {β₁ : W'.toScheme ⟶ W.toScheme} (hβ₁ : IsBlowupTower β₁) :
    IsBlowupTower (β₂ ≫ β₁) := by
  induction hβ₂ with
  | id W' => rw [Category.id_comp]; exact hβ₁
  | step g hg p hp ih =>
    rw [Category.assoc]
    exact IsBlowupTower.step (g ≫ β₁) (ih hβ₁) p hp

/-- One point blowup is a tower (of length one). -/
theorem pointBlowup.π_isBlowupTower {k : Type u} [Field k] [PerfectField k]
    (W : SmoothProjectiveSurface k) (x : W.toScheme) (hx : IsClosed ({x} : Set W.toScheme)) :
    IsBlowupTower (pointBlowup.π W x hx) := by
  have h := IsBlowupTower.step (𝟙 W.toScheme) (IsBlowupTower.id W) x hx
  rwa [Category.comp_id] at h

/-- The centre condition is stable under composition: if `g` is a point-blowup sequence
over `A ⊆ Y` and `f` one over `B ⊆ X`, and `f` maps `A` into `B`, then `g ≫ f` is a point-blowup
sequence over `B`. -/
theorem MiyaokaMori.Statement.IsPointBlowupSequenceOver.comp {X Y Z : AlgebraicGeometry.Scheme.{u}}
    {A : Set Y} {B : Set X} {g : Z ⟶ Y}
    (hg : MiyaokaMori.Statement.IsPointBlowupSequenceOver Y A g) {f : Y ⟶ X}
    (hf : MiyaokaMori.Statement.IsPointBlowupSequenceOver X B f) (hAB : ∀ a ∈ A, f a ∈ B) :
    MiyaokaMori.Statement.IsPointBlowupSequenceOver X B (g ≫ f) := by
  induction hg with
  | id => rw [Category.id_comp]; exact hf
  | cons f' b _ c hc hall hb ih =>
    rw [Category.assoc]
    refine MiyaokaMori.Statement.IsPointBlowupSequenceOver.cons (f' ≫ f) b ih c hc ?_ hb
    rw [AlgebraicGeometry.Scheme.Hom.comp_apply]
    exact hAB _ hall

/-- One point blowup `π : Bl_x W → W` is a point-blowup sequence over any set containing `x`
(`blowup_isBlowup` + `vanishingIdeal_singleton_eq_pointIdeal`). -/
theorem pointBlowup.π_isPointBlowupSequenceOver {k : Type u} [Field k] [PerfectField k]
    (W : SmoothProjectiveSurface k) (x : W.toScheme) (hx : IsClosed ({x} : Set W.toScheme))
    (B : Set W.toScheme) (hxB : x ∈ B) :
    MiyaokaMori.Statement.IsPointBlowupSequenceOver W.toScheme B (pointBlowup.π W x hx) := by
  have hb : MiyaokaMori.Statement.IsBlowup (MiyaokaMori.Statement.pointIdeal W.toScheme x)
      (pointBlowup.π W x hx) := by
    rw [← AlgebraicGeometry.Scheme.vanishingIdeal_singleton_eq_pointIdeal x hx]
    exact AlgebraicGeometry.Scheme.blowup_isBlowup _
  have h := MiyaokaMori.Statement.IsPointBlowupSequenceOver.cons (𝟙 W.toScheme)
    (pointBlowup.π W x hx) MiyaokaMori.Statement.IsPointBlowupSequenceOver.id x hx
    (by simpa using hxB) hb
  rwa [Category.comp_id] at h

/-- Composition of avoiding towers: if `β₂ : S → Bl_x W` avoids `A` and its centres map into
the complement of `B`, and `x ∉ B`, then `β₂ ≫ π_x` avoids `B`. -/
theorem IsBlowupTowerAvoiding.comp_pointBlowup_π {k : Type u} [Field k] [PerfectField k]
    {W : SmoothProjectiveSurface k} (x : W.toScheme) (hx : IsClosed ({x} : Set W.toScheme))
    {S : SmoothProjectiveSurface k} {β₂ : S.toScheme ⟶ (pointBlowup W x hx).toScheme}
    {A : Set (pointBlowup W x hx).toScheme} {B : Set W.toScheme}
    (hβ₂ : IsBlowupTowerAvoiding β₂ A) (hxB : x ∉ B)
    (hAB : ∀ a, a ∉ A → pointBlowup.π W x hx a ∉ B) :
    IsBlowupTowerAvoiding (β₂ ≫ pointBlowup.π W x hx) B := by
  unfold IsBlowupTowerAvoiding at *
  exact hβ₂.comp (pointBlowup.π_isPointBlowupSequenceOver W x hx Bᶜ hxB) (fun a ha => hAB a ha)

/-- Pullback of an effective Cartier divisor along a point-blowup tower (Stacks 0809 at every
step; `IdealSheafData.comap_comp`). -/
theorem IsBlowupTower.exists_effectiveCartierDivisor_comap {k : Type u} [Field k] [PerfectField k]
    {S W : SmoothProjectiveSurface k} {β : S.toScheme ⟶ W.toScheme} (hβ : IsBlowupTower β)
    (D : AlgebraicGeometry.EffectiveCartierDivisor W.toScheme) :
    ∃ D' : AlgebraicGeometry.EffectiveCartierDivisor S.toScheme,
      D'.idealSheaf = D.idealSheaf.comap β := by
  induction hβ with
  | id W => exact ⟨D, by rw [AlgebraicGeometry.Scheme.IdealSheafData.comap_id]⟩
  | step g hg p hp ih =>
    obtain ⟨D₁, hD₁⟩ := ih D
    obtain ⟨D₂, hD₂⟩ := AlgebraicGeometry.EffectiveCartierDivisor.exists_comap_blowup
      (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩) D₁
    refine ⟨D₂, ?_⟩
    rw [AlgebraicGeometry.Scheme.IdealSheafData.comap_comp, ← hD₁]
    exact hD₂

end
