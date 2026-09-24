import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.SectionPullbackAlong
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree

/-!
# Compatibility of the existing pullback sections

`ModuleSections.pullback` (the `Γ(-, ⊤)`-typed `abbrev` of the one definition `sectionPullbackAlong`,
`SectionPullbackAlong.lean`) is the global-section map of the actual
pullback-pushforward adjunction unit; `pullbackOn` restricts it to an open of the source. The comparison for composite morphisms
therefore follows from the mate defining `Scheme.Modules.pullbackComp`.
For an open immersion the comparison with restriction is the uniqueness
isomorphism between the two actual left adjoints to pushforward.

The restriction formulas retain `restrictAppIso`, and the scalar formula
uses the inverse of the actual structure-ring `appIso`. This additive
identification of section carriers is not an identification of their scalar rings.
The unit comparison is the existing `SheafOfModules.pullbackObjUnitToUnit`.

Sources: §2 of the paper (the seed's `A` and coordinate sections); Stacks Project, `sheaves.tex`,
`lemma-adjoint-pullback-pushforward-modules` and `lemma-push-pull-composition-modules`. No frame or
desired comparison identity is an input, and no new pullback or section model is defined.

The statements of this file are on the abbrev `AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback`, whose type
spelling `Γ(g^*M, ⊤)` is what their `rw`/`OfNat`/`•` sites need (restating them on
`sectionPullbackAlong` breaks `ModuleChartPullback`, `QcPullbackAffineSections` and
`pullback_unit_one` on the spelling alone).
-/

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules.ModuleSections

set_option backward.isDefEq.respectTransparency false

variable {X Y Z : Scheme.{u}}

section movedFromProjectiveEmbeddingSections

variable (g : X ⟶ Y) {M N : Y.Modules}

/-- Restrict the pulled-back global section to an open of the source scheme. -/
def pullbackOn (s : Γ(M, ⊤)) (U : X.Opens) : Γ((Scheme.Modules.pullback g).obj M, U) :=
  ((Scheme.Modules.pullback g).obj M).presheaf.map
    (CategoryTheory.homOfLE (show U ≤ ⊤ from le_top)).op (pullback g s)

/-- Pullback on the top open is the global pullback section. -/
@[simp]
theorem pullbackOn_top (s : Γ(M, ⊤)) : pullbackOn g s ⊤ = pullback g s := by
  change ((Scheme.Modules.pullback g).obj M).presheaf.map (𝟙 (op ⊤)) _ = _
  simp

/-- Pulled-back sections commute with restriction to smaller opens. -/
@[simp]
theorem pullbackOn_restrict (s : Γ(M, ⊤)) {U V : X.Opens} (j : V ⟶ U) :
    ((Scheme.Modules.pullback g).obj M).presheaf.map j.op (pullbackOn g s U) =
      pullbackOn g s V := by
  unfold pullbackOn
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- Pullback of sections is natural with respect to morphisms of sheaves of modules. -/
theorem pullback_naturality (φ : M ⟶ N) (s : Γ(M, ⊤)) :
    ((Scheme.Modules.pullback g).map φ).app ⊤ (pullback g s) =
      pullback g (φ.app ⊤ s) := by
  have h := (Scheme.Modules.pullbackPushforwardAdjunction g).unit.naturality φ
  exact (congrArg (fun ψ ↦ ψ.app ⊤ s) h).symm

end movedFromProjectiveEmbeddingSections

local instance unitSectionOfNat (S : Scheme.{u}) (U : S.Opens) :
    OfNat (Γ(SheafOfModules.unit (R := S.ringCatSheaf), U)) 1 where
  ofNat := show Γ(S, U) from 1

/-- A morphism out of a pullback acts on `pullbackOn` by restricting its global value. -/
theorem app_pullbackOn (f : X ⟶ Y) {M : Y.Modules} {N : X.Modules}
    (φ : (Scheme.Modules.pullback f).obj M ⟶ N) (s : Γ(M, ⊤)) (U : X.Opens) :
    φ.app U (pullbackOn f s U) =
      N.presheaf.map (CategoryTheory.homOfLE (show U ≤ ⊤ from le_top)).op
        (φ.app ⊤ (pullback f s)) :=
  φ.mapPresheaf.naturality_apply (CategoryTheory.homOfLE (show U ≤ ⊤ from le_top)).op _

/-- The inverse composition comparison sends composite pullback to iterated pullback. -/
theorem pullback_comp_inv (f : X ⟶ Y) (g : Y ⟶ Z) {M : Z.Modules}
    (s : Γ(M, ⊤)) :
    ((Scheme.Modules.pullbackComp f g).app M).inv.app ⊤ (pullback (f ≫ g) s) =
      pullback f (pullback g s) := by
  have h := unit_conjugateEquiv
    ((Scheme.Modules.pullbackPushforwardAdjunction g).comp
      (Scheme.Modules.pullbackPushforwardAdjunction f))
    (Scheme.Modules.pullbackPushforwardAdjunction (f ≫ g))
    (Scheme.Modules.pullbackComp f g).inv M
  rw [Scheme.Modules.conjugateEquiv_pullbackComp_inv, Adjunction.comp_unit_app] at h
  have hs := congrArg (fun φ : M ⟶ (Scheme.Modules.pushforward (f ≫ g)).obj
      ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj M)) ↦
        φ.app ⊤ s) h
  convert hs.symm using 1 <;> rfl

/-- The canonical composition comparison preserves the original pulled-back section. -/
theorem pullback_comp (f : X ⟶ Y) (g : Y ⟶ Z) {M : Z.Modules} (s : Γ(M, ⊤)) :
    ((Scheme.Modules.pullbackComp f g).app M).hom.app ⊤
      (pullback f (pullback g s)) = pullback (f ≫ g) s := by
  rw [← pullback_comp_inv f g s]
  change (((Scheme.Modules.pullbackComp f g).app M).inv ≫
    ((Scheme.Modules.pullbackComp f g).app M).hom).app ⊤ _ = _
  simp only [Iso.inv_hom_id]
  rfl

/-- Composition of pullbacks preserves the original section on every source open. -/
theorem pullbackOn_comp (f : X ⟶ Y) (g : Y ⟶ Z) {M : Z.Modules}
    (s : Γ(M, ⊤)) (U : X.Opens) :
    ((Scheme.Modules.pullbackComp f g).app M).hom.app U
      (pullbackOn f (pullback g s) U) = pullbackOn (f ≫ g) s U := by
  have h := app_pullbackOn (f := f) (M := (Scheme.Modules.pullback g).obj M)
    (N := (Scheme.Modules.pullback (f ≫ g)).obj M)
    ((Scheme.Modules.pullbackComp f g).app M).hom (pullback g s) U
  calc
    _ = ((Scheme.Modules.pullback (f ≫ g)).obj M).presheaf.map
        (CategoryTheory.homOfLE (show U ≤ ⊤ from le_top)).op
        (((Scheme.Modules.pullbackComp f g).app M).hom.app ⊤
          (pullback f (pullback g s))) := h
    _ = pullbackOn (f ≫ g) s U := by
      rw [pullback_comp]
      rfl

/-- Transport along equality of scheme morphisms preserves the original global section. -/
theorem pullbackCongr_apply {f g : X ⟶ Y} (h : f = g) {M : Y.Modules}
    (s : Γ(M, ⊤)) :
    ((Scheme.Modules.pullbackCongr h).app M).hom.app ⊤ (pullback f s) =
      pullback g s := by
  cases h
  rfl

/-- The same equality transport preserves the original section on each source open. -/
theorem pullbackOn_congr {f g : X ⟶ Y} (h : f = g) {M : Y.Modules}
    (s : Γ(M, ⊤)) (U : X.Opens) :
    ((Scheme.Modules.pullbackCongr h).app M).hom.app U (pullbackOn f s U) =
      pullbackOn g s U := by
  cases h
  rfl

/-- For an open immersion, the inverse comparison gives the actual restriction of the section. -/
theorem restrictIso_inv_pullback (f : X ⟶ Y) [IsOpenImmersion f] {M : Y.Modules}
    (s : Γ(M, ⊤)) :
    (M.restrictAppIso f ⊤).hom
      (((Scheme.Modules.restrictFunctorIsoPullback f).app M).inv.app ⊤ (pullback f s)) =
        M.presheaf.map (CategoryTheory.homOfLE (show f ''ᵁ (⊤ : X.Opens) ≤ ⊤ from le_top)).op s := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    (Scheme.Modules.pullbackPushforwardAdjunction f) (Scheme.Modules.restrictAdjunction f) M
  change (Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M ≫
      (Scheme.Modules.pushforward f).map
        ((Scheme.Modules.restrictFunctorIsoPullback f).app M).inv =
      (Scheme.Modules.restrictAdjunction f).unit.app M at h
  have hs := congrArg (fun φ : M ⟶ (Scheme.Modules.pushforward f).obj (M.restrict f) ↦
    φ.app ⊤ s) h
  change ((Scheme.Modules.restrictFunctorIsoPullback f).app M).inv.app
      (f ⁻¹ᵁ (⊤ : Y.Opens)) (pullback f s) = _
  change ((Scheme.Modules.restrictFunctorIsoPullback f).app M).inv.app
      (f ⁻¹ᵁ (⊤ : Y.Opens)) (pullback f s) = _ at hs
  exact hs

/-- On each source open, the inverse comparison restricts the original global section. -/
theorem restrictIso_inv_pullbackOn (f : X ⟶ Y) [IsOpenImmersion f] {M : Y.Modules}
    (s : Γ(M, ⊤)) (U : X.Opens) :
    (M.restrictAppIso f U).hom
      (((Scheme.Modules.restrictFunctorIsoPullback f).app M).inv.app U
        (pullbackOn f s U)) =
      M.presheaf.map (CategoryTheory.homOfLE (show f ''ᵁ U ≤ ⊤ from le_top)).op s := by
  change ((Scheme.Modules.restrictFunctorIsoPullback f).app M).inv.app U
    (pullbackOn f s U) = _
  rw [app_pullbackOn]
  have ht := restrictIso_inv_pullback f s
  change ((Scheme.Modules.restrictFunctorIsoPullback f).app M).inv.app ⊤
    (pullback f s) = _ at ht
  rw [ht]
  change M.presheaf.map (f.opensFunctor.map (CategoryTheory.homOfLE (show U ≤ ⊤ from le_top))).op
    (M.presheaf.map (CategoryTheory.homOfLE (show f ''ᵁ (⊤ : X.Opens) ≤ ⊤ from le_top)).op s) = _
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- The forward open-immersion comparison sends the original restricted section to pullback. -/
theorem restrictIso_hom_restrict (f : X ⟶ Y) [IsOpenImmersion f] {M : Y.Modules}
    (s : Γ(M, ⊤)) :
    ((Scheme.Modules.restrictFunctorIsoPullback f).app M).hom.app ⊤
      ((M.restrictAppIso f ⊤).inv
        (M.presheaf.map (CategoryTheory.homOfLE (show f ''ᵁ (⊤ : X.Opens) ≤ ⊤ from le_top)).op s)) =
      pullback f s := by
  rw [← restrictIso_inv_pullback f s]
  change (((Scheme.Modules.restrictFunctorIsoPullback f).app M).inv ≫
    ((Scheme.Modules.restrictFunctorIsoPullback f).app M).hom).app ⊤ _ = _
  simp only [Iso.inv_hom_id]
  rfl

/-- The forward comparison sends the original restriction to `pullbackOn` on each source open. -/
theorem restrictIso_hom_restrictOn (f : X ⟶ Y) [IsOpenImmersion f] {M : Y.Modules}
    (s : Γ(M, ⊤)) (U : X.Opens) :
    ((Scheme.Modules.restrictFunctorIsoPullback f).app M).hom.app U
      ((M.restrictAppIso f U).inv
        (M.presheaf.map (CategoryTheory.homOfLE (show f ''ᵁ U ≤ ⊤ from le_top)).op s)) =
      pullbackOn f s U := by
  rw [← restrictIso_inv_pullbackOn f s U]
  change (((Scheme.Modules.restrictFunctorIsoPullback f).app M).inv ≫
    ((Scheme.Modules.restrictFunctorIsoPullback f).app M).hom).app U _ = _
  simp only [Iso.inv_hom_id]
  rfl

/-- The additive section identification transports scalars by the actual inverse `appIso`. -/
theorem restrictIso_inv_smul (f : X ⟶ Y) [IsOpenImmersion f] {M : Y.Modules}
    (U : X.Opens) (r : Γ(X, U)) (t : Γ((Scheme.Modules.pullback f).obj M, U)) :
    (M.restrictAppIso f U).hom
      (((Scheme.Modules.restrictFunctorIsoPullback f).app M).inv.app U (r • t)) =
      (f.appIso U).inv r • (M.restrictAppIso f U).hom
        (((Scheme.Modules.restrictFunctorIsoPullback f).app M).inv.app U t) := by
  rw [Scheme.Modules.Hom.app_smul]
  exact CategoryTheory.congr_fun (Scheme.Modules.smul_restrictAppIso_hom f M U r) _

/-- The canonical unit comparison sends a pulled-back scalar to its actual structure-ring image. -/
theorem pullback_unit (f : X ⟶ Y) (r : Γ(Y, ⊤)) :
    Scheme.Modules.Hom.app
      (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) ⊤
        (pullback f (M := SheafOfModules.unit (R := Y.ringCatSheaf)) r) =
      f.app ⊤ r := by
  have h := SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
    f.toRingCatSheafHom
  rw [Adjunction.homEquiv_unit] at h
  exact congrArg (fun φ : SheafOfModules.unit (R := Y.ringCatSheaf) ⟶
      (Scheme.Modules.pushforward f).obj (SheafOfModules.unit (R := X.ringCatSheaf)) ↦
        Scheme.Modules.Hom.app φ ⊤ r) h

/-- The actual canonical comparison of the pulled-back unit sheaf preserves its unit section. -/
theorem pullback_unit_one (f : X ⟶ Y) :
    Scheme.Modules.Hom.app
      (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) ⊤
        (pullback f (M := SheafOfModules.unit (R := Y.ringCatSheaf)) 1) = 1 := by
  rw [pullback_unit, map_one]

/-- The canonical unit comparison preserves the pulled-back unit on every source open. -/
theorem pullbackOn_unit_one (f : X ⟶ Y) (U : X.Opens) :
    Scheme.Modules.Hom.app
      (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) U
        (pullbackOn f (M := SheafOfModules.unit (R := Y.ringCatSheaf)) 1 U) = 1 := by
  have h := app_pullbackOn (f := f)
    (M := SheafOfModules.unit (R := Y.ringCatSheaf))
    (N := SheafOfModules.unit (R := X.ringCatSheaf))
    (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom)
    (1 : Γ(SheafOfModules.unit (R := Y.ringCatSheaf), ⊤)) U
  calc
    _ = _ := h
    _ = 1 := by
      have hu := pullback_unit f
        (1 : Γ(SheafOfModules.unit (R := Y.ringCatSheaf), ⊤))
      change X.presheaf.map (CategoryTheory.homOfLE (show U ≤ ⊤ from le_top)).op
        (Scheme.Modules.Hom.app (SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom) ⊤
          (pullback f (M := SheafOfModules.unit (R := Y.ringCatSheaf)) 1)) = 1
      rw [hu]
      change X.presheaf.map (CategoryTheory.homOfLE (show U ≤ ⊤ from le_top)).op
        (f.app ⊤ (1 : Γ(Y, ⊤))) = 1
      rw [map_one]
      exact map_one _

end AlgebraicGeometry.Scheme.Modules.ModuleSections
