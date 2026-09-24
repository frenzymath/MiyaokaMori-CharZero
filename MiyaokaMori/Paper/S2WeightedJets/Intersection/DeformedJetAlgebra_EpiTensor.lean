import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.ModulesBiproductLocallyFree
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.SheafDualLocallyFree
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorMonoidalIso
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPullbackMonoidal
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesRestrictMonoidal
import MiyaokaMori.CategoryTheory.PresheafModulesTensorLocallySurjective
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModulesDual
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.ModulesPow
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.ModulesPowLocallyFree
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensor
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.SheafOfModulesMonoidal
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.ModulesExactIffLocallyLift
import MiyaokaMori.AlgebraicGeometry.Modules.FreeTensorFreeIso
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.Stacks01b6
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.LocalTrivializationPullback

/-! # Tensoring preserves epimorphisms of sheaves of modules

**Tensoring preserves epimorphisms in `X.Modules`**: for an epimorphism `f : A ⟶ B` of `O_X`-modules and
any `P`, the whiskerings `f ▷ P`, `P ◁ f` are epimorphisms; hence `f ⊗ₘ g` is an epimorphism whenever
`f`, `g` are.

Source: Stacks 01CD (the tensor product of sheaves of modules is right exact in each variable; here only
"epi ⊗ epi = epi" is needed). Proof: epi in `X.Modules` ⇔ locally surjective on sections
(`ModulesLocLiftAux.locSurj_of_epi`); the presheaf tensor
`f₀ ▷ P₀` of a locally surjective map is locally surjective (objectwise `TensorProduct.map` is surjective,
`PresheafOfModules.isLocallySurjective_whiskerRight`); sheafification preserves local surjectivity, and a
locally surjective map of sheaves is an epimorphism; finally `sheafifyTensorTo` (`tensorIsoTensorObj`)
identifies the sheafified presheaf tensor with the monoidal `⊗` of `X.Modules`, and the braiding transports
`▷` to `◁`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open scoped CategoryTheory.MonoidalCategory

theorem AlgebraicGeometry.Scheme.Modules.sheafification_tensor_map_epi {X : AlgebraicGeometry.Scheme.{u}}
    {A B P : X.Modules} (f : A ⟶ B) [Epi f] :
    Epi ((_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (((SheafOfModules.forget X.ringCatSheaf ⋙
        _root_.PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map f) ▷
        ((SheafOfModules.forget X.ringCatSheaf ⋙
          _root_.PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj P))) := by
  let J := Opens.grothendieckTopology X
  let f₀ := (SheafOfModules.forget X.ringCatSheaf ⋙
    _root_.PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map f
  let p₀ := (SheafOfModules.forget X.ringCatSheaf ⋙
    _root_.PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj P
  have hf : Presheaf.IsLocallySurjective J
      ((_root_.PresheafOfModules.toPresheaf
        (X.presheaf ⋙ forget₂ CommRingCat RingCat)).map f₀) := by
    change Presheaf.IsLocallySurjective J
      ((_root_.PresheafOfModules.toPresheaf
        (X.presheaf ⋙ forget₂ CommRingCat RingCat)).map
        ((SheafOfModules.forget X.ringCatSheaf ⋙
          _root_.PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map f))
    exact (ModulesLocLiftAux.locSurj_iff f).mp (ModulesLocLiftAux.locSurj_of_epi f)
  letI : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      ((_root_.PresheafOfModules.toPresheaf
        (X.presheaf ⋙ forget₂ CommRingCat RingCat)).map
        ((SheafOfModules.forget X.ringCatSheaf ⋙
          _root_.PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map f)) := by
    exact hf
  have htp := _root_.PresheafOfModules.isLocallySurjective_whiskerRight
    (R := X.presheaf) (M := (SheafOfModules.forget X.ringCatSheaf ⋙
      _root_.PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj A)
    (N := (SheafOfModules.forget X.ringCatSheaf ⋙
      _root_.PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj B)
    J ((SheafOfModules.forget X.ringCatSheaf ⋙
      _root_.PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map f) p₀
  have htp' : Presheaf.IsLocallySurjective J
      ((_root_.PresheafOfModules.toPresheaf
        (X.presheaf ⋙ forget₂ CommRingCat RingCat)).map (f₀ ▷ p₀)) := htp
  let sf := _root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let g := sf.map (f₀ ▷ p₀)
  have hg : Epi g := by
    have hloc : Sheaf.IsLocallySurjective
        ((CategoryTheory.presheafToSheaf J AddCommGrpCat).map
          ((_root_.PresheafOfModules.toPresheaf
            (X.presheaf ⋙ forget₂ CommRingCat RingCat)).map (f₀ ▷ p₀))) :=
      (Presheaf.isLocallySurjective_presheafToSheaf_map_iff J
        ((_root_.PresheafOfModules.toPresheaf
          (X.presheaf ⋙ forget₂ CommRingCat RingCat)).map (f₀ ▷ p₀))).2 htp'
    have hloc' : TopCat.Presheaf.IsLocallySurjective
        ((SheafOfModules.toSheaf X.ringCatSheaf).map g).hom := by
      change Sheaf.IsLocallySurjective
        ((CategoryTheory.presheafToSheaf J AddCommGrpCat).map
        ((_root_.PresheafOfModules.toPresheaf
          (X.presheaf ⋙ forget₂ CommRingCat RingCat)).map (f₀ ▷ p₀)))
      exact hloc
    have he : Epi ((SheafOfModules.toSheaf X.ringCatSheaf).map g) :=
      (TopCat.Sheaf.isLocallySurjective_iff_epi _).mp hloc'
    exact (SheafOfModules.toSheaf X.ringCatSheaf).epi_of_epi_map he
  exact hg

theorem AlgebraicGeometry.Scheme.Modules.epi_whiskerRight {X : AlgebraicGeometry.Scheme.{u}}
    {A B P : X.Modules} (f : A ⟶ B) [Epi f] : Epi (f ▷ P) := by
  letI := AlgebraicGeometry.Scheme.Modules.monoidalCategory X
  let F := (SheafOfModules.forget X.ringCatSheaf ⋙
    _root_.PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj))
  let f₀ := F.map f
  let p₀ := F.obj P
  let sf := _root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let g := sf.map (f₀ ▷ p₀)
  have hg : Epi g := by
    change Epi (sf.map (f₀ ▷ p₀))
    exact sheafification_tensor_map_epi f
  let sA := AlgebraicGeometry.Scheme.Modules.sheafifyTensorTo A P
  let sB := AlgebraicGeometry.Scheme.Modules.sheafifyTensorTo B P
  have hsA : Epi sA := by
    letI : IsIso sA := by
      dsimp [sA]
      exact Iso.isIso_hom (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj A P)
    exact IsIso.epi_of_iso sA
  have hsB : Epi sB := by
    letI : IsIso sB := by
      dsimp [sB]
      exact Iso.isIso_hom (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj B P)
    exact IsIso.epi_of_iso sB
  have hn := AlgebraicGeometry.Scheme.Modules.sheafifyTensorTo_naturality
    (X := X) f (𝟙 P)
  change sA ≫
      (CategoryTheory.MonoidalCategoryStruct.tensorHom (C := X.Modules) f (𝟙 P)) =
    sf.map (CategoryTheory.MonoidalCategoryStruct.tensorHom (C :=
      _root_.PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat))
      (F.map f) (F.map (𝟙 P))) ≫ sB at hn
  have hmap : F.map (𝟙 P) = 𝟙 p₀ := F.map_id P
  rw [hmap, MonoidalCategory.tensorHom_id] at hn
  have hfg : sA ≫ (f ▷ P) = g ≫ sB := by
    dsimp [sA, sB, g, f₀, p₀, F]
    exact hn
  letI : Epi g := hg
  letI : Epi sB := hsB
  have hcomp : Epi (sA ≫ (f ▷ P)) := by
    rw [hfg]
    exact epi_comp _ _
  letI : Epi sA := hsA
  exact (epi_comp_iff_of_epi sA _).mp hcomp

theorem AlgebraicGeometry.Scheme.Modules.epi_whiskerLeft {X : AlgebraicGeometry.Scheme.{u}}
    {A P Q : X.Modules} (g : P ⟶ Q) [Epi g] : Epi (A ◁ g) := by
  letI := AlgebraicGeometry.Scheme.Modules.monoidalCategory X
  let e₁ := β_ A P
  let e₂ := β_ A Q
  haveI : IsIso e₁.hom := Iso.isIso_hom e₁
  haveI : IsIso e₂.inv := Iso.isIso_inv e₂
  have hright : Epi (g ▷ A) := epi_whiskerRight g
  haveI : Epi (g ▷ A) := hright
  have hcomp : Epi (e₁.hom ≫ (g ▷ A) ≫ e₂.inv) := by
    exact epi_comp (e₁.hom ≫ (g ▷ A)) e₂.inv
  have hnat : (A ◁ g) ≫ e₂.hom = e₁.hom ≫ (g ▷ A) :=
    BraidedCategory.braiding_naturality_right A g
  haveI : Epi (e₁.hom ≫ (g ▷ A) ≫ e₂.inv) := hcomp
  have heq : A ◁ g = e₁.hom ≫ (g ▷ A) ≫ e₂.inv := by
    apply (cancel_mono e₂.hom).1
    calc
      (A ◁ g) ≫ e₂.hom = e₁.hom ≫ (g ▷ A) := hnat
      _ = (e₁.hom ≫ (g ▷ A) ≫ e₂.inv) ≫ e₂.hom := by simp
  rw [heq]
  infer_instance

theorem AlgebraicGeometry.Scheme.Modules.epi_tensorHom {X : AlgebraicGeometry.Scheme.{u}}
    {A A' B B' : X.Modules} (f : A ⟶ A') (g : B ⟶ B')
    (hf : Epi f) (hg : Epi g) :
    Epi (CategoryTheory.MonoidalCategoryStruct.tensorHom (C := X.Modules) f g) := by
  letI := AlgebraicGeometry.Scheme.Modules.monoidalCategory X
  letI : Epi f := hf
  letI : Epi g := hg
  rw [MonoidalCategory.tensorHom_def]
  haveI : Epi (f ▷ B) := epi_whiskerRight f
  haveI : Epi (A' ◁ g) := epi_whiskerLeft g
  exact epi_comp _ _

end
