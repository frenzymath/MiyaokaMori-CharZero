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

/-! # Instances for sheaves of modules of finite type

Instances showing that finite type is preserved by `V^{⊕n}` (`Modules.pow`), by the dual of a locally
free sheaf of finite type, by pullback, and by tensor products (one instance for `Modules.tensor` and
one for the monoidal `⊗`). They let the `[V.IsFiniteType]` hypotheses of `projBundle` / `totalSpace` /
`zeroSection` / `totalSpaceHomEquiv` be synthesized automatically for `A^{⊕(N+1)}`, `V^∨`, `f^*V`,
`V ⊗ W`.

Source: Stacks 01B6, 01CE.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open scoped CategoryTheory.MonoidalCategory

private theorem sheafification_tensor_map_epi {X : AlgebraicGeometry.Scheme.{u}}
    {A B P : X.Modules} (f : A ⟶ B) [Epi f] :
    Epi ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (((SheafOfModules.forget X.ringCatSheaf ⋙
        PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map f) ▷
        ((SheafOfModules.forget X.ringCatSheaf ⋙
          PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj P))) := by
  let J := Opens.grothendieckTopology X
  let f₀ := (SheafOfModules.forget X.ringCatSheaf ⋙
    PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map f
  let p₀ := (SheafOfModules.forget X.ringCatSheaf ⋙
    PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj P
  have hf : Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf
        (X.presheaf ⋙ forget₂ CommRingCat RingCat)).map f₀) := by
    change Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf
        (X.presheaf ⋙ forget₂ CommRingCat RingCat)).map
        ((SheafOfModules.forget X.ringCatSheaf ⋙
          PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map f))
    exact (ModulesLocLiftAux.locSurj_iff f).mp (ModulesLocLiftAux.locSurj_of_epi f)
  letI : Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      ((PresheafOfModules.toPresheaf
        (X.presheaf ⋙ forget₂ CommRingCat RingCat)).map
        ((SheafOfModules.forget X.ringCatSheaf ⋙
          PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map f)) := by
    exact hf
  have htp := PresheafOfModules.isLocallySurjective_whiskerRight
    (R := X.presheaf) (M := (SheafOfModules.forget X.ringCatSheaf ⋙
      PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj A)
    (N := (SheafOfModules.forget X.ringCatSheaf ⋙
      PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj B)
    J ((SheafOfModules.forget X.ringCatSheaf ⋙
      PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map f) p₀
  have htp' : Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf
        (X.presheaf ⋙ forget₂ CommRingCat RingCat)).map (f₀ ▷ p₀)) := htp
  let sf := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let g := sf.map (f₀ ▷ p₀)
  have hg : Epi g := by
    have hloc : Sheaf.IsLocallySurjective
        ((CategoryTheory.presheafToSheaf J AddCommGrpCat).map
          ((PresheafOfModules.toPresheaf
            (X.presheaf ⋙ forget₂ CommRingCat RingCat)).map (f₀ ▷ p₀))) :=
      (Presheaf.isLocallySurjective_presheafToSheaf_map_iff J
        ((PresheafOfModules.toPresheaf
          (X.presheaf ⋙ forget₂ CommRingCat RingCat)).map (f₀ ▷ p₀))).2 htp'
    have hloc' : TopCat.Presheaf.IsLocallySurjective
        ((SheafOfModules.toSheaf X.ringCatSheaf).map g).hom := by
      change Sheaf.IsLocallySurjective
        ((CategoryTheory.presheafToSheaf J AddCommGrpCat).map
        ((PresheafOfModules.toPresheaf
          (X.presheaf ⋙ forget₂ CommRingCat RingCat)).map (f₀ ▷ p₀)))
      exact hloc
    have he : Epi ((SheafOfModules.toSheaf X.ringCatSheaf).map g) :=
      (TopCat.Sheaf.isLocallySurjective_iff_epi _).mp hloc'
    exact (SheafOfModules.toSheaf X.ringCatSheaf).epi_of_epi_map he
  exact hg

private theorem epi_whiskerRight {X : AlgebraicGeometry.Scheme.{u}}
    {A B P : X.Modules} (f : A ⟶ B) [Epi f] : Epi (f ▷ P) := by
  letI := AlgebraicGeometry.Scheme.Modules.monoidalCategory X
  let F := (SheafOfModules.forget X.ringCatSheaf ⋙
    PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj))
  let f₀ := F.map f
  let p₀ := F.obj P
  let sf := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
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
      PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat))
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

private theorem epi_whiskerLeft {X : AlgebraicGeometry.Scheme.{u}}
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

private theorem epi_tensorHom {X : AlgebraicGeometry.Scheme.{u}}
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

private theorem finiteType_tensorObj {X : AlgebraicGeometry.Scheme.{u}} (F G : X.Modules)
    [F.IsFiniteType] [G.IsFiniteType] :
    (CategoryTheory.MonoidalCategoryStruct.tensorObj (C := X.Modules) F G).IsFiniteType := by
  refine AlgebraicGeometry.Scheme.Modules.isFiniteType_of_epi_free_pullback _ (fun x => ?_)
  obtain ⟨UF, J, hJ, πF, hxF, hπF⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_epi_free_pullback_of_isFiniteType F x
  obtain ⟨UG, K, hK, πG, hxG, hπG⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_epi_free_pullback_of_isFiniteType G x
  have hxV : x ∈ (UF ⊓ UG : X.Opens) := ⟨hxF, hxG⟩
  letI := AlgebraicGeometry.Scheme.Modules.monoidalCategory (UF ⊓ UG).toScheme
  obtain ⟨πF', hπF'⟩ :=
    AlgebraicGeometry.Scheme.Modules.epi_free_pullback_of_le F inf_le_left J πF hπF
  obtain ⟨πG', hπG'⟩ :=
    AlgebraicGeometry.Scheme.Modules.epi_free_pullback_of_le G inf_le_right K πG hπG
  letI : Epi πF' := hπF'
  letI : Epi πG' := hπG'
  let t := CategoryTheory.MonoidalCategoryStruct.tensorHom (C := (UF ⊓ UG).toScheme.Modules)
    πF' πG'
  have ht : Epi t := by
    dsimp [t]
    exact epi_tensorHom (X := (UF ⊓ UG).toScheme) πF' πG' hπF' hπG'
  let e := AlgebraicGeometry.Scheme.Modules.freeTensorFreeIso
    (X := (UF ⊓ UG).toScheme) J K
  have he : Epi e.inv := by
    letI : IsIso e.inv := Iso.isIso_inv e
    exact IsIso.epi_of_iso e.inv
  letI : Epi e.inv := he
  letI : Epi t := ht
  let q := e.inv ≫ t ≫
    (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjIsoOpen (UF ⊓ UG).ι F G).inv
  have hq : Epi q := by
    dsimp [q]
    exact epi_comp _ _
  exact ⟨UF ⊓ UG, J × K, inferInstance, q, hxV, hq⟩

private theorem finiteType_of_iso {X : AlgebraicGeometry.Scheme.{u}}
    {M N : X.Modules} (e : M ≅ N) [M.IsFiniteType] : N.IsFiniteType := by
  refine AlgebraicGeometry.Scheme.Modules.isFiniteType_of_epi_free_pullback N (fun x => ?_)
  obtain ⟨U, J, hJ, π, hx, hπ⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_epi_free_pullback_of_isFiniteType M x
  let e' := (AlgebraicGeometry.Scheme.Modules.pullback U.ι).mapIso e
  let π' := π ≫ e'.hom
  have he : Epi e'.hom := by
    letI : IsIso e'.hom := Iso.isIso_hom e'
    exact IsIso.epi_of_iso e'.hom
  letI : Epi e'.hom := he
  have hp : Epi π' := by
    dsimp [π']
    exact @epi_comp _ _ _ _ _ _ hπ _ he
  exact ⟨U, J, hJ, π', hx, hp⟩

private theorem finiteType_tensor {X : AlgebraicGeometry.Scheme.{u}} (F G : X.Modules)
    [F.IsFiniteType] [G.IsFiniteType] :
    (AlgebraicGeometry.Scheme.Modules.tensor F G).IsFiniteType := by
  letI := AlgebraicGeometry.Scheme.Modules.monoidalCategory X
  letI : (CategoryTheory.MonoidalCategoryStruct.tensorObj (C := X.Modules) F G).IsFiniteType :=
    finiteType_tensorObj F G
  exact finiteType_of_iso (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj F G).symm

/- Instances for finite type. `projBundle` / `totalSpace` / `zeroSection` / `totalSpaceHomEquiv` require
   `[V.IsFiniteType]` (otherwise `V^∨` need not be quasi-coherent and `Sym(V^∨)` falls into the trivial
   branch of a `dite`); the instances below make sure that the sheaves occurring in the paper,
   `V = A^{⊕(N+1)}`, `O ⊕ L`, `L`, `f^*V`, `V^∨`, `V ⊗ W`, are found to be of finite type by instance
   search. Line bundle ⇒ finite type is in `SheafOfModulesIsLineBundle`; finite and binary biproducts in
   `ModulesBiproductLocallyFree` / `ModulesBiprodLocallyFree`. -/

/-- `V^{⊕n}` is of finite type: `Modules.pow` is an irreducible `def` that instance search does not see
through; unfold it and use the instance for finite biproducts. -/

instance AlgebraicGeometry.Scheme.Modules.pow_isFiniteType {X : AlgebraicGeometry.Scheme.{u}}
    (V : X.Modules) [V.IsFiniteType] (n : ℕ) : (AlgebraicGeometry.Scheme.Modules.pow V n).IsFiniteType := by
  unfold AlgebraicGeometry.Scheme.Modules.pow
  infer_instance

/- The structure sheaf is of finite type and locally free (`IsLineBundle.unit` gives this through the
   priority-100 line bundle instances, but instance search fails to match the conclusion of
   `IsLineBundle.isFiniteType` on `SheafOfModules.unit`, so it is registered directly); likewise `O^{⊕n}`
   is registered separately (the pattern of `pow_isFiniteType` does not match on `pow (unit …) n`). -/

instance AlgebraicGeometry.Scheme.Modules.unit_isFiniteType (X : AlgebraicGeometry.Scheme.{u}) :
    (SheafOfModules.unit X.ringCatSheaf).IsFiniteType :=
  SheafOfModules.IsLineBundle.isFiniteType (X := X) (SheafOfModules.unit X.ringCatSheaf)

instance AlgebraicGeometry.Scheme.Modules.unit_isLocallyFree (X : AlgebraicGeometry.Scheme.{u}) :
    (SheafOfModules.unit X.ringCatSheaf).IsLocallyFree :=
  SheafOfModules.IsLineBundle.isLocallyFree (X := X) (SheafOfModules.unit X.ringCatSheaf)

instance AlgebraicGeometry.Scheme.Modules.powUnit_isFiniteType (X : AlgebraicGeometry.Scheme.{u}) (n : ℕ) :
    (AlgebraicGeometry.Scheme.Modules.pow (SheafOfModules.unit X.ringCatSheaf) n).IsFiniteType :=
  AlgebraicGeometry.Scheme.Modules.pow_isFiniteType _ n

instance AlgebraicGeometry.Scheme.Modules.powUnit_isLocallyFree (X : AlgebraicGeometry.Scheme.{u}) (n : ℕ) :
    (AlgebraicGeometry.Scheme.Modules.pow (SheafOfModules.unit X.ringCatSheaf) n).IsLocallyFree :=
  AlgebraicGeometry.Scheme.Modules.pow_isLocallyFree _ n

/-- The dual of a locally free sheaf of finite type is of finite type (instance form of
`isFiniteType_dual`). -/

instance AlgebraicGeometry.Scheme.Modules.dual_isFiniteType {X : AlgebraicGeometry.Scheme.{u}}
    (E : X.Modules) [E.IsLocallyFree] [E.IsFiniteType] :
    (AlgebraicGeometry.Scheme.Modules.dual E).IsFiniteType :=
  AlgebraicGeometry.Scheme.Modules.isFiniteType_dual E inferInstance

/-- Pullback preserves finite type (Stacks 01B6; instance form of `isFiniteType_pullback`). -/

instance AlgebraicGeometry.Scheme.Modules.pullback_isFiniteType {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) (F : Y.Modules) [F.IsFiniteType] :
    ((AlgebraicGeometry.Scheme.Modules.pullback f).obj F).IsFiniteType :=
  AlgebraicGeometry.Scheme.Modules.isFiniteType_pullback f F

/- The tensor product preserves finite type (Stacks 01CE(3)): locally `O^m ↠ F`, `O^n ↠ G` give
   `O^{mn} ↠ F ⊗ G` (`⊗` is right exact). One instance for each spelling: `Modules.tensor` and the `⊗` of
   Mathlib's localized monoidal structure (isomorphic via `tensorIsoTensorObj`). -/

instance AlgebraicGeometry.Scheme.Modules.tensor_isFiniteType {X : AlgebraicGeometry.Scheme.{u}}
    (F G : X.Modules) [F.IsFiniteType] [G.IsFiniteType] :
    (AlgebraicGeometry.Scheme.Modules.tensor F G).IsFiniteType := by
  exact finiteType_tensor F G

instance AlgebraicGeometry.Scheme.Modules.tensorObj_isFiniteType {X : AlgebraicGeometry.Scheme.{u}}
    (F G : X.Modules) [F.IsFiniteType] [G.IsFiniteType] :
    (F ⊗ G).IsFiniteType := by
  exact finiteType_tensorObj F G

end
