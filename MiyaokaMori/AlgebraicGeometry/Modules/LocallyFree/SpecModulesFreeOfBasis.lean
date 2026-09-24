import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.ModulesUnitHomTopSection
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.TildeBasisFrame

/-! # A quasi-coherent module on `Spec R` with a basis of global sections is free

For a quasi-coherent module `M` on an affine scheme `Spec R` whose global sections `Γ(M, ⊤)` have an
`R`-basis `b : I → Γ(M, ⊤)`, the canonical morphism `free I ⟶ M` sending the `i`-th generator to `b i`
is an isomorphism. More generally, for any scheme `X`, any module `M` and any family of global
sections `v : I → Γ(M, ⊤)`, the canonical morphism `freeHomOfTopSections M v : free I ⟶ M` (the
inverse of `SheafOfModules.freeHomEquiv`) is defined and its values on the generators are recorded.

Proof sketch:
1. `freeHomOfTopSections` comes from Mathlib's `freeHomEquiv`; `ιFree i ≫ freeHomOfTopSections M v` is
   `homOfTopSection M (v i)` (`unitHomEquiv_symm_freeHomEquiv_apply`), which sends `1` on `⊤` to `v i`.
2. On `Spec R`: Mathlib's `fromTildeΓ : tilde Γ(M,⊤) ⟶ M` is an isomorphism for quasi-coherent `M`
   (`isIso_fromTildeΓ_of_isQuasicoherent`), and `TildeBasisFrame.basisIso b : tilde Γ(M,⊤) ≅ free I` is
   given by the basis. `freeHomOfTopSections M b = (basisIso b).inv ≫ fromTildeΓ`: both are morphisms
   out of `free I`, compared on generators (`Cofan.IsColimit.hom_ext`); the right side on `ιFree i` is
   `tildeSelf.inv ≫ tilde.map (toSpanSingleton (b i)) ≫ fromTildeΓ` (`ιFree_tildeFinsupp_inv`,
   `lsingle_repr_inv`), and `tilde.toOpen (of R R) ⊤ 1 = 1` (`StructureSheaf.const_one`),
   `toOpen_map_app`, `toOpen_fromTildeΓ_app` compute that it sends `1` on `⊤` to `b i`, matching the
   left side (`unitHomEquivTop` is injective).
3. Hence `freeHomOfTopSections M b` is a composite of two isomorphisms.

References: Stacks 01I7/01I8 (a quasi-coherent sheaf is determined by its global sections); Mathlib
`AlgebraicGeometry.Modules.Tilde`; `TildeBasisFrame`. Used for the local algebra isomorphism of the
fibres of the weighted projectivization (§2 of the paper).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

section General

variable {X : Scheme.{u}} (M : X.Modules) {I : Type u} (v : I → Γ(M, ⊤))

/-- The canonical morphism `free I ⟶ M` determined by a family of global sections `v : I → Γ(M, ⊤)`,
`i`-th generator `↦ v i`. -/
def freeHomOfTopSections : (SheafOfModules.free (R := X.ringCatSheaf) I : X.Modules) ⟶ M :=
  (SheafOfModules.freeHomEquiv M).symm
    (fun i => (SheafOfModules.unitHomEquiv M) (homOfTopSection M (v i)))

theorem ιFree_comp_freeHomOfTopSections (i : I) :
    SheafOfModules.ιFree (R := X.ringCatSheaf) i ≫ freeHomOfTopSections M v =
      homOfTopSection M (v i) := by
  refine (SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply (freeHomOfTopSections M v) i).symm.trans ?_
  unfold freeHomOfTopSections
  rw [Equiv.apply_symm_apply, Equiv.symm_apply_apply]

/-- The `1` on `⊤` of the generator `ιFree i` is sent to `v i`. -/
theorem freeHomOfTopSections_app_top_ιFree (i : I) :
    Scheme.Modules.Hom.app (M := (SheafOfModules.free (R := X.ringCatSheaf) I : X.Modules)) (N := M)
      (freeHomOfTopSections M v) ⊤
      (Scheme.Modules.Hom.app (M := (SheafOfModules.unit X.ringCatSheaf : X.Modules))
        (N := (SheafOfModules.free (R := X.ringCatSheaf) I : X.Modules))
        (SheafOfModules.ιFree (R := X.ringCatSheaf) i) ⊤ (1 : Γ(X, ⊤))) = v i := by
  have h := congrArg (fun k : SheafOfModules.unit X.ringCatSheaf ⟶ M => topSectionOfHom M k)
    (ιFree_comp_freeHomOfTopSections M v i)
  exact h.trans ((unitHomEquivTop M).right_inv (v i))

end General

section Spec

variable {R : CommRingCat.{u}}

theorem tilde_toOpen_self_top_one :
    (tilde.toOpen (ModuleCat.of R R) ⊤).hom (1 : R) = (1 : Γ(Spec R, ⊤)) := by
  show ((StructureSheaf.toOpenₗ R R ⊤) 1 : Γ(Spec R, ⊤)) = 1
  rw [StructureSheaf.toOpenₗ_eq_const]
  exact StructureSheaf.const_one ⊤

/-- `ιFree i ≫ (basisIso b).inv` is `tildeSelf.inv ≫ tilde.map (toSpanSingleton (b i))`
(a proof of `TildeBasisFrame.ιFree_basisIso_inv`). -/
theorem ιFree_basisIso_inv' {M : ModuleCat.{u} R} {I : Type u} (b : Module.Basis I R M) (i : I) :
    SheafOfModules.ιFree (R := (Spec R).ringCatSheaf) i ≫
        (AlgebraicGeometry.Scheme.Modules.TildeBasisFrame.basisIso b).inv =
      (tildeSelf (R := R)).inv ≫
        tilde.map (ModuleCat.ofHom (LinearMap.toSpanSingleton R M (b i))) := by
  show SheafOfModules.ιFree i ≫ ((tildeFinsupp I).inv ≫ tilde.map b.repr.toModuleIso.inv) = _
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun k => k ≫ tilde.map b.repr.toModuleIso.inv)
    (AlgebraicGeometry.Scheme.Modules.TildeBasisFrame.ιFree_tildeFinsupp_inv I i)).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine congrArg (fun k => (tildeSelf (R := R)).inv ≫ k) ?_
  refine (tilde.map_comp _ _).symm.trans ?_
  exact congrArg tilde.map (AlgebraicGeometry.Scheme.Modules.TildeBasisFrame.lsingle_repr_inv b i)

/-- The pointwise form of `toOpen_fromTildeΓ_app` on `⊤`. -/
theorem fromTildeΓ_app_top_toOpen (M : (Spec R).Modules)
    (y : (modulesSpecToSheaf.obj M).presheaf.obj (.op ⊤)) :
    (M.fromTildeΓ.val.app (op ⊤)).hom ((tilde.toOpen _ ⊤).hom y) = y := by
  have h := congrArg (fun k => k.hom y) (Scheme.Modules.toOpen_fromTildeΓ_app M ⊤)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  refine h.trans ?_
  rw [show (homOfLE (le_top : (⊤ : (Spec R).Opens) ≤ ⊤)).op = 𝟙 (op (⊤ : (Spec R).Opens)) from rfl,
    (modulesSpecToSheaf.obj M).1.map_id]
  rfl

theorem tilde_map_app_top_toOpen {M N : ModuleCat.{u} R} (f : M ⟶ N) (x : M) :
    ((tilde.map f).val.app (op ⊤)).hom ((tilde.toOpen M ⊤).hom x) =
      (tilde.toOpen N ⊤).hom (f.hom x) := by
  have h := congrArg (fun k => k.hom x) (tilde.toOpen_map_app f ⊤)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h

/-- Under `tilde (of R R) = 𝒪`, `tilde.map (r ↦ r • v) ≫ fromTildeΓ` is "`1 ↦ v`". -/
theorem tilde_map_toSpanSingleton_comp_fromTildeΓ (M : (Spec R).Modules) (v : Γ(M, ⊤)) :
    (tilde.map (ModuleCat.ofHom (LinearMap.toSpanSingleton R
        ((modulesSpecToSheaf.obj M).presheaf.obj (.op ⊤)) v)) ≫ M.fromTildeΓ :
      SheafOfModules.unit (Spec R).ringCatSheaf ⟶ M) =
      homOfTopSection M v := by
  apply (unitHomEquivTop M).injective
  refine Eq.trans ?_ ((unitHomEquivTop M).right_inv v).symm
  show (M.fromTildeΓ.val.app (op ⊤)).hom
    (((tilde.map (ModuleCat.ofHom (LinearMap.toSpanSingleton R
        ((modulesSpecToSheaf.obj M).presheaf.obj (.op ⊤)) v))).val.app (op ⊤)).hom
      (1 : Γ(Spec R, ⊤))) = v
  rw [← tilde_toOpen_self_top_one, tilde_map_app_top_toOpen, fromTildeΓ_app_top_toOpen]
  exact one_smul R v

variable (M : (Spec R).Modules) {I : Type u} (b : Module.Basis I R Γ(M, ⊤))

/-- The canonical morphism of a basis is the composite of the inverse of `basisIso b` with
`fromTildeΓ`. -/
theorem freeHomOfTopSections_basis_eq :
    freeHomOfTopSections M (fun i => b i) =
      (AlgebraicGeometry.Scheme.Modules.TildeBasisFrame.basisIso
        (M := (modulesSpecToSheaf.obj M).presheaf.obj (.op ⊤)) b).inv ≫ M.fromTildeΓ := by
  refine Cofan.IsColimit.hom_ext (SheafOfModules.isColimitFreeCofan (R := (Spec R).ringCatSheaf) I)
    _ _ (fun i => ?_)
  rw [SheafOfModules.freeCofan_inj]
  have h1 : SheafOfModules.ιFree (R := (Spec R).ringCatSheaf) i ≫
      freeHomOfTopSections M (fun i => b i) = homOfTopSection M (b i) :=
    ιFree_comp_freeHomOfTopSections M (fun i => b i) i
  have h2 : SheafOfModules.ιFree (R := (Spec R).ringCatSheaf) i ≫
      ((AlgebraicGeometry.Scheme.Modules.TildeBasisFrame.basisIso
        (M := (modulesSpecToSheaf.obj M).presheaf.obj (.op ⊤)) b).inv ≫ M.fromTildeΓ) =
      ((tildeSelf (R := R)).inv ≫ tilde.map (ModuleCat.ofHom (LinearMap.toSpanSingleton R
        ((modulesSpecToSheaf.obj M).presheaf.obj (.op ⊤)) (b i)))) ≫ M.fromTildeΓ := by
    refine (Category.assoc _ _ _).symm.trans ?_
    exact congrArg (fun k => k ≫ M.fromTildeΓ)
      (ιFree_basisIso_inv' (M := (modulesSpecToSheaf.obj M).presheaf.obj (.op ⊤)) b i)
  have h3 : ((tildeSelf (R := R)).inv ≫ tilde.map (ModuleCat.ofHom (LinearMap.toSpanSingleton R
        ((modulesSpecToSheaf.obj M).presheaf.obj (.op ⊤)) (b i)))) ≫ M.fromTildeΓ =
      homOfTopSection M (b i) := by
    refine Eq.trans ?_ (tilde_map_toSpanSingleton_comp_fromTildeΓ M (b i))
    exact congrArg (fun k => k ≫ M.fromTildeΓ) (Category.id_comp _)
  exact h1.trans (h3.symm.trans h2.symm)

/-- **Quasi-coherent with a basis of global sections ⇒ the canonical morphism is an isomorphism.** -/
theorem isIso_freeHomOfTopSections_basis [M.IsQuasicoherent] :
    IsIso (freeHomOfTopSections M (fun i => b i)) := by
  rw [freeHomOfTopSections_basis_eq M b]
  have h1 : IsIso M.fromTildeΓ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent M
  have h2 : IsIso (AlgebraicGeometry.Scheme.Modules.TildeBasisFrame.basisIso
      (M := (modulesSpecToSheaf.obj M).presheaf.obj (.op ⊤)) b).inv :=
    ⟨⟨(AlgebraicGeometry.Scheme.Modules.TildeBasisFrame.basisIso
      (M := (modulesSpecToSheaf.obj M).presheaf.obj (.op ⊤)) b).hom,
      Iso.inv_hom_id _, Iso.hom_inv_id _⟩⟩
  exact IsIso.comp_isIso' h2 h1

end Spec

end AlgebraicGeometry.Scheme.Modules

end
