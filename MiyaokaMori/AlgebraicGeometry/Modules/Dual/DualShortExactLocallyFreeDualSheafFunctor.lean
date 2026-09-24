import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.DualSheaf
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.DualRestrictOpen

/-! # The dual sheaf as an additive functor commuting with restriction to opens

This file supports `DualShortExactLocallyFree`.

* `dualSheafFunctor X : X.Modulesᵒᵖ ⥤ X.Modules`: the sheafification-free dual
  `AlgebraicGeometry.Scheme.Modules.dualSheaf` (`DualSheaf`; sections = compatible families of local functionals,
  `AlgebraicGeometry.Scheme.Modules.LocalDualSections`) made contravariantly functorial by precomposition
  (`AlgebraicGeometry.Scheme.Modules.moduleDualPresheafPrecomp`, in `ModuleDualFunctor`).
* `dualSheafFunctor_additive`: it is additive (precomposition is additive in the morphism;
  checked on sections). Stated as a theorem, used via `letI` — no global instance.
* `dualSheafRestrictNatIso X U : dualSheafFunctor X ⋙ restrictFunctor U.ι ≅
  (restrictFunctor U.ι).op ⋙ dualSheafFunctor U`: the dual commutes with restriction to an open
  `U`, **naturally** in the module. Objectwise this is `DualRestrictOpen`'s
  `openLocalDualRestrictLinearEquiv` (a functional on `Γ(U.ι ''ᵁ W, M)` is the same thing as a
  functional on `Γ(W, M|_U)`; only the scalar ring is renamed along `U.ι.appIso W`, which is the
  identity, `Scheme.Opens.ι_appIso`). Naturality is `rfl` on sections because both sides send a
  family `α` to `W ↦ α (U.ι ''ᵁ W) ∘ φ (U.ι ''ᵁ W)`. Since `dualSheaf` is not a sheafification,
  no unit/descent argument is needed (contrast `Scheme.Modules.dual_restrict`, which is only an
  objectwise `Nonempty` iso).

Source: Stacks 01CM (internal Hom `𝓗om(F, G)(U) = Hom_{O_U}(F|_U, G|_U)` is compatible with
restriction by definition).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- The morphism `N^∨ ⟶ M^∨` of sheafification-free duals induced by `φ : M ⟶ N`
(precomposition of every local functional with `φ`). -/
def dualSheafMap {M N : X.Modules} (φ : M ⟶ N) : dualSheaf N ⟶ dualSheaf M :=
  ⟨AlgebraicGeometry.Scheme.Modules.moduleDualPresheafPrecomp φ⟩

theorem dualSheafMap_id (M : X.Modules) : dualSheafMap (𝟙 M) = 𝟙 (dualSheaf M) :=
  SheafOfModules.Hom.ext (AlgebraicGeometry.Scheme.Modules.moduleDualPresheafPrecomp_id M)

theorem dualSheafMap_comp {M N P : X.Modules} (φ : M ⟶ N) (ψ : N ⟶ P) :
    dualSheafMap (φ ≫ ψ) = dualSheafMap ψ ≫ dualSheafMap φ :=
  SheafOfModules.Hom.ext (AlgebraicGeometry.Scheme.Modules.moduleDualPresheafPrecomp_comp φ ψ)

set_option backward.isDefEq.respectTransparency false in
theorem dualSheafMap_add {M N : X.Modules} (φ ψ : M ⟶ N) :
    dualSheafMap (φ + ψ) = dualSheafMap φ + dualSheafMap ψ := by
  refine SheafOfModules.Hom.ext (PresheafOfModules.hom_ext fun V => ?_)
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro α
  apply Subtype.ext
  funext W
  apply LinearMap.ext
  intro x
  change α.val W (φ.app W.left x + ψ.app W.left x) =
    α.val W (φ.app W.left x) + α.val W (ψ.app W.left x)
  exact _root_.map_add _ _ _

/-- The sheafification-free dual `M ↦ M^∨ = 𝓗om(M, O_X)` as a contravariant functor. -/
def dualSheafFunctor (X : Scheme.{u}) : X.Modulesᵒᵖ ⥤ X.Modules where
  obj M := dualSheaf M.unop
  map φ := dualSheafMap φ.unop
  map_id M := dualSheafMap_id M.unop
  map_comp φ ψ := dualSheafMap_comp ψ.unop φ.unop

theorem dualSheafFunctor_additive (X : Scheme.{u}) : (dualSheafFunctor X).Additive where
  map_add {_ _ f g} := dualSheafMap_add f.unop g.unop

section Restrict

variable (X) (U : X.Opens) (M : X.Modules)

set_option backward.isDefEq.respectTransparency false in
/-- Sections of `(M^∨)|_U` over `V ⊆ U` are sections of `(M|_U)^∨` over `V`: same compatible
family of functionals, scalars renamed along `U.ι.appIso V = Iso.refl` (`Scheme.Opens.ι_appIso`).
Typed exactly as `PresheafOfModules.isoMk` expects (objects of `ModuleCat (𝒪_U(V))`), so that no
`CommRingCat`/`RingCat` carrier defeq is left to the kernel. -/
def dualSheafRestrictLinearEquiv (V : U.toScheme.Opensᵒᵖ) :
    ((restrictFunctor U.ι).obj (dualSheaf M)).val.obj V ≃ₗ[U.toScheme.ringCatSheaf.obj.obj V]
      (dualSheaf ((restrictFunctor U.ι).obj M)).val.obj V where
  toFun x := MiyaokaMori.DualRestrictScratch.openLocalDualRestrictLinearEquiv X U M V.unop x
  invFun y :=
    (MiyaokaMori.DualRestrictScratch.openLocalDualRestrictLinearEquiv X U M V.unop).symm y
  map_add' x y :=
    _root_.map_add (MiyaokaMori.DualRestrictScratch.openLocalDualRestrictLinearEquiv X U M V.unop)
      x y
  map_smul' r x :=
    (congrArg (MiyaokaMori.DualRestrictScratch.openLocalDualRestrictLinearEquiv X U M V.unop)
      (MiyaokaMori.DualRestrictScratch.openRestrict_smul X U (dualSheaf M) V.unop r x)).trans
      ((MiyaokaMori.DualRestrictScratch.openLocalDualRestrictLinearEquiv X U M V.unop).map_smul r
        (show LocalDualSections X M (U.ι ''ᵁ V.unop) from x))
  left_inv x :=
    (MiyaokaMori.DualRestrictScratch.openLocalDualRestrictLinearEquiv X U M V.unop).left_inv x
  right_inv y :=
    (MiyaokaMori.DualRestrictScratch.openLocalDualRestrictLinearEquiv X U M V.unop).right_inv y

set_option backward.isDefEq.respectTransparency false in
/-- `(M^∨)|_U ≅ (M|_U)^∨` at the level of presheaves of modules. -/
def dualSheafRestrictPresheafIso :
    ((restrictFunctor U.ι).obj (dualSheaf M)).val ≅ (dualSheaf ((restrictFunctor U.ι).obj M)).val :=
  PresheafOfModules.isoMk (fun V ↦ (dualSheafRestrictLinearEquiv X U M V).toModuleIso) (by
    intro V W j
    ext φ
    rfl)

/-- `(M^∨)|_U ≅ (M|_U)^∨` as sheaves of modules on `U`. -/
def dualSheafRestrictIso :
    (restrictFunctor U.ι).obj (dualSheaf M) ≅ dualSheaf ((restrictFunctor U.ι).obj M) :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso (dualSheafRestrictPresheafIso X U M)

set_option backward.isDefEq.respectTransparency false in
/-- The dual commutes with restriction to an open subscheme, naturally in the module. -/
def dualSheafRestrictNatIso :
    dualSheafFunctor X ⋙ restrictFunctor U.ι ≅
      (restrictFunctor U.ι).op ⋙ dualSheafFunctor U.toScheme :=
  NatIso.ofComponents (fun M ↦ dualSheafRestrictIso X U M.unop) (by
    intro M N φ
    refine SheafOfModules.Hom.ext (PresheafOfModules.hom_ext fun V => ?_)
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro α
    apply Subtype.ext
    funext W
    apply LinearMap.ext
    intro x
    rfl)

end Restrict

end AlgebraicGeometry.Scheme.Modules

end
