import MiyaokaMori.AlgebraicGeometry.Modules.ExteriorPower.ExteriorPowerRestrictionIso
import MiyaokaMori.AlgebraicGeometry.Modules.ExteriorPower.ExteriorDualComparisonIsoExt

/-!
# The exterior-restriction comparison along `U.ι` is an isomorphism

`moduleExteriorRestrictComparison U.ι M n : ⋀ⁿ(M|_U) ⟶ (⋀ⁿM)|_U` (`ExteriorPowerRestriction`) is identified
with `sheafification.map (exteriorRestrictPresheafIso M n U).inv ≫ openModuleSheafificationMap X U (⋀ⁿ_pre M)`
(`restrictComparison_eq`): both are maps out of the sheafified exterior power of `M|_U`
(`moduleExteriorPower_hom_ext` reduces to wedge sections over `V`), and both send the wedge of sections over `V`
to the wedge of the same sections over `U.ι ''ᵁ V`. The second factor is invertible by the theorem
`openModuleSheafificationMap_isIso` ("sheafification commutes with restriction to an open"), so the comparison is
an isomorphism (`moduleExteriorRestrictComparison_isIso`).

The presheaf identification `openModulePresheafRestrictIso` is an `Eq.mpr`-cast of `Iso.refl` (produced
by `simp only [Scheme.Opens.ι_appIso]`), whose value on sections cannot be computed outside its file, so
a computable copy `restrictPresheafIso` (the identity on sections) is built here;
`moduleExteriorPowerRestrictIso` itself is not used. This is kept in its own module: the kernel check of
`openModuleSheafificationMap_app_unit` takes about 25 s (it has to identify the sheafification
instances synthesized in `OpenModuleSheafification` with the ones synthesized here).

Sources: Stacks Project, `modules.tex`, `lemma-stalk-tensor-algebra` (exterior powers commute with
restriction to opens); `sheaves.tex`, restriction of a sheafification to an open.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

namespace AlgebraicGeometry.Scheme.Modules

universe u

set_option backward.isDefEq.respectTransparency false

namespace ExteriorPowerRestrictionComparison

variable {X : Scheme.{u}} (M : X.Modules) (n : ℕ) (U : X.Opens)

/-- The restricted exterior power of `M` is the exterior power of the restriction: the wedge of
restricted sections goes to the wedge over the image open. -/
theorem restrictComparison_wedge (V : U.toScheme.Opens) (w : Fin n → Γ(M.restrict U.ι, V)) :
    (moduleExteriorRestrictComparison U.ι M n).app V
        (moduleExteriorWedge U.toScheme (M.restrict U.ι) n V w) =
      moduleExteriorWedge X M n (U.ι ''ᵁ V) w := by
  rw [moduleExteriorRestrictComparison_wedge]
  rfl

/- The ring of sections of `U.toScheme` in the spelling used by the sheafification API. -/
local instance restrictCommRing {Y : Scheme.{u}} (V : Y.Opensᵒᵖ) :
    CommRing (Y.ringCatSheaf.obj.obj V) :=
  inferInstanceAs (CommRing Γ(Y, V.unop))

open MiyaokaMori.ExteriorPowerRestrictionIso

/-- Sections of `F` over `U.ι ''ᵁ V`, as the module of sections of the presheaf restriction and as
the module of sections of `F.restrict U.ι`: the identity map. (The two module structures differ only
by the scalar map `(U.ι.appIso V).inv`, which is the identity by `Scheme.Opens.ι_appIso`.) -/
def restrictSectionsLinearEquiv (F : X.Modules) (V : U.toScheme.Opensᵒᵖ) :
    ((openModulePresheafRestrictFunctor X U).obj F.val).obj V ≃ₗ[U.toScheme.ringCatSheaf.obj.obj V]
      ((Scheme.Modules.restrictFunctor U.ι).obj F).val.obj V where
  toFun x := x
  invFun x := x
  map_add' _ _ := rfl
  map_smul' r x := by
    unfold Scheme.Modules.restrictFunctor
    rw [ModuleCat.restrictScalars.smul_def]
    simp only [Scheme.Opens.ι_appIso, Iso.refl_inv]
    rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- The presheaf restriction of `F.val` to `U` is the presheaf of `F.restrict U.ι`; the identity on
sections (a computable version of `openModulePresheafRestrictIso`, whose `Eq.mpr`-cast components
cannot be evaluated). -/
def restrictPresheafIso (F : X.Modules) :
    (openModulePresheafRestrictFunctor X U).obj F.val ≅ ((Scheme.Modules.restrictFunctor U.ι).obj F).val :=
  PresheafOfModules.isoMk (fun V ↦ (restrictSectionsLinearEquiv U F V).toModuleIso) (by
    intro V W j
    ext x
    rfl)

theorem restrictPresheafIso_inv_app (F : X.Modules) (V : U.toScheme.Opensᵒᵖ)
    (x : ((Scheme.Modules.restrictFunctor U.ι).obj F).val.obj V) :
    (restrictPresheafIso U F).inv.app V x = x := rfl

/-- The exterior presheaf of `M.restrict U.ι` is the presheaf restriction of the exterior presheaf
of `M` (identity on wedges). -/
def exteriorRestrictPresheafIso :
    (openModulePresheafRestrictFunctor X U).obj (moduleExteriorPresheaf X M.val n) ≅
      moduleExteriorPresheaf U.toScheme (M.restrict U.ι).val n :=
  exteriorPresheafRestrictIso X U M.val n ≪≫
    (moduleExteriorPresheafFunctor U.toScheme n).mapIso (restrictPresheafIso U M)

theorem exteriorRestrictPresheafIso_inv_app_mk (V : U.toScheme.Opens) (v : Fin n → Γ(M.restrict U.ι, V)) :
    (exteriorRestrictPresheafIso M n U).inv.app (op V) (ModuleCat.exteriorPower.mk v) =
      ModuleCat.exteriorPower.mk (M := M.val.obj (op (U.ι ''ᵁ V))) v := by
  change (exteriorPresheafRestrictIso X U M.val n).inv.app (op V)
    ((moduleExteriorPresheafMap U.toScheme n (restrictPresheafIso U M).inv).app (op V)
      (ModuleCat.exteriorPower.mk v)) = _
  rw [moduleExteriorPresheafMap_mk]
  rfl

/-- Naturality of the sheafification unit: `sheafification.map φ` sends the wedge `unit (mk v)` to
`unit (φ (mk v))`. -/
theorem sheafification_map_app_wedge (V : U.toScheme.Opens) (v : Fin n → Γ(M.restrict U.ι, V)) :
    Scheme.Modules.Hom.app (((PresheafOfModules.sheafification (𝟙 U.toScheme.ringCatSheaf.obj)).map
        (exteriorRestrictPresheafIso M n U).inv :
          moduleExteriorPower U.toScheme (M.restrict U.ι) n ⟶
            (PresheafOfModules.sheafification (𝟙 U.toScheme.ringCatSheaf.obj)).obj
              ((openModulePresheafRestrictFunctor X U).obj (moduleExteriorPresheaf X M.val n)))) V
      (moduleExteriorWedge U.toScheme (M.restrict U.ι) n V v) =
      ((PresheafOfModules.sheafificationAdjunction (𝟙 U.toScheme.ringCatSheaf.obj)).unit.app
        ((openModulePresheafRestrictFunctor X U).obj (moduleExteriorPresheaf X M.val n))).app (op V)
        ((exteriorRestrictPresheafIso M n U).inv.app (op V) (ModuleCat.exteriorPower.mk v)) := by
  have h := (PresheafOfModules.sheafificationAdjunction (𝟙 U.toScheme.ringCatSheaf.obj)).unit.naturality
    (exteriorRestrictPresheafIso M n U).inv
  have h' := congrArg (fun ψ ↦ ψ.app (op V) (ModuleCat.exteriorPower.mk v)) h
  exact h'.symm

/-- Descent along `sheafificationHomEquiv.symm`, composed with the sheafification unit, is the given
map. Generic form: the presheaves, the sheaf and all instance arguments are parameters, so that at a use
site they are taken from the goal (the kernel then never has to identify two independently synthesized
sheafification instances — that identification costs it tens of seconds). -/
theorem sheafificationHomEquiv_symm_app_unit {Y : Scheme.{u}}
    [i₁ : Presheaf.IsLocallyInjective (Opens.grothendieckTopology Y) (𝟙 Y.ringCatSheaf.obj)]
    [i₂ : Presheaf.IsLocallySurjective (Opens.grothendieckTopology Y) (𝟙 Y.ringCatSheaf.obj)]
    [i₃ : (Opens.grothendieckTopology Y).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [i₄ : HasWeakSheafify (Opens.grothendieckTopology Y) AddCommGrpCat.{u}]
    {P : Y.PresheafOfModules} {F : Y.Modules}
    (g : P ⟶ (PresheafOfModules.restrictScalars (𝟙 Y.ringCatSheaf.obj)).obj F.val) (V : Y.Opens)
    (y : P.obj (op V)) :
    Scheme.Modules.Hom.app
      ((@PresheafOfModules.sheafificationHomEquiv _ _ _ _ _ (𝟙 Y.ringCatSheaf.obj) i₁ i₂ i₃ i₄ P F).symm g) V
      (((@PresheafOfModules.sheafificationAdjunction _ _ _ _ _ (𝟙 Y.ringCatSheaf.obj) i₁ i₂ i₃ i₄).unit.app P).app
        (op V) y) =
      g.app (op V) y := by
  have h : (@PresheafOfModules.sheafificationAdjunction _ _ _ _ _ (𝟙 Y.ringCatSheaf.obj) i₁ i₂ i₃ i₄).homEquiv _ _
      ((@PresheafOfModules.sheafificationHomEquiv _ _ _ _ _ (𝟙 Y.ringCatSheaf.obj) i₁ i₂ i₃ i₄ P F).symm g) = g :=
    Equiv.apply_symm_apply (@PresheafOfModules.sheafificationHomEquiv _ _ _ _ _ (𝟙 Y.ringCatSheaf.obj) i₁ i₂ i₃ i₄ P F) g
  rw [Adjunction.homEquiv_unit] at h
  exact congrArg (fun ψ ↦ ψ.app (op V) y) h

/-- `openModuleSheafificationUnit` is the sheafification unit of the presheaf over `U.ι ''ᵁ V`. -/
theorem openModuleSheafificationUnit_app (P : X.PresheafOfModules) (V : U.toScheme.Opens)
    (y : ((openModulePresheafRestrictFunctor X U).obj P).obj (op V)) :
    (openModuleSheafificationUnit X U P).app (op V) y =
      ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app P).app
        (op (U.ι ''ᵁ V)) y := rfl

/-- The map `openModuleSheafificationMap` sends `unit y` to `openModuleSheafificationUnit y`
(the objects are spelled as in `ExteriorPowerRestrictionIso`; `restrictComparison_eq` uses it through `erw`). -/
theorem openModuleSheafificationMap_app_unit (V : U.toScheme.Opens)
    (y : ((openModulePresheafRestrictFunctor X U).obj (moduleExteriorPresheaf X M.val n)).obj (op V)) :
    Scheme.Modules.Hom.app (openModuleSheafificationMap X U (moduleExteriorPresheaf X M.val n)) V
      (((PresheafOfModules.sheafificationAdjunction (𝟙 U.toScheme.ringCatSheaf.obj)).unit.app
        ((openModulePresheafRestrictFunctor X U).obj (moduleExteriorPresheaf X M.val n))).app (op V) y) =
      (openModuleSheafificationUnit X U (moduleExteriorPresheaf X M.val n)).app (op V) y := by
  unfold openModuleSheafificationMap
  exact sheafificationHomEquiv_symm_app_unit _ V y

/-- The exterior-restriction comparison along `U.ι` is the composite of the sheafification of the
presheaf identification above with the map `openModuleSheafificationMap` ("sheafification
commutes with restriction to an open"): both send the wedge of sections over `V` to the wedge of the
same sections over `U.ι ''ᵁ V`. -/
theorem restrictComparison_eq :
    moduleExteriorRestrictComparison U.ι M n =
      (PresheafOfModules.sheafification (𝟙 U.toScheme.ringCatSheaf.obj)).map
          (exteriorRestrictPresheafIso M n U).inv ≫
        openModuleSheafificationMap X U (moduleExteriorPresheaf X M.val n) := by
  apply moduleExteriorPower_hom_ext
  intro V v
  calc Scheme.Modules.Hom.app (moduleExteriorRestrictComparison U.ι M n) V
        (moduleExteriorWedge U.toScheme (M.restrict U.ι) n V v)
      = moduleExteriorWedge X M n (U.ι ''ᵁ V) v := restrictComparison_wedge M n U V v
    _ = ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
          (moduleExteriorPresheaf X M.val n)).app (op (U.ι ''ᵁ V))
          (ModuleCat.exteriorPower.mk (M := M.val.obj (op (U.ι ''ᵁ V))) v) :=
        moduleExteriorWedge_apply X M n (U.ι ''ᵁ V) v
    _ = (openModuleSheafificationUnit X U (moduleExteriorPresheaf X M.val n)).app (op V)
          (ModuleCat.exteriorPower.mk (M := M.val.obj (op (U.ι ''ᵁ V))) v) :=
        (openModuleSheafificationUnit_app U (moduleExteriorPresheaf X M.val n) V _).symm
    _ = (openModuleSheafificationUnit X U (moduleExteriorPresheaf X M.val n)).app (op V)
          ((exteriorRestrictPresheafIso M n U).inv.app (op V) (ModuleCat.exteriorPower.mk v)) :=
        congrArg _ (exteriorRestrictPresheafIso_inv_app_mk M n U V v).symm
    _ = Scheme.Modules.Hom.app (openModuleSheafificationMap X U (moduleExteriorPresheaf X M.val n)) V
          (((PresheafOfModules.sheafificationAdjunction (𝟙 U.toScheme.ringCatSheaf.obj)).unit.app
            ((openModulePresheafRestrictFunctor X U).obj (moduleExteriorPresheaf X M.val n))).app (op V)
            ((exteriorRestrictPresheafIso M n U).inv.app (op V) (ModuleCat.exteriorPower.mk v))) :=
        (openModuleSheafificationMap_app_unit M n U V _).symm
    _ = Scheme.Modules.Hom.app (openModuleSheafificationMap X U (moduleExteriorPresheaf X M.val n)) V
          (Scheme.Modules.Hom.app (((PresheafOfModules.sheafification (𝟙 U.toScheme.ringCatSheaf.obj)).map
            (exteriorRestrictPresheafIso M n U).inv :
              moduleExteriorPower U.toScheme (M.restrict U.ι) n ⟶
                (PresheafOfModules.sheafification (𝟙 U.toScheme.ringCatSheaf.obj)).obj
                  ((openModulePresheafRestrictFunctor X U).obj (moduleExteriorPresheaf X M.val n)))) V
            (moduleExteriorWedge U.toScheme (M.restrict U.ι) n V v)) :=
        congrArg _ (sheafification_map_app_wedge M n U V v).symm
    _ = Scheme.Modules.Hom.app ((PresheafOfModules.sheafification (𝟙 U.toScheme.ringCatSheaf.obj)).map
            (exteriorRestrictPresheafIso M n U).inv ≫
          openModuleSheafificationMap X U (moduleExteriorPresheaf X M.val n)) V
          (moduleExteriorWedge U.toScheme (M.restrict U.ι) n V v) := rfl

/-- Exterior powers commute with restriction to an open subscheme via the canonical comparison
(the case `f = U.ι` of the former `ExteriorPowerRestrictionStalk.moduleExteriorRestrictComparison_isIso`;
the invertibility comes from the theorem `openModuleSheafificationMap_isIso`).
Not installed as an instance. -/
theorem moduleExteriorRestrictComparison_isIso :
    IsIso (moduleExteriorRestrictComparison U.ι M n) := by
  rw [restrictComparison_eq]
  haveI := openModuleSheafificationMap_isIso X U (moduleExteriorPresheaf X M.val n)
  infer_instance

end ExteriorPowerRestrictionComparison

end AlgebraicGeometry.Scheme.Modules

end
