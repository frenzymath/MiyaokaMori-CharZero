import MiyaokaMori.AlgebraicGeometry.Modules.ExteriorPower.ModuleExteriorPower

/-!
# Exterior-power generators, functoriality and open restriction

This file uses the existing `moduleExteriorPower`, the sheafification of the actual
exterior-power presheaf. Its unit gives alternating wedge sections. Their restriction
formula follows from the unit's naturality and the existing `exteriorRestriction_mk`.

The exterior power of a module morphism is constructed on each open and sheafified;
isomorphism transport consequently uses the actual functor. For an open immersion
`f : X ⟶ Y`, the restriction comparison has direction
`moduleExteriorPower X (M.restrict f) n ⟶ (moduleExteriorPower Y M n).restrict f`.
It is defined by the alternating wedge map over each image open and the sheafification
adjunction. Its generator formula fixes the map, including degree zero.

The comparison being an isomorphism is a separately registered substantive theorem.
None of the maps or generator identities uses that admission, and no isomorphism is
chosen from an admitted existence statement.

Sources: Stacks Project, `modules.tex`, `lemma-local-tensor-algebra` and
`lemma-pullback-tensor-algebra`; `algebra.tex`, exterior powers and their alternating
universal property. The same objects are used for the local rank of the top exterior power.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

namespace AlgebraicGeometry.Scheme.Modules

universe u

section Functoriality

variable (X : Scheme.{u}) (n : ℕ)

local instance (U : X.Opensᵒᵖ) : CommRing (X.ringCatSheaf.obj.obj U) :=
  inferInstanceAs (CommRing Γ(X, U.unop))

/-- The exterior-power morphism of the same module presheaves, evaluated on every open. -/
def moduleExteriorPresheafMap {M N : X.PresheafOfModules} (φ : M ⟶ N) :
    moduleExteriorPresheaf X M n ⟶ moduleExteriorPresheaf X N n where
  app U := ModuleCat.exteriorPower.map (φ.app U) n
  naturality {U V} i := by
    apply ModuleCat.exteriorPower.hom_ext
    ext v
    change ModuleCat.exteriorPower.map (φ.app V) n
        (exteriorRestriction X M n i (ModuleCat.exteriorPower.mk v)) =
      exteriorRestriction X N n i
        (ModuleCat.exteriorPower.map (φ.app U) n (ModuleCat.exteriorPower.mk v))
    rw [exteriorRestriction_mk, ModuleCat.exteriorPower.map_mk,
      ModuleCat.exteriorPower.map_mk, exteriorRestriction_mk]
    congr 1
    funext j
    exact PresheafOfModules.naturality_apply φ i (v j)

/-- On pure wedges the presheaf morphism applies the given map to every entry. -/
@[simp]
theorem moduleExteriorPresheafMap_mk {M N : X.PresheafOfModules} (φ : M ⟶ N)
    (U : X.Opensᵒᵖ) (v : Fin n → M.obj U) :
    (moduleExteriorPresheafMap X n φ).app U (ModuleCat.exteriorPower.mk v) =
      ModuleCat.exteriorPower.mk (φ.app U ∘ v) :=
  ModuleCat.exteriorPower.map_mk _ _

/-- The existing exterior-power presheaf construction is functorial in its module. -/
def moduleExteriorPresheafFunctor : X.PresheafOfModules ⥤ X.PresheafOfModules where
  obj M := moduleExteriorPresheaf X M n
  map φ := moduleExteriorPresheafMap X n φ
  map_id M := by
    apply PresheafOfModules.hom_ext
    intro U
    exact (ModuleCat.exteriorPower.functor (X.ringCatSheaf.obj.obj U) n).map_id (M.obj U)
  map_comp φ ψ := by
    apply PresheafOfModules.hom_ext
    intro U
    exact (ModuleCat.exteriorPower.functor (X.ringCatSheaf.obj.obj U) n).map_comp
      (φ.app U) (ψ.app U)

/-- The exterior-power functor whose objects are exactly the existing sheafifications. -/
def moduleExteriorFunctor : X.Modules ⥤ X.Modules :=
  Scheme.Modules.toPresheafOfModules X ⋙ moduleExteriorPresheafFunctor X n ⋙
    PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)

/-- The actual map on the existing exterior-power sheaves induced by a module morphism. -/
def moduleExteriorMap {M N : X.Modules} (φ : M ⟶ N) :
    moduleExteriorPower X M n ⟶ moduleExteriorPower X N n :=
  (moduleExteriorFunctor X n).map φ

/-- The same exterior-power functor transports a supplied, actual module isomorphism. -/
def moduleExteriorIso {M N : X.Modules} (e : M ≅ N) :
    moduleExteriorPower X M n ≅ moduleExteriorPower X N n :=
  (moduleExteriorFunctor X n).mapIso e

/-- The transported isomorphism's forward map is precisely the exterior-power map. -/
@[simp]
theorem moduleExteriorIso_hom {M N : X.Modules} (e : M ≅ N) :
    (moduleExteriorIso X n e).hom = moduleExteriorMap X n e.hom := rfl

end Functoriality

section WedgeSections

variable (X : Scheme.{u}) (M : X.Modules) (n : ℕ)

local instance (U : X.Opensᵒᵖ) : CommRing (X.ringCatSheaf.obj.obj U) :=
  inferInstanceAs (CommRing Γ(X, U.unop))

/-- The actual unit from the exterior presheaf into its existing sheafification. -/
def moduleExteriorSheafUnit :
    moduleExteriorPresheaf X M.val n ⟶
      (PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj
        (moduleExteriorPower X M n).val :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
    (moduleExteriorPresheaf X M.val n)

/-- A tuple of sections gives its alternating wedge in the same exterior-power sheaf. -/
def moduleExteriorWedge (U : X.Opens) :
    AlternatingMap Γ(X, U) Γ(M, U) Γ(moduleExteriorPower X M n, U) (Fin n) := by
  change (M.val.obj (op U)).AlternatingMap
    ((moduleExteriorPower X M n).val.obj (op U)) n
  exact ModuleCat.AlternatingMap.postcomp ModuleCat.exteriorPower.mk
    ((moduleExteriorSheafUnit X M n).app (op U) ≫
      (ModuleCat.restrictScalarsId'App _ rfl
        ((moduleExteriorPower X M n).val.obj (op U))).hom)

/-- Wedge sections are the images of the presheaf's actual pure wedge generators. -/
@[simp]
theorem moduleExteriorWedge_apply (U : X.Opens) (v : Fin n → Γ(M, U)) :
    moduleExteriorWedge X M n U v =
      (moduleExteriorSheafUnit X M n).app (op U) (ModuleCat.exteriorPower.mk v) := rfl

/-- Restriction of a wedge section is the wedge of the restrictions of its entries. -/
theorem moduleExteriorWedge_restrict {U V : X.Opens} (i : V ⟶ U)
    (v : Fin n → Γ(M, U)) :
    (moduleExteriorPower X M n).presheaf.map i.op (moduleExteriorWedge X M n U v) =
      moduleExteriorWedge X M n V (M.presheaf.map i.op ∘ v) := by
  change (moduleExteriorPower X M n).val.map i.op
      ((moduleExteriorSheafUnit X M n).app (op U) (ModuleCat.exteriorPower.mk v)) =
    (moduleExteriorSheafUnit X M n).app (op V)
      (ModuleCat.exteriorPower.mk (M := M.val.obj (op V)) (M.val.map i.op ∘ v))
  exact (PresheafOfModules.naturality_apply (moduleExteriorSheafUnit X M n) i.op
    (ModuleCat.exteriorPower.mk v)).symm.trans
      (congrArg ((moduleExteriorSheafUnit X M n).app (op V))
        (exteriorRestriction_mk X M.val n i.op v))

/-- The wedges of a compatible family of sections form a compatible exterior section. -/
def moduleExteriorWedgeSection (s : Fin n → M.sections) :
    (moduleExteriorPower X M n).sections :=
  PresheafOfModules.sectionsMk
    (fun U ↦ moduleExteriorWedge X M n U.unop (fun i ↦ (s i).val U)) (by
      intro U V i
      change (moduleExteriorPower X M n).presheaf.map i
        (moduleExteriorWedge X M n U.unop (fun j ↦ (s j).val U)) = _
      exact (moduleExteriorWedge_restrict X M n i.unop (fun j ↦ (s j).val U)).trans
        (congrArg (moduleExteriorWedge X M n V.unop)
          (funext fun j ↦ PresheafOfModules.sections_property (s j) i)))

/-- Evaluation of the compatible wedge is the wedge of the evaluated sections. -/
@[simp]
theorem moduleExteriorWedgeSection_apply (s : Fin n → M.sections) (U : X.Opens) :
    (moduleExteriorWedgeSection X M n s).val (op U) =
      moduleExteriorWedge X M n U (fun i ↦ (s i).val (op U)) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- A sheaf morphism acts on wedge sections entry by entry. -/
theorem moduleExteriorMap_wedge {N : X.Modules} (φ : M ⟶ N) (U : X.Opens)
    (v : Fin n → Γ(M, U)) :
    (moduleExteriorMap X n φ).app U (moduleExteriorWedge X M n U v) =
      moduleExteriorWedge X N n U (φ.app U ∘ v) := by
  change (moduleExteriorMap X n φ).val.app (op U)
      ((moduleExteriorSheafUnit X M n).app (op U) (ModuleCat.exteriorPower.mk v)) =
    (moduleExteriorSheafUnit X N n).app (op U)
      (ModuleCat.exteriorPower.mk (M := N.val.obj (op U)) (φ.val.app (op U) ∘ v))
  have h := (PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).unit.naturality (moduleExteriorPresheafMap X n φ.val)
  have h' := congrArg (fun ψ ↦
    (ModuleCat.restrictScalarsId'App _ rfl
      ((moduleExteriorPower X N n).val.obj (op U))).hom
        (ψ.app (op U) (ModuleCat.exteriorPower.mk v))) h.symm
  change (moduleExteriorMap X n φ).val.app (op U)
      ((moduleExteriorSheafUnit X M n).app (op U) (ModuleCat.exteriorPower.mk v)) =
    (moduleExteriorSheafUnit X N n).app (op U)
      ((moduleExteriorPresheafMap X n φ.val).app (op U)
        (ModuleCat.exteriorPower.mk v)) at h'
  simpa only [moduleExteriorPresheafMap_mk] using h'

/-- Descent of a specified exterior-presheaf map through its actual sheafification. -/
def moduleExteriorDesc (N : X.Modules)
    (φ : moduleExteriorPresheaf X M.val n ⟶
      (PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj N.val) :
    moduleExteriorPower X M n ⟶ N :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv
    (moduleExteriorPresheaf X M.val n) N).symm φ

/-- The descended morphism has exactly the specified composite with the sheafification unit. -/
theorem moduleExteriorDesc_unit_comp (N : X.Modules)
    (φ : moduleExteriorPresheaf X M.val n ⟶
      (PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj N.val) :
    moduleExteriorSheafUnit X M n ≫
        (PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map
          (moduleExteriorDesc X M n N φ).val = φ := by
  unfold moduleExteriorDesc moduleExteriorSheafUnit
  exact ((PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).homEquiv_unit
      (moduleExteriorPresheaf X M.val n) N _).symm.trans (Equiv.apply_symm_apply _ _)

/-- On wedge sections, descent evaluates the input presheaf map on the pure wedge. -/
theorem moduleExteriorDesc_wedge (N : X.Modules)
    (φ : moduleExteriorPresheaf X M.val n ⟶
      (PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj N.val)
    (U : X.Opens) (v : Fin n → Γ(M, U)) :
    (moduleExteriorDesc X M n N φ).app U (moduleExteriorWedge X M n U v) =
      φ.app (op U) (ModuleCat.exteriorPower.mk v) := by
  change (moduleExteriorDesc X M n N φ).val.app (op U)
      ((moduleExteriorSheafUnit X M n).app (op U) (ModuleCat.exteriorPower.mk v)) =
    φ.app (op U) (ModuleCat.exteriorPower.mk v)
  exact congrArg (fun ψ ↦ ψ.app (op U) (ModuleCat.exteriorPower.mk v))
    (moduleExteriorDesc_unit_comp X M n N φ)

end WedgeSections

section OpenRestriction

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (M : Y.Modules) (n : ℕ)

local instance (U : X.Opensᵒᵖ) : CommRing (X.ringCatSheaf.obj.obj U) :=
  inferInstanceAs (CommRing Γ(X, U.unop))

set_option backward.isDefEq.respectTransparency false in
/-- The comparison on a restricted open is induced by wedges over its actual image open. -/
def moduleExteriorRestrictAlternating (U : X.Opens) :
    ((M.restrict f).val.obj (op U)).AlternatingMap
      (((moduleExteriorPower Y M n).restrict f).val.obj (op U)) n where
  toFun v := ((moduleExteriorPower Y M n).restrictAppIso f U).inv
    (moduleExteriorWedge Y M n (f ''ᵁ U) ((M.restrictAppIso f U).hom ∘ v))
  map_update_add' v j a b := by
    simp only [Function.comp_update, map_add, AlternatingMap.map_update_add]
  map_update_smul' v j r a := by
    have hM : (M.restrictAppIso f U).hom (r • a) =
        (f.appIso U).inv r • (M.restrictAppIso f U).hom a :=
      ConcreteCategory.congr_hom (Scheme.Modules.smul_restrictAppIso_hom f M U r) a
    simp only [Function.comp_update]
    rw [hM, AlternatingMap.map_update_smul]
    simpa using ConcreteCategory.congr_hom
      (Scheme.Modules.smul_restrictAppIso_inv f (moduleExteriorPower Y M n) U
        ((f.appIso U).inv r))
      (moduleExteriorWedge Y M n (f ''ᵁ U)
        (Function.update ((M.restrictAppIso f U).hom ∘ v) j
          ((M.restrictAppIso f U).hom a)))
  map_eq_zero_of_eq' v j l h hjl := by
    exact (congrArg ((moduleExteriorPower Y M n).restrictAppIso f U).inv
      ((moduleExteriorWedge Y M n (f ''ᵁ U)).map_eq_zero_of_eq
        ((M.restrictAppIso f U).hom ∘ v)
        (congrArg (M.restrictAppIso f U).hom h) hjl)).trans (map_zero _)

/-- The actual exterior-presheaf map to the restricted exterior-power sheaf. -/
def moduleExteriorRestrictPresheafComparison :
    moduleExteriorPresheaf X (M.restrict f).val n ⟶
      (PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj
        ((moduleExteriorPower Y M n).restrict f).val where
  app U := ModuleCat.exteriorPower.desc (moduleExteriorRestrictAlternating f M n U.unop)
  naturality {U V} i := by
    apply ModuleCat.exteriorPower.hom_ext
    ext v
    change ModuleCat.exteriorPower.desc (moduleExteriorRestrictAlternating f M n V.unop)
        (exteriorRestriction X (M.restrict f).val n i (ModuleCat.exteriorPower.mk v)) =
      ((moduleExteriorPower Y M n).restrict f).val.map i
        (ModuleCat.exteriorPower.desc (moduleExteriorRestrictAlternating f M n U.unop)
          (ModuleCat.exteriorPower.mk v))
    rw [exteriorRestriction_mk, ModuleCat.exteriorPower.desc_mk,
      ModuleCat.exteriorPower.desc_mk]
    exact (moduleExteriorWedge_restrict Y M n (f.opensFunctor.map i.unop) v).symm

/-- The canonical comparison from the exterior power of a restriction to the restricted exterior. -/
def moduleExteriorRestrictComparison :
    moduleExteriorPower X (M.restrict f) n ⟶ (moduleExteriorPower Y M n).restrict f :=
  moduleExteriorDesc X (M.restrict f) n ((moduleExteriorPower Y M n).restrict f)
    (moduleExteriorRestrictPresheafComparison f M n)

/-- The restriction comparison sends a wedge to the same wedge over the image open. -/
theorem moduleExteriorRestrictComparison_wedge (U : X.Opens)
    (v : Fin n → Γ(M.restrict f, U)) :
    (moduleExteriorRestrictComparison f M n).app U
        (moduleExteriorWedge X (M.restrict f) n U v) =
      ((moduleExteriorPower Y M n).restrictAppIso f U).inv
        (moduleExteriorWedge Y M n (f ''ᵁ U) ((M.restrictAppIso f U).hom ∘ v)) := by
  rw [moduleExteriorRestrictComparison, moduleExteriorDesc_wedge]
  exact ModuleCat.exteriorPower.desc_mk _ _

-- The invertibility `moduleExteriorRestrictComparison_isIso` is proved in
-- `ExteriorPowerRestrictionComparisonIso`, whose ingredients import this module.

end OpenRestriction

end AlgebraicGeometry.Scheme.Modules
