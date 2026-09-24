import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModuleGenericFiber
import Mathlib.AlgebraicGeometry.Restrict
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free

/-!
# Actual local and generic coordinates of a line module

A frame of the same module sheaf on an open subscheme identifies its actual stalks
with the corresponding local rings. Restriction uses Mathlib's stalk isomorphism,
with its semilinearity proved on germs. The free sheaf on `ULift (Fin 1)` is the
one-term coproduct of the unit sheaf. Its abelian stalk is identified with the
local ring by preservation of filtered colimits.

These comparisons commute with the actual specialization map supplied by
`ModuleGenericFiber`. Consequently the coordinates of a nonzero generic section
in two such frames have a ratio given by a unit of each common local ring.
The separate `LineRationalSectionCartier` module binds these same coordinates to
B's canonical `CartierLocalData`; no line, field, stalk or valuation is duplicated.

Sources: Stacks Project, `divisors.tex`, Section `section-c1`, especially the
coordinate argument preceding `definition-order-vanishing-meromorphic`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.Divisors.LineGenericCoordinates

private abbrev ringAb : CommRingCat.{u} ⥤ Ab.{u} :=
  forget₂ CommRingCat RingCat ⋙ forget₂ RingCat Ab

private def unitStalkAbIso (X : Scheme.{u}) (x : X) :
    (Scheme.Modules.presheaf (SheafOfModules.unit X.ringCatSheaf)).stalk x ≅
      ringAb.obj (X.presheaf.stalk x) :=
  (preservesColimitIso ringAb ((OpenNhds.inclusion x).op ⋙ X.presheaf)).symm

private theorem unitStalkAbIso_germ (X : Scheme.{u}) (x : X) (U : X.Opens)
    (hx : x ∈ U) (r : Γ(X, U)) :
    (unitStalkAbIso X x).hom
        ((Scheme.Modules.presheaf (SheafOfModules.unit X.ringCatSheaf)).germ U x hx r) =
      X.presheaf.germ U x hx r :=
  ConcreteCategory.congr_hom
    (ι_preservesColimitIso_inv ringAb ((OpenNhds.inclusion x).op ⋙ X.presheaf)
      (op ⟨U, hx⟩)) r

/-- The actual stalk of the structure module is linearly isomorphic to the local ring. -/
def unitStalkLinearEquiv (X : Scheme.{u}) (x : X) :
    letI := AlgebraicGeometry.Scheme.Modules.moduleStalkModule X (SheafOfModules.unit X.ringCatSheaf) x
    (Scheme.Modules.presheaf (SheafOfModules.unit X.ringCatSheaf)).stalk x ≃ₗ[
      X.presheaf.stalk x] X.presheaf.stalk x := by
  letI := AlgebraicGeometry.Scheme.Modules.moduleStalkModule X (SheafOfModules.unit X.ringCatSheaf) x
  refine { (unitStalkAbIso X x).addCommGroupIsoToAddEquiv with map_smul' := ?_ }
  intro r m
  obtain ⟨U, hxU, a, rfl⟩ := X.presheaf.exists_germ_eq r
  obtain ⟨V, hVU, hxV, b, rfl⟩ :=
    (Scheme.Modules.presheaf (SheafOfModules.unit X.ringCatSheaf)).exists_le_germ_eq m hxU
  change Γ(X, V) at b
  rw [← X.presheaf.germ_res_apply (homOfLE hVU) x hxV a]
  erw [← PresheafOfModules.germ_smul (R := X.presheaf)
    (SheafOfModules.unit X.ringCatSheaf).val]
  change (unitStalkAbIso X x).hom
      ((Scheme.Modules.presheaf (SheafOfModules.unit X.ringCatSheaf)).germ V x hxV
        (X.presheaf.map (homOfLE hVU).op a * b)) = _
  rw [unitStalkAbIso_germ]
  exact ((X.presheaf.germ V x hxV).hom.map_mul _ _).trans
    (congrArg (fun t : X.presheaf.stalk x ↦
      X.presheaf.germ V x hxV (X.presheaf.map (homOfLE hVU).op a) * t)
      (unitStalkAbIso_germ X x V hxV b).symm)

/-- The linear comparison sends a structure-module germ to the same regular-function germ. -/
@[simp]
theorem unitStalkLinearEquiv_germ (X : Scheme.{u}) (x : X) (U : X.Opens)
    (hx : x ∈ U) (r : Γ(X, U)) :
    unitStalkLinearEquiv X x
        ((Scheme.Modules.presheaf (SheafOfModules.unit X.ringCatSheaf)).germ U x hx r) =
      X.presheaf.germ U x hx r :=
  unitStalkAbIso_germ X x U hx r

/-- The free module on one generator is the structure module through the one-term
coproduct isomorphism. -/
def moduleFreeOneIsoUnit (X : Scheme.{u}) :
    SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin 1)) ≅
      SheafOfModules.unit X.ringCatSheaf :=
  coproductUniqueIso (fun _ : ULift.{u} (Fin 1) ↦ SheafOfModules.unit X.ringCatSheaf)

/-- The actual stalk of the free module on one generator is a free local-ring module of
rank one, identified with the local ring itself. -/
def freeOneStalkLinearEquiv (X : Scheme.{u}) (x : X) :
    letI := AlgebraicGeometry.Scheme.Modules.moduleStalkModule X (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin 1))) x
    (Scheme.Modules.presheaf
      (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin 1)))).stalk x ≃ₗ[
        X.presheaf.stalk x] X.presheaf.stalk x :=
  ((AlgebraicGeometry.Scheme.Modules.moduleStalkFunctor X x).mapIso (moduleFreeOneIsoUnit X)).toLinearEquiv.trans
    (unitStalkLinearEquiv X x)

/-- On germs, the rank-one stalk comparison applies the canonical free-to-unit map to the
section before taking its regular-function germ. -/
@[simp]
theorem freeOneStalkLinearEquiv_germ (X : Scheme.{u}) (x : X) (U : X.Opens)
    (hx : x ∈ U) (m : Γ(SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin 1)), U)) :
    freeOneStalkLinearEquiv X x
        ((Scheme.Modules.presheaf
          (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin 1)))).germ
          U x hx m) =
      X.presheaf.germ U x hx ((moduleFreeOneIsoUnit X).hom.val.app (op U) m) := by
  change unitStalkLinearEquiv X x
    (AlgebraicGeometry.Scheme.Modules.moduleStalkMap X x (moduleFreeOneIsoUnit X).hom
      ((Scheme.Modules.presheaf
        (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin 1)))).germ
        U x hx m)) = _
  erw [AlgebraicGeometry.Scheme.Modules.moduleStalkMap_germ, unitStalkLinearEquiv_germ]
  rfl

/-- Restriction to an open subscheme preserves the actual module stalk, with scalars
transported through the canonical local-ring isomorphism. -/
def moduleRestrictStalkEquiv (X : Scheme.{u}) (M : X.Modules) (U : X.Opens) (x : U) :
    letI := AlgebraicGeometry.Scheme.Modules.moduleStalkModule U.toScheme (M.restrict U.ι) x
    letI := AlgebraicGeometry.Scheme.Modules.moduleStalkModule X M x.1
    let e := (U.stalkIso x).commRingCatIsoToRingEquiv
    haveI := RingHomInvPair.of_ringEquiv e
    haveI := RingHomInvPair.of_ringEquiv_symm e
    (M.restrict U.ι).presheaf.stalk x ≃ₛₗ[
      (↑e : U.toScheme.presheaf.stalk x →+* X.presheaf.stalk x.1)]
      M.presheaf.stalk x.1 := by
  letI := AlgebraicGeometry.Scheme.Modules.moduleStalkModule U.toScheme (M.restrict U.ι) x
  letI := AlgebraicGeometry.Scheme.Modules.moduleStalkModule X M x.1
  let e := (U.stalkIso x).commRingCatIsoToRingEquiv
  haveI := RingHomInvPair.of_ringEquiv e
  haveI := RingHomInvPair.of_ringEquiv_symm e
  exact
  { ((Scheme.Modules.restrictStalkNatIso U.ι x).app M).addCommGroupIsoToAddEquiv with
    map_smul' := by
      intro r m
      obtain ⟨V, hxV, a, rfl⟩ := U.toScheme.presheaf.exists_germ_eq r
      obtain ⟨W, hWV, hxW, b, rfl⟩ :=
        (M.restrict U.ι).presheaf.exists_le_germ_eq m hxV
      rw [← U.toScheme.presheaf.germ_res_apply (homOfLE hWV) x hxW a]
      erw [← PresheafOfModules.germ_smul (R := U.toScheme.presheaf) (M.restrict U.ι).val]
      change (Scheme.Modules.restrictStalkNatIso U.ι x).hom.app M
          ((M.restrict U.ι).presheaf.germ W x hxW (_ • b)) = _
      have hg (c : Γ(M.restrict U.ι, W)) :
          (Scheme.Modules.restrictStalkNatIso U.ι x).hom.app M
            ((M.restrict U.ι).presheaf.germ W x hxW c) =
          M.presheaf.germ (U.ι ''ᵁ W) x.1 ⟨x, hxW, rfl⟩ c :=
        congrArg (fun f ↦ f c)
          (Scheme.Modules.germ_restrictStalkNatIso_hom_app U.ι x M hxW)
      erw [hg]
      change M.presheaf.germ (U.ι ''ᵁ W) x.1 _ (_ • b) = _
      erw [PresheafOfModules.germ_smul (R := X.presheaf) M.val]
      congr 1
      · change X.presheaf.germ (U.ι ''ᵁ W) x.1 _
            ((U.ι.appIso W).inv (U.toScheme.presheaf.map (homOfLE hWV).op a)) = _
        rw [U.ι_appIso]
        exact congrArg (fun f ↦ f (U.toScheme.presheaf.map (homOfLE hWV).op a))
          (U.germ_stalkIso_hom x hxW).symm
      · exact congrArg (fun f ↦ f b)
          (Scheme.Modules.germ_restrictStalkNatIso_hom_app U.ι x M hxW).symm }

/-- The restriction equivalence sends a germ to the same section's germ on the original
scheme. -/
@[simp]
theorem moduleRestrictStalkEquiv_germ (X : Scheme.{u}) (M : X.Modules) (U : X.Opens)
    (x : U) (V : U.toScheme.Opens) (hx : x ∈ V) (m : Γ(M.restrict U.ι, V)) :
    moduleRestrictStalkEquiv X M U x ((M.restrict U.ι).presheaf.germ V x hx m) =
      M.presheaf.germ (U.ι ''ᵁ V) x.1 ⟨x, hx, rfl⟩ m :=
  congrArg (fun f ↦ f m)
    (Scheme.Modules.germ_restrictStalkNatIso_hom_app U.ι x M hx)

/-- A rank-one trivialization on an open neighborhood identifies the original module stalk
with its actual local ring. The restriction ring isomorphism transports both scalars. -/
def lineStalkEquivOfTrivialization (X : Scheme.{u}) (M : X.Modules)
    (U : X.Opens) (x : U)
    (eM : M.restrict U.ι ≅ SheafOfModules.free (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin 1))) :
    M.presheaf.stalk x.1 ≃ₗ[X.presheaf.stalk x.1] X.presheaf.stalk x.1 := by
  let e := (U.stalkIso x).commRingCatIsoToRingEquiv
  haveI := RingHomInvPair.of_ringEquiv e
  haveI := RingHomInvPair.of_ringEquiv_symm e
  let e₁ := moduleRestrictStalkEquiv X M U x
  let e₂ := ((AlgebraicGeometry.Scheme.Modules.moduleStalkFunctor U.toScheme x).mapIso eM).toLinearEquiv.trans
    (freeOneStalkLinearEquiv U.toScheme x)
  exact (e₁.symm.trans e₂).trans e.toSemilinearEquiv

/-- Local line coordinates send a module germ to the germ of its coordinate section on
the same open neighborhood of the original scheme. -/
theorem lineStalkEquivOfTrivialization_germ (X : Scheme.{u}) (M : X.Modules)
    (U : X.Opens) (x : U)
    (eM : M.restrict U.ι ≅ SheafOfModules.free (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin 1)))
    (V : U.toScheme.Opens) (hx : x ∈ V) (m : Γ(M.restrict U.ι, V)) :
    lineStalkEquivOfTrivialization X M U x eM
        (M.presheaf.germ (U.ι ''ᵁ V) x.1 ⟨x, hx, rfl⟩ m) =
      X.presheaf.germ (U.ι ''ᵁ V) x.1 ⟨x, hx, rfl⟩
        ((eM ≪≫ moduleFreeOneIsoUnit U.toScheme).hom.val.app (op V) m) := by
  have hr := (moduleRestrictStalkEquiv X M U x).symm_apply_apply
    ((M.restrict U.ι).presheaf.germ V x hx m)
  rw [moduleRestrictStalkEquiv_germ] at hr
  change (U.stalkIso x).hom
      (freeOneStalkLinearEquiv U.toScheme x
        (AlgebraicGeometry.Scheme.Modules.moduleStalkMap U.toScheme x eM.hom
          ((moduleRestrictStalkEquiv X M U x).symm
            (M.presheaf.germ (U.ι ''ᵁ V) x.1 ⟨x, hx, rfl⟩ m)))) = _
  rw [hr]
  erw [AlgebraicGeometry.Scheme.Modules.moduleStalkMap_germ, freeOneStalkLinearEquiv_germ]
  exact ConcreteCategory.congr_hom (U.germ_stalkIso_hom x hx)
    ((eM ≪≫ moduleFreeOneIsoUnit U.toScheme).hom.val.app (op V) m)

/-- The coordinates provided by one fixed local trivialization commute with the actual
specialization maps of the module and structure sheaves. -/
theorem lineStalkEquivOfTrivialization_specializes (X : Scheme.{u}) (M : X.Modules)
    (U : X.Opens)
    (eM : M.restrict U.ι ≅ SheafOfModules.free (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin 1)))
    (x y : U) (h : x.1 ⤳ y.1) (m : M.presheaf.stalk y.1) :
    lineStalkEquivOfTrivialization X M U x eM (AlgebraicGeometry.Scheme.Modules.moduleStalkSpecializes X M h m) =
      X.presheaf.stalkSpecializes h (lineStalkEquivOfTrivialization X M U y eM m) := by
  obtain ⟨V, hyV, b, hb⟩ := (M.restrict U.ι).presheaf.exists_germ_eq
    ((moduleRestrictStalkEquiv X M U y).symm m)
  have hm : M.presheaf.germ (U.ι ''ᵁ V) y.1 ⟨y, hyV, rfl⟩ b = m := by
    rw [← moduleRestrictStalkEquiv_germ X M U y V hyV b, hb]
    exact (moduleRestrictStalkEquiv X M U y).apply_symm_apply m
  have hxV : x ∈ V := ((subtype_specializes_iff x y).mpr h).mem_open V.isOpen hyV
  rw [← hm]
  erw [AlgebraicGeometry.Scheme.Modules.moduleStalkSpecializes_germ]
  rw [lineStalkEquivOfTrivialization_germ X M U x eM V hxV b,
    lineStalkEquivOfTrivialization_germ X M U y eM V hyV b]
  exact (TopCat.Presheaf.germ_stalkSpecializes_apply X.presheaf (U := U.ι ''ᵁ V)
    ⟨y, hyV, rfl⟩ h _).symm

/-- Local line coordinates at a point and at the generic point agree after the canonical
map to the generic fiber, provided they come from the same open trivialization. -/
theorem lineStalkEquivOfTrivialization_toGenericFiber (X : Scheme.{u}) [IsIntegral X]
    (M : X.Modules) (U : X.Opens)
    (eM : M.restrict U.ι ≅ SheafOfModules.free (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin 1)))
    (x : U) (hη : genericPoint X ∈ U) (m : M.presheaf.stalk x.1) :
    lineStalkEquivOfTrivialization X M U ⟨genericPoint X, hη⟩ eM
        (AlgebraicGeometry.Scheme.Modules.moduleStalkToGenericFiber X M x.1 m) =
      algebraMap (X.presheaf.stalk x.1) X.functionField
        (lineStalkEquivOfTrivialization X M U x eM m) :=
  lineStalkEquivOfTrivialization_specializes X M U eM ⟨genericPoint X, hη⟩ x
    ((genericPoint_spec X).specializes trivial) m

/-- Compatible local and generic frames give a unit-valued ratio of generic coordinates. -/
theorem exists_unit_lineCoordinateRatio
    {R K M V : Type*} [CommRing R] [Field K] [Algebra R K]
    [AddCommGroup M] [Module R M] [AddCommGroup V] [Module K V]
    (e0 e1 : M ≃ₗ[R] R) (f0 f1 : V ≃ₗ[K] K)
    (j : M →ₛₗ[algebraMap R K] V)
    (h0 : ∀ m, f0 (j m) = algebraMap R K (e0 m))
    (h1 : ∀ m, f1 (j m) = algebraMap R K (e1 m))
    (s : V) (hs : s ≠ 0) :
    ∃ u : Rˣ, algebraMap R K (u : R) = f0 s / f1 s := by
  let a := e0 (e1.symm 1)
  have hchange (m : M) : e0 m = e1 m * a := by
    have hm : m = e1 m • e1.symm 1 := by
      apply e1.injective
      simp
    calc
      e0 m = e0 (e1 m • e1.symm 1) := congrArg e0 hm
      _ = e1 m * a := by rw [map_smul]; rfl
  have ha : IsUnit a := by
    apply isUnit_iff_exists_inv.mpr
    refine ⟨e1 (e0.symm 1), ?_⟩
    simpa [mul_comm] using (hchange (e0.symm 1)).symm
  obtain ⟨u, hu⟩ := ha
  refine ⟨u, ?_⟩
  have hf1 : f1 s ≠ 0 := fun h ↦ hs (f1.injective (by simpa using h))
  have hs' : s = f1 s • j (e1.symm 1) := by
    apply f1.injective
    simp [h1]
  rw [hu, eq_div_iff hf1]
  calc
    algebraMap R K a * f1 s = f0 (f1 s • j (e1.symm 1)) := by
      rw [map_smul, h0]
      exact mul_comm _ _
    _ = f0 s := congrArg f0 hs'.symm

/-- Every nonempty open of an integral scheme contains its actual generic point. -/
theorem genericPoint_mem_of_nonempty (X : Scheme.{u}) [IsIntegral X]
    (U : X.Opens) (hU : Nonempty U) : genericPoint X ∈ U := by
  obtain ⟨x⟩ := hU
  exact ((genericPoint_spec X).specializes trivial).mem_open U.isOpen x.property

/-- A specified actual local frame gives the coordinates of the same generic stalk. -/
def genericCoordinate (X : Scheme.{u}) [IsIntegral X] (M : X.Modules)
    (U : X.Opens) (hU : Nonempty U)
    (e : M.restrict U.ι ≅
      SheafOfModules.free (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin 1))) :
    M.presheaf.stalk (genericPoint X) ≃ₗ[X.functionField] X.functionField :=
  lineStalkEquivOfTrivialization X M U
    ⟨genericPoint X, genericPoint_mem_of_nonempty X U hU⟩ e

/-- The coordinate of a nonzero generic section in a genuine frame is nonzero. -/
theorem genericCoordinate_ne_zero (X : Scheme.{u}) [IsIntegral X] (M : X.Modules)
    (U : X.Opens) (hU : Nonempty U)
    (e : M.restrict U.ι ≅
      SheafOfModules.free (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin 1)))
    (s : M.presheaf.stalk (genericPoint X)) (hs : s ≠ 0) :
    genericCoordinate X M U hU e s ≠ 0 := by
  intro h
  exact hs ((genericCoordinate X M U hU e).injective (by simpa using h))

/-- Two actual frames give a unit ratio in each local ring of their overlap. -/
theorem genericCoordinate_ratio_is_local_unit (X : Scheme.{u}) [IsIntegral X]
    (M : X.Modules) (U V : X.Opens) (x : X) (hxU : x ∈ U) (hxV : x ∈ V)
    (eU : M.restrict U.ι ≅
      SheafOfModules.free (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin 1)))
    (eV : M.restrict V.ι ≅
      SheafOfModules.free (R := V.toScheme.ringCatSheaf) (ULift.{u} (Fin 1)))
    (s : M.presheaf.stalk (genericPoint X)) (hs : s ≠ 0) :
    ∃ a : (X.presheaf.stalk x)ˣ,
      algebraMap (X.presheaf.stalk x) X.functionField (a : X.presheaf.stalk x) =
        genericCoordinate X M U ⟨⟨x, hxU⟩⟩ eU s /
          genericCoordinate X M V ⟨⟨x, hxV⟩⟩ eV s := by
  exact exists_unit_lineCoordinateRatio
    (lineStalkEquivOfTrivialization X M U ⟨x, hxU⟩ eU)
    (lineStalkEquivOfTrivialization X M V ⟨x, hxV⟩ eV)
    (genericCoordinate X M U ⟨⟨x, hxU⟩⟩ eU)
    (genericCoordinate X M V ⟨⟨x, hxV⟩⟩ eV)
    (AlgebraicGeometry.Scheme.Modules.moduleStalkToGenericFiber X M x)
    (lineStalkEquivOfTrivialization_toGenericFiber X M U eU ⟨x, hxU⟩ _)
    (lineStalkEquivOfTrivialization_toGenericFiber X M V eV ⟨x, hxV⟩ _) s hs

end AlgebraicGeometry.Divisors.LineGenericCoordinates
