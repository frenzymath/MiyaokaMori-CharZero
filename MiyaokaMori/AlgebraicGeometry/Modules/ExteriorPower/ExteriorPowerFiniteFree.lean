import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.LocallyFreeRank
import MiyaokaMori.AlgebraicGeometry.Modules.ExteriorPower.ExteriorPowerRestriction
import MiyaokaMori.Algebra.TopExteriorBasis
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineGenericCoordinates
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Pi

/-! # The top exterior power of a finite free sheaf of modules

The top exterior power of a finite free sheaf of modules is isomorphic to the unit sheaf.

Proof:
1. Construct coordinates on the sections of the free sheaf from the finite product decomposition and
   the standard `Pi` basis.
2. Define the isomorphism from the top exterior power to the unit sheaf by the determinant formula
   for the exterior power basis.
3. Check the naturality of the determinant under restriction maps, then sheafify to get an
   isomorphism of sheaves.

Source: Mathlib's exterior power basis; cf. `TopExteriorBasis`.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace MiyaokaMori.ExteriorPowerFiniteFree

universe u

variable (X : Scheme.{u})

local instance sectionCommRing (U : X.Opensᵒᵖ) : CommRing (X.ringCatSheaf.obj.obj U) :=
  inferInstanceAs (CommRing Γ(X, U.unop))

def finiteFreeProductIso (I : Type u) [Finite I] :
    SheafOfModules.free (R := X.ringCatSheaf) I ≅
      ∏ᶜ (fun _ : I ↦ SheafOfModules.unit X.ringCatSheaf) := by
  letI := Fintype.ofFinite I
  letI : HasBiproduct (fun _ : I ↦ SheafOfModules.unit X.ringCatSheaf) :=
    HasBiproduct.of_hasCoproduct _
  exact (biproduct.isoCoproduct _).symm ≪≫ biproduct.isoProduct _

def finiteFreeSectionsIso (I : Type u) [Finite I] (U : X.Opens) :
    (SheafOfModules.free (R := X.ringCatSheaf) I).val.obj (op U) ≅
      ModuleCat.of (X.ringCatSheaf.obj.obj (op U))
        (I → X.ringCatSheaf.obj.obj (op U)) :=
  (SheafOfModules.evaluation X.ringCatSheaf (op U)).mapIso (finiteFreeProductIso X I) ≪≫
    PreservesProduct.iso (SheafOfModules.evaluation X.ringCatSheaf (op U)) _ ≪≫
      IsLimit.conePointUniqueUpToIso (limit.isLimit _)
        (ModuleCat.HasLimit.productLimitCone
          (fun _ : I ↦ ModuleCat.of (X.ringCatSheaf.obj.obj (op U))
            (X.ringCatSheaf.obj.obj (op U)))).isLimit

set_option backward.isDefEq.respectTransparency false in
theorem finiteFreeSectionsIso_apply (I : Type u) [Finite I] (U : X.Opens)
    (x : Γ(SheafOfModules.free (R := X.ringCatSheaf) I, U)) (i : I) :
    (finiteFreeSectionsIso X I U).hom.hom x i =
      (((finiteFreeProductIso X I).hom ≫ Pi.π _ i).val.app (op U)) x := by
  have hp :
      (IsLimit.conePointUniqueUpToIso (limit.isLimit _)
        (ModuleCat.HasLimit.productLimitCone
          (fun _ : I ↦ ModuleCat.of (X.ringCatSheaf.obj.obj (op U))
            (X.ringCatSheaf.obj.obj (op U)))).isLimit).hom ≫
          ModuleCat.ofHom (LinearMap.proj i) =
            Pi.π (fun _ : I ↦ ModuleCat.of (X.ringCatSheaf.obj.obj (op U))
              (X.ringCatSheaf.obj.obj (op U))) i :=
    IsLimit.conePointUniqueUpToIso_hom_comp _ _ (Discrete.mk i)
  change ((finiteFreeSectionsIso X I U).hom ≫
    ModuleCat.ofHom (LinearMap.proj i)).hom x = _
  unfold finiteFreeSectionsIso
  simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc, hp,
    PreservesProduct.iso_hom]
  erw [piComparison_comp_π (SheafOfModules.evaluation X.ringCatSheaf (op U))
      (fun _ : I ↦ SheafOfModules.unit X.ringCatSheaf) i]
  rfl

def finiteFreeSectionBasis (n : ℕ) (U : X.Opens) :
    Module.Basis (Fin n) (X.ringCatSheaf.obj.obj (op U))
      ((SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin n))).val.obj (op U)) := by
  let c :
      ((SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin n))).val.obj (op U)) ≃ₗ[
        (X.ringCatSheaf.obj.obj (op U))]
        (Fin n → X.ringCatSheaf.obj.obj (op U)) :=
    (finiteFreeSectionsIso X (ULift.{u} (Fin n)) U).toLinearEquiv ≪≫ₗ
      LinearEquiv.funCongrLeft (X.ringCatSheaf.obj.obj (op U))
        (X.ringCatSheaf.obj.obj (op U)) (Equiv.ulift.symm)
  exact (Pi.basisFun (X.ringCatSheaf.obj.obj (op U)) (Fin n)).map c.symm

theorem finiteFreeSectionBasis_coord (n : ℕ) (U : X.Opens)
    (x : (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin n))).val.obj (op U))
    (i : Fin n) :
    (finiteFreeSectionBasis X n U).coord i x =
      (finiteFreeSectionsIso X (ULift.{u} (Fin n)) U).hom.hom x (ULift.up i) := by
  let c :
      ((SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin n))).val.obj (op U)) ≃ₗ[
        (X.ringCatSheaf.obj.obj (op U))]
        (Fin n → X.ringCatSheaf.obj.obj (op U)) :=
    (finiteFreeSectionsIso X (ULift.{u} (Fin n)) U).toLinearEquiv ≪≫ₗ
      LinearEquiv.funCongrLeft (X.ringCatSheaf.obj.obj (op U))
        (X.ringCatSheaf.obj.obj (op U)) (Equiv.ulift.symm)
  change ((Pi.basisFun (X.ringCatSheaf.obj.obj (op U)) (Fin n)).map c.symm).coord i x = _
  simp only [Module.Basis.coord_apply, Module.Basis.map_repr, Pi.basisFun_repr]
  rfl

def exteriorFiniteFreeSectionsIso (n : ℕ) (U : X.Opens) :
    ((SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin n))).val.obj (op U)).exteriorPower n ≅
      ModuleCat.of (X.ringCatSheaf.obj.obj (op U))
        (X.ringCatSheaf.obj.obj (op U)) :=
  (MiyaokaMori.Algebra.TopExteriorBasis.topExteriorEquiv
    (finiteFreeSectionBasis X n U)).toModuleIso

theorem exteriorFiniteFreeSectionsIso_mk (n : ℕ) (U : X.Opens)
    (v : Fin n → (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin n))).val.obj (op U)) :
    (exteriorFiniteFreeSectionsIso X n U).hom.hom (ModuleCat.exteriorPower.mk v) =
      (Matrix.of fun i j ↦
        (finiteFreeSectionsIso X (ULift.{u} (Fin n)) U).hom.hom (v j) (ULift.up i)).det := by
  change MiyaokaMori.Algebra.TopExteriorBasis.topExteriorEquiv (finiteFreeSectionBasis X n U)
    (exteriorPower.ιMulti (X.ringCatSheaf.obj.obj (op U)) n v) = _
  rw [MiyaokaMori.Algebra.TopExteriorBasis.topExteriorEquiv_wedge_coords]
  congr 1

theorem finiteFreeSectionsIso_restrict (I : Type u) [Finite I] {U V : X.Opens}
    (j : V ⟶ U) (x : Γ(SheafOfModules.free (R := X.ringCatSheaf) I, U)) (i : I) :
    (finiteFreeSectionsIso X I V).hom.hom
        ((SheafOfModules.free (R := X.ringCatSheaf) I).val.presheaf.map j.op x) i =
      X.presheaf.map j.op ((finiteFreeSectionsIso X I U).hom.hom x i) := by
  change (finiteFreeSectionsIso X I V).hom.hom
      ((SheafOfModules.free (R := X.ringCatSheaf) I).val.presheaf.map j.op x) i =
    X.presheaf.map j.op ((finiteFreeSectionsIso X I U).hom.hom x i)
  erw [finiteFreeSectionsIso_apply, finiteFreeSectionsIso_apply]
  exact PresheafOfModules.naturality_apply
    (((finiteFreeProductIso X I).hom ≫ Pi.π _ i).val) j.op x

def exteriorFiniteFreePresheafIso (n : ℕ) :
    AlgebraicGeometry.Scheme.Modules.moduleExteriorPresheaf X
        (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin n))).val n ≅
      (SheafOfModules.unit X.ringCatSheaf).val :=
  PresheafOfModules.isoMk (fun U ↦ exteriorFiniteFreeSectionsIso X n U.unop) (by
    intro U V i
    apply ModuleCat.exteriorPower.hom_ext
    ext v
    change (exteriorFiniteFreeSectionsIso X n V.unop).hom.hom
        (AlgebraicGeometry.Scheme.Modules.exteriorRestriction X
          (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin n))).val n i
          (ModuleCat.exteriorPower.mk v)) =
      X.ringCatSheaf.obj.map i
        ((exteriorFiniteFreeSectionsIso X n U.unop).hom.hom
          (ModuleCat.exteriorPower.mk v))
    rw [AlgebraicGeometry.Scheme.Modules.exteriorRestriction_mk,
      exteriorFiniteFreeSectionsIso_mk, exteriorFiniteFreeSectionsIso_mk]
    erw [(X.ringCatSheaf.obj.map i).hom.map_det]
    congr 1
    ext a b
    change _ = _
    exact finiteFreeSectionsIso_restrict X (ULift.{u} (Fin n)) i.unop
      (v b) (ULift.up a))

def moduleExteriorPowerFiniteFreeIso (n : ℕ) :
    AlgebraicGeometry.Scheme.Modules.moduleExteriorPower X
        (SheafOfModules.free (R := X.ringCatSheaf) (ULift.{u} (Fin n))) n ≅
      SheafOfModules.unit X.ringCatSheaf :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso
      (exteriorFiniteFreePresheafIso X n) ≪≫
    (asIso (PresheafOfModules.sheafificationAdjunction
      (𝟙 X.ringCatSheaf.obj)).counit).app (SheafOfModules.unit X.ringCatSheaf)

end MiyaokaMori.ExteriorPowerFiniteFree
