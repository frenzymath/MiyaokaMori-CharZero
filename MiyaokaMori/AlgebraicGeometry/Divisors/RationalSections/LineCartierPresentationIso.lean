import MiyaokaMori.AlgebraicGeometry.Divisors.RationalSections.LineRationalSectionCartier

/-!
# Transport of line Cartier presentations across module isomorphisms

The coordinate constructions in `LineGenericCoordinates` are attached to the actual
module sheaf and its stalks.  This file records their naturality under restriction and
under an isomorphism of module sheaves.  In particular, a Cartier presentation is
transported by using the same Cartier local data and transporting each local frame
through the restricted module isomorphism.

No presentation-existence or degree theorem is used here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.Divisors.LineGenericCoordinates

variable {X : Scheme.{u}} {M N : X.Modules} (U : X.Opens) (x : U)

/-- The restriction stalk comparison is natural in the module sheaf. -/
theorem moduleRestrictStalkEquiv_naturality (e : M ⟶ N)
    (m : (M.restrict U.ι).presheaf.stalk x) :
    moduleRestrictStalkEquiv X N U x
        (AlgebraicGeometry.Scheme.Modules.moduleStalkMap U.toScheme x ((Scheme.Modules.restrictFunctor U.ι).map e) m) =
      AlgebraicGeometry.Scheme.Modules.moduleStalkMap X x.1 e
        (moduleRestrictStalkEquiv X M U x m) := by
  change (Scheme.Modules.restrictStalkNatIso U.ι x).hom.app N
      (AlgebraicGeometry.Scheme.Modules.moduleStalkMap U.toScheme x ((Scheme.Modules.restrictFunctor U.ι).map e) m) =
    AlgebraicGeometry.Scheme.Modules.moduleStalkMap X x.1 e
      ((Scheme.Modules.restrictStalkNatIso U.ι x).hom.app M m)
  exact CategoryTheory.congr_fun (C := AddCommGrpCat.{u})
    ((Scheme.Modules.restrictStalkNatIso U.ι x).hom.naturality e) m

/-- Local line coordinates commute with an isomorphism of the underlying module sheaf. -/
theorem lineStalkEquivOfTrivialization_mapIso
    (e : M ≅ N)
    (eM : M.restrict U.ι ≅
      SheafOfModules.free (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin 1)))
    (m : M.presheaf.stalk x.1) :
    lineStalkEquivOfTrivialization X N U x
        (((Scheme.Modules.restrictFunctor U.ι).mapIso e).symm ≪≫ eM)
        (AlgebraicGeometry.Scheme.Modules.moduleStalkMap X x.1 e.hom m) =
      lineStalkEquivOfTrivialization X M U x eM m := by
  let ρ := (U.stalkIso x).commRingCatIsoToRingEquiv
  haveI := RingHomInvPair.of_ringEquiv ρ
  haveI := RingHomInvPair.of_ringEquiv_symm ρ
  let e₁M := moduleRestrictStalkEquiv X M U x
  let e₁N := moduleRestrictStalkEquiv X N U x
  let e₂M := ((AlgebraicGeometry.Scheme.Modules.moduleStalkFunctor U.toScheme x).mapIso eM).toLinearEquiv.trans
    (freeOneStalkLinearEquiv U.toScheme x)
  let e₂N := ((AlgebraicGeometry.Scheme.Modules.moduleStalkFunctor U.toScheme x).mapIso
      (((Scheme.Modules.restrictFunctor U.ι).mapIso e).symm ≪≫ eM)).toLinearEquiv.trans
    (freeOneStalkLinearEquiv U.toScheme x)
  change (e₁N.symm.trans e₂N).trans ρ.toSemilinearEquiv
      (AlgebraicGeometry.Scheme.Modules.moduleStalkMap X x.1 e.hom m) =
    (e₁M.symm.trans e₂M).trans ρ.toSemilinearEquiv m
  change ρ.toSemilinearEquiv (e₂N (e₁N.symm (AlgebraicGeometry.Scheme.Modules.moduleStalkMap X x.1 e.hom m))) =
    ρ.toSemilinearEquiv (e₂M (e₁M.symm m))
  have hnat :
      e₁N.symm (AlgebraicGeometry.Scheme.Modules.moduleStalkMap X x.1 e.hom m) =
        AlgebraicGeometry.Scheme.Modules.moduleStalkMap U.toScheme x ((Scheme.Modules.restrictFunctor U.ι).map e.hom)
          (e₁M.symm m) := by
    apply e₁N.injective
    rw [e₁N.apply_symm_apply]
    calc
      AlgebraicGeometry.Scheme.Modules.moduleStalkMap X x.1 e.hom m =
          AlgebraicGeometry.Scheme.Modules.moduleStalkMap X x.1 e.hom (e₁M (e₁M.symm m)) := by
            rw [e₁M.apply_symm_apply]
      _ = e₁N (AlgebraicGeometry.Scheme.Modules.moduleStalkMap U.toScheme x
          ((Scheme.Modules.restrictFunctor U.ι).map e.hom) (e₁M.symm m)) :=
        (moduleRestrictStalkEquiv_naturality (X := X) U x e.hom
          (e₁M.symm m)).symm
  rw [hnat]
  have h₂ : e₂N (AlgebraicGeometry.Scheme.Modules.moduleStalkMap U.toScheme x
        ((Scheme.Modules.restrictFunctor U.ι).map e.hom) (e₁M.symm m)) =
      e₂M (e₁M.symm m) := by
    simp only [e₂N, e₂M]
    change freeOneStalkLinearEquiv U.toScheme x
        ((((AlgebraicGeometry.Scheme.Modules.moduleStalkFunctor U.toScheme x).mapIso
          (((Scheme.Modules.restrictFunctor U.ι).mapIso e).symm ≪≫ eM)).hom)
          ((AlgebraicGeometry.Scheme.Modules.moduleStalkMap U.toScheme x
            ((Scheme.Modules.restrictFunctor U.ι).map e.hom)) (e₁M.symm m))) =
      freeOneStalkLinearEquiv U.toScheme x
        ((((AlgebraicGeometry.Scheme.Modules.moduleStalkFunctor U.toScheme x).mapIso eM).hom) (e₁M.symm m))
    congr 1
    change (AlgebraicGeometry.Scheme.Modules.moduleStalkFunctor U.toScheme x).map
          (((Scheme.Modules.restrictFunctor U.ι).mapIso e).symm.hom ≫ eM.hom)
          ((AlgebraicGeometry.Scheme.Modules.moduleStalkFunctor U.toScheme x).map
            ((Scheme.Modules.restrictFunctor U.ι).map e.hom) (e₁M.symm m)) =
      (AlgebraicGeometry.Scheme.Modules.moduleStalkFunctor U.toScheme x).map eM.hom (e₁M.symm m)
    change ((AlgebraicGeometry.Scheme.Modules.moduleStalkFunctor U.toScheme x).map
          ((Scheme.Modules.restrictFunctor U.ι).map e.hom) ≫
        (AlgebraicGeometry.Scheme.Modules.moduleStalkFunctor U.toScheme x).map
          (((Scheme.Modules.restrictFunctor U.ι).mapIso e).symm.hom ≫ eM.hom))
          (e₁M.symm m) =
      (AlgebraicGeometry.Scheme.Modules.moduleStalkFunctor U.toScheme x).map eM.hom (e₁M.symm m)
    have hmap := (AlgebraicGeometry.Scheme.Modules.moduleStalkFunctor U.toScheme x).map_comp
      ((Scheme.Modules.restrictFunctor U.ι).map e.hom)
      (((Scheme.Modules.restrictFunctor U.ι).mapIso e).symm.hom ≫ eM.hom)
    rw [← hmap]
    have hbeq : (Scheme.Modules.restrictFunctor U.ι).map e.hom =
        ((Scheme.Modules.restrictFunctor U.ι).mapIso e).hom := rfl
    have hcat :
        (Scheme.Modules.restrictFunctor U.ι).map e.hom ≫
            (((Scheme.Modules.restrictFunctor U.ι).mapIso e).symm.hom ≫ eM.hom) =
          eM.hom := by
      rw [hbeq]
      have hs : ((Scheme.Modules.restrictFunctor U.ι).mapIso e).symm.hom =
          ((Scheme.Modules.restrictFunctor U.ι).mapIso e).inv := rfl
      rw [hs]
      exact ((Scheme.Modules.restrictFunctor U.ι).mapIso e).hom_inv_id_assoc eM.hom
    rw [hcat]
  exact congrArg ρ.toSemilinearEquiv h₂

/-- Generic coordinates are natural under an isomorphism of module sheaves. -/
theorem genericCoordinate_mapIso
    [IsIntegral X] (e : M ≅ N) (U : X.Opens) (hU : Nonempty U)
    (eM : M.restrict U.ι ≅
      SheafOfModules.free (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin 1)))
    (s : M.presheaf.stalk (genericPoint X)) :
    genericCoordinate X N U hU
        (((Scheme.Modules.restrictFunctor U.ι).mapIso e).symm ≪≫ eM)
        (AlgebraicGeometry.Scheme.Modules.moduleStalkMap X (genericPoint X) e.hom s) =
      genericCoordinate X M U hU eM s := by
  exact lineStalkEquivOfTrivialization_mapIso U
    ⟨genericPoint X, genericPoint_mem_of_nonempty X U hU⟩ e eM s

end AlgebraicGeometry.Divisors.LineGenericCoordinates

namespace AlgebraicGeometry.Divisors
open AlgebraicGeometry.Proj AlgebraicGeometry.Scheme.Modules

variable {k : Type u} [Field k]

/-- Transport a genuine Cartier presentation along an isomorphism of module sheaves.

The Cartier local data are retained verbatim; each frame is transported through the
restricted module isomorphism, and the equation field follows from generic-coordinate
naturality.
-/
def LineCartierPresentation.mapIso {X : SchemeOver k} [IsIntegral X.scheme]
    [IsLocallyNoetherian X.scheme] {M N : X.scheme.Modules}
    {s : M.presheaf.stalk (genericPoint X.scheme)}
    (P : LineCartierPresentation X M s) (e : M ≅ N) :
    LineCartierPresentation X N (moduleStalkMap X.scheme (genericPoint X.scheme) e.hom s) where
  section_ne_zero := by
    intro h
    apply P.section_ne_zero
    have hi := congrArg (moduleStalkMap X.scheme (genericPoint X.scheme) e.inv) h
    have hcomp :
        moduleStalkMap X.scheme (genericPoint X.scheme) e.inv
            (moduleStalkMap X.scheme (genericPoint X.scheme) e.hom s) = s := by
      change (moduleStalkFunctor X.scheme (genericPoint X.scheme)).map e.inv
          ((moduleStalkFunctor X.scheme (genericPoint X.scheme)).map e.hom s) = s
      change ((moduleStalkFunctor X.scheme (genericPoint X.scheme)).map e.hom ≫
        (moduleStalkFunctor X.scheme (genericPoint X.scheme)).map e.inv) s = s
      have hmap := (moduleStalkFunctor X.scheme (genericPoint X.scheme)).map_comp e.hom e.inv
      rw [← hmap, e.hom_inv_id]
      have hId := (moduleStalkFunctor X.scheme (genericPoint X.scheme)).map_id M
      rw [hId]
      rfl
    calc
      s = moduleStalkMap X.scheme (genericPoint X.scheme) e.inv
            (moduleStalkMap X.scheme (genericPoint X.scheme) e.hom s) := hcomp.symm
      _ = moduleStalkMap X.scheme (genericPoint X.scheme) e.inv 0 := hi
      _ = 0 := map_zero _
  cartier := P.cartier
  frame := fun i ↦
    ((Scheme.Modules.restrictFunctor (P.cartier.opens i).ι).mapIso e).symm ≪≫ P.frame i
  equation_eq := by
    intro i hU
    calc
      P.cartier.equation i =
          LineGenericCoordinates.genericCoordinate X.scheme M (P.cartier.opens i) hU
            (P.frame i) s := P.equation_eq i hU
      _ = LineGenericCoordinates.genericCoordinate X.scheme N (P.cartier.opens i) hU
            (((Scheme.Modules.restrictFunctor (P.cartier.opens i).ι).mapIso e).symm ≪≫
              P.frame i)
            (moduleStalkMap X.scheme (genericPoint X.scheme) e.hom s) :=
        (LineGenericCoordinates.genericCoordinate_mapIso
          (X := X.scheme) e (P.cartier.opens i) hU (P.frame i) s).symm

end AlgebraicGeometry.Divisors
