import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModuleGenericFiber
import Mathlib.Topology.Sheaves.Sheafify

/-!
# The original module sheafification unit on stalks

For every presheaf of modules on the same scheme, the actual sheafification unit
induces a linear equivalence over the original local ring. Its underlying map is
the stalk map of that unit, including its original `restrictScalars` target.
The equivalence preserves germs and is natural for every presheaf-module morphism.

Sources: Stacks Project, `sheaves.tex`, `lemma-stalk-sheafification` and
`lemma-sheafification-presheaf-modules`. This supplies the sheafification step in
the tensor/exterior stalk comparisons used for the determinant of a pullback.
It does not assert a determinant or degree comparison.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false

/-- The original associated module sheaf on the same scheme. -/
abbrev moduleSheafification (X : Scheme.{u}) (P : X.PresheafOfModules) : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj P

/-- The original module sheafification unit as a linear map on sections. -/
def moduleSheafificationUnit (X : Scheme.{u}) (P : X.PresheafOfModules) (U : X.Opens) :
    P.obj (op U) →ₗ[Γ(X, U)] Γ(moduleSheafification X P, U) :=
  (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
    P).app (op U)).hom

/-- The original unit respects scalar multiplication on each open set. -/
theorem moduleSheafificationUnit_smul (X : Scheme.{u}) (P : X.PresheafOfModules)
    (U : X.Opens) (r : Γ(X, U)) (m : P.obj (op U)) :
    moduleSheafificationUnit X P U (r • m) = r • moduleSheafificationUnit X P U m :=
  (moduleSheafificationUnit X P U).map_smul r m

/-- Naturality of the original unit for an arbitrary presheaf-module morphism. -/
theorem moduleSheafificationUnit_naturality (X : Scheme.{u})
    {P Q : X.PresheafOfModules} (f : P ⟶ Q) (U : X.Opens) (m : P.obj (op U)) :
    ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map f).val.app (op U)
        (moduleSheafificationUnit X P U m) =
      moduleSheafificationUnit X Q U (f.app (op U) m) := by
  have h := (PresheafOfModules.sheafificationAdjunction
    (𝟙 X.ringCatSheaf.obj)).unit.naturality f
  exact congrArg (fun (g : P ⟶ _) => g.app (op U) m) h.symm

/-- The actual unit-induced stalk map, linear over the unchanged local ring. -/
def moduleSheafificationStalkMap (X : Scheme.{u}) (P : X.PresheafOfModules) (x : X) :
    ↑(TopCat.Presheaf.stalk (C := Ab) P.presheaf x) →ₗ[X.presheaf.stalk x]
      (moduleSheafification X P).presheaf.stalk x where
  toFun := (TopCat.Presheaf.stalkFunctor Ab x).map
    (CategoryTheory.toSheafify (Opens.grothendieckTopology X) P.presheaf)
  map_add' := map_add _
  map_smul' r m := by
    obtain ⟨U, hxU, a, rfl⟩ := X.presheaf.exists_germ_eq r
    obtain ⟨V, hVU, hxV, b, rfl⟩ := TopCat.Presheaf.exists_le_germ_eq P.presheaf m hxU
    rw [← X.presheaf.germ_res_apply (CategoryTheory.homOfLE hVU) x hxV a]
    erw [← PresheafOfModules.germ_smul (R := X.presheaf) P,
      TopCat.Presheaf.stalkFunctor_map_germ_apply]
    change (moduleSheafification X P).presheaf.germ V x hxV
      (moduleSheafificationUnit X P V
        (X.presheaf.map (CategoryTheory.homOfLE hVU).op a • (show P.obj (op V) from b))) = _
    erw [moduleSheafificationUnit_smul,
      PresheafOfModules.germ_smul (R := X.presheaf) (moduleSheafification X P).val,
      TopCat.Presheaf.stalkFunctor_map_germ_apply]
    rfl

/-- The linear map is exactly the stalk map of the original adjunction unit.
Its right-adjoint target retains the original identity restriction of scalars. -/
theorem moduleSheafificationStalkMap_unit_apply (X : Scheme.{u})
    (P : X.PresheafOfModules) (x : X)
    (m : ↑(TopCat.Presheaf.stalk (C := Ab) P.presheaf x)) :
    moduleSheafificationStalkMap X P x m =
      (TopCat.Presheaf.stalkFunctor Ab x).map
        ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
          ((PresheafOfModules.sheafificationAdjunction
            (𝟙 X.ringCatSheaf.obj)).unit.app P)) m := rfl

/-- The map takes a germ to the germ of its original unit image. -/
@[simp]
theorem moduleSheafificationStalkMap_germ (X : Scheme.{u}) (P : X.PresheafOfModules)
    (x : X) (U : X.Opens) (hx : x ∈ U) (m : P.obj (op U)) :
    moduleSheafificationStalkMap X P x (TopCat.Presheaf.germ P.presheaf U x hx m) =
      (moduleSheafification X P).presheaf.germ U x hx
        (moduleSheafificationUnit X P U m) :=
  TopCat.Presheaf.stalkFunctor_map_germ_apply (C := Ab) U x hx
    (CategoryTheory.toSheafify (Opens.grothendieckTopology X) P.presheaf) m

/-- Bijectivity comes from the actual sheafification unit's stalk isomorphism. -/
theorem moduleSheafificationStalkMap_bijective (X : Scheme.{u})
    (P : X.PresheafOfModules) (x : X) :
    Function.Bijective (moduleSheafificationStalkMap X P x) := by
  let := TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x Ab P.presheaf
  exact (asIso ((TopCat.Presheaf.stalkFunctor Ab x).map
    (CategoryTheory.toSheafify (Opens.grothendieckTopology X)
      P.presheaf))).addCommGroupIsoToAddEquiv.bijective

/-- Sheafification preserves the original stalk as a module over its local ring. -/
def moduleSheafificationStalkEquiv (X : Scheme.{u}) (P : X.PresheafOfModules) (x : X) :
    ↑(TopCat.Presheaf.stalk (C := Ab) P.presheaf x) ≃ₗ[X.presheaf.stalk x]
      (moduleSheafification X P).presheaf.stalk x :=
  LinearEquiv.ofBijective (moduleSheafificationStalkMap X P x)
    (moduleSheafificationStalkMap_bijective X P x)

/-- The equivalence's forward map is the original linear stalk map. -/
theorem moduleSheafificationStalkEquiv_apply (X : Scheme.{u})
    (P : X.PresheafOfModules) (x : X)
    (m : ↑(TopCat.Presheaf.stalk (C := Ab) P.presheaf x)) :
    moduleSheafificationStalkEquiv X P x m = moduleSheafificationStalkMap X P x m := rfl

/-- The equivalence preserves each original germ and its unit image. -/
@[simp]
theorem moduleSheafificationStalkEquiv_germ (X : Scheme.{u}) (P : X.PresheafOfModules)
    (x : X) (U : X.Opens) (hx : x ∈ U) (m : P.obj (op U)) :
    moduleSheafificationStalkEquiv X P x (TopCat.Presheaf.germ P.presheaf U x hx m) =
      (moduleSheafification X P).presheaf.germ U x hx
        (moduleSheafificationUnit X P U m) :=
  moduleSheafificationStalkMap_germ X P x U hx m

/-- The inverse equivalence recovers every original germ from its unit image. -/
@[simp]
theorem moduleSheafificationStalkEquiv_symm_germ (X : Scheme.{u})
    (P : X.PresheafOfModules) (x : X) (U : X.Opens) (hx : x ∈ U) (m : P.obj (op U)) :
    (moduleSheafificationStalkEquiv X P x).symm
      ((moduleSheafification X P).presheaf.germ U x hx
        (moduleSheafificationUnit X P U m)) = TopCat.Presheaf.germ P.presheaf U x hx m := by
  rw [← moduleSheafificationStalkEquiv_germ]
  exact (moduleSheafificationStalkEquiv X P x).symm_apply_apply _

/-- Naturality on all stalk elements for an arbitrary presheaf-module morphism. -/
theorem moduleSheafificationStalkEquiv_naturality (X : Scheme.{u})
    {P Q : X.PresheafOfModules} (f : P ⟶ Q) (x : X)
    (m : ↑(TopCat.Presheaf.stalk (C := Ab) P.presheaf x)) :
    moduleStalkMap X x
        ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map f)
        (moduleSheafificationStalkEquiv X P x m) =
      moduleSheafificationStalkEquiv X Q x
        ((TopCat.Presheaf.stalkFunctor Ab x).map
          ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map f) m) := by
  obtain ⟨U, hxU, a, rfl⟩ := TopCat.Presheaf.exists_germ_eq P.presheaf m
  rw [moduleSheafificationStalkEquiv_germ, moduleStalkMap_germ]
  erw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
  erw [moduleSheafificationStalkEquiv_germ, moduleSheafificationUnit_naturality]
  rfl

end AlgebraicGeometry.Scheme.Modules
