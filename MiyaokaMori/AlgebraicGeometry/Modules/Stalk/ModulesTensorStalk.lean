import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorMonoidalIso
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.TensorPresheafStalk
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModuleSheafificationStalk
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModuleStalkIso

/-! # Stalks of tensor products of sheaves of modules

**Stalks of a tensor product** (Stacks 01CB): for any two `O_X`-modules `A`, `B` and a point `x`,
the canonical map gives `(A ⊗ B)_x ≅ A_x ⊗_{O_{X,x}} B_x`, sending the germ of the section pairing
`tensorSections A B U a b` to `a_x ⊗ₜ b_x`. No quasi-coherence, finite presentation, local freeness
or flatness is needed.

Source: Stacks Project, `modules.tex`, Tag 01CB (proof "Omitted" there).

Proof in three steps:
1. `A ⊗ B` (the localized monoidal structure on sheaves of modules) and
   `Modules.tensor A B = L(G A ⊗ G B)` (the sheafification of the tensor presheaf) are canonically
   isomorphic via `Modules.tensorIsoTensorObj`; an isomorphism of sheaves of modules is a linear
   isomorphism on every stalk (`AlgebraicGeometry.Scheme.Modules.moduleHom_isIso_iff_stalk_bijective`).
2. **Sheafification does not change stalks**: `AlgebraicGeometry.Scheme.Modules.moduleSheafificationStalkEquiv` (via
   Mathlib's `TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso`).
3. **The stalk of the presheaf tensor product is the tensor product of stalks**:
   `AlgebraicGeometry.Scheme.Modules.tensorPresheafStalkEquiv` (`TensorPresheafStalk`): filtered colimits commute with
   tensor products; the inverse sends two germs on a common neighbourhood to the germ of their pure
   tensor, well defined because filtered colimits of sets commute with finite products.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry TensorProduct

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- An isomorphism of sheaves of modules induces on every stalk a linear isomorphism over the local
ring (`AlgebraicGeometry.Scheme.Modules.moduleStalkMap` together with "isomorphism ⇔ bijective on stalks",
`AlgebraicGeometry.Scheme.Modules.moduleHom_isIso_iff_stalk_bijective`). -/
def moduleStalkLinearEquiv (X : AlgebraicGeometry.Scheme.{u}) (x : X) {M N : X.Modules}
    (e : M ≅ N) :
    M.presheaf.stalk x ≃ₗ[X.presheaf.stalk x] N.presheaf.stalk x :=
  LinearEquiv.ofBijective (AlgebraicGeometry.Scheme.Modules.moduleStalkMap X x e.hom)
    ((AlgebraicGeometry.Scheme.Modules.moduleHom_isIso_iff_stalk_bijective e.hom).mp inferInstance x)

@[simp]
theorem moduleStalkLinearEquiv_germ (X : AlgebraicGeometry.Scheme.{u}) (x : X) {M N : X.Modules}
    (e : M ≅ N) (U : X.Opens) (hx : x ∈ U) (m : Γ(M, U)) :
    moduleStalkLinearEquiv X x e ((M.presheaf.germ U x hx) m) =
      (N.presheaf.germ U x hx) (e.hom.app U m) :=
  AlgebraicGeometry.Scheme.Modules.moduleStalkMap_germ X x e.hom U hx m

/-- **Stacks 01CB, stalks of a tensor product**: `(A ⊗ B)_x ≅ A_x ⊗_{O_{X,x}} B_x`. -/
def tensorStalkEquiv (A B : X.Modules) (x : X) :
    (CategoryTheory.MonoidalCategoryStruct.tensorObj (C := X.Modules) A B).presheaf.stalk x
      ≃ₗ[X.presheaf.stalk x]
      (A.presheaf.stalk x ⊗[X.presheaf.stalk x] B.presheaf.stalk x) :=
  (moduleStalkLinearEquiv X x (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj A B)).symm ≪≫ₗ
    (AlgebraicGeometry.Scheme.Modules.moduleSheafificationStalkEquiv X (AlgebraicGeometry.Scheme.Modules.moduleTensorPresheaf A B) x).symm ≪≫ₗ
      AlgebraicGeometry.Scheme.Modules.tensorPresheafStalkEquiv X A.val B.val x

/-- The value of the stalk isomorphism on section pairings: the germ of `tensorSections A B U a b`
is sent to `a_x ⊗ₜ b_x`. Since such germs generate `(A ⊗ B)_x`, this property determines
`tensorStalkEquiv`. -/
@[simp]
theorem tensorStalkEquiv_germ_tensorSections (A B : X.Modules) (x : X) (U : X.Opens) (hx : x ∈ U)
    (a : A.val.obj (op U)) (b : B.val.obj (op U)) :
    tensorStalkEquiv A B x
        ((CategoryTheory.MonoidalCategoryStruct.tensorObj (C := X.Modules) A B).presheaf.germ U x hx
          (AlgebraicGeometry.Scheme.Modules.tensorSections A B U a b)) =
      (A.presheaf.germ U x hx) a ⊗ₜ[X.presheaf.stalk x] (B.presheaf.germ U x hx) b := by
  have key : moduleStalkLinearEquiv X x (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj A B)
      ((AlgebraicGeometry.Scheme.Modules.moduleSheafificationStalkEquiv X (AlgebraicGeometry.Scheme.Modules.moduleTensorPresheaf A B) x)
        (TopCat.Presheaf.germ (AlgebraicGeometry.Scheme.Modules.moduleTensorPresheaf A B).presheaf U x hx
          (a ⊗ₜ[X.presheaf.obj (op U)] b))) =
      (CategoryTheory.MonoidalCategoryStruct.tensorObj (C := X.Modules) A B).presheaf.germ U x hx
        (AlgebraicGeometry.Scheme.Modules.tensorSections A B U a b) := by
    rw [AlgebraicGeometry.Scheme.Modules.moduleSheafificationStalkEquiv_germ]
    exact AlgebraicGeometry.Scheme.Modules.moduleStalkMap_germ X x
      (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj A B).hom U hx _
  rw [← key]
  show AlgebraicGeometry.Scheme.Modules.tensorPresheafStalkEquiv X A.val B.val x
    ((AlgebraicGeometry.Scheme.Modules.moduleSheafificationStalkEquiv X (AlgebraicGeometry.Scheme.Modules.moduleTensorPresheaf A B) x).symm
      ((moduleStalkLinearEquiv X x
        (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj A B)).symm _)) = _
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
  exact AlgebraicGeometry.Scheme.Modules.tensorPresheafStalkEquiv_germ_tmul X A.val B.val x U hx a b

/-- Two stalk elements have representatives on a common neighbourhood (the sheaf-of-modules form of
`modulePresheafStalk_exists_pair`). -/
theorem exists_germ_pair (A B : X.Modules) (x : X)
    (m : A.presheaf.stalk x) (n : B.presheaf.stalk x) :
    ∃ (U : X.Opens) (hx : x ∈ U) (a : A.val.obj (op U)) (b : B.val.obj (op U)),
      (A.presheaf.germ U x hx) a = m ∧ (B.presheaf.germ U x hx) b = n :=
  AlgebraicGeometry.Scheme.Modules.modulePresheafStalk_exists_pair X A.val B.val x m n

end AlgebraicGeometry.Scheme.Modules

end
