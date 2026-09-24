import Mathlib.AlgebraicGeometry.FunctionField
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# Function fields and degrees of finite dominant morphisms

This supplies the field-extension interface for finite covers of curves (§3 of the paper). It
applies to integral schemes in
any characteristic; smoothness and projectivity are not needed for this step.

The map of function fields is the actual generic-stalk map of the specified
morphism. Its algebra structure is named explicitly, so an unrelated scalar
action cannot determine the degree. Finiteness of the field extension is proved
from finiteness of the morphism, and positivity excludes the infinite-dimensional
default value of `Module.finrank`. This is the degree of Stacks Project,
Definition 29.52.8 (tag 02NY), including inseparable finite morphisms.

This file constructs neither a normalization in a prescribed extension nor a
ramified cover. Those are separate geometric steps of the same paper argument.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]

/-- A dominant morphism of integral schemes maps the generic point to the generic point. -/
theorem dominantMap_genericPoint (f : X ⟶ Y) [IsDominant f] :
    f (genericPoint X) = genericPoint Y := by
  apply IsGenericPoint.eq _ (genericPoint_spec Y)
  simpa only [Set.image_univ, f.denseRange.closure_range] using
    (genericPoint_spec X).image f.continuous

/-- The contravariant function-field map induced by the morphism's generic-stalk map. -/
def dominantFunctionFieldMap (f : X ⟶ Y) [IsDominant f] :
    Y.functionField ⟶ X.functionField :=
  (Y.presheaf.stalkCongr (.of_eq (dominantMap_genericPoint f).symm)).hom ≫
    f.stalkMap (genericPoint X)

/-- The scalar algebra structure induced by the specified dominant morphism. -/
@[instance_reducible]
def dominantFunctionFieldAlgebra (f : X ⟶ Y) [IsDominant f] :
    Algebra Y.functionField X.functionField :=
  (dominantFunctionFieldMap f).hom.toAlgebra

/-- A finite dominant morphism induces a finite extension of its actual function fields. -/
theorem finiteMap_functionField_finite (f : X ⟶ Y) [IsDominant f] [IsFinite f] :
    letI := dominantFunctionFieldAlgebra f
    Module.Finite Y.functionField X.functionField := by
  let e := Y.presheaf.stalkCongr (.of_eq (dominantMap_genericPoint f).symm)
  have he : e.hom.hom.QuasiFinite :=
    RingHom.QuasiFinite.of_finite
      (RingHom.Finite.of_surjective e.hom.hom e.commRingCatIsoToRingEquiv.surjective)
  have hq : (dominantFunctionFieldMap f).hom.QuasiFinite :=
    (f.quasiFiniteAt (genericPoint X)).comp he
  let := dominantFunctionFieldAlgebra f
  have : Algebra.QuasiFinite Y.functionField X.functionField := hq
  exact Module.Finite.of_quasiFinite

/-- The field-extension degree of the specified finite dominant scheme morphism. -/
def finiteMapFunctionFieldDegree (f : X ⟶ Y) [IsDominant f] [IsFinite f] : ℕ :=
  letI := dominantFunctionFieldAlgebra f
  letI := finiteMap_functionField_finite f
  Module.finrank Y.functionField X.functionField

/-- The degree is positive because the extension is finite and its underlying field is nontrivial. -/
theorem finiteMapFunctionFieldDegree_pos (f : X ⟶ Y) [IsDominant f] [IsFinite f] :
    0 < finiteMapFunctionFieldDegree f := by
  let := dominantFunctionFieldAlgebra f
  have := finiteMap_functionField_finite f
  exact Module.finrank_pos

end AlgebraicGeometry.Scheme
