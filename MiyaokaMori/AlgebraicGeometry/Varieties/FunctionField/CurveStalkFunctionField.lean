import MiyaokaMori.AlgebraicGeometry.Varieties.FunctionField.FiniteCurveField

/-!
# Compatibility of stalk maps with the induced function-field map

For the same dominant morphism of integral schemes, the canonical embeddings of
the two local rings into their function fields commute with the stalk map and
`dominantFunctionFieldMap`. Consequently every stalk map is injective. Explicit
algebra structures record the two compatible scalar towers needed by the local
DVR ramification formula.

This is the geometric map interface for the ramification computation on curves. It assumes
neither a valuation formula nor finiteness of a local-ring extension. The actual
DVR conditions and the comparison of orders are separate interfaces.

Sources: Stacks Project, tag 0CC1 (dominant maps of integral schemes), tag 01RW
(function fields), and the definition of morphisms of locally ringed spaces.
The commuting square is the naturality of the stalk maps under specialization
to the generic point. Function fields and their maps are the existing canonical
objects from `FiniteCurveField` and Mathlib; none are redefined here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
variable (f : X ⟶ Y) [IsDominant f] (x : X)

/-- The actual stalk map and induced function-field map form a commuting square. -/
theorem dominantFunctionFieldMap_comp_algebraMap :
    (dominantFunctionFieldMap f).hom.comp
        (algebraMap (Y.presheaf.stalk (f x)) Y.functionField) =
      (algebraMap (X.presheaf.stalk x) X.functionField).comp (f.stalkMap x).hom := by
  change
    (Y.presheaf.stalkSpecializes ((genericPoint_spec Y).specializes trivial) ≫
        (Y.presheaf.stalkCongr (.of_eq (dominantMap_genericPoint f).symm)).hom ≫
        f.stalkMap (genericPoint X)).hom =
      (f.stalkMap x ≫
        X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes trivial)).hom
  congr 1
  erw [TopCat.Presheaf.stalkCongr_hom, ← Category.assoc,
    TopCat.Presheaf.stalkSpecializes_comp]
  exact f.stalkSpecializes_stalkMap (genericPoint X) x
    ((genericPoint_spec X).specializes trivial)

/-- Elementwise form of the same stalk/function-field commuting square. -/
theorem dominantFunctionFieldMap_algebraMap (a : Y.presheaf.stalk (f x)) :
    dominantFunctionFieldMap f (algebraMap (Y.presheaf.stalk (f x)) Y.functionField a) =
      algebraMap (X.presheaf.stalk x) X.functionField (f.stalkMap x a) :=
  DFunLike.congr_fun (dominantFunctionFieldMap_comp_algebraMap f x) a

/-- Dominance between integral schemes makes every actual local-ring map injective. -/
theorem dominant_stalkMap_injective : Function.Injective (f.stalkMap x) := by
  intro a b hab
  apply IsFractionRing.injective (Y.presheaf.stalk (f x)) Y.functionField
  apply (dominantFunctionFieldMap f).hom.injective
  rw [dominantFunctionFieldMap_algebraMap f x, dominantFunctionFieldMap_algebraMap f x]
  exact congrArg (algebraMap (X.presheaf.stalk x) X.functionField) hab

/-- The algebra on the target stalk induced by this morphism's actual stalk map. -/
@[instance_reducible]
def morphismStalkAlgebra : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
  (f.stalkMap x).hom.toAlgebra

/-- The source stalk acts on the target function field through the same function-field map. -/
@[instance_reducible]
def sourceStalkFunctionFieldAlgebra : Algebra (Y.presheaf.stalk (f x)) X.functionField :=
  ((dominantFunctionFieldMap f).hom.comp
    (algebraMap (Y.presheaf.stalk (f x)) Y.functionField)).toAlgebra

/-- The named source-stalk action factors through the canonical source function field. -/
theorem sourceStalk_functionField_isScalarTower :
    letI := dominantFunctionFieldAlgebra f
    letI := sourceStalkFunctionFieldAlgebra f x
    IsScalarTower (Y.presheaf.stalk (f x)) Y.functionField X.functionField := by
  let := dominantFunctionFieldAlgebra f
  let := sourceStalkFunctionFieldAlgebra f x
  apply IsScalarTower.of_algebraMap_eq'
  rfl

/-- The same source-stalk action also factors through the actual target stalk. -/
theorem sourceStalk_targetStalk_isScalarTower :
    letI := morphismStalkAlgebra f x
    letI := sourceStalkFunctionFieldAlgebra f x
    IsScalarTower (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) X.functionField := by
  let := morphismStalkAlgebra f x
  let := sourceStalkFunctionFieldAlgebra f x
  apply IsScalarTower.of_algebraMap_eq'
  exact dominantFunctionFieldMap_comp_algebraMap f x

end AlgebraicGeometry.Scheme
