import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Morphisms.PartialMapPullbackAlong
import MiyaokaMori.AlgebraicGeometry.Varieties.FunctionField.CurveStalkFunctionField

/-! # Pullback of a partial map and the function field point

A dominant morphism `f : X' → X` of integral schemes induces an embedding of function fields
`θ : K(X) → K(X')`, compatible with the stalk maps at every point; the function field point of
a partial map pulled back along `f` is `Spec θ ≫` the original function field point.

Sources: Hartshorne I, Theorem 4.4 and II, Exercise 3.6 (a dominant morphism induces an embedding
of function fields); Stacks 0BX6.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open AlgebraicGeometry

/-- The function field point of a partial map pulled back along `f` is
`Spec (f^♯ : K(X) → K(X')) ≫` the original function field point, where
`f^♯ = AlgebraicGeometry.Scheme.dominantFunctionFieldMap f` (the stalk map at the generic point composed with
`stalkCongr`).

Proof: both sides are morphisms `Spec K(X') ⟶ Z`; after unfolding `fromFunctionField`,
`fromSpecStalkOfMem` and `pullbackAlong` it suffices to compare two morphisms to `g.domain`, and
since `g.domain.ι` is a monomorphism it suffices to compare after composing with `ι`:
the left side is `X'.fromSpecStalk η' ≫ f` (`Opens.fromSpecStalkOfMem_ι`, `morphismRestrict_ι`),
the right side is `Spec.map (f.stalkMap η') ≫ Spec.map (stalkSpecializes) ≫ X.fromSpecStalk η`
`= Spec.map (f.stalkMap η') ≫ X.fromSpecStalk (f η')` (`SpecMap_stalkSpecializes_fromSpecStalk`)
`= X'.fromSpecStalk η' ≫ f` (`SpecMap_stalkMap_fromSpecStalk`). -/
theorem AlgebraicGeometry.Scheme.PartialMap.pullbackAlong_fromFunctionField
    {X' X Z : Scheme.{u}} [IsIntegral X'] [IsIntegral X] (f : X' ⟶ X) [IsDominant f]
    (g : X.PartialMap Z) (hd : Dense ((f ⁻¹ᵁ g.domain : X'.Opens) : Set X')) :
    (g.pullbackAlong f hd).fromFunctionField =
      Spec.map (AlgebraicGeometry.Scheme.dominantFunctionFieldMap f) ≫ g.fromFunctionField := by
  have key : ∀ (h1 : genericPoint X' ∈ f ⁻¹ᵁ g.domain) (h2 : genericPoint X ∈ g.domain),
      (f ⁻¹ᵁ g.domain).fromSpecStalkOfMem (genericPoint X') h1 ≫ (f ∣_ g.domain) =
        Spec.map (AlgebraicGeometry.Scheme.dominantFunctionFieldMap f) ≫
          g.domain.fromSpecStalkOfMem (genericPoint X) h2 := by
    intro h1 h2
    have hsp : f (genericPoint X') ⤳ genericPoint X :=
      specializes_of_eq (AlgebraicGeometry.Scheme.dominantMap_genericPoint f)
    have e : (X.presheaf.stalkCongr (.of_eq (AlgebraicGeometry.Scheme.dominantMap_genericPoint f).symm)).hom =
        X.presheaf.stalkSpecializes hsp :=
      TopCat.Presheaf.stalkCongr_hom _ _
    rw [← cancel_mono g.domain.ι, Category.assoc, morphismRestrict_ι,
      Opens.fromSpecStalkOfMem_ι_assoc, Category.assoc, Opens.fromSpecStalkOfMem_ι,
      AlgebraicGeometry.Scheme.dominantFunctionFieldMap, e, Spec.map_comp, Category.assoc,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk, Scheme.SpecMap_stalkMap_fromSpecStalk]
  have h1 : genericPoint X' ∈ f ⁻¹ᵁ g.domain :=
    (genericPoint_specializes _).mem_open (f ⁻¹ᵁ g.domain).2 hd.nonempty.choose_spec
  have h2 : genericPoint X ∈ g.domain :=
    (genericPoint_specializes _).mem_open g.domain.2 g.dense_domain.nonempty.choose_spec
  change (f ⁻¹ᵁ g.domain).fromSpecStalkOfMem (genericPoint X') h1 ≫ (f ∣_ g.domain) ≫ g.hom =
    Spec.map (AlgebraicGeometry.Scheme.dominantFunctionFieldMap f) ≫
      g.domain.fromSpecStalkOfMem (genericPoint X) h2 ≫ g.hom
  rw [← Category.assoc, ← Category.assoc, key h1 h2]

/-- A dominant morphism `f : X' → X` of integral schemes induces a field embedding `θ : K(X) → K(X')`
compatible with the stalk maps, and the function field point of a pulled-back partial map is
`Spec θ ≫` the original one.

Proof: let `η'`, `η` be the generic points of `X'`, `X`; `f` dominant gives `f η' = η`
(`AlgebraicGeometry.Scheme.dominantMap_genericPoint`). Take
`θ := AlgebraicGeometry.Scheme.dominantFunctionFieldMap f = (X.presheaf.stalkCongr _).hom ≫ f.stalkMap η'`.
(1) The commutative square is `AlgebraicGeometry.Scheme.dominantFunctionFieldMap_comp_algebraMap`
(`Scheme.Hom.stalkSpecializes_stalkMap`, `TopCat.Presheaf.stalkSpecializes_comp`;
`algebraMap (stalk x) K` is by definition `(stalkSpecializes _).hom`, `stalkFunctionFieldAlgebra`).
(2) The function field point: `pullbackAlong_fromFunctionField`. -/
theorem AlgebraicGeometry.Scheme.PartialMap.exists_functionField_hom_pullbackAlong
    {X' X Z : Scheme.{u}} [IsIntegral X'] [IsIntegral X] (f : X' ⟶ X) [IsDominant f]
    (g : X.PartialMap Z) (hd : Dense ((f ⁻¹ᵁ g.domain : X'.Opens) : Set X')) :
    ∃ θ : X.functionField ⟶ X'.functionField,
      (∀ x' : X', θ.hom.comp (algebraMap (X.presheaf.stalk (f x')) X.functionField) =
        (algebraMap (X'.presheaf.stalk x') X'.functionField).comp (f.stalkMap x').hom) ∧
      (g.pullbackAlong f hd).fromFunctionField = Spec.map θ ≫ g.fromFunctionField :=
  ⟨AlgebraicGeometry.Scheme.dominantFunctionFieldMap f, AlgebraicGeometry.Scheme.dominantFunctionFieldMap_comp_algebraMap f,
    g.pullbackAlong_fromFunctionField f hd⟩

end
