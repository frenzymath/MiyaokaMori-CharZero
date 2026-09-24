import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Morphisms.MorphismFiniteType
import MiyaokaMori.AlgebraicGeometry.Varieties.Points.PointClosureSubscheme
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety

/-! # Closed subvarieties

A closed subvariety of a variety `X` is an integral scheme `V` together with a closed
immersion `V ⟶ X`; closed subvarieties are the generators of the cycle groups.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- A closed subvariety of `X`: an integral scheme with a closed immersion into `X`. -/
structure ClosedSubvariety {k : Type u} [Field k] (X : Variety k) where
  carrier : AlgebraicGeometry.Scheme.{u}
  ι : carrier ⟶ X.toScheme
  [isClosedImmersion : AlgebraicGeometry.IsClosedImmersion ι]
  [isIntegral : AlgebraicGeometry.IsIntegral carrier]

attribute [instance] ClosedSubvariety.isClosedImmersion ClosedSubvariety.isIntegral

/-- A closed subvariety is itself a `k`-variety: the structure morphism is `ι ≫ (X ↘ Spec k)`;
separatedness and finite type are inherited through the closed immersion. -/

noncomputable def ClosedSubvariety.toVariety {k : Type u} [Field k] {X : Variety k}
    (V : ClosedSubvariety X) : Variety k where
  carrier := V.carrier
  «over» := ⟨V.ι ≫ X.structureMorphism⟩
  integral := V.isIntegral
  separated := inferInstanceAs (AlgebraicGeometry.IsSeparated (V.ι ≫ X.structureMorphism))
  finiteType := ({ toLocallyOfFiniteType := inferInstance, toQuasiCompact := inferInstance } :
    AlgebraicGeometry.IsOfFiniteType (V.ι ≫ X.structureMorphism))

/-- The closure of a point `x` as a closed subvariety: the reduced induced subscheme on the
closure `{x}⁻` (`AlgebraicGeometry.Intersection.ReducedPointClosure`, the same construction as
`pointClosure`); it is integral and its inclusion is a closed immersion. -/

noncomputable def ClosedSubvariety.ofPoint {k : Type u} [Field k] {X : Variety k} (x : X.toScheme) :
    ClosedSubvariety X where
  carrier := AlgebraicGeometry.Intersection.ReducedPointClosure.scheme X.toScheme x
  ι := AlgebraicGeometry.Intersection.ReducedPointClosure.inclusion X.toScheme x
  isClosedImmersion := AlgebraicGeometry.Intersection.ReducedPointClosure.inclusion_isClosedImmersion X.toScheme x
  isIntegral := AlgebraicGeometry.Intersection.ReducedPointClosure.scheme_isIntegral X.toScheme x

/-- The generic point of a closed subvariety, as a point of `X`; the cycle `[V]` is recorded at
this point. -/

noncomputable def ClosedSubvariety.genericPt {k : Type u} [Field k] {X : Variety k}
    (V : ClosedSubvariety X) : X.toScheme :=
  V.ι.base (genericPoint V.carrier)

theorem ClosedSubvariety.genericPt_ofPoint {k : Type u} [Field k] {X : Variety k} (x : X.toScheme) :
    (ClosedSubvariety.ofPoint x).genericPt = x := by
  -- `x` is a generic point of its closure, and generic points are unique
  change (AlgebraicGeometry.Intersection.ReducedPointClosure.inclusion X.toScheme x).base
      (genericPoint (AlgebraicGeometry.Intersection.ReducedPointClosure.scheme X.toScheme x)) = x
  rw [← (AlgebraicGeometry.Intersection.ReducedPointClosure.generic_spec X.toScheme x).eq (genericPoint_spec _)]
  rfl

/-- `X` itself as a closed subvariety of `X` (needed for the cycle `[C] ∈ Z_1(C)`). -/

noncomputable def ClosedSubvariety.self {k : Type u} [Field k] (X : Variety k) : ClosedSubvariety X where
  carrier := X.toScheme
  ι := CategoryTheory.CategoryStruct.id X.toScheme

end
