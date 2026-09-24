import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpaceCanonicallyOver
import MiyaokaMori.AlgebraicGeometry.Varieties.FiniteCover

/-! # Structure morphisms are `S`-morphisms

The following four kinds of morphisms are `S`-morphisms (`Scheme.Hom.IsOver S`), registered as instances:
(1) the inclusion `U.ι` of an open subscheme (`U : X.Opens`, `X` an `S`-scheme); (2) the embedding
`π.fiberι y` of a fibre (`π : X ⟶ Y`, `X` an `S`-scheme); (3) the projection `(Scheme.totalSpace V).hom` of
the total space of a vector bundle (`X` an `S`-scheme); (4) the structure morphism `ρ.hom` of a finite cover
(`ρ : FiniteCover k C`, `S = Spec k`).

Proof.
1. In cases (1)–(3) the `S`-structure morphism of the source is "canonical `X`-structure ≫ `S`-structure
   of `X`": Mathlib provides `U.toScheme.CanonicallyOver X` (`AlgebraicGeometry/Restrict.lean`, `hom = U.ι`)
   and `(π.fiber y).CanonicallyOver X` (`AlgebraicGeometry/Fiber.lean`, `hom = π.fiberι y`); this library
   provides `(Scheme.totalSpace V).left.CanonicallyOver X` (module `TotalSpaceCanonicallyOver`,
   `hom = (totalSpace V).hom`). The composite instance of `CanonicallyOverClass` defines `Z ↘ S` as
   `(Z ↘ X) ≫ (X ↘ S)`, so the required `f ≫ (X ↘ S) = Z ↘ S` holds by definition: `⟨rfl⟩`.
2. Mathlib only registers the forms `U.ι.IsOver X` and `IsOverTower Z X S` (i.e. `HomIsOver (Z ↘ X) S`);
   instance search matches on the syntactic shape of the named morphisms `U.ι`, `π.fiberι y`,
   `(totalSpace V).hom` and does not recognise them as `Z ↘ X`. The instances here are stated in the named
   form so that instance search finds them.
3. In case (4) the field `isOver : ρ.hom ≫ (C.carrier ↘ Spec k) = ρ.source.carrier ↘ Spec k` of
   `FiniteCover` is exactly the content of `HomIsOver`.

Reference: Mathlib `CategoryTheory/Comma/Over/OverClass.lean` (`CanonicallyOverClass`, `HomIsOver`),
`AlgebraicGeometry/Restrict.lean`, `AlgebraicGeometry/Fiber.lean`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The inclusion of an open subscheme is an `S`-morphism. -/
instance AlgebraicGeometry.Scheme.Opens.ι_isOver {X : AlgebraicGeometry.Scheme.{u}}
    (U : X.Opens) (S : AlgebraicGeometry.Scheme.{u}) [X.Over S] :
    U.ι.IsOver S :=
  ⟨rfl⟩

/-- The embedding of a fibre is an `S`-morphism. -/
instance AlgebraicGeometry.Scheme.Hom.fiberι_isOver {X Y : AlgebraicGeometry.Scheme.{u}}
    (π : X ⟶ Y) (y : Y) (S : AlgebraicGeometry.Scheme.{u}) [X.Over S] :
    (π.fiberι y).IsOver S :=
  ⟨rfl⟩

/-- The projection of the total space of a vector bundle is an `S`-morphism. -/
instance AlgebraicGeometry.Scheme.totalSpace_hom_isOver {X : AlgebraicGeometry.Scheme.{u}}
    (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType]
    (S : AlgebraicGeometry.Scheme.{u}) [X.Over S] :
    (AlgebraicGeometry.Scheme.totalSpace V).hom.IsOver S :=
  ⟨rfl⟩

/-- The structure morphism of a finite cover is a `k`-morphism. -/
instance FiniteCover.hom_isOver {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (ρ : FiniteCover k C) :
    ρ.hom.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
  ⟨ρ.isOver⟩

end
