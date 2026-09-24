import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.ClosedSubvariety
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.CurveDimensionOne
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.CycleGroup
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.FundamentalClass
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.OneCycle
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.SchemeDimension
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProperOverField

/-! # Integral curves in a scheme

An integral curve in a `k`-scheme `X` is an integral, proper, one-dimensional scheme `Γ` over
`k` together with a closed immersion `ι : Γ → X`. Only a `k`-scheme structure is required of `X`
(not smoothness, integrality or properness): the paper uses this for the singular `Y_k^GG`, for
components of fibres of a surface, and for singular rational curves; `Γ` is not required to be
smooth either. `Γ` inherits its `k`-scheme structure through `ι` (structure morphism
`ι ≫ (X ↘ Spec k)`), and properness means that this composite is proper. When `X` is a variety
over `k`, `Γ` is a one-dimensional closed subvariety of `X` and has a fundamental class
`[Γ] ∈ Z_1(X)`. Users needing smoothness (Riemann–Roch, Serre duality, normal bundles) add it as
a separate hypothesis.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- An integral curve in `X`: an integral scheme `Γ`, proper and one-dimensional over `k`, with a
closed immersion `ι : Γ ⟶ X`. -/
structure IntegralCurve (k : Type u) [Field k] (X : AlgebraicGeometry.Scheme.{u})
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] where
  carrier : AlgebraicGeometry.Scheme.{u}
  ι : carrier ⟶ X
  [isClosedImmersion : AlgebraicGeometry.IsClosedImmersion ι]
  [isIntegral : AlgebraicGeometry.IsIntegral carrier]
  [isProper : AlgebraicGeometry.IsProper (ι ≫ (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))]
  dim_eq_one : SchemeIsOneDimensional carrier

attribute [instance] IntegralCurve.isClosedImmersion IntegralCurve.isIntegral IntegralCurve.isProper

/- `Γ` becomes a `k`-scheme through `ι`, and it is proper over `k`. -/

instance IntegralCurve.over {k : Type u} [Field k] {X : AlgebraicGeometry.Scheme.{u}}
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (Γ : IntegralCurve k X) :
    Γ.carrier.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
  ⟨Γ.ι ≫ (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩

theorem IntegralCurve.isProperOver {k : Type u} [Field k] {X : AlgebraicGeometry.Scheme.{u}}
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (Γ : IntegralCurve k X) :
    IsProperOver k Γ.carrier := by
  exact Γ.isProper

theorem IntegralCurve.carrier_dimension {k : Type u} [Field k] {X : AlgebraicGeometry.Scheme.{u}}
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (Γ : IntegralCurve k X) :
    Γ.carrier.dimension = 1 := by
  rw [AlgebraicGeometry.Scheme.dimension]
  rw [Γ.dim_eq_one]
  norm_num

/- When the ambient scheme is a variety, `Γ` is a one-dimensional closed subvariety and its
   fundamental class lies in `Z_1(X)`. -/

def IntegralCurve.toClosedSubvariety {k : Type u} [Field k] {X : Variety k}
    (Γ : IntegralCurve k X.toScheme) : ClosedSubvariety X :=
  ⟨Γ.carrier, Γ.ι⟩

theorem IntegralCurve.dimension_eq_one {k : Type u} [Field k] {X : Variety k}
    (Γ : IntegralCurve k X.toScheme) : Γ.toClosedSubvariety.dimension = 1 := by
  change Γ.carrier.dimension = 1
  exact Γ.carrier_dimension

noncomputable def IntegralCurve.fundamentalClass {k : Type u} [Field k] {X : Variety k}
    (Γ : IntegralCurve k X.toScheme) : OneCycle X :=
  cast (congrArg (fun i : ℕ => ↥(CycleGroup X i)) Γ.dimension_eq_one)
    Γ.toClosedSubvariety.fundamentalClass

/- When `X` is proper over `k`, every one-dimensional closed subvariety of `X` is an integral
   curve. -/

def IntegralCurve.ofClosedSubvariety {k : Type u} [Field k] {X : Variety k}
    (hX : IsProperOver k X.toScheme) (V : ClosedSubvariety X)
    (hV : SchemeIsOneDimensional V.carrier) : IntegralCurve k X.toScheme :=
  haveI : AlgebraicGeometry.IsProper (X.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := hX
  { carrier := V.carrier
    ι := V.ι
    dim_eq_one := hV }

end
