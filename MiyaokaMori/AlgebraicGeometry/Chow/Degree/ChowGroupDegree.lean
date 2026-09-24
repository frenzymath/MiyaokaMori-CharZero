import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S1Intro.BaseField
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.ClosedSubvariety
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProjectiveOverField
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.SmoothProjectiveVariety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Chow.RationalEquivalence.ChowGroup
import MiyaokaMori.AlgebraicGeometry.Chow.Pushforward.ChowPushforward
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ZeroCycleDegreeScheme

/-! # The degree of zero-dimensional Chow classes on a smooth projective variety

The degree `deg : A_0(X) → ℤ` of zero-cycles (`X` proper over `k`): `Σ n_p [κ(p) : k]` (the intersection
number of Theorem 1.1 of the paper takes values in `ℤ`). It is the scheme-level degree
`AlgebraicGeometry.ChowGroup.degreeOver k X.toScheme _` (Stacks 0AZ1: `Σ_p n_p [κ(p):k]` descended to the
quotient, `X` proper). The hypothesis `[IsAlgClosed k]` is not used but kept for the shape of the
signature at the call sites. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Projective ⇒ the structure morphism is proper. -/
instance SmoothProjectiveVariety.isProper_structureMorphism {k : Type u} [Field k]
    (X : SmoothProjectiveVariety k) : AlgebraicGeometry.IsProper X.structureMorphism :=
  ((isProjectiveOver_iff_isProper_and_isAmple k X.carrier).mp X.projective).1

/-- The degree `deg : A_0(X) → ℤ` of zero-cycles: the scheme-level `degreeOver` (`Σ n_p [κ(p):k]`), `X`
being proper over `Spec k` through its structure morphism. -/
noncomputable def ChowGroup.degree {k : Type u} [Field k] [IsAlgClosed k]
    (X : SmoothProjectiveVariety k) : ChowGroup X.toVariety 0 →+ ℤ :=
  AlgebraicGeometry.ChowGroup.degreeOver k X.toScheme
    (SmoothProjectiveVariety.isProper_structureMorphism X)

/-- By definition, the degree on the variety is the scheme-level `degreeOver`. -/
theorem ChowGroup.degree_eq_degreeOver {k : Type u} [Field k] [IsAlgClosed k]
    (X : SmoothProjectiveVariety k) (α : ChowGroup X.toVariety 0) :
    ChowGroup.degree X α =
      AlgebraicGeometry.ChowGroup.degreeOver k X.toScheme
        (SmoothProjectiveVariety.isProper_structureMorphism X) α := rfl

end
