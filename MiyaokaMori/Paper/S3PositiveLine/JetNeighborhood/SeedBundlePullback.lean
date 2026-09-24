import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedQcAlgebraPullback
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierDivisorPullback
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.ClosedSubvariety
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.VarietyLineBundle
import MiyaokaMori.AlgebraicGeometry.Divisors.LineBundle.OXOne
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.SmoothProjectiveVariety
import MiyaokaMori.Paper.S1Intro.TangentBundlePullback
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundle
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundlePullback
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.AlgebraicGeometry.Varieties.FiniteCover
import MiyaokaMori.Paper.S2WeightedJets.Cone.HyperplaneBundlePullback
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.IdealSheafToModules
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.SectionPullbackAlong
import MiyaokaMori.Paper.S2WeightedJets.Cone.SeedLineBundleIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.VarietyChosenEmbedding
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedPolynomialAlgebraPullback
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundlePullback
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.NefPullback

/-! # The seed line bundle and its pullback along a finite cover

The seed line bundle `A = f^*O_X(1)` (packaged as a `LineBundle`), its pullback `A_ρ = ρ^*A` along a finite cover
`ρ`, and the map `seedCoordPullback` transporting the coordinate sections of `seedLineBundle` to `ρ^*A` (through
the `eqToHom` of `OX_toModules`; this is the same transport as in the body of `BasedJet.coneCoordinate`).
`A` and `A_ρ` are definitions rather than two nested `LineBundle.pullback`s in every statement: when the unfolded
expression appears in a type, `whnf` unfolds the pullback and sheafification layers and the statement itself
times out.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The seed line bundle `A = f^*O_X(1)` (packaged as a `LineBundle`). Its underlying module is by definition
    `(Modules.pullback f).obj (X.OX 1).toModules`, the spelling of the target of `BasedJet.coneCoordinate`; it
    agrees with `seedLineBundle X.embedding f = f^*(e.oX 1)` only up to the propositional equality
    `SmoothProjectiveVariety.OX_toModules`. -/

noncomputable def seedBundle {k : Type u} [Field k] {X : SmoothProjectiveVariety k}
    {C : SmoothProjectiveCurve k} (f : C.toScheme ⟶ X.toScheme) : LineBundle C.toVariety :=
  LineBundle.pullback (X := C.toVariety) f (X.OX 1)

/-- The pullback `A_ρ = ρ^*A` of the seed bundle along the finite cover `ρ`. A definition rather than two nested
    `LineBundle.pullback`s: once the unfolded expression enters a type, comparing the two sides of an equation or
    feeding a section to `restrictToThickening` / `xiDegree` makes `whnf` unfold the pullback and sheafification
    layers, and the statement alone exceeds the heartbeat limit. -/

noncomputable def seedBundlePullback {k : Type u} [Field k] {X : SmoothProjectiveVariety k}
    {C : SmoothProjectiveCurve k} (f : C.toScheme ⟶ X.toScheme) (ρ : FiniteCover k C) :
    LineBundle ρ.source.toVariety :=
  LineBundle.pullback (X := ρ.source.toVariety) ρ.hom (seedBundle f)

/-- Transport a section of `seedLineBundle X.embedding f` to `A = seedBundle f` (through the `eqToHom` of
    `OX_toModules`) and pull it back along `ρ`: a global section of `ρ^*A`. The body of `coneCoordinate` uses the
    same transport. -/

noncomputable def seedCoordPullback {k : Type u} [Field k] {X : SmoothProjectiveVariety k}
    {C : SmoothProjectiveCurve k} (f : C.toScheme ⟶ X.toScheme) (ρ : FiniteCover k C)
    (s : ((seedLineBundle X.embedding f).val.obj (Opposite.op ⊤) : Type u)) :
    (((AlgebraicGeometry.Scheme.Modules.pullback ρ.hom).obj
      (seedBundle f).toModules).val.obj (Opposite.op ⊤) : Type u) :=
  (((AlgebraicGeometry.Scheme.Modules.pullback ρ.hom).map
      ((AlgebraicGeometry.Scheme.Modules.pullback f).map
        (CategoryTheory.eqToHom (X.OX_toModules 1).symm))).val.app (Opposite.op ⊤)).hom
    (sectionPullbackAlong ρ.hom s)

end
