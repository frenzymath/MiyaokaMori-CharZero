import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ChowGroupDegree
import MiyaokaMori.AlgebraicGeometry.Chow.Pushforward.ChowPushforward
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.IdealSheafCycleEqPushforward
import MiyaokaMori.AlgebraicGeometry.Chow.Pushforward.Stacks02r5
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ChowDegreeRatPushforward

/-! # Proper pushforward preserves the degree of zero-cycles

Proper pushforward preserves the degree of zero-dimensional cycle classes: `deg_Y(f_*α) = deg_X α`
(Stacks 0AZ1). Since `ChowGroup.degree` is the scheme-level `degreeOver` and `chowPushforward` is
`AlgebraicGeometry.chowPushforward`, this is the ℤ-version of `degreeOver_chowPushforward`
(`ChowDegreeRatPushforward.lean`); only the instance `f.IsOver (Spec k)` has to be built from `hf`. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- `deg_Y(f_*α) = deg_X α` for a proper morphism `f : X → Y` of smooth projective varieties over `k`
and a zero-dimensional class `α`. -/
theorem ChowGroup.degree_chowPushforward {k : Type u} [Field k] [IsAlgClosed k]
    {X Y : SmoothProjectiveVariety k} (f : X.toScheme ⟶ Y.toScheme) [AlgebraicGeometry.IsProper f]
    (hf : f ≫ Y.structureMorphism = X.structureMorphism)
    (α : ChowGroup X.toVariety 0) :
    ChowGroup.degree Y (chowPushforward f 0 α) = ChowGroup.degree X α := by
  haveI : f.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) := ⟨hf⟩
  rw [ChowGroup.degree_eq_degreeOver, ChowGroup.degree_eq_degreeOver]
  exact MiyaokaMori.ChowDegreeRatPushforward.degreeOver_chowPushforward
    (SmoothProjectiveVariety.isProper_structureMorphism X)
    (SmoothProjectiveVariety.isProper_structureMorphism Y) f α

end
