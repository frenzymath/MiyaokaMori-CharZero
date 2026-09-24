import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.VarietyLineBundle
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.GeneratedInDegreeOne
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.GradedQuasicoherentAlgebra
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.RelativeProjTwistQC
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.SufficientlyDivisible
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.VeroneseSubalgebra
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.VeroneseTwistPullback
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.Stacks01ms
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.Stacks01nq
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.Stacks01nr
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.Stacks01o4

/-! # `O(m)` is invertible for sufficiently divisible `m`

For sufficiently divisible `m`, the twisting sheaf `O_{Proj_X S}(m)` on a relative Proj is invertible. In the
weighted case `O(1)` itself is not invertible, which is why the paper uses `O(m)` only for sufficiently
divisible `m`.

Source: Lemma 2.2 of the paper (`O(m)` is invertible and relatively very ample for
sufficiently divisible `m`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- For sufficiently divisible `m` (i.e. `m > 0` and the Veronese subalgebra `S^{(m)}` is generated in degree
one), `O_{Proj_X S}(m)` is a line bundle: it is the pullback of `O(1)` on `Proj_X S^{(m)}`, which is the
universal quotient line bundle. -/
theorem AlgebraicGeometry.Scheme.relativeProj.isLineBundle_twist {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) (m : ℕ) (hm : S.SufficientlyDivisible m) :
    (AlgebraicGeometry.Scheme.relativeProj.twist S (m : ℤ)).IsLineBundle := by
  obtain ⟨hmpos, hgen⟩ := hm
  have hver := AlgebraicGeometry.Scheme.relativeProj.twist_one_universalQuotient
    (S.veronese m) hgen
  have htw : (AlgebraicGeometry.Scheme.relativeProj.twist (S.veronese m) (1 : ℤ)).IsLineBundle := by
    exact hver.1 1
  haveI : (AlgebraicGeometry.Scheme.relativeProj.twist (S.veronese m) (1 : ℤ)).IsLineBundle := htw
  obtain ⟨e⟩ := AlgebraicGeometry.Scheme.relativeProj.veronese_twist_pullback_iso S m hmpos
  exact AlgebraicGeometry.Scheme.Modules.IsLineBundle.of_iso e.symm

end
