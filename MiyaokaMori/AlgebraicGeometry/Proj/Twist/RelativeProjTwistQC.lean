import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedQcAlgebraSectionsRing
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.GradedQuasicoherentAlgebra
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.ProjTwistPushTransition
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.ProjTwistingSheaf
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjQC
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.Stacks01no
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.RelativeProjTwistLimit

/-! # The twisting sheaf `O_{Proj_X S}(m)` of a relative Proj

The twisting sheaf `O_{Proj_X S}(m)` on the relative Proj of a graded quasi-coherent algebra
(in general only a quasi-coherent sheaf, not necessarily invertible; see Lemma 2.2 of the paper). `relativeProj.twist S m` is an `abbrev` for
`S.toGradedAffineAlgebra.twist m` (module `RelativeProjTwistLimit`), whose transition maps
are the ring-level maps `Proj.twistPushTransition` (`θ_f`); the inner constant
`GradedAffineAlgebra.twist` is `irreducible` (see the note at the end of the file).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- `O_{Proj_X S}(m)`: the twisting sheaf, the limit of the sheaves `O(m)` on the charts
`Proj A(U)` pushed forward along `projChart`. A reducible alias (`abbrev`) of the primary
definition `GradedAffineAlgebra.twist`, which is irreducible. -/
noncomputable abbrev AlgebraicGeometry.Scheme.relativeProj.twist {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) (m : ℤ) : (AlgebraicGeometry.Scheme.relativeProj S).left.Modules :=
  S.toGradedAffineAlgebra.twist m

/-- The projection `O(m) ⟶ (ι_U)_* O_U(m)` to the pushforward of a chart (a reducible alias
of `GradedAffineAlgebra.twistπ`). -/
noncomputable abbrev AlgebraicGeometry.Scheme.relativeProj.twistπ {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) (m : ℤ) (U : X.affineOpens) :
    AlgebraicGeometry.Scheme.relativeProj.twist S m ⟶
      (AlgebraicGeometry.Scheme.Modules.pushforward
          (S.toGradedAffineAlgebra.projChart ⟨U.1, U.2⟩)).obj
        (AlgebraicGeometry.Proj.twist (S.sectionsGrading U.1) m) :=
  S.toGradedAffineAlgebra.twistπ m ⟨U.1, U.2⟩

/- `relativeProj.twist` is deliberately *not* made irreducible. The inner constant
`GradedAffineAlgebra.twist` carries `attribute [irreducible]`, so `relativeProj.twist S m`
unfolds exactly one step (to `S.toGradedAffineAlgebra.twist m`) and stops, instead of unfolding
all the way to `limit (twistDiagram m)`, the `Proj.twist` of the charts and the sheafification
predicate on homogeneous localizations. Sealing the outer name as well would break
`Stacks01nr.twistAffineHom`, whose body uses the definitional equality
`twist S n ≡ S.toGradedAffineAlgebra.twist n` to connect with `twistChartHom`. Sealing only the
inner constant blocks the expensive unfolding while keeping this one step available; the outer
`abbrev` is reducible, the inner constant irreducible, and the equality above holds at reducible
transparency. -/

end
