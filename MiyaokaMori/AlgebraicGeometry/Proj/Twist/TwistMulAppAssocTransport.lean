import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.RelativeProjTwistMulAssoc
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.TensorTripleHomExt

/-! # `twistMul_app_assoc` with a free index proof (transport form)

`twistMul_app_assoc` (`RelativeProjTwistMulAssoc`) states the section-level associativity of `twistMul` with the index transport `eqToHom (congrArg (twist S) (add_assoc a b c).symm)`.
`twistMul_app_assoc'` below is the same statement with the index equation `p : a + b + c = a + (b + c)` as a variable
and the `eqToHom` on the other side.

Why a separate module: the only step is the cancellation of the two inverse `eqToHom`s, and the kernel check of that
step takes about 20 s here — the kernel, comparing two non-identical `eqToHom`s between the distinct objects
`twist S (a + b + c)` and `twist S (a + (b + c))`, attempts a K-like reduction whose (doomed) defeq test unfolds
`twist`. Every user of the section-level associativity that has its own index proof would pay this again; stating the
transported form once, with `p` a variable, makes the downstream uses syntactic (`twistPairMul_app_assoc_sections`,
`TwistPullbackPowBlock`).

Source: Stacks 01MO. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory Opposite
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.relativeProj

variable {X : AlgebraicGeometry.Scheme.{u}} (S : X.GradedQCAlgebra)

/-- `twistMul_app_assoc`, transport form: `x · (y · z) = eqToHom ((x · y) · z)` with `p : a + b + c = a + (b + c)` free. -/
theorem twistMul_app_assoc' (a b c : ℤ) (p : a + b + c = a + (b + c))
    (V : (AlgebraicGeometry.Scheme.relativeProj S).left.Opens)
    (x : Γ(AlgebraicGeometry.Scheme.relativeProj.twist S a, V))
    (y : Γ(AlgebraicGeometry.Scheme.relativeProj.twist S b, V))
    (z : Γ(AlgebraicGeometry.Scheme.relativeProj.twist S c, V)) :
    (AlgebraicGeometry.Scheme.relativeProj.twistMul S a (b + c)).app V
        (AlgebraicGeometry.Scheme.Modules.moduleTensorSection x
          ((AlgebraicGeometry.Scheme.relativeProj.twistMul S b c).app V (AlgebraicGeometry.Scheme.Modules.moduleTensorSection y z))) =
      (CategoryTheory.eqToHom (congrArg (AlgebraicGeometry.Scheme.relativeProj.twist S) p)).app V
        ((AlgebraicGeometry.Scheme.relativeProj.twistMul S (a + b) c).app V
          (AlgebraicGeometry.Scheme.Modules.moduleTensorSection
            ((AlgebraicGeometry.Scheme.relativeProj.twistMul S a b).app V (AlgebraicGeometry.Scheme.Modules.moduleTensorSection x y)) z)) := by
  have hA : (AlgebraicGeometry.Scheme.relativeProj.twistMul S (a + b) c).app V
        (AlgebraicGeometry.Scheme.Modules.moduleTensorSection
          ((AlgebraicGeometry.Scheme.relativeProj.twistMul S a b).app V (AlgebraicGeometry.Scheme.Modules.moduleTensorSection x y)) z) =
      (CategoryTheory.eqToHom (congrArg (AlgebraicGeometry.Scheme.relativeProj.twist S) p.symm)).app V
        ((AlgebraicGeometry.Scheme.relativeProj.twistMul S a (b + c)).app V
          (AlgebraicGeometry.Scheme.Modules.moduleTensorSection x
            ((AlgebraicGeometry.Scheme.relativeProj.twistMul S b c).app V (AlgebraicGeometry.Scheme.Modules.moduleTensorSection y z)))) :=
    AlgebraicGeometry.Scheme.relativeProj.twistMul_app_assoc S a b c V x y z
  exact ((congrArg ((CategoryTheory.eqToHom (congrArg (AlgebraicGeometry.Scheme.relativeProj.twist S) p)).app V) hA).trans
    (AlgebraicGeometry.Scheme.Modules.eqToHom_app_eqToHom_app _ _ V _)).symm

end AlgebraicGeometry.Scheme.relativeProj

end
