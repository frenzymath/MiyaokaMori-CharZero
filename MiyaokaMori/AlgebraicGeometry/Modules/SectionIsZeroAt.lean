import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.TrivialLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModuleSheafStalk
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModuleSheafStalkStmt
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.SectionPullbackAlong

/-! # Vanishing of a section at a point

A section vanishes at a point: `s ∈ Γ(X, M)` has germ at `x` in `𝔪_x·M_x` (i.e. the image of `s` in the
fibre `M_x ⊗ κ(x)` is zero). Used to express that homogeneous coordinate sections have no common zero.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/- The germ `s_x ∈ M_x` of `s` at `x` (an `O_{X,x}`-module) lies in `𝔪_x • M_x`. -/

def IsZeroAt {X : AlgebraicGeometry.Scheme.{u}} {M : X.Modules}
    (s : (M.val.obj (Opposite.op ⊤) : Type u)) (x : X) : Prop :=
  let M' : _root_.PresheafOfModules.{u} (X.presheaf ⋙ CategoryTheory.forget₂ CommRingCat RingCat) :=
    M.val
  (show (M.stalk x : Type u) from (TopCat.Presheaf.germ M'.presheaf ⊤ x trivial).hom s) ∈
    (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) •
      (⊤ : Submodule (X.presheaf.stalk x) (M.stalk x))

end
