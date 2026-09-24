import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.DualSheaf
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.FrameTrivialization
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundle

/-! # The dual of a line bundle

Statement: the dual sheaf `dualSheaf L` of a line bundle is a line bundle (an instance, given directly by the
dual frame); bundled version `LineBundle.dual`.

The sections of `dualSheaf` are families of local functionals, and the dual frame `e^∨ = coord_e` of a frame
`e` is explicit (`IsFrame.dualFrame_isFrame`); "has a frame ⟺ line bundle" (`isLineBundle_iff_exists_frame`)
then gives the claim.

Reference: Stacks 01CT.
-/

set_option autoImplicit false

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}}

/-- The dual of a line bundle is a line bundle. -/
instance Modules.dualSheaf_isLineBundle (M : X.Modules) [M.IsLineBundle] :
    (Modules.dualSheaf M).IsLineBundle :=
  (Modules.isLineBundle_iff_exists_frame _).mpr fun p ↦ by
    obtain ⟨W, hp, e, he⟩ := Modules.exists_frame M p
    exact ⟨W, hp, _, he.dualFrame_isFrame⟩

/-- The dual `L^∨` of a bundled line bundle. -/
def LineBundle.dual (L : X.LineBundle) : X.LineBundle := .ofModules (Modules.dualSheaf L.toModules)

@[simp] theorem LineBundle.dual_toModules (L : X.LineBundle) :
    L.dual.toModules = Modules.dualSheaf L.toModules := rfl

end AlgebraicGeometry.Scheme

end
