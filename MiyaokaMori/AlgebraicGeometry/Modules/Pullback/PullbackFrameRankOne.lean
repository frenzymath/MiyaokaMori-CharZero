import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.PullbackFrameIsFrame

/-! # The pullback of a frame of a line bundle is a frame

**The pullback of a frame of a line bundle is a frame** (rank-1 case of `isFrameOn_pullback`,
Stacks 01C6/01CR), and **the adjunction unit is linear**: for `f : X ⟶ Y`, `F : Y.Modules`,
`e ∈ Γ(F, V)` a frame of `F` on `V ⊆ Y` (`IsFrame`), the unit section
`unitSec f F e ∈ Γ(f^*F, f⁻¹V)` is a frame of `f^*F` on `f⁻¹V`; and
`unitSec f F (r • m) = f.app V r • unitSec f F m`.

Proof: `IsFrame M U e ↔ IsFrameOn M (fun _ : PUnit => e)` (`isFrameOn_punit_iff`): the frame map
of the singleton family is `r ↦ r () • e|`, so both bijectivity statements are the same up to the
equivalence `(PUnit → R) ≃ R`. Then apply `isFrameOn_pullback` (`PullbackFrameIsFrame.lean`), whose
pulled-back family
`unitFrame' f F V (fun _ => e)` is definitionally `fun _ => unitSec f F e`. Linearity of the unit
section is `Hom.app_smul` for the unit `F ⟶ f_* f^* F`, the `Γ(Y, V)`-action on `Γ(f_* f^*F, V) =
Γ(f^*F, f⁻¹V)` being through `f.app V`.

Used for `O_X(f^*D) ≅ f^*O_Y(D)` (frames `f^*(g_i^{-1})` of `f^*O_Y(D)` on `f^{-1}U_i`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory Opposite TopologicalSpace
open scoped AlgebraicGeometry
open AlgebraicGeometry

noncomputable section

namespace MiyaokaMori.DualPullback

open AlgebraicGeometry.Scheme.Modules (res res_res res_self res_smul)

set_option backward.isDefEq.respectTransparency false

variable {X : Scheme.{u}}

/-- The frame map of a singleton family is `r ↦ r () • e|`. -/
theorem frameMap_punit_apply (M : X.Modules) {U : X.Opens} (e : Γ(M, U)) {W : X.Opens}
    (hW : W ≤ U) (r : PUnit.{u + 1} → Γ(X, W)) :
    frameMap M (fun _ : PUnit.{u + 1} => e) hW r = r PUnit.unit • res M hW e := by
  rw [frameMap_apply, Fintype.sum_unique]

/-- `IsFrame` is `IsFrameOn` for the singleton family. -/
theorem isFrameOn_punit_iff (M : X.Modules) {U : X.Opens} (e : Γ(M, U)) :
    IsFrameOn M (fun _ : PUnit.{u + 1} => e) ↔ Scheme.Modules.IsFrame M U e := by
  have key : ∀ (W : X.Opens) (hW : W ≤ U),
      ⇑(frameMap M (fun _ : PUnit.{u + 1} => e) hW) =
        (fun r : Γ(X, W) => r • Scheme.Modules.res M hW e) ∘
          (Equiv.funUnique PUnit.{u + 1} Γ(X, W)) := by
    intro W hW
    funext r
    exact frameMap_punit_apply M e hW r
  constructor
  · intro h W hW
    have := h W hW
    rw [key] at this
    exact (Function.Bijective.of_comp_iff _ (Equiv.funUnique _ _).bijective).mp this
  · intro h W hW
    rw [key]
    exact (h W hW).comp (Equiv.funUnique _ _).bijective

variable {Y : Scheme.{u}}

/-- **The pullback of a frame is a frame** (rank 1): `unit(e)` is a frame of `f^*F` on `f⁻¹V`. -/
theorem isFrame_unitSec_pullback (f : X ⟶ Y) (F : Y.Modules) {V : Y.Opens} {e : Γ(F, V)}
    (he : Scheme.Modules.IsFrame F V e) :
    Scheme.Modules.IsFrame ((Scheme.Modules.pullback f).obj F) (f ⁻¹ᵁ V) (unitSec f F e) :=
  (isFrameOn_punit_iff _ _).mp (isFrameOn_pullback f F V ((isFrameOn_punit_iff F e).mpr he))

/-- The unit section is linear: `unit(r • m) = f^♯(r) • unit(m)`. -/
theorem unitSec_smul (f : X ⟶ Y) (F : Y.Modules) {Z : Y.Opens} (r : Γ(Y, Z)) (m : Γ(F, Z)) :
    unitSec f F (r • m) = f.app Z r • unitSec f F m :=
  Scheme.Modules.Hom.app_smul ((Scheme.Modules.pullbackPushforwardAdjunction f).unit.app F) r m

end MiyaokaMori.DualPullback

end
