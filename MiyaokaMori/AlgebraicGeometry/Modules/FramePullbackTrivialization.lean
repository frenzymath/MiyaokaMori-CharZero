import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.PullbackFrameRankOne
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.ModuleSheafFrameIso

/-! # A frame pulled back to a scheme lying inside its domain gives a global trivialization

`ι : Y ⟶ T` lands in `W_T ⊆ T` (`⊤ ≤ ι⁻¹W_T`), `t` is a frame of `N` on `W_T`. Then `η(t)|_⊤` is a global
frame of `ι^*N` (`isFrame_unitSec_pullback` + `IsFrame.restrict`), and the inverse of its
`topTrivialization` is a trivialization `e' : ι^*N ≅ O_Y` with `e'(η(t)|_⊤) = 1`. This is the shape of
trivialization `relativeProj.liftLocalPieceAux` consumes. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false

variable {Y T : AlgebraicGeometry.Scheme.{u}}

/-- The global trivialization attached to a global frame reads off the coordinate:
`(topTrivialization e).inv (r • e) = r`; in particular it sends `e` to `1`. -/
theorem IsFrame.topTrivialization_inv_app_frame {M : Y.Modules} {e : Γ(M, ⊤)} (hf : IsFrame M ⊤ e) :
    Hom.app hf.topTrivialization.inv ⊤ e = (1 : Γ(Y, ⊤)) := by
  have h1 : Hom.app hf.topTrivialization.hom ⊤ (1 : Γ(Y, ⊤)) = e := by
    refine (homOfSection_app M e ⊤ (1 : Γ(Y, ⊤))).trans ?_
    rw [res_self, one_smul]
  refine (congrArg (fun z => Hom.app hf.topTrivialization.inv ⊤ z) h1.symm).trans ?_
  exact congrArg (fun φ : SheafOfModules.unit Y.ringCatSheaf ⟶ SheafOfModules.unit Y.ringCatSheaf =>
    Hom.app φ ⊤ (1 : Γ(Y, ⊤))) hf.topTrivialization.hom_inv_id

/-- **Frame ⇒ trivialization of the pullback.** If `ι` lands in `W_T` and `t` is a frame of `N` on `W_T`,
there is `e' : ι^*N ≅ O_Y` with `e'(η(t)|_⊤) = 1`. -/
theorem exists_iso_unit_app_res_unitSec_eq_one (ι : Y ⟶ T) (N : T.Modules) {W_T : T.Opens}
    (hι : (⊤ : Y.Opens) ≤ ι ⁻¹ᵁ W_T) {t : Γ(N, W_T)} (ht : IsFrame N W_T t) :
    ∃ e' : (pullback ι).obj N ≅ SheafOfModules.unit Y.ringCatSheaf,
      Hom.app e'.hom ⊤ (((pullback ι).obj N).res hι (MiyaokaMori.DualPullback.unitSec ι N t)) =
        (1 : Γ(Y, ⊤)) := by
  have hu : IsFrame ((pullback ι).obj N) ⊤
      (((pullback ι).obj N).res hι (MiyaokaMori.DualPullback.unitSec ι N t)) :=
    (MiyaokaMori.DualPullback.isFrame_unitSec_pullback ι N ht).restrict hι
  exact ⟨hu.topTrivialization.symm, hu.topTrivialization_inv_app_frame⟩

end AlgebraicGeometry.Scheme.Modules

end
