import MiyaokaMori.AlgebraicGeometry.Modules.Dual.DualEvSections
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModuleDualSectionEquiv
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.DualSheaf

/-! # The dual frame in `Modules.dual`

Glue for `totalSpace_exists_coordinate_of_isFrame` (module `…MonomialRingEquivCoordinate`): the dual
frame as a section of the sheafified dual. Everything here is at the variable level.

`Modules.dual M = moduleSheafDual M` is the sheafification of the presheaf of compatible local
functionals (`LocalDualSections`), whose sections over `W` are, by `DualSheaf`, exactly
`Γ(dualSheaf M, W)`; the sheafification unit `Frame.dualUnit` (= `ModuleDualSectionEquiv.sectionEquiv`) is a
linear isomorphism compatible with restriction. For a frame `e` of `M` on `W`:
* `IsFrame.dualSec`: the dual frame `e^∨ ∈ Γ(dual M, W)` (image of `IsFrame.dualFrame` under `dualUnit`);
* `IsFrame.dualEv_dualSec_frame`: `⟨e^∨, e⟩ = 1` under the evaluation `dualEv M : M^∨ ⊗ M → O_X`
  (`dualEv_app_tensorSections_dualUnit` + `coord_frame`);
* `IsFrame.dualSec_isFrame`: `e^∨` is a frame of `dual M` on `W` (`dualFrame_isFrame` transported along
  `sectionEquiv`, which commutes with restriction: `sectionEquiv_restrict`).
Source: Stacks 01CM (the dual of a free module is free on the dual basis), 01CR.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- The dual frame `e^∨ ∈ Γ(dual M, W)` of a frame `e` of `M` on `W`: the coordinate functional
`x ↦ coord_e(x)` (`IsFrame.dualFrame`, a section of `dualSheaf M`, i.e. a compatible family of local
functionals), pushed into the sheafified dual by the unit `Frame.dualUnit`. -/
def IsFrame.dualSec {M : X.Modules} {W : X.Opens} {e : Γ(M, W)} (hf : IsFrame M W e) :
    Γ(AlgebraicGeometry.Scheme.Modules.dual M, W) :=
  AlgebraicGeometry.Scheme.Modules.Frame.dualUnit M W
    (AlgebraicGeometry.Scheme.Modules.dualSheafSections M W hf.dualFrame)

/-- `⟨e^∨, e⟩ = 1`: evaluation of the dual frame on the frame. -/
theorem IsFrame.dualEv_dualSec_frame {M : X.Modules} {W : X.Opens} {e : Γ(M, W)} (hf : IsFrame M W e) :
    (AlgebraicGeometry.Scheme.Modules.dualEv M).app W
        (AlgebraicGeometry.Scheme.Modules.tensorSections (AlgebraicGeometry.Scheme.Modules.dual M) M W
          hf.dualSec e) = (show Γ(SheafOfModules.unit X.ringCatSheaf, W) from (1 : Γ(X, W))) := by
  unfold IsFrame.dualSec
  rw [AlgebraicGeometry.Scheme.Modules.DualZigzag.dualEv_app_tensorSections_dualUnit]
  have h := hf.coord_frame le_rfl
  rw [res_self] at h
  exact h

/-- `dualUnit` is `sectionEquiv` (same sheafification unit, two spellings). -/
theorem Frame.dualUnit_eq_sectionEquiv (M : X.Modules) (W : X.Opens)
    (ψ : AlgebraicGeometry.Scheme.Modules.Frame.LH M W) :
    AlgebraicGeometry.Scheme.Modules.Frame.dualUnit M W ψ =
      MiyaokaMori.ModuleDualSectionEquiv.sectionEquiv M W ψ := rfl

/-- Restriction of a section of `dual M` given by `sectionEquiv`: `res (sectionEquiv ψ) = sectionEquiv (ψ|)`. -/
theorem res_sectionEquiv (M : X.Modules) {W' W : X.Opens} (h : W' ≤ W)
    (ψ : AlgebraicGeometry.Scheme.Modules.LocalDualSections X M W) :
    AlgebraicGeometry.Scheme.Modules.res (AlgebraicGeometry.Scheme.Modules.dual M) h
        (MiyaokaMori.ModuleDualSectionEquiv.sectionEquiv M W ψ) =
      MiyaokaMori.ModuleDualSectionEquiv.sectionEquiv M W' (AlgebraicGeometry.Scheme.Modules.localDualRestrict M (homOfLE h) ψ) :=
  MiyaokaMori.ModuleDualSectionEquiv.sectionEquiv_restrict M (homOfLE h) ψ

/-- The dual frame is a frame of `dual M` on `W`. -/
theorem IsFrame.dualSec_isFrame {M : X.Modules} {W : X.Opens} {e : Γ(M, W)} (hf : IsFrame M W e) :
    IsFrame (AlgebraicGeometry.Scheme.Modules.dual M) W hf.dualSec := by
  intro W' h
  have hd := hf.dualFrame_isFrame W' h
  have h1 : AlgebraicGeometry.Scheme.Modules.res (AlgebraicGeometry.Scheme.Modules.dual M) h hf.dualSec =
      MiyaokaMori.ModuleDualSectionEquiv.sectionEquiv M W'
        (AlgebraicGeometry.Scheme.Modules.res (AlgebraicGeometry.Scheme.Modules.dualSheaf M) h hf.dualFrame) := by
    unfold IsFrame.dualSec
    rw [Frame.dualUnit_eq_sectionEquiv, res_sectionEquiv]
    rfl
  have key : ∀ r : Γ(X, W'), r • AlgebraicGeometry.Scheme.Modules.res
      (AlgebraicGeometry.Scheme.Modules.dual M) h hf.dualSec =
      MiyaokaMori.ModuleDualSectionEquiv.sectionEquiv M W'
        (r • AlgebraicGeometry.Scheme.Modules.res (AlgebraicGeometry.Scheme.Modules.dualSheaf M) h hf.dualFrame) := by
    intro r
    refine (congrArg (fun z : Γ(AlgebraicGeometry.Scheme.Modules.dual M, W') => r • z) h1).trans ?_
    exact ((MiyaokaMori.ModuleDualSectionEquiv.sectionEquiv M W').map_smul r _).symm
  have hfun : (fun r : Γ(X, W') => r • AlgebraicGeometry.Scheme.Modules.res
      (AlgebraicGeometry.Scheme.Modules.dual M) h hf.dualSec) =
      (MiyaokaMori.ModuleDualSectionEquiv.sectionEquiv M W') ∘
        (fun r : Γ(X, W') => r • AlgebraicGeometry.Scheme.Modules.res
          (AlgebraicGeometry.Scheme.Modules.dualSheaf M) h hf.dualFrame) := funext key
  rw [hfun]
  exact (MiyaokaMori.ModuleDualSectionEquiv.sectionEquiv M W').bijective.comp hd

end AlgebraicGeometry.Scheme.Modules

end
