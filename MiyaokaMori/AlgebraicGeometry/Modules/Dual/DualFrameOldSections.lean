import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.Bridge
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.DualSheaf

/-! # Sections of the sheafified dual over a frame open

**Sections of the (sheafified) dual `Modules.dual M` over a frame open are multiples of the dual frame.**
If `e` is a frame of `M` on `W` (`IsFrame M W e`) and `φ ∈ Γ(W, M^∨)` (the old dual `Modules.dual M =
moduleSheafDual M`), then `φ = a • e^∨` for the scalar `a = φ(e) ∈ Γ(W, O_X)`, where `e^∨ ∈ Γ(W, M^∨)` is the dual
frame `IsFrame.dualFrame` (`DualSheaf`, a section of the non-sheafified `dualSheaf M`) transported
along the bridge `dualSheafSectionsEquivOld` (`Divisors.Effective.Bridge`).

This is a step in the computation of the nonvanishing locus of coordinate power sections
(`splitCoordGen`, §2 of the paper), separated out because those coordinates take sections of the
sheafified dual.

Proof: `IsFrame.eq_smul_dualFrame` gives `ψ = ψ(e) • e^∨` for `ψ ∈ Γ(W, dualSheaf M)`; apply it to
`ψ := equiv⁻¹ φ` and push through the `Γ(W, O_X)`-linear equivalence `equiv` (`map_smul`).
Edge cases: `W = ⊥` (everything is `0`), fine.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- The dual frame `e^∨` as a section of the old (sheafified) dual `Modules.dual M`. -/
def IsFrame.dualFrameOld {M : X.Modules} {W : X.Opens} {e : Γ(M, W)} (hf : IsFrame M W e) :
    Γ(AlgebraicGeometry.Scheme.Modules.dual M, W) :=
  MiyaokaMori.Found.CartierBridge.dualSheafSectionsEquivOld M W hf.dualFrame

/-- `φ = φ(e) • e^∨` for every `φ ∈ Γ(W, M^∨)` (old dual) on a frame open `W`. -/
theorem IsFrame.exists_eq_smul_dualFrameOld {M : X.Modules} {W : X.Opens} {e : Γ(M, W)}
    (hf : IsFrame M W e) (φ : Γ(AlgebraicGeometry.Scheme.Modules.dual M, W)) :
    ∃ a : Γ(X, W), φ = a • hf.dualFrameOld := by
  set ψ : Γ(dualSheaf M, W) := (MiyaokaMori.Found.CartierBridge.dualSheafSectionsEquivOld M W).symm φ with hψ
  have h := hf.eq_smul_dualFrame le_rfl ψ
  rw [res_self, res_self] at h
  refine ⟨dualPair ψ le_rfl e, ?_⟩
  unfold IsFrame.dualFrameOld
  rw [← LinearEquiv.map_smul, h, hψ, LinearEquiv.apply_symm_apply]

end AlgebraicGeometry.Scheme.Modules

end
