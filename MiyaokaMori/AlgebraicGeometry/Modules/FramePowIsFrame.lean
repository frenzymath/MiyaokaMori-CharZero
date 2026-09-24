import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.TensorFrameGermCriterion
import MiyaokaMori.Paper.S3PositiveLine.Realization.ProjectivizationOfNowhereZeroTuple
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.FrameTensorPowSection
import MiyaokaMori.AlgebraicGeometry.Modules.Stacks0892_TensorPowSectionLocus
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.FrameLocus

/-! # Tensor powers of a frame are frames

**Tensor powers of a frame are frames** (used for the frame factor `η(ε^{⊗k})` in the
coordinate-power formula for sections): for a line bundle `L` with a frame `e` on `W`,
`framePow e N = e ⊗ ⋯ ⊗ e ∈ Γ(L^{⊗N}, W)` is a frame of `L^{⊗N}` on `W`.

Two general facts:
* `IsFrame.of_forall_germ_notMem` — **a section of a line bundle whose germ at every point of `W` lies outside
  `𝔪_y · M_y` is a frame on `W`** (the local-section version of `IsFrame.of_not_isZeroAt`, Stacks 01CY): near `y` write
  `s = f • e'` with `e'` a frame (`exists_frame_le`); `s_y ∉ 𝔪_y M_y` forces `f_y` to be a unit, i.e. `y ∈ X_f`
  (`mem_basicOpen`); on `X_f` the coordinate `f` is a unit (`isUnit_res_basicOpen`), so `s|_{X_f}` is a frame
  (`IsFrame.of_isUnit_coord`); frames are local (`IsFrame.of_iSup`).
* `isFrame_framePow` — by induction on `N`: `N = 0` is `isFrame_tensorPow_zero_one`; for `N + 1`, `L^{⊗(N+1)} =
  L^{⊗N} ⊗ L` is a line bundle (`IsLineBundle.tensorPow`), and the germ of `framePow e N ⊗ e` lies in `𝔪_y • ⊤` iff
  the germ of `framePow e N` does (`germ_moduleTensorSection_mem_maximalIdeal_smul_iff`, `e` a frame), which the
  induction hypothesis excludes (`IsFrame.germ_notMem_maximalIdeal_smul`).

References: Stacks 01CY, 01CB.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory Opposite TopologicalSpace

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- **A nowhere-vanishing section of a line bundle is a frame** (local-section version of `IsFrame.of_not_isZeroAt`,
Stacks 01CY): if the germ of `s ∈ Γ(M, W)` at every `y ∈ W` is not in `𝔪_y • M_y`, then `s` is a frame of `M` on `W`. -/
theorem IsFrame.of_forall_germ_notMem (M : X.Modules) [M.IsLineBundle] {W : X.Opens} (s : Γ(M, W))
    (h : ∀ (y : X) (hy : y ∈ W), M.presheaf.germ W y hy s ∉
      (IsLocalRing.maximalIdeal (X.presheaf.stalk y)) •
        (⊤ : Submodule (X.presheaf.stalk y) (M.presheaf.stalk y))) :
    IsFrame M W s := by
  -- near every `y ∈ W` there is a basic open `X_f ∋ y` on which `s` is a frame
  have key : ∀ y : X, y ∈ W → ∃ V : X.Opens, ∃ hV : V ≤ W, y ∈ V ∧ IsFrame M V (M.res hV s) := by
    intro y hy
    obtain ⟨W₁, hW₁W, hyW₁, e, he⟩ := exists_frame_le M hy
    set f : Γ(X, W₁) := he.coord le_rfl (M.res hW₁W s) with hfdef
    have hse : M.res hW₁W s = f • e := by
      have h1 := he.coord_smul_frame le_rfl (M.res hW₁W s)
      rw [res_self] at h1
      exact h1.symm
    have hgerm : M.presheaf.germ W y hy s =
        X.presheaf.germ W₁ y hyW₁ f • M.presheaf.germ W₁ y hyW₁ e := by
      rw [← TopCat.Presheaf.germ_res_apply M.presheaf (homOfLE hW₁W) y hyW₁ s]
      change M.presheaf.germ W₁ y hyW₁ (M.res hW₁W s) = _
      rw [hse, germ_smul']
    have hy' : y ∈ X.basicOpen f := by
      rw [X.mem_basicOpen f y hyW₁]
      by_contra hnu
      apply h y hy
      rw [hgerm]
      exact Submodule.smul_mem_smul ((IsLocalRing.mem_maximalIdeal _).mpr hnu) Submodule.mem_top
    have hle : X.basicOpen f ≤ W₁ := X.basicOpen_le f
    refine ⟨X.basicOpen f, hle.trans hW₁W, hy', ?_⟩
    have hfr : IsFrame M (X.basicOpen f) (M.res hle e) := he.restrict hle
    apply hfr.of_isUnit_coord
    have hc : hfr.coord le_rfl (M.res (hle.trans hW₁W) s) = X.presheaf.map (homOfLE hle).op f := by
      apply hfr.coord_unique
      rw [res_self, ← res_smul, ← hse]
      exact res_res M hle hW₁W s
    rw [hc]
    exact X.toRingedSpace.isUnit_res_basicOpen f
  choose V hVW hyV hfr using key
  refine IsFrame.of_iSup (fun y : W => V y.1 y.2) (fun y => hVW y.1 y.2) ?_ (fun y => hfr y.1 y.2)
  intro y hy
  exact Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hyV y hy⟩

/-- **Tensor powers of a frame are frames**: `framePow e N` is a frame of `L^{⊗N}` on `W` when `e` is a frame of the
line bundle `L` on `W`. -/
theorem isFrame_framePow {L : X.Modules} [L.IsLineBundle] {W : X.Opens} {e : Γ(L, W)} (he : IsFrame L W e)
    (N : ℕ) : IsFrame (AlgebraicGeometry.Scheme.Modules.tensorPow L N) W (framePow e N) := by
  induction N with
  | zero => exact isFrame_tensorPow_zero_one L W
  | succ N ih =>
    refine IsFrame.of_forall_germ_notMem (AlgebraicGeometry.Scheme.Modules.tensorPow L (N + 1))
      (framePow e (N + 1)) ?_
    intro y hy hmem
    have hmem' := (he.germ_moduleTensorSection_mem_maximalIdeal_smul_iff
      (AlgebraicGeometry.Scheme.Modules.tensorPow L N) hy (framePow e N)).mp hmem
    exact ih.germ_notMem_maximalIdeal_smul hy hmem'

end AlgebraicGeometry.Scheme.Modules

end
