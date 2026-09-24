import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.SectionTensor
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.Frame
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Stacks01q1_FrameChartBasicOpen

/-! # Tensor powers of a section in a local frame

Local tensor powers of a section of a line bundle, and how the global tensor power
`s^{⊗N} = tensorPowSection s N` looks in a local frame.

For `e ∈ Γ(L, W)` define `framePow e N ∈ Γ(L^{⊗N}, W)` by `framePow e 0 = 1`,
`framePow e (N+1) = framePow e N ⊗ e` (same recursion as `tensorPowSection`, which is the
case `W = ⊤`: `tensorPowSection_eq_framePow`). Then:

* `framePow_res`: `(framePow e N)|_V = framePow (e|_V) N`;
* `framePow_smul`: `framePow (u • e) N = u^N • framePow e N`;
* `res_tensorPowSection_eq_pow_smul_framePow`: if `s|_W = f • e` then
  `(s^{⊗N})|_W = f^N • framePow e N`.

These are the "`s|_{U_j} = f_j q_j`, hence `s^{⊗n}|_{U_j} = f_j^n q_j^{⊗n}`" computations of the
proof of Stacks 01PW (properties-lemma-invert-s-sections), made into reusable lemmas.

Reference: Stacks 01PW (proof).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- Tensoring a pure tensor section by a scalar in the first factor. -/
theorem moduleTensorSection_smul_left {M N : X.Modules} {U : X.Opens} (a : Γ(X, U))
    (s : Γ(M, U)) (t : Γ(N, U)) :
    AlgebraicGeometry.Scheme.Modules.moduleTensorSection (a • s) t = a • AlgebraicGeometry.Scheme.Modules.moduleTensorSection s t := by
  have h := AlgebraicGeometry.Scheme.Modules.moduleTensorSection_smul a (1 : Γ(X, U)) s t
  rwa [one_smul, mul_one] at h

/-- Tensoring a pure tensor section by a scalar in the second factor. -/
theorem moduleTensorSection_smul_right {M N : X.Modules} {U : X.Opens} (b : Γ(X, U))
    (s : Γ(M, U)) (t : Γ(N, U)) :
    AlgebraicGeometry.Scheme.Modules.moduleTensorSection s (b • t) = b • AlgebraicGeometry.Scheme.Modules.moduleTensorSection s t := by
  have h := AlgebraicGeometry.Scheme.Modules.moduleTensorSection_smul (1 : Γ(X, U)) b s t
  rwa [one_smul, one_mul] at h

/-- Pure tensor sections are additive in the first factor; in particular they respect
subtraction. -/
theorem moduleTensorSection_sub_left {M N : X.Modules} {U : X.Opens}
    (s s' : Γ(M, U)) (t : Γ(N, U)) :
    AlgebraicGeometry.Scheme.Modules.moduleTensorSection (s - s') t =
      AlgebraicGeometry.Scheme.Modules.moduleTensorSection s t - AlgebraicGeometry.Scheme.Modules.moduleTensorSection s' t := by
  have h := AlgebraicGeometry.Scheme.Modules.moduleTensorSection_add_left (s - s') s' t
  rw [sub_add_cancel] at h
  rw [h, add_sub_cancel_right]

/-- Local tensor powers of a section `e ∈ Γ(L, W)`: `framePow e 0 = 1`,
`framePow e (N+1) = framePow e N ⊗ e` (same recursion as `tensorPowSection`). -/
def framePow {L : X.Modules} {W : X.Opens} (e : Γ(L, W)) :
    (N : ℕ) → Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L N, W)
  | 0 => (1 : Γ(X, W))
  | N + 1 => AlgebraicGeometry.Scheme.Modules.moduleTensorSection (framePow e N) e

@[simp] theorem framePow_zero {L : X.Modules} {W : X.Opens} (e : Γ(L, W)) :
    framePow e 0 = (1 : Γ(X, W)) := rfl

@[simp] theorem framePow_succ {L : X.Modules} {W : X.Opens} (e : Γ(L, W)) (N : ℕ) :
    framePow e (N + 1) = AlgebraicGeometry.Scheme.Modules.moduleTensorSection (framePow e N) e := rfl

/-- The global tensor power `tensorPowSection s N` is `framePow s N` (`W = ⊤`). -/
theorem tensorPowSection_eq_framePow {L : X.Modules} (s : Γ(L, ⊤)) (N : ℕ) :
    AlgebraicGeometry.Scheme.Modules.tensorPowSection s N = framePow s N := by
  induction N with
  | zero => rfl
  | succ N ih =>
    show sectionTensor (AlgebraicGeometry.Scheme.Modules.tensorPowSection s N) s = _
    rw [ih]
    rfl

/-- Restriction of `1 ∈ Γ(L^{⊗0}, W) = Γ(𝒪_X, W)`. -/
theorem res_one_tensorPow_zero (L : X.Modules) {V W : X.Opens} (h : V ≤ W) :
    (AlgebraicGeometry.Scheme.Modules.tensorPow L 0).res h (1 : Γ(X, W)) = (1 : Γ(X, V)) := by
  change (X.presheaf.map (homOfLE h).op).hom (1 : Γ(X, W)) = 1
  exact map_one _

/-- `framePow` commutes with restriction. -/
theorem framePow_res {L : X.Modules} {V W : X.Opens} (h : V ≤ W) (e : Γ(L, W)) (N : ℕ) :
    (AlgebraicGeometry.Scheme.Modules.tensorPow L N).res h (framePow e N) =
      framePow (L.res h e) N := by
  induction N with
  | zero => exact res_one_tensorPow_zero L h
  | succ N ih =>
    rw [framePow_succ, framePow_succ]
    change (AlgebraicGeometry.Scheme.Modules.moduleTensor _ L).presheaf.map (homOfLE h).op
      (AlgebraicGeometry.Scheme.Modules.moduleTensorSection (framePow e N) e) = _
    rw [AlgebraicGeometry.Scheme.Modules.moduleTensorSection_restrict, ← ih]

/-- `framePow (u • e) N = u^N • framePow e N`. -/
theorem framePow_smul {L : X.Modules} {W : X.Opens} (u : Γ(X, W)) (e : Γ(L, W)) (N : ℕ) :
    framePow (u • e) N = u ^ N • framePow e N := by
  induction N with
  | zero =>
    show framePow e 0 = u ^ 0 • framePow e 0
    rw [pow_zero, one_smul]
  | succ N ih =>
    rw [framePow_succ, framePow_succ, ih, AlgebraicGeometry.Scheme.Modules.moduleTensorSection_smul, pow_succ]
    rfl

/-- If `s|_W = f • e` then `(s^{⊗N})|_W = f^N • framePow e N`. -/
theorem res_tensorPowSection_eq_pow_smul_framePow {L : X.Modules} {W : X.Opens} (s : Γ(L, ⊤))
    (f : Γ(X, W)) (e : Γ(L, W)) (hs : L.res le_top s = f • e) (N : ℕ) :
    (AlgebraicGeometry.Scheme.Modules.tensorPow L N).res le_top
        (AlgebraicGeometry.Scheme.Modules.tensorPowSection s N) =
      f ^ N • framePow e N := by
  rw [tensorPowSection_eq_framePow, framePow_res, hs, framePow_smul]

/-- Coordinate of `s|_W` in the frame `e`: `s|_W = coord • e`. -/
theorem IsFrame.res_top_eq_coord_smul {L : X.Modules} {W : X.Opens} {e : Γ(L, W)}
    (hf : IsFrame L W e) (s : Γ(L, ⊤)) :
    L.res le_top s = hf.coord le_rfl (L.res le_top s) • e := by
  have h := hf.coord_smul_frame le_rfl (L.res le_top s)
  rw [res_self] at h
  exact h.symm

/-- Restricting a frame to `V ≤ W`, the coordinate of `s|_V` is the restriction of the
coordinate of `s|_W`. -/
theorem IsFrame.coord_res_top {L : X.Modules} {W : X.Opens} {e : Γ(L, W)}
    (hf : IsFrame L W e) (s : Γ(L, ⊤)) {V : X.Opens} (hV : V ≤ W) :
    (hf.restrict hV).coord le_rfl (L.res le_top s) =
      X.presheaf.map (homOfLE hV).op (hf.coord le_rfl (L.res le_top s)) := by
  rw [← hf.coord_map hV le_rfl (L.res le_top s)]
  apply (hf.restrict hV).coord_unique
  rw [res_self]
  have := hf.coord_smul_frame (hV.trans le_rfl) (L.res hV (L.res le_top s))
  exact this.trans (res_res L hV le_top s)

end AlgebraicGeometry.Scheme.Modules

end
