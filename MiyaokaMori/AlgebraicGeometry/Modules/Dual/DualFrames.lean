import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.FiniteFrames
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModulesDual
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModuleDualSectionEquiv

/-! # Dual frames

Let `e : I → Γ(M, U)` be a finite frame of `M` on `U` (`IsFrameOn`, helper 1). A compatible family
of local functionals `φ ∈ LocalDualSections X M W` (`W ≤ U`) is determined by its values
`dualCoord e φ i := φ_W(eᵢ|_W)` on the frame vectors, and every tuple `a : I → Γ(X, W)` arises
(`ofCoords`): `dualCoordLinearEquiv : LocalDualSections X M W ≃ₗ (I → Γ(X, W))`.
The functionals `eᵢ^∨` with `dualCoord eᵢ^∨ = δᵢ` form the *dual frame*; transported through
`sectionEquiv : LocalDualSections X M U ≃ₗ Γ(M^∨, U)` (`ModuleDualSectionEquiv`) they form a
frame of `M^∨ = moduleSheafDual M` on `U` (`isFrameOn_dual`). This is the section-level content of
"the dual of a free module of rank `r` is free of rank `r` with the dual basis"
(Stacks 01CM).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

noncomputable section

namespace MiyaokaMori.DualPullback

-- `res`/`res_res`/`res_self`/`res_smul` are the `Scheme.Modules` ones.
open AlgebraicGeometry.Scheme.Modules (res res_res res_self res_smul)

variable {X : Scheme.{u}} {M : X.Modules}

section Eval

variable {W : X.Opens}

/-- A compatible family of functionals is compatible with restricting a section from `W` to
`V.left`. -/
lemma apply_res (φ : LocalDualSections X M W) (V : Over W) (s : Γ(M, W)) :
    φ.1 V (res M (leOfHom V.hom) s) = resO (leOfHom V.hom) (φ.1 (Over.mk (𝟙 W)) s) :=
  φ.2 V (Over.mk (𝟙 W)) (Over.homMk V.hom (by simp)) s

lemma smul_apply_top (r : Γ(X, W)) (φ : LocalDualSections X M W) (s : Γ(M, W)) :
    (show Γ(X, W) from (r • φ).1 (Over.mk (𝟙 W)) s) =
      r * (show Γ(X, W) from φ.1 (Over.mk (𝟙 W)) s) := by
  change X.presheaf.map (𝟙 (op W)) r * (show Γ(X, W) from φ.1 (Over.mk (𝟙 W)) s) = _
  rw [X.presheaf.map_id]
  rfl

lemma add_apply' (φ ψ : LocalDualSections X M W) (V : Over W) (s : Γ(M, V.left)) :
    (φ + ψ).1 V s = φ.1 V s + ψ.1 V s := rfl

lemma smul_apply' (r : Γ(X, W)) (φ : LocalDualSections X M W) (V : Over W) (s : Γ(M, V.left)) :
    (r • φ).1 V s = resO (leOfHom V.hom) r * φ.1 V s := rfl

lemma sum_apply' {ι : Type*} (t : Finset ι) (φ : ι → LocalDualSections X M W) (V : Over W)
    (s : Γ(M, V.left)) : (∑ j ∈ t, φ j).1 V s = ∑ j ∈ t, (φ j).1 V s := by
  classical
  induction t using Finset.induction_on with
  | empty => rfl
  | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, add_apply', ih]

lemma localDualRestrict_apply' {W' : X.Opens} (k : W' ⟶ W) (φ : LocalDualSections X M W)
    (V : Over W') (s : Γ(M, V.left)) :
    (localDualRestrict M k φ).1 V s = φ.1 ((Over.map k).obj V) s := rfl

end Eval

section DualCoord

variable {U : X.Opens} {I : Type u}

/-- The coordinates of a compatible family of functionals with respect to a frame:
`dualCoord e φ i = φ_W(eᵢ|_W)`. -/
def dualCoord (e : I → Γ(M, U)) {W : X.Opens} (hW : W ≤ U) (φ : LocalDualSections X M W) (i : I) :
    Γ(X, W) :=
  φ.1 (Over.mk (𝟙 W)) (res M hW (e i))

lemma dualCoord_add (e : I → Γ(M, U)) {W : X.Opens} (hW : W ≤ U) (φ ψ : LocalDualSections X M W) :
    dualCoord e hW (φ + ψ) = dualCoord e hW φ + dualCoord e hW ψ := rfl

lemma dualCoord_smul (e : I → Γ(M, U)) {W : X.Opens} (hW : W ≤ U) (r : Γ(X, W))
    (φ : LocalDualSections X M W) : dualCoord e hW (r • φ) = r • dualCoord e hW φ := by
  funext i
  exact smul_apply_top r φ (res M hW (e i))

lemma dualCoord_sum (e : I → Γ(M, U)) {W : X.Opens} (hW : W ≤ U) {ι : Type*} (t : Finset ι)
    (φ : ι → LocalDualSections X M W) :
    dualCoord e hW (∑ j ∈ t, φ j) = ∑ j ∈ t, dualCoord e hW (φ j) := by
  funext i
  simp only [dualCoord, Finset.sum_apply]
  exact sum_apply' t φ _ _

/-- Coordinates commute with restriction. -/
lemma dualCoord_restrict (e : I → Γ(M, U)) {W' W : X.Opens} (hW : W ≤ U) (h' : W' ≤ W)
    (φ : LocalDualSections X M W) (i : I) :
    dualCoord e (h'.trans hW) (localDualRestrict M (homOfLE h') φ) i =
      resO h' (dualCoord e hW φ i) := by
  unfold dualCoord
  rw [localDualRestrict_apply', ← res_res M h' hW]
  exact apply_res φ ((Over.map (homOfLE h')).obj (Over.mk (𝟙 W'))) (res M hW (e i))

variable [Fintype I] {e : I → Γ(M, U)} (he : IsFrameOn M e)
include he

/-- Evaluation formula: `φ_V(s) = ∑ᵢ (dualCoord φ)ᵢ|_V · (coords s)ᵢ`. -/
lemma apply_eq_sum_dualCoord {W : X.Opens} (hW : W ≤ U) (φ : LocalDualSections X M W)
    (V : Over W) (s : Γ(M, V.left)) :
    φ.1 V s = ∑ i : I, resO (leOfHom V.hom) (dualCoord e hW φ i) *
      coords he ((leOfHom V.hom).trans hW) s i := by
  conv_lhs => rw [section_eq_sum_coords he ((leOfHom V.hom).trans hW) s]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.map_smul, smul_eq_mul, mul_comm]
  congr 1
  unfold dualCoord
  rw [← apply_res φ V (res M hW (e i)), res_res]

lemma ext_of_dualCoord {W : X.Opens} (hW : W ≤ U) {φ ψ : LocalDualSections X M W}
    (h : dualCoord e hW φ = dualCoord e hW ψ) : φ = ψ := by
  apply Subtype.ext
  funext V
  apply LinearMap.ext
  intro s
  rw [apply_eq_sum_dualCoord he hW φ V s, apply_eq_sum_dualCoord he hW ψ V s, h]

/-- The compatible family of functionals with prescribed coordinates `a`, on `V ∈ Over W`. -/
def ofCoordsFun {W : X.Opens} (hW : W ≤ U) (a : I → Γ(X, W)) (V : Over W) :
    LocalFunctional X M W V :=
  ∑ i : I, resO (leOfHom V.hom) (a i) • coordsLin he ((leOfHom V.hom).trans hW) i

lemma ofCoordsFun_apply {W : X.Opens} (hW : W ≤ U) (a : I → Γ(X, W)) (V : Over W)
    (s : Γ(M, V.left)) :
    ofCoordsFun he hW a V s =
      ∑ i : I, resO (leOfHom V.hom) (a i) * coords he ((leOfHom V.hom).trans hW) s i := by
  simp [ofCoordsFun, coordsLin_apply]

lemma ofCoordsFun_mem {W : X.Opens} (hW : W ≤ U) (a : I → Γ(X, W)) :
    ofCoordsFun he hW a ∈ localDualSubmodule X M W := by
  intro V V' j x
  rw [ofCoordsFun_apply, ofCoordsFun_apply, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul]
  have hV : V.hom = j.left ≫ V'.hom := (Over.w j).symm
  congr 1
  · change resO (leOfHom V.hom) (a i) = resO (leOfHom j.left) (resO (leOfHom V'.hom) (a i))
    rw [resO_resO]
  · change coords he _ (res M (leOfHom j.left) x) i = resO (leOfHom j.left) (coords he _ x i)
    rw [coords_res he ((leOfHom V'.hom).trans hW) (leOfHom j.left) x i]

/-- The compatible family of functionals with prescribed coordinates. -/
def ofCoords {W : X.Opens} (hW : W ≤ U) (a : I → Γ(X, W)) : LocalDualSections X M W :=
  ⟨ofCoordsFun he hW a, ofCoordsFun_mem he hW a⟩

lemma ofCoords_apply {W : X.Opens} (hW : W ≤ U) (a : I → Γ(X, W)) (V : Over W)
    (s : Γ(M, V.left)) :
    (ofCoords he hW a).1 V s =
      ∑ i : I, resO (leOfHom V.hom) (a i) * coords he ((leOfHom V.hom).trans hW) s i :=
  ofCoordsFun_apply he hW a V s

open Classical in
lemma coords_res_frame_apply {W : X.Opens} (hW : W ≤ U) (i j : I) :
    coords he hW (res M hW (e i)) j = if j = i then 1 else 0 := by
  rw [coords_res_frame he hW i]
  by_cases h : j = i
  · subst h; simp
  · simp [h]

lemma dualCoord_ofCoords {W : X.Opens} (hW : W ≤ U) (a : I → Γ(X, W)) :
    dualCoord e hW (ofCoords he hW a) = a := by
  classical
  funext i
  unfold dualCoord
  rw [ofCoords_apply]
  have h : ∀ j, resO (leOfHom (Over.mk (𝟙 W)).hom) (a j) *
      coords he ((leOfHom (Over.mk (𝟙 W)).hom).trans hW) (res M hW (e i)) j =
      if j = i then a i else 0 := by
    intro j
    rw [coords_res_frame_apply he]
    by_cases hj : j = i
    · subst hj
      simp only [if_true, mul_one]
      exact resO_self _ _
    · simp [hj]
  rw [Finset.sum_congr rfl fun j _ => h j]
  simp

/-- The coordinate bijection for compatible families of functionals. -/
def dualCoordLinearEquiv {W : X.Opens} (hW : W ≤ U) :
    LocalDualSections X M W ≃ₗ[Γ(X, W)] (I → Γ(X, W)) where
  toFun := dualCoord e hW
  invFun := ofCoords he hW
  left_inv _ := ext_of_dualCoord he hW (dualCoord_ofCoords he hW _)
  right_inv a := dualCoord_ofCoords he hW a
  map_add' φ ψ := dualCoord_add e hW φ ψ
  map_smul' r φ := dualCoord_smul e hW r φ

lemma dualCoordLinearEquiv_apply {W : X.Opens} (hW : W ≤ U) (φ : LocalDualSections X M W) :
    dualCoordLinearEquiv he hW φ = dualCoord e hW φ := rfl

lemma dualCoordLinearEquiv_symm_apply {W : X.Opens} (hW : W ≤ U) (a : I → Γ(X, W)) :
    (dualCoordLinearEquiv he hW).symm a = ofCoords he hW a := rfl

open Classical in
/-- The dual frame `eᵢ^∨ ∈ LocalDualSections X M U`: the functionals with `eᵢ^∨(eⱼ) = δᵢⱼ`. -/
def dualFrame (i : I) : LocalDualSections X M U :=
  ofCoords he le_rfl (fun j => if j = i then 1 else 0)

open Classical in
lemma dualCoord_dualFrame (i j : I) :
    dualCoord e le_rfl (dualFrame he i) j = if j = i then 1 else 0 := by
  unfold dualFrame
  rw [dualCoord_ofCoords]

open Classical in
lemma dualCoord_restrict_dualFrame {W : X.Opens} (hW : W ≤ U) (i j : I) :
    dualCoord e hW (localDualRestrict M (homOfLE hW) (dualFrame he i)) j =
      if j = i then 1 else 0 := by
  have h := dualCoord_restrict e le_rfl hW (dualFrame he i) j
  rw [dualCoord_dualFrame] at h
  refine h.trans ?_
  by_cases hj : j = i
  · simp [hj]
  · simp [hj]

/-- The dual frame vectors as sections of the dual sheaf `M^∨ = moduleSheafDual M`. -/
def dualFrameSec (i : I) : Γ(moduleSheafDual M, U) :=
  MiyaokaMori.ModuleDualSectionEquiv.sectionEquiv M U (dualFrame he i)

lemma res_dualFrameSec {W : X.Opens} (hW : W ≤ U) (i : I) :
    res (moduleSheafDual M) hW (dualFrameSec he i) =
      MiyaokaMori.ModuleDualSectionEquiv.sectionEquiv M W
        (localDualRestrict M (homOfLE hW) (dualFrame he i)) :=
  MiyaokaMori.ModuleDualSectionEquiv.sectionEquiv_restrict M (homOfLE hW) (dualFrame he i)

/-- `frameMap` for the dual frame, computed through `sectionEquiv` and the coordinate equivalence. -/
lemma frameMap_dualFrameSec {W : X.Opens} (hW : W ≤ U) (a : I → Γ(X, W)) :
    frameMap (moduleSheafDual M) (dualFrameSec he) hW a =
      MiyaokaMori.ModuleDualSectionEquiv.sectionEquiv M W
        ((dualCoordLinearEquiv he hW).symm a) := by
  classical
  rw [frameMap_apply]
  have h1 : ∀ i, a i • res (moduleSheafDual M) hW (dualFrameSec he i) =
      MiyaokaMori.ModuleDualSectionEquiv.sectionEquiv M W
        (a i • localDualRestrict M (homOfLE hW) (dualFrame he i)) := by
    intro i
    rw [res_dualFrameSec, LinearEquiv.map_smul]
  rw [Finset.sum_congr rfl fun i _ => h1 i, ← map_sum]
  congr 1
  apply (dualCoordLinearEquiv he hW).injective
  rw [LinearEquiv.apply_symm_apply, dualCoordLinearEquiv_apply, dualCoord_sum]
  funext j
  simp only [Finset.sum_apply, dualCoord_smul, Pi.smul_apply, dualCoord_restrict_dualFrame,
    smul_eq_mul]
  simp

/-- The dual frame is a frame of `M^∨` on `U`. -/
theorem isFrameOn_dual : IsFrameOn (moduleSheafDual M) (dualFrameSec he) := by
  intro W hW
  have h : (frameMap (moduleSheafDual M) (dualFrameSec he) hW : (I → Γ(X, W)) → _) =
      (MiyaokaMori.ModuleDualSectionEquiv.sectionEquiv M W) ∘ (dualCoordLinearEquiv he hW).symm := by
    funext a
    exact frameMap_dualFrameSec he hW a
  rw [h]
  exact (MiyaokaMori.ModuleDualSectionEquiv.sectionEquiv M W).bijective.comp
    (dualCoordLinearEquiv he hW).symm.bijective

/-- Coordinates of a section of `M^∨` with respect to the dual frame, computed on the underlying
compatible family: `dualCoord (dualFrameSec) (sectionEquiv φ) = dualCoord e φ` (on `W ≤ U`), i.e.
evaluating the section of `M^∨^∨`... more precisely the frame coordinates of `sectionEquiv φ`
w.r.t. `e^∨` are the `e`-dual-coordinates of `φ`. -/
lemma coords_dual_sectionEquiv {W : X.Opens} (hW : W ≤ U) (φ : LocalDualSections X M W) :
    coords (isFrameOn_dual he) hW (MiyaokaMori.ModuleDualSectionEquiv.sectionEquiv M W φ) =
      dualCoord e hW φ := by
  have h := frameMap_dualFrameSec he hW (dualCoord e hW φ)
  rw [← dualCoordLinearEquiv_apply he hW, LinearEquiv.symm_apply_apply] at h
  rw [← h, coords_frameMap (isFrameOn_dual he) hW]
  rfl

end DualCoord

end MiyaokaMori.DualPullback

end
