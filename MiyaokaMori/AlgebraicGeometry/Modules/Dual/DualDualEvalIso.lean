import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.DualFrames
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModuleLocalIso

/-! # The evaluation map `M ⟶ M^∨^∨` is an isomorphism

`evHom M : M ⟶ M^∨^∨` sends a section `s ∈ Γ(M, W)` to the compatible family of functionals
`ψ ↦ ψ(s|_V)` on `Γ(M^∨, V)`, `V ⊆ W` (through `sectionEquiv`, which identifies sections of the
sheafified dual with compatible families of local functionals). If `M` is locally free of finite
type, `evHom M` is an isomorphism: invertibility is local (`moduleHom_isIso_of_locally_isIso`),
and on an open `U` with a finite frame `e` of `M` the map is, in the coordinates given by `e` on `M`
and by the double dual frame `e^∨^∨` on `M^∨^∨`, the identity (`coords_evHom_app`).

Source: Stacks 01CM (a finite locally free module is reflexive); used for the conormal sheaf
`I/I² = E^∨|_U` in §2.1 of the paper.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules MiyaokaMori.ModuleDualSectionEquiv

noncomputable section

namespace MiyaokaMori.DualPullback

-- `res`/`res_res`/`res_self`/`res_smul` are the `Scheme.Modules` ones.
open AlgebraicGeometry.Scheme.Modules (res res_res res_self res_smul)

variable {X : Scheme.{u}} (M : X.Modules)

/-- `sectionEquiv⁻¹` commutes with restriction. -/
lemma sectionEquiv_symm_res {W' W : X.Opens} (h : W' ≤ W) (ψ : Γ(moduleSheafDual M, W)) :
    (sectionEquiv M W').symm (res (moduleSheafDual M) h ψ) =
      localDualRestrict M (homOfLE h) ((sectionEquiv M W).symm ψ) := by
  have := sectionEquiv_restrict M (homOfLE h) ((sectionEquiv M W).symm ψ)
  rw [LinearEquiv.apply_symm_apply] at this
  change (sectionEquiv M W').symm (res (moduleSheafDual M) h ψ) = _
  rw [show res (moduleSheafDual M) h ψ = _ from this, LinearEquiv.symm_apply_apply]

/-- Evaluation at a fixed section, as a linear map on compatible families of functionals. -/
def evalTopLin (W : X.Opens) (t : Γ(M, W)) : LocalDualSections X M W →ₗ[Γ(X, W)] Γ(X, W) where
  toFun φ := φ.1 (Over.mk (𝟙 W)) t
  map_add' _ _ := rfl
  map_smul' r φ := smul_apply_top r φ t

lemma evalTopLin_apply (W : X.Opens) (t : Γ(M, W)) (φ : LocalDualSections X M W) :
    evalTopLin M W t φ = φ.1 (Over.mk (𝟙 W)) t := rfl

/-- The functional `ψ ↦ ψ(s|_V)` on `Γ(M^∨, V)`. -/
def evFun {W : X.Opens} (s : Γ(M, W)) (V : Over W) : LocalFunctional X (moduleSheafDual M) W V :=
  (evalTopLin M V.left (res M (leOfHom V.hom) s)).comp (sectionEquiv M V.left).symm.toLinearMap

lemma evFun_apply {W : X.Opens} (s : Γ(M, W)) (V : Over W) (ψ : Γ(moduleSheafDual M, V.left)) :
    evFun M s V ψ = ((sectionEquiv M V.left).symm ψ).1 (Over.mk (𝟙 V.left)) (res M (leOfHom V.hom) s) :=
  rfl

lemma evFun_mem {W : X.Opens} (s : Γ(M, W)) :
    evFun M s ∈ localDualSubmodule X (moduleSheafDual M) W := by
  intro V V' j ψ
  rw [evFun_apply, evFun_apply]
  change ((sectionEquiv M V.left).symm (res (moduleSheafDual M) (leOfHom j.left) ψ)).1
      (Over.mk (𝟙 V.left)) (res M (leOfHom V.hom) s) = resO (leOfHom j.left) _
  rw [sectionEquiv_symm_res, localDualRestrict_apply']
  have hV : V.hom = j.left ≫ V'.hom := (Over.w j).symm
  have h1 : res M (leOfHom V.hom) s = res M (leOfHom j.left) (res M (leOfHom V'.hom) s) := by
    rw [res_res]
  rw [h1]
  exact apply_res ((sectionEquiv M V'.left).symm ψ) ((Over.map j.left).obj (Over.mk (𝟙 V.left)))
    (res M (leOfHom V'.hom) s)

/-- The compatible family of functionals `ψ ↦ ψ(s|_V)`. -/
def evSec {W : X.Opens} (s : Γ(M, W)) : LocalDualSections X (moduleSheafDual M) W :=
  ⟨evFun M s, evFun_mem M s⟩

lemma evSec_apply {W : X.Opens} (s : Γ(M, W)) (V : Over W) (ψ : Γ(moduleSheafDual M, V.left)) :
    (evSec M s).1 V ψ =
      ((sectionEquiv M V.left).symm ψ).1 (Over.mk (𝟙 V.left)) (res M (leOfHom V.hom) s) := rfl

lemma evSec_add {W : X.Opens} (s t : Γ(M, W)) : evSec M (s + t) = evSec M s + evSec M t := by
  apply Subtype.ext
  funext V
  apply LinearMap.ext
  intro ψ
  change (evSec M (s + t)).1 V ψ = (evSec M s).1 V ψ + (evSec M t).1 V ψ
  rw [evSec_apply, evSec_apply, evSec_apply, res_add, map_add]

lemma evSec_smul {W : X.Opens} (r : Γ(X, W)) (s : Γ(M, W)) : evSec M (r • s) = r • evSec M s := by
  apply Subtype.ext
  funext V
  apply LinearMap.ext
  intro ψ
  change (evSec M (r • s)).1 V ψ = resO (leOfHom V.hom) r * (evSec M s).1 V ψ
  rw [evSec_apply, evSec_apply, res_smul, LinearMap.map_smul, smul_eq_mul]

lemma evSec_res {W' W : X.Opens} (h : W' ≤ W) (s : Γ(M, W)) :
    evSec M (res M h s) = localDualRestrict (moduleSheafDual M) (homOfLE h) (evSec M s) := by
  apply Subtype.ext
  funext V
  apply LinearMap.ext
  intro ψ
  change (evSec M (res M h s)).1 V ψ = (evSec M s).1 ((Over.map (homOfLE h)).obj V) ψ
  rw [evSec_apply, evSec_apply]
  change ((sectionEquiv M V.left).symm ψ).1 (Over.mk (𝟙 V.left)) (res M (leOfHom V.hom) (res M h s)) =
    ((sectionEquiv M V.left).symm ψ).1 (Over.mk (𝟙 V.left)) (res M (leOfHom (V.hom ≫ homOfLE h)) s)
  rw [res_res]

/-- `evSec` as a linear map. -/
def evSecLin (W : X.Opens) : Γ(M, W) →ₗ[Γ(X, W)] LocalDualSections X (moduleSheafDual M) W where
  toFun := evSec M
  map_add' := evSec_add M
  map_smul' r s := evSec_smul M r s

/-- Evaluation as a linear map `Γ(M, W) → Γ(M^∨^∨, W)`. -/
def evLin (W : X.Opens) : Γ(M, W) →ₗ[Γ(X, W)] Γ(moduleSheafDual (moduleSheafDual M), W) :=
  (sectionEquiv (moduleSheafDual M) W).toLinearMap.comp (evSecLin M W)

lemma evLin_apply (W : X.Opens) (s : Γ(M, W)) :
    evLin M W s = sectionEquiv (moduleSheafDual M) W (evSec M s) := rfl

lemma evLin_res {W' W : X.Opens} (h : W' ≤ W) (s : Γ(M, W)) :
    evLin M W' (res M h s) = res (moduleSheafDual (moduleSheafDual M)) h (evLin M W s) := by
  rw [evLin_apply, evLin_apply, evSec_res]
  exact (sectionEquiv_restrict (moduleSheafDual M) (homOfLE h) (evSec M s)).symm

/-- The evaluation morphism `M ⟶ M^∨^∨`. -/
def evHom : M ⟶ moduleSheafDual (moduleSheafDual M) :=
  homOfLin (evLin M) (fun h s => evLin_res M h s)

lemma evHom_app (W : X.Opens) (s : Γ(M, W)) :
    (evHom M).app W s = sectionEquiv (moduleSheafDual M) W (evSec M s) := rfl

section Frame

variable {M} {U : X.Opens} {I : Type u} [Fintype I] {e : I → Γ(M, U)} (he : IsFrameOn M e)
include he

/-- In the coordinates of a frame `e` and its double dual frame, `evHom` is the identity. -/
lemma coords_evHom_app {W : X.Opens} (hW : W ≤ U) (s : Γ(M, W)) :
    coords (isFrameOn_dual (isFrameOn_dual he)) hW ((evHom M).app W s) = coords he hW s := by
  classical
  rw [evHom_app, coords_dual_sectionEquiv (isFrameOn_dual he) hW]
  funext i
  unfold dualCoord
  rw [evSec_apply, res_dualFrameSec, LinearEquiv.symm_apply_apply, localDualRestrict_apply']
  unfold dualFrame
  rw [ofCoords_apply, Finset.sum_eq_single i]
  · rw [if_pos rfl]
    change X.presheaf.map _ 1 * _ = _
    rw [map_one, one_mul]
    exact congrFun (congrArg (coords he hW) (res_self M s)) i
  · intro j _ hj
    rw [if_neg hj]
    change X.presheaf.map _ 0 * _ = 0
    rw [map_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ i) h

lemma evHom_app_bijective {W : X.Opens} (hW : W ≤ U) :
    Function.Bijective ((evHom M).app W) := by
  have h1 : Function.Bijective (coords (isFrameOn_dual (isFrameOn_dual he)) hW) :=
    (frameEquiv (isFrameOn_dual (isFrameOn_dual he)) hW).symm.bijective
  have h2 : (coords (isFrameOn_dual (isFrameOn_dual he)) hW) ∘ ((evHom M).app W) = coords he hW := by
    funext s
    exact coords_evHom_app he hW s
  have h3 : Function.Bijective ((coords (isFrameOn_dual (isFrameOn_dual he)) hW) ∘
      ((evHom M).app W)) := by
    rw [h2]
    exact (frameEquiv he hW).symm.bijective
  exact (Function.Bijective.of_comp_iff' h1 _).mp h3

end Frame

/-- The evaluation map of a locally free sheaf of finite type is an isomorphism. -/
theorem evHom_isIso [M.IsLocallyFree] [M.IsFiniteType] : IsIso (evHom M) := by
  apply moduleHom_isIso_of_locally_isIso
  intro x
  obtain ⟨U, I, _, e, hxU, he⟩ := exists_frame M x
  refine ⟨U, hxU, ?_⟩
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro W
  rw [ConcreteCategory.isIso_iff_bijective]
  exact evHom_app_bijective he (U.ι_image_le W)

end MiyaokaMori.DualPullback

end
