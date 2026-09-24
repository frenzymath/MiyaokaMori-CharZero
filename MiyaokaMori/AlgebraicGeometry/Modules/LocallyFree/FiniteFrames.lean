import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.DualFreeSheafFree
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.LocalTrivializationPullback
import MiyaokaMori.AlgebraicGeometry.Modules.FiniteTypeRestrictFreeIndexFinite
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.DualRestrictOpen
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.ModuleSheafFrame

/-! # Finite local frames of a module sheaf

A *frame* of `M : X.Modules` on an open `U`, indexed by a finite type `I`, is a family
`e : I → Γ(M, U)` such that for every open `W ≤ U` the map
`(I → Γ(X, W)) → Γ(M, W)`, `r ↦ ∑ᵢ rᵢ • eᵢ|_W`, is bijective (`IsFrameOn`).
This is the section-level form of "`M|_U ≅ O_U^{(I)}` with basis `e`": we prove that
`IsFrameOn M e` is equivalent to `frameHom e : O_U^{(I)} ⟶ M|_U` being an isomorphism, and that a
locally free sheaf of finite type has a frame around every point
(from `exists_pullback_iso_free_of_isLocallyFree` and `finite_index_of_restrict_iso_free`).

Source: Stacks 01C6 (locally free of finite rank). All proofs are section-level bookkeeping.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
open AlgebraicGeometry

noncomputable section

namespace MiyaokaMori.DualPullback

open AlgebraicGeometry.Scheme.Modules (res res_res res_self res_smul)

variable {X : Scheme.{u}}

/- `res` and its lemmas `res_res`, `res_self`, `res_smul` are those of `AlgebraicGeometry.Scheme.Modules`
   (the abbreviation of `M.presheaf.map (homOfLE h).op`, `ModuleSheafFrame`), opened above; `res_add`
   and `res_sum` below are lemmas about that `res`. -/

/-- Restriction of a section of the structure sheaf along `W ≤ U`. -/
abbrev resO {W U : X.Opens} (h : W ≤ U) : Γ(X, U) → Γ(X, W) :=
  X.presheaf.map (homOfLE h).op

lemma resO_resO {W' W U : X.Opens} (h' : W' ≤ W) (h : W ≤ U) (r : Γ(X, U)) :
    resO h' (resO h r) = resO (h'.trans h) r := by
  change (X.presheaf.map (homOfLE h).op ≫ X.presheaf.map (homOfLE h').op) r = _
  rw [← X.presheaf.map_comp]
  rfl

lemma resO_self {U : X.Opens} (h : U ≤ U) (r : Γ(X, U)) : resO h r = r := by
  change X.presheaf.map (𝟙 (op U)) r = r
  rw [X.presheaf.map_id]
  rfl

lemma res_add (M : X.Modules) {W U : X.Opens} (h : W ≤ U) (s t : Γ(M, U)) :
    res M h (s + t) = res M h s + res M h t := map_add _ s t

lemma res_sum (M : X.Modules) {W U : X.Opens} (h : W ≤ U) {ι : Type*} (s : Finset ι)
    (f : ι → Γ(M, U)) : res M h (∑ i ∈ s, f i) = ∑ i ∈ s, res M h (f i) := map_sum _ _ _

section HomOfLin

/-- A morphism of `X.Modules` from a family of linear maps on sections compatible with
restriction. (Built through `PresheafOfModules.homMk`, which avoids elaboration problems with
the module instances on sections of sheafified or pushed-forward sheaves.) -/
def homOfLin {M N : X.Modules} (L : ∀ W : X.Opens, Γ(M, W) →ₗ[Γ(X, W)] Γ(N, W))
    (hL : ∀ {W' W : X.Opens} (h : W' ≤ W) (s : Γ(M, W)), L W' (res M h s) = res N h (L W s)) :
    M ⟶ N :=
  ⟨PresheafOfModules.homMk
    { app := fun W => AddCommGrpCat.ofHom (L W.unop).toAddMonoidHom
      naturality := fun {W W'} i => by
        ext s
        change L W'.unop (M.presheaf.map i s) = N.presheaf.map i (L W.unop s)
        exact hL (leOfHom i.unop) s }
    (fun W r m => (L W.unop).map_smul r m)⟩

lemma homOfLin_app {M N : X.Modules} (L : ∀ W : X.Opens, Γ(M, W) →ₗ[Γ(X, W)] Γ(N, W))
    (hL : ∀ {W' W : X.Opens} (h : W' ≤ W) (s : Γ(M, W)), L W' (res M h s) = res N h (L W s))
    (W : X.Opens) (s : Γ(M, W)) : (homOfLin L hL).app W s = L W s := rfl

end HomOfLin

section Frame

variable (M : X.Modules) {U : X.Opens} {I : Type u} [Fintype I]

/-- `r ↦ ∑ᵢ rᵢ • eᵢ|_W` as a linear map. -/
def frameMap (e : I → Γ(M, U)) {W : X.Opens} (hW : W ≤ U) :
    (I → Γ(X, W)) →ₗ[Γ(X, W)] Γ(M, W) :=
  ∑ i : I, (LinearMap.proj i).smulRight (res M hW (e i))

lemma frameMap_apply (e : I → Γ(M, U)) {W : X.Opens} (hW : W ≤ U) (r : I → Γ(X, W)) :
    frameMap M e hW r = ∑ i : I, r i • res M hW (e i) := by
  simp [frameMap]

/-- `e` is a frame of `M` on `U`: on every open `W ≤ U` the sections of `M` are uniquely
`∑ᵢ rᵢ • eᵢ|_W`. -/
def IsFrameOn (e : I → Γ(M, U)) : Prop :=
  ∀ (W : X.Opens) (hW : W ≤ U), Function.Bijective (frameMap M e hW)

variable {M}

lemma frameMap_res (e : I → Γ(M, U)) {W' W : X.Opens} (hW : W ≤ U) (h' : W' ≤ W)
    (r : I → Γ(X, W)) :
    res M h' (frameMap M e hW r) =
      frameMap M e (h'.trans hW) (fun i => resO h' (r i)) := by
  rw [frameMap_apply, frameMap_apply, res_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [res_smul, res_res]

open Classical in
lemma frameMap_single (e : I → Γ(M, U)) {W : X.Opens} (hW : W ≤ U) (i : I) :
    frameMap M e hW (Pi.single i 1) = res M hW (e i) := by
  rw [frameMap_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [hj]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-- The linear equivalence given by a frame on `W ≤ U`. -/
def frameEquiv {e : I → Γ(M, U)} (he : IsFrameOn M e) {W : X.Opens} (hW : W ≤ U) :
    (I → Γ(X, W)) ≃ₗ[Γ(X, W)] Γ(M, W) :=
  LinearEquiv.ofBijective (frameMap M e hW) (he W hW)

/-- The coordinates of a section with respect to a frame. -/
def coords {e : I → Γ(M, U)} (he : IsFrameOn M e) {W : X.Opens} (hW : W ≤ U) (s : Γ(M, W)) :
    I → Γ(X, W) :=
  (frameEquiv he hW).symm s

lemma frameEquiv_apply {e : I → Γ(M, U)} (he : IsFrameOn M e) {W : X.Opens} (hW : W ≤ U)
    (r : I → Γ(X, W)) : frameEquiv he hW r = frameMap M e hW r := rfl

lemma frameMap_coords {e : I → Γ(M, U)} (he : IsFrameOn M e) {W : X.Opens} (hW : W ≤ U)
    (s : Γ(M, W)) : frameMap M e hW (coords he hW s) = s :=
  (frameEquiv he hW).apply_symm_apply s

lemma coords_frameMap {e : I → Γ(M, U)} (he : IsFrameOn M e) {W : X.Opens} (hW : W ≤ U)
    (r : I → Γ(X, W)) : coords he hW (frameMap M e hW r) = r :=
  (frameEquiv he hW).symm_apply_apply r

lemma coords_sum_smul {e : I → Γ(M, U)} (he : IsFrameOn M e) {W : X.Opens} (hW : W ≤ U)
    (r : I → Γ(X, W)) : coords he hW (∑ i : I, r i • res M hW (e i)) = r := by
  rw [← frameMap_apply, coords_frameMap]

lemma section_eq_sum_coords {e : I → Γ(M, U)} (he : IsFrameOn M e) {W : X.Opens} (hW : W ≤ U)
    (s : Γ(M, W)) : s = ∑ i : I, coords he hW s i • res M hW (e i) := by
  rw [← frameMap_apply, frameMap_coords]

lemma coords_res {e : I → Γ(M, U)} (he : IsFrameOn M e) {W' W : X.Opens} (hW : W ≤ U)
    (h' : W' ≤ W) (s : Γ(M, W)) (i : I) :
    coords he (h'.trans hW) (res M h' s) i =
      resO h' (coords he hW s i) := by
  conv_lhs => rw [← frameMap_coords he hW s, frameMap_res, coords_frameMap]

lemma coords_smul {e : I → Γ(M, U)} (he : IsFrameOn M e) {W : X.Opens} (hW : W ≤ U)
    (r : Γ(X, W)) (s : Γ(M, W)) : coords he hW (r • s) = r • coords he hW s :=
  (frameEquiv he hW).symm.map_smul r s

lemma coords_add {e : I → Γ(M, U)} (he : IsFrameOn M e) {W : X.Opens} (hW : W ≤ U)
    (s t : Γ(M, W)) : coords he hW (s + t) = coords he hW s + coords he hW t :=
  (frameEquiv he hW).symm.map_add s t

open Classical in
lemma coords_res_frame {e : I → Γ(M, U)} (he : IsFrameOn M e) {W : X.Opens} (hW : W ≤ U)
    (i : I) : coords he hW (res M hW (e i)) = Pi.single i 1 := by
  rw [← frameMap_single, coords_frameMap]

/-- Coordinate `i` as a linear map. -/
def coordsLin {e : I → Γ(M, U)} (he : IsFrameOn M e) {W : X.Opens} (hW : W ≤ U) (i : I) :
    Γ(M, W) →ₗ[Γ(X, W)] Γ(X, W) :=
  (LinearMap.proj i).comp (frameEquiv he hW).symm.toLinearMap

lemma coordsLin_apply {e : I → Γ(M, U)} (he : IsFrameOn M e) {W : X.Opens} (hW : W ≤ U) (i : I)
    (s : Γ(M, W)) : coordsLin he hW i s = coords he hW s i := rfl

end Frame

section FrameHom

variable (M : X.Modules) (U : X.Opens) {I : Type u} [Fintype I]

omit [Fintype I] in
/-- The `i`-th frame vector as a global section of `M|_U`. -/
def frameSection (e : I → Γ(M, U)) (i : I) : (M.restrict U.ι).sections :=
  PresheafOfModules.sectionsMk (fun W => (res M (U.ι_image_le W.unop) (e i) : Γ(M, U.ι ''ᵁ W.unop)))
    (by
      intro W W' g
      change (M.presheaf.map (homOfLE (U.ι_image_le W.unop)).op ≫
        M.presheaf.map (U.ι.opensFunctor.map g.unop).op) (e i) =
        M.presheaf.map (homOfLE (U.ι_image_le W'.unop)).op (e i)
      rw [← M.presheaf.map_comp]
      rfl)

omit [Fintype I] in
lemma frameSection_val (e : I → Γ(M, U)) (i : I) (W : U.toScheme.Opens) :
    (frameSection M U e i).val (op W) = res M (U.ι_image_le W) (e i) := rfl

/-- The morphism `O_U^{(I)} ⟶ M|_U` determined by the frame vectors. -/
def frameHom (e : I → Γ(M, U)) :
    MiyaokaMori.FreeStalk.freeM U.toScheme I ⟶ M.restrict U.ι :=
  (M.restrict U.ι).freeHomEquiv.symm (frameSection M U e)

omit [Fintype I] in
lemma freeHomEquiv_frameHom (e : I → Γ(M, U)) :
    (M.restrict U.ι).freeHomEquiv (frameHom M U e) = frameSection M U e :=
  (M.restrict U.ι).freeHomEquiv.apply_symm_apply _

omit [Fintype I] in
lemma frameHom_app_e (e : I → Γ(M, U)) (W : U.toScheme.Opens) (i : I) :
    (frameHom M U e).app W (MiyaokaMori.FreeStalk.e I i W) =
      (res M (U.ι_image_le W) (e i) : Γ(M, U.ι ''ᵁ W)) := by
  have h := congrArg (fun s : (M.restrict U.ι).sections => s.val (op W))
    (congrFun (freeHomEquiv_frameHom M U e) i)
  exact h

open MiyaokaMori.DualFreeScratch in
lemma frameHom_app (e : I → Γ(M, U)) (W : U.toScheme.Opens)
    (s : Γ(MiyaokaMori.FreeStalk.freeM U.toScheme I, W)) :
    (frameHom M U e).app W s =
      (∑ i : I, (show Γ(X, U.ι ''ᵁ W) from coord (X := U.toScheme) i s) •
        res M (U.ι_image_le W) (e i) : Γ(M, U.ι ''ᵁ W)) := by
  conv_lhs => rw [section_decomp' W s]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Scheme.Modules.Hom.app_smul, frameHom_app_e]
  exact MiyaokaMori.DualRestrictScratch.openRestrict_smul X U M W _ _

open MiyaokaMori.DualFreeScratch in
/-- `frameHom e` evaluated on `W` is `frameMap` composed with the coordinate bijection of the
free sheaf. -/
lemma frameHom_app_eq (e : I → Γ(M, U)) (W : U.toScheme.Opens)
    (s : Γ(MiyaokaMori.FreeStalk.freeM U.toScheme I, W)) :
    (frameHom M U e).app W s =
      (frameMap M e (U.ι_image_le W)
        (fun i => show Γ(X, U.ι ''ᵁ W) from coord (X := U.toScheme) i s) : Γ(M, U.ι ''ᵁ W)) := by
  rw [frameHom_app, frameMap_apply]

open MiyaokaMori.DualFreeScratch in
/-- The coordinate map of the free sheaf on `W` is bijective. -/
lemma coord_bijective (W : U.toScheme.Opens) :
    Function.Bijective (fun s : Γ(MiyaokaMori.FreeStalk.freeM U.toScheme I, W) =>
      fun i : I => coord (X := U.toScheme) i s) := by
  constructor
  · intro s t hst
    rw [section_decomp' W s, section_decomp' W t]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hi : coord (X := U.toScheme) i s = coord (X := U.toScheme) i t := congrFun hst i
    rw [hi]
  · intro a
    refine ⟨∑ i : I, a i • MiyaokaMori.FreeStalk.e I i W, ?_⟩
    funext i
    exact coord_sum_smul_e W a i

open MiyaokaMori.DualFreeScratch in
lemma frameHom_app_comp (e : I → Γ(M, U)) (W : U.toScheme.Opens) :
    (frameMap M e (U.ι_image_le W)) ∘
        (fun s : Γ(MiyaokaMori.FreeStalk.freeM U.toScheme I, W) =>
          fun i : I => show Γ(X, U.ι ''ᵁ W) from coord (X := U.toScheme) i s) =
      fun s => ((frameHom M U e).app W s : Γ(M, U.ι ''ᵁ W)) := by
  funext s
  exact (frameHom_app_eq M U e W s).symm

lemma isFrameOn_of_isIso_frameHom (e : I → Γ(M, U)) [IsIso (frameHom M U e)] :
    IsFrameOn M e := by
  intro W hW
  obtain ⟨W', rfl⟩ : ∃ W' : U.toScheme.Opens, U.ι ''ᵁ W' = W :=
    ⟨U.ι ⁻¹ᵁ W, by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
      exact inf_eq_right.mpr hW⟩
  have h1 : Function.Bijective (fun s : Γ(MiyaokaMori.FreeStalk.freeM U.toScheme I, W') =>
      ((frameHom M U e).app W' s : Γ(M, U.ι ''ᵁ W'))) :=
    (ConcreteCategory.isIso_iff_bijective _).mp inferInstance
  rw [← frameHom_app_comp M U e W'] at h1
  exact (Function.Bijective.of_comp_iff (frameMap M e _) (coord_bijective U W')).mp h1

lemma isIso_frameHom_of_isFrameOn (e : I → Γ(M, U)) (he : IsFrameOn M e) :
    IsIso (frameHom M U e) := by
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro W
  rw [ConcreteCategory.isIso_iff_bijective]
  have h1 : Function.Bijective (fun s : Γ(MiyaokaMori.FreeStalk.freeM U.toScheme I, W) =>
      ((frameHom M U e).app W s : Γ(M, U.ι ''ᵁ W))) := by
    rw [← frameHom_app_comp M U e W]
    exact (he _ _).comp (coord_bijective U W)
  exact h1

/-- A locally free sheaf of finite type has a finite frame around every point. -/
theorem exists_frame (M : X.Modules) [M.IsLocallyFree] [M.IsFiniteType] (x : X) :
    ∃ (U : X.Opens) (I : Type u) (_ : Fintype I) (e : I → Γ(M, U)), x ∈ U ∧ IsFrameOn M e := by
  obtain ⟨U, I, hxU, ⟨g⟩⟩ := Scheme.Modules.exists_pullback_iso_free_of_isLocallyFree M x
  have : Finite I := Scheme.Modules.finite_index_of_restrict_iso_free M U I g x hxU
  let _ : Fintype I := Fintype.ofFinite I
  let g' : MiyaokaMori.FreeStalk.freeM U.toScheme I ≅ M.restrict U.ι :=
    g.symm ≪≫ ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app M).symm
  let s : I → (M.restrict U.ι).sections := (M.restrict U.ι).freeHomEquiv g'.hom
  let e : I → Γ(M, U) := fun i =>
    res M (le_of_eq U.ι_image_top.symm) ((s i).val (op ⊤) : Γ(M, U.ι ''ᵁ ⊤))
  refine ⟨U, I, inferInstance, e, hxU, ?_⟩
  have hfr : frameHom M U e = g'.hom := by
    apply (M.restrict U.ι).freeHomEquiv.injective
    rw [freeHomEquiv_frameHom]
    funext i
    apply PresheafOfModules.sections_ext
    rintro ⟨W⟩
    rw [frameSection_val]
    have h1 := res_res M (U.ι_image_le W) (le_of_eq U.ι_image_top.symm) ((s i).val (op ⊤))
    refine h1.trans ?_
    have := PresheafOfModules.sections_property (s i)
      ((homOfLE (le_top : W ≤ ⊤)).op : op (⊤ : U.toScheme.Opens) ⟶ op W)
    rw [← this]
    rfl
  have : IsIso (frameHom M U e) := by rw [hfr]; infer_instance
  exact isFrameOn_of_isIso_frameHom M U e

end FrameHom

end MiyaokaMori.DualPullback

end
