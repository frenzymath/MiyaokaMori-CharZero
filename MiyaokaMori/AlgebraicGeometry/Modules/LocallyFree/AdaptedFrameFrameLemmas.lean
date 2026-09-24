import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.MatrixCocycle
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.FiniteFrames
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.RankAtStalkLocalIso
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundleRank

/-! # Section-level lemmas about frames

Section-level lemmas about frames `Scheme.Modules.IsFrameOn V W e` (`MatrixCocycle.lean`:
`e : Fin r → Γ(V, W)` restricts to a basis of `Γ(V, W')` for every `W' ≤ W`), used by
`AdaptedFrameUpperTriangular`:

* a frame restricts to any smaller open (`isFrameOn_restrict`);
* a frame is transported along an isomorphism of module sheaves (`isFrameOn_map_iso`);
* a `DualPullback.IsFrameOn` frame (bijective coordinate map, `DualPullbackCommute_Frame.lean`)
  reindexed by `Fin n ≃ I` is a frame in the above sense (`isFrameOn_of_dualPullback`);
* a locally free sheaf of finite type has, around every point `x`, a frame indexed by
  `Fin (rankAtStalk M x)` (`exists_frame_fin`; from `DualPullback.exists_frame`,
  `isIso_frameHom_of_isFrameOn` and `rankAtStalk_of_restrict_iso_free`);
* coordinates of a section with respect to a frame (`coords`, `sum_coords_smul`, `coords_unique`).

Source: the frames and transition matrices (2.7) of §2 of the paper; Stacks 01C6.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
open AlgebraicGeometry

noncomputable section

namespace MiyaokaMori.AdaptedFrame

variable {X : Scheme.{u}}

/-- Two restrictions compose to one (Opens is a thin category). -/
theorem map_map_res (M : X.Modules) {T W U : X.Opens} (h₁ : T ≤ W) (h₂ : W ≤ U) (s : Γ(M, U)) :
    M.presheaf.map (homOfLE h₁).op (M.presheaf.map (homOfLE h₂).op s) =
      M.presheaf.map (homOfLE (h₁.trans h₂)).op s := by
  change (M.presheaf.map (homOfLE h₂).op ≫ M.presheaf.map (homOfLE h₁).op) s = _
  rw [← M.presheaf.map_comp]
  rfl

/-- Restriction along `W ≤ W` is the identity. -/
theorem map_res_self (M : X.Modules) {W : X.Opens} (h : W ≤ W) (s : Γ(M, W)) :
    M.presheaf.map (homOfLE h).op s = s := by
  change M.presheaf.map (𝟙 (op W)) s = s
  rw [M.presheaf.map_id]
  rfl

/-- A morphism of module sheaves commutes with restriction (naturality, on elements). -/
theorem app_res {M N : X.Modules} (φ : M ⟶ N) {W U : X.Opens} (h : W ≤ U) (s : Γ(M, U)) :
    φ.app W (M.presheaf.map (homOfLE h).op s) = N.presheaf.map (homOfLE h).op (φ.app U s) :=
  ConcreteCategory.congr_hom (φ.mapPresheaf.naturality (homOfLE h).op) s

/-- A frame on `U` restricts to a frame on any `W ≤ U`. -/
theorem isFrameOn_restrict {r : ℕ} {M : X.Modules} {U : X.Opens} {e : Fin r → Γ(M, U)}
    (he : M.IsFrameOn U e) {W : X.Opens} (hW : W ≤ U) :
    M.IsFrameOn W (fun i => M.presheaf.map (homOfLE hW).op (e i)) := by
  intro W' h
  have := he W' (h.trans hW)
  simpa only [map_map_res] using this

/-- The linear map on sections induced by a morphism of module sheaves. -/
def appLinear {M N : X.Modules} (φ : M ⟶ N) (W : X.Opens) : Γ(M, W) →ₗ[Γ(X, W)] Γ(N, W) where
  toFun := (φ.app W).hom
  map_add' := (φ.app W).hom.map_add
  map_smul' := fun r a => Scheme.Modules.Hom.app_smul φ r a

@[simp] theorem appLinear_apply {M N : X.Modules} (φ : M ⟶ N) (W : X.Opens) (s : Γ(M, W)) :
    appLinear φ W s = φ.app W s := rfl

/-- A frame is transported along an isomorphism of module sheaves. -/
theorem isFrameOn_map_iso {r : ℕ} {M N : X.Modules} (φ : M ⟶ N) [IsIso φ] {U : X.Opens}
    {e : Fin r → Γ(M, U)} (he : M.IsFrameOn U e) :
    N.IsFrameOn U (fun i => φ.app U (e i)) := by
  intro W' h
  obtain ⟨hli, hsp⟩ := he W' h
  have hbij : Function.Bijective (φ.app W') := ConcreteCategory.bijective_of_isIso (φ.app W')
  have hrw : (fun i => N.presheaf.map (homOfLE h).op (φ.app U (e i))) =
      (appLinear φ W') ∘ (fun i => M.presheaf.map (homOfLE h).op (e i)) := by
    funext i
    simp only [Function.comp, appLinear_apply, app_res]
  rw [hrw]
  constructor
  · exact hli.map' _ (LinearMap.ker_eq_bot.mpr hbij.1)
  · rw [Set.range_comp, ← Submodule.map_span, hsp, Submodule.map_top, LinearMap.range_eq_top]
    exact hbij.2

/-- A frame reindexed along an equivalence `Fin n ≃ Fin r` is a frame. -/
theorem isFrameOn_reindex {r n : ℕ} {M : X.Modules} {U : X.Opens} {e : Fin r → Γ(M, U)}
    (he : M.IsFrameOn U e) (σ : Fin n ≃ Fin r) : M.IsFrameOn U (fun i => e (σ i)) := by
  intro W' h
  obtain ⟨hli, hsp⟩ := he W' h
  refine ⟨(linearIndependent_equiv σ).mpr hli, ?_⟩
  rw [← hsp]
  congr 1
  exact σ.surjective.range_comp (fun i => M.presheaf.map (homOfLE h).op (e i))

/-- A `DualPullback.IsFrameOn` frame reindexed by `Fin n ≃ I` is a frame. -/
theorem isFrameOn_of_dualPullback {M : X.Modules} {U : X.Opens} {I : Type u} [Fintype I]
    {e : I → Γ(M, U)} (he : MiyaokaMori.DualPullback.IsFrameOn M e) {n : ℕ} (σ : Fin n ≃ I) :
    M.IsFrameOn U (fun i => e (σ i)) := by
  intro W' h
  have hb := he W' h
  constructor
  · rw [Fintype.linearIndependent_iff]
    intro c hc i
    have h1 : MiyaokaMori.DualPullback.frameMap M e h (fun j => c (σ.symm j)) =
        MiyaokaMori.DualPullback.frameMap M e h 0 := by
      rw [map_zero, MiyaokaMori.DualPullback.frameMap_apply, ← hc]
      rw [← Equiv.sum_comp σ]
      simp only [Equiv.symm_apply_apply]
    have h2 := hb.1 h1
    have h3 := congrFun h2 (σ i)
    simpa using h3
  · rw [eq_top_iff]
    intro t _
    obtain ⟨c, hc⟩ := hb.2 t
    rw [Submodule.mem_span_range_iff_exists_fun]
    refine ⟨fun i => c (σ i), ?_⟩
    rw [← hc, MiyaokaMori.DualPullback.frameMap_apply, ← Equiv.sum_comp σ]

/-- A locally free sheaf of finite type has, around every point `x`, a frame indexed by
`Fin (rankAtStalk M x)`. -/
theorem exists_frame_fin (M : X.Modules) [M.IsLocallyFree] [M.IsFiniteType] (x : X) :
    ∃ (U : X.Opens) (_ : x ∈ U) (e : Fin (Scheme.Modules.rankAtStalk M x) → Γ(M, U)),
      M.IsFrameOn U e := by
  obtain ⟨U, I, _, e, hxU, he⟩ := MiyaokaMori.DualPullback.exists_frame M x
  have hiso := MiyaokaMori.DualPullback.isIso_frameHom_of_isFrameOn M U e he
  let g : (Scheme.Modules.pullback U.ι).obj M ≅
      SheafOfModules.free (R := U.toScheme.ringCatSheaf) I :=
    ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app M).symm ≪≫
      (asIso (MiyaokaMori.DualPullback.frameHom M U e)).symm
  have hrank := Scheme.Modules.rankAtStalk_of_restrict_iso_free M U I g x hxU
  have hcard : Fintype.card (Fin (Scheme.Modules.rankAtStalk M x)) = Fintype.card I := by
    rw [Fintype.card_fin, hrank]
  exact ⟨U, hxU, fun i => e (Fintype.equivOfCardEq hcard i),
    isFrameOn_of_dualPullback he (Fintype.equivOfCardEq hcard)⟩

section Coords

variable {r : ℕ} {M : X.Modules} {W : X.Opens} {e : Fin r → Γ(M, W)}

/-- The frame itself (no restriction) is linearly independent and spans. -/
theorem linearIndependent_of_isFrameOn (he : M.IsFrameOn W e) : LinearIndependent Γ(X, W) e := by
  have := (he W le_rfl).1
  simpa only [map_res_self] using this

theorem span_eq_top_of_isFrameOn (he : M.IsFrameOn W e) :
    Submodule.span Γ(X, W) (Set.range e) = ⊤ := by
  have := (he W le_rfl).2
  simpa only [map_res_self] using this

theorem exists_coords (he : M.IsFrameOn W e) (s : Γ(M, W)) :
    ∃ c : Fin r → Γ(X, W), ∑ i, c i • e i = s := by
  have hs : s ∈ Submodule.span Γ(X, W) (Set.range e) := by
    rw [span_eq_top_of_isFrameOn he]; trivial
  exact (Submodule.mem_span_range_iff_exists_fun _).mp hs

/-- Coordinates of a section with respect to a frame. -/
def coords (he : M.IsFrameOn W e) (s : Γ(M, W)) : Fin r → Γ(X, W) :=
  Classical.choose (exists_coords he s)

theorem sum_coords_smul (he : M.IsFrameOn W e) (s : Γ(M, W)) :
    ∑ i, coords he s i • e i = s :=
  Classical.choose_spec (exists_coords he s)

/-- Coordinates are unique. -/
theorem coords_unique (he : M.IsFrameOn W e) {s : Γ(M, W)} {c : Fin r → Γ(X, W)}
    (hc : ∑ i, c i • e i = s) (i : Fin r) : coords he s i = c i :=
  (Fintype.linearIndependent_iffₛ.mp (linearIndependent_of_isFrameOn he)) _ _
    ((sum_coords_smul he s).trans hc.symm) i

end Coords

end MiyaokaMori.AdaptedFrame

end
