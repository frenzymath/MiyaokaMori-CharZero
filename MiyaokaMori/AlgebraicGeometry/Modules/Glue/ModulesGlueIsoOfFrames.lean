import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Glue.ModulesGlueIso
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.Frame
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModuleChartPullback

/-! # Gluing isomorphisms of sheaves of modules along an open cover, via frames

The gluing condition is expressed through **frames** (Stacks 01CR combined with 04TN):

Given an open cover `U i`, isomorphisms `φ i : M|_{U i} ≅ N|_{U i}` on the pieces, and families
of global sections `s i ∈ Γ(M, ⊤)`, `t i ∈ Γ(N, ⊤)` such that `s i` is a frame of `M` on `U i` and
each `φ i` sends every `s j|_{U i}` to `t j|_{U i}`, there is a global isomorphism `e : M ≅ N` with
`e(s j) = t j` for all `j`.

Used for the pullback of the twisting sheaf along the projectivization morphism
(`projectivizationMorphism_pullback_twist`): `U ℓ = V_ℓ`, `M = φ^*O(1)`, `s ℓ = φ^*x_ℓ` (a frame
on `V_ℓ`), `N = M`, `t j = P_j`.

Proof (the gluing lemma is `AlgebraicGeometry.Scheme.Modules.glueIso`):
1. For `V ≤ U i`, the section map of `φ i` on `V` sends `s j|_V` to `t j|_V` (definition of the
   section map, naturality of `φ i`, transitivity of restriction).
2. Compatibility: on `V ≤ U i ⊓ U j` both section maps are `Γ(X, V)`-linear and `s i|_V` is a
   frame, so every section is a multiple of it; by 1 both maps send `s i|_V` to `t i|_V`, hence
   they agree.
3. `glueIso` gives `e` with `e.app V = ` the section map of `φ i` for `V ≤ U i`; `e(s j)` and `t j`
   agree on every `U i` (by 1), hence globally by the sheaf property of `N`
   (`TopCat.Sheaf.eq_of_locally_eq'`).

Also here: `IsFrame.of_restrictIso_eq_one` — if `M|_W ≅ O_W` sends `s|_W` to `1`, then `s` is a
frame on `W` (an explicit version of `Trivialization.exists_isFrame`).

**Kernel performance.** When these lemmas are instantiated with concrete sheaves, two terms the
kernel has to compare must be literally identical below the projection heads `restrict`
(an abbrev), `Functor.obj`, `Iso.hom`, etc. — even a single β-reduction makes the kernel unfold
the whole pushforward/pullback module, costing 5–50 s per occurrence. Therefore this file also
provides versions spelled with `restrictedGlobalSection` (`…'`), and
`exists_iso_of_local_frames_ulift`, where the index type `ι'` is lifted to `ULift ι'` and the
family of opens is passed as a **partially applied** `U' : ι' → X.Opens`, so that after
instantiation the expected type `M.restrict (U' i.down).ι` of `φ` is literally the type of the
concrete isomorphism (no `(fun i => …) i` remains).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false

variable {X : Scheme.{u}}

/-- The preimage `e⁻¹(1)` under a trivialization `e : M|_W ≅ O_W` is a frame of `M` on `W.ι ''ᵁ ⊤`
(an explicit version of `Trivialization.exists_isFrame`, with the same proof). -/
theorem isFrame_restrictIso_inv_one {M : X.Modules} {W : X.Opens}
    (e : M.restrict W.ι ≅ SheafOfModules.unit W.toScheme.ringCatSheaf) :
    IsFrame M (W.ι ''ᵁ ⊤)
      (e.inv.val.app (op ⊤) (1 : Γ(W.toScheme, ⊤)) : Γ(M, W.ι ''ᵁ ⊤)) := by
  intro W' h
  obtain ⟨O, rfl⟩ : ∃ O : W.toScheme.Opens, W' = W.ι ''ᵁ O :=
    ⟨W.ι ⁻¹ᵁ W', by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
      exact (inf_eq_right.mpr (h.trans (by simp))).symm⟩
  have hnat : (M.presheaf.map (homOfLE h).op
        (e.inv.val.app (op ⊤) (1 : Γ(W.toScheme, ⊤)) : Γ(M, W.ι ''ᵁ ⊤)) : Γ(M, W.ι ''ᵁ O)) =
      e.inv.val.app (op O) (1 : Γ(W.toScheme, O)) := by
    have := PresheafOfModules.naturality_apply e.inv.val (homOfLE (le_top : O ≤ ⊤)).op
      (1 : Γ(W.toScheme, ⊤))
    have h1 : (ConcreteCategory.hom ((SheafOfModules.unit W.toScheme.ringCatSheaf).val.map
        (homOfLE (le_top : O ≤ ⊤)).op)) (1 : Γ(W.toScheme, ⊤)) = (1 : Γ(W.toScheme, O)) :=
      map_one (W.toScheme.presheaf.map (homOfLE (le_top : O ≤ ⊤)).op).hom
    exact this.symm.trans (congrArg _ h1)
  have key : ∀ r : Γ(X, W.ι ''ᵁ O),
      r • (M.presheaf.map (homOfLE h).op
        (e.inv.val.app (op ⊤) (1 : Γ(W.toScheme, ⊤)) : Γ(M, W.ι ''ᵁ ⊤)) : Γ(M, W.ι ''ᵁ O)) =
      e.inv.val.app (op O) (show Γ(W.toScheme, O) from r) := by
    intro r
    rw [hnat]
    have := (e.inv.val.app (op O)).hom.map_smul (show Γ(W.toScheme, O) from r)
      (1 : Γ(W.toScheme, O))
    have h2 : (show Γ(W.toScheme, O) from r) • (1 : Γ(W.toScheme, O)) =
        (show Γ(W.toScheme, O) from r) := mul_one _
    refine Eq.trans ?_ (this.symm.trans (congrArg _ h2))
    have hs : ∀ y : Γ(M.restrict W.ι, O), (show Γ(W.toScheme, O) from r) • y =
        (((W.ι.appIso O).inv (show Γ(W.toScheme, O) from r) : Γ(X, W.ι ''ᵁ O)) •
          (show Γ(M, W.ι ''ᵁ O) from y) : Γ(M, W.ι ''ᵁ O)) := fun _ => rfl
    have hr : ((W.ι.appIso O).inv (show Γ(W.toScheme, O) from r) : Γ(X, W.ι ''ᵁ O)) = r := by
      rw [Scheme.Opens.ι_appIso]; rfl
    refine Eq.trans ?_ (hs _).symm
    rw [hr]
  have hbij : Function.Bijective (e.inv.val.app (op O)) := by
    refine Function.bijective_iff_has_inverse.mpr ⟨e.hom.val.app (op O), fun x => ?_, fun x => ?_⟩
    · exact ConcreteCategory.congr_hom
        (congrArg (fun k : SheafOfModules.unit W.toScheme.ringCatSheaf ⟶ _ => k.val.app (op O))
          e.inv_hom_id) x
    · exact ConcreteCategory.congr_hom
        (congrArg (fun k : M.restrict W.ι ⟶ _ => k.val.app (op O)) e.hom_inv_id) x
  show Function.Bijective
    (fun r : Γ(X, W.ι ''ᵁ O) => r • (M.presheaf.map (homOfLE h).op _ : Γ(M, W.ι ''ᵁ O)))
  rw [funext key]
  exact hbij

/-- `W.ι ''ᵁ ⊤ = W`: if `s|_{W.ι ''ᵁ ⊤}` is a frame then `s` is a frame on `W`. -/
theorem IsFrame.of_image_top {M : X.Modules} {W : X.Opens} {s : Γ(M, W)}
    (hf : IsFrame M (W.ι ''ᵁ ⊤) (M.res (image_ι_le W ⊤) s)) : IsFrame M W s := by
  intro W' h
  have h' : W' ≤ W.ι ''ᵁ ⊤ := h.trans_eq W.ι_image_top.symm
  have := hf W' h'
  simpa only [res_res] using this

/-- **A trivialization sending `s` to `1` makes `s` a frame**: if `e : M|_W ≅ O_W` satisfies
`e(s|_W) = 1`, then `s` is a frame on `W`. -/
theorem IsFrame.of_restrictIso_eq_one {M : X.Modules} {W : X.Opens}
    (e : M.restrict W.ι ≅ SheafOfModules.unit W.toScheme.ringCatSheaf) (s : Γ(M, W))
    (hs : e.hom.val.app (op ⊤)
      (show Γ(M.restrict W.ι, ⊤) from M.res (image_ι_le W ⊤) s) = (1 : Γ(W.toScheme, ⊤))) :
    IsFrame M W s := by
  have hinv : (e.inv.val.app (op ⊤) (1 : Γ(W.toScheme, ⊤)) : Γ(M, W.ι ''ᵁ ⊤)) =
      M.res (image_ι_le W ⊤) s := by
    rw [← hs]
    exact ConcreteCategory.congr_hom
      (congrArg (fun k : M.restrict W.ι ⟶ _ => k.val.app (op ⊤)) e.hom_inv_id) _
  have h1 := isFrame_restrictIso_inv_one e
  rw [hinv] at h1
  exact IsFrame.of_image_top h1

/-- The section map induced on `V ≤ W` by a morphism `ψ : M|_W ⟶ N|_W` of restricted sheaves,
applied to the restriction of a global section: apply on `⊤` first, then restrict. -/
theorem sectionMapOfRestrictHom_res_top {M N : X.Modules} {W : X.Opens}
    (ψ : M.restrict W.ι ⟶ N.restrict W.ι) (V : X.Opens) (hV : V ≤ W) (x : Γ(M, ⊤)) :
    sectionMapOfRestrictHom ψ V hV (M.res le_top x) =
      N.res (hV.trans_eq W.ι_image_top.symm)
        (show Γ(N, W.ι ''ᵁ ⊤) from ψ.val.app (op ⊤)
          (show Γ(M.restrict W.ι, ⊤) from M.res le_top x)) := by
  have h2 : V ≤ W.ι ''ᵁ W.ι ⁻¹ᵁ V := by
    rw [AlgebraicGeometry.Scheme.Hom.image_preimage_eq_opensRange_inf,
      AlgebraicGeometry.Scheme.Opens.opensRange_ι]
    exact le_inf hV le_rfl
  have hle : W.ι ''ᵁ W.ι ⁻¹ᵁ V ≤ W.ι ''ᵁ ⊤ :=
    leOfHom (W.ι.opensFunctor.map (homOfLE (le_top : W.ι ⁻¹ᵁ V ≤ ⊤)))
  have h := PresheafOfModules.naturality_apply ψ.val
    (homOfLE (le_top : W.ι ⁻¹ᵁ V ≤ ⊤)).op
    (show Γ(M.restrict W.ι, ⊤) from M.res le_top x)
  have hM : ((M.restrict W.ι).val.map (homOfLE (le_top : W.ι ⁻¹ᵁ V ≤ ⊤)).op
        (show Γ(M.restrict W.ι, ⊤) from M.res le_top x) : Γ(M, W.ι ''ᵁ W.ι ⁻¹ᵁ V)) =
      M.res (W.ι.image_preimage_le V) (M.res le_top x) := by
    change M.res hle (M.res le_top x) = _
    rw [res_res, res_res]
  have hN : ((N.restrict W.ι).val.map (homOfLE (le_top : W.ι ⁻¹ᵁ V ≤ ⊤)).op
        (ψ.val.app (op ⊤) (show Γ(M.restrict W.ι, ⊤) from M.res le_top x)) :
          Γ(N, W.ι ''ᵁ W.ι ⁻¹ᵁ V)) =
      N.res hle (show Γ(N, W.ι ''ᵁ ⊤) from ψ.val.app (op ⊤)
        (show Γ(M.restrict W.ι, ⊤) from M.res le_top x)) := rfl
  have hnat : (ψ.val.app (op (W.ι ⁻¹ᵁ V))
        (show Γ(M.restrict W.ι, W.ι ⁻¹ᵁ V) from
          M.res (W.ι.image_preimage_le V) (M.res le_top x)) : Γ(N, W.ι ''ᵁ W.ι ⁻¹ᵁ V)) =
      N.res hle (show Γ(N, W.ι ''ᵁ ⊤) from ψ.val.app (op ⊤)
        (show Γ(M.restrict W.ι, ⊤) from M.res le_top x)) :=
    (congrArg (fun y : Γ(M.restrict W.ι, W.ι ⁻¹ᵁ V) => ψ.val.app (op (W.ι ⁻¹ᵁ V)) y) hM).symm.trans
      (h.trans hN)
  change N.res h2 (ψ.val.app (op (W.ι ⁻¹ᵁ V))
    (show Γ(M.restrict W.ι, W.ι ⁻¹ᵁ V) from
      M.res (W.ι.image_preimage_le V) (M.res le_top x))) = _
  rw [hnat, res_res]

/-- **Gluing an isomorphism of sheaves of modules along an open cover via frames** (see the module
docstring). -/
theorem exists_iso_of_local_frames {ι : Type u} (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤)
    {M N : X.Modules} (φ : ∀ i, M.restrict (U i).ι ≅ N.restrict (U i).ι)
    (s : ι → Γ(M, ⊤)) (t : ι → Γ(N, ⊤))
    (hs : ∀ i, IsFrame M (U i) (M.res le_top (s i)))
    (hφ : ∀ i j, (φ i).hom.val.app (op ⊤)
        (show Γ(M.restrict (U i).ι, ⊤) from M.res le_top (s j)) =
      (show Γ(N.restrict (U i).ι, ⊤) from N.res le_top (t j))) :
    ∃ e : M ≅ N, ∀ j, e.hom.app ⊤ (s j) = t j := by
  -- Step 1: the section maps send `s j|_V` to `t j|_V`
  have step1 : ∀ i j (V : X.Opens) (hV : V ≤ U i),
      sectionMapOfRestrictHom (φ i).hom V hV (M.res le_top (s j)) = N.res le_top (t j) := by
    intro i j V hV
    rw [sectionMapOfRestrictHom_res_top, hφ i j, res_res]
  -- Step 2: compatibility
  have hcompat : ∀ i j (V : X.Opens) (hi : V ≤ U i) (hj : V ≤ U j),
      restrictSectionMap (φ i).hom V hi = restrictSectionMap (φ j).hom V hj := by
    intro i j V hi hj
    ext x
    have hfr : IsFrame M V (M.res (hi.trans le_top) (s i)) := by
      have := (hs i).restrict hi
      rwa [res_res] at this
    have hx : x = hfr.coord le_rfl x • M.res (hi.trans le_top) (s i) := by
      have := hfr.coord_smul_frame le_rfl x
      rw [res_self] at this
      exact this.symm
    change sectionMapOfRestrictHom (φ i).hom V hi x = sectionMapOfRestrictHom (φ j).hom V hj x
    rw [hx, sectionMapOfRestrictHom_smul, sectionMapOfRestrictHom_smul, step1, step1]
  -- Step 3: glue
  obtain ⟨e, he⟩ := glueIso U hU M N φ hcompat
  refine ⟨e, fun j => ?_⟩
  -- Step 4: check `e(s j) = t j` locally
  refine TopCat.Sheaf.eq_of_locally_eq' ⟨N.presheaf, N.isSheaf⟩ U ⊤ (fun i => homOfLE le_top)
    (by rw [hU]) _ _ fun i => ?_
  have hnat := PresheafOfModules.naturality_apply e.hom.val (homOfLE (le_top : U i ≤ ⊤)).op (s j)
  change N.res le_top (e.hom.app ⊤ (s j)) = N.res le_top (t j)
  have h1 : N.res le_top (e.hom.app ⊤ (s j)) = e.hom.app (U i) (M.res le_top (s j)) := by
    exact hnat.symm
  rw [h1, he i (U i) le_rfl]
  exact step1 i j (U i) le_rfl

open AlgebraicGeometry.Scheme.Modules.HomogeneousTupleTwistPullback in
/-- `IsFrame.of_restrictIso_eq_one` spelled with `restrictedGlobalSection`: if `e` sends the
restriction of a global section `t` to `1`, then `t|_U` is a frame. -/
theorem IsFrame.of_restrictIso_eq_one' {P : X.Modules} {U : X.Opens}
    (e : P.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) (t : Γ(P, ⊤))
    (h : e.hom.app ⊤ (restrictedGlobalSection P U t) = (1 : Γ(U.toScheme, ⊤))) :
    IsFrame P U (P.res le_top t) := by
  refine IsFrame.of_restrictIso_eq_one e (P.res le_top t) ?_
  have h' : e.hom.val.app (op ⊤) (show Γ(P.restrict U.ι, ⊤) from P.res le_top t) =
      (1 : Γ(U.toScheme, ⊤)) := h
  simpa only [res_res] using h'

open AlgebraicGeometry.Scheme.Modules.HomogeneousTupleTwistPullback in
/-- A pulled-back frame followed by the inverse of a frame on the source side:
`(e₁ ≪≫ hf.restrictIso.symm)(t|) = q|` provided `e₁(t|) = r` (via `topIso`) and `r • p = q|`. -/
theorem twistIsoOn_coordinate {P M : X.Modules} {U : X.Opens}
    (e₁ : P.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf)
    {p : Γ(M, U)} (hf : IsFrame M U p) (t : Γ(P, ⊤)) (r : Γ(X, U)) (q : Γ(M, ⊤))
    (h₁ : e₁.hom.app ⊤ (restrictedGlobalSection P U t) = U.topIso.inv.hom r)
    (h₂ : r • p = M.res le_top q) :
    (e₁ ≪≫ hf.restrictIso.symm).hom.app ⊤ (restrictedGlobalSection P U t) =
      restrictedGlobalSection M U q := by
  change hf.restrictIso.inv.val.app (op ⊤) (e₁.hom.app ⊤ (restrictedGlobalSection P U t)) = _
  rw [h₁, hf.restrictIso_inv_app]
  have hr : ((U.ι.appIso ⊤).inv (U.topIso.inv.hom r) : Γ(X, U.ι ''ᵁ ⊤)) =
      X.presheaf.map (homOfLE (image_ι_le U ⊤)).op r := by
    rw [AlgebraicGeometry.Scheme.Opens.ι_appIso]
    change U.topIso.inv.hom r = _
    rw [AlgebraicGeometry.Scheme.Opens.topIso_inv]
    congr 1
  rw [hr]
  change X.presheaf.map (homOfLE (image_ι_le U ⊤)).op r • M.res (image_ι_le U ⊤) p =
    M.res le_top q
  rw [← res_smul, h₂, res_res]

open AlgebraicGeometry.Scheme.Modules.HomogeneousTupleTwistPullback in
/-- `exists_iso_of_local_frames` spelled with `restrictedGlobalSection`. -/
theorem exists_iso_of_local_frames' {ι : Type u} (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤)
    {M N : X.Modules} (φ : ∀ i, M.restrict (U i).ι ≅ N.restrict (U i).ι)
    (s : ι → Γ(M, ⊤)) (t : ι → Γ(N, ⊤))
    (hs : ∀ i, IsFrame M (U i) (M.res le_top (s i)))
    (hφ : ∀ i j, (φ i).hom.app ⊤ (restrictedGlobalSection M (U i) (s j)) =
      restrictedGlobalSection N (U i) (t j)) :
    ∃ e : M ≅ N, ∀ j, e.hom.app ⊤ (s j) = t j :=
  exists_iso_of_local_frames U hU φ s t hs (fun i j => hφ i j)

open AlgebraicGeometry.Scheme.Modules.HomogeneousTupleTwistPullback in
/-- `exists_iso_of_local_frames'` with the cover indexed by `ULift ι'` and the family of opens
passed as a partially applied `U'` (see the module docstring on kernel performance). -/
theorem exists_iso_of_local_frames_ulift {ι' : Type} (U' : ι' → X.Opens)
    (hU : ⨆ i : ULift.{u} ι', U' i.down = ⊤)
    {M N : X.Modules} (φ : ∀ i : ULift.{u} ι', M.restrict (U' i.down).ι ≅ N.restrict (U' i.down).ι)
    (s : ι' → Γ(M, ⊤)) (t : ι' → Γ(N, ⊤))
    (hs : ∀ i, IsFrame M (U' i) (M.res le_top (s i)))
    (hφ : ∀ (i : ULift.{u} ι') (j : ι'),
      (φ i).hom.app ⊤ (restrictedGlobalSection M (U' i.down) (s j)) =
        restrictedGlobalSection N (U' i.down) (t j)) :
    ∃ e : M ≅ N, ∀ j, e.hom.app ⊤ (s j) = t j := by
  obtain ⟨e, he⟩ := exists_iso_of_local_frames' (fun i : ULift.{u} ι' => U' i.down) hU φ
    (fun i => s i.down) (fun i => t i.down) (fun i => hs i.down) (fun i j => hφ i j.down)
  exact ⟨e, fun j => he (ULift.up j)⟩

end AlgebraicGeometry.Scheme.Modules

end
