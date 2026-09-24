import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleNonvanishingLocus
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.NonvanishingLocusIsoInvariant
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.NonvanishingLocusTensorSection
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.ProjectivizationChartLocalFormula
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.Bridge
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.FrameLocus
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorMonoidalIso
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorPowCanonicalIso
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorUnitIso
import MiyaokaMori.AlgebraicGeometry.Modules.Ample.Stacks0892_ExtendLocalSection

/-! # Extending a line bundle section from a basic open (pullback form)

On a quasi-compact quasi-separated scheme, a section of a line bundle over the basic open `X_u`
(written as a section of the pullback along `X_u → X`), multiplied by a high power of `u`, extends
to a global section whose nonvanishing locus is exactly the image of the nonvanishing locus of the
original section (a "nonvanishing locus" packaging of the extension result Stacks 01PW(2) / 01P7).

Reference: Stacks 01PW (`properties-lemma-invert-s-sections`, (2)); the open-set form is
`exists_section_nonvanishingLocus_inf_eq` (`Stacks0892_ExtendLocalSection`).

This file also proves:
* `nonvanishingLocus_unit_eq_basicOpen`: for `𝒪_X` viewed as a line bundle, the nonvanishing
  locus of `u` is `X.basicOpen u`;
* `nonvanishingLocus_smul`: `X_{u • σ} = X_σ ⊓ X.basicOpen u`;
* `restrict_res_eq`, `restrict_smul_res_of_le`, `isFrame_restrict_iff`: a section of `M|_W` is a
  frame iff it is a frame as a section of `M` over `W.ι ''ᵁ V` (transport of frames between the
  pullback form and the open-set form, using only `rfl`-level defeqs of `restrictFunctor`);
* `germ_notMem_maximalIdeal_smul_iff_exists_isFrame`: the germ at `y` of a section `s` over an
  open `U` is not in `𝔪_y L_y` iff `s` is a frame on some open neighbourhood of `y`
  (local-section version of `frameLocus_eq_nonvanishingLocus`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- **For the structure sheaf viewed as a line bundle, the nonvanishing locus of a global function
`u` is the basic open `X.basicOpen u`.**
Proof: `1` is a frame of `𝒪_X` on `⊤` (`isFrame_unit_one`) and the coordinate of `u` in this frame
is `u` itself, so `u_y ∈ 𝔪_y • ⊤ ⟺ u_y ∈ 𝔪_y ⟺ ¬ IsUnit u_y`
(`IsFrame.germ_mem_maximalIdeal_smul_iff_coord`), while `y ∈ X.basicOpen u ⟺ IsUnit u_y`
(`Scheme.mem_basicOpen`). -/
theorem nonvanishingLocus_unit_eq_basicOpen (u : Γ(X, ⊤)) :
    AlgebraicGeometry.Scheme.Modules.nonvanishingLocus (X := X)
      (SheafOfModules.unit X.ringCatSheaf) u = X.basicOpen u := by
  apply TopologicalSpace.Opens.ext
  ext y
  have hf := ProjectivizationChartLocalFormula.isFrame_unit_one (X := X) ⊤
  have hc : hf.coord le_rfl (res (X := X) (SheafOfModules.unit X.ringCatSheaf) le_top u) = u := by
    refine hf.coord_unique le_rfl _ _ ?_
    rw [res_self, res_self]
    change u * (1 : Γ(X, ⊤)) = u
    exact mul_one u
  have h1 := hf.germ_mem_maximalIdeal_smul_iff_coord (y := y) trivial u
  rw [hc] at h1
  refine Iff.trans (mem_nonvanishingLocus (X := X) (SheafOfModules.unit X.ringCatSheaf) u y) ?_
  refine Iff.trans (not_congr h1) ?_
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not]
  exact (X.mem_basicOpen u y trivial).symm

/-- **Nonvanishing locus of `u • σ`**: `X_{u • σ} = X_σ ⊓ X.basicOpen u`. Pointwise:
`(u • σ)_y = u_y • σ_y` (`germ_smul'`); if `u_y` is a unit then
`u_y • σ_y ∈ 𝔪_y • ⊤ ⟺ σ_y ∈ 𝔪_y • ⊤`; if `u_y ∈ 𝔪_y` then `u_y • σ_y ∈ 𝔪_y • ⊤`. -/
theorem nonvanishingLocus_smul (F : X.Modules) [F.IsLineBundle] (u : Γ(X, ⊤)) (σ : Γ(F, ⊤)) :
    F.nonvanishingLocus (u • σ) = F.nonvanishingLocus σ ⊓ X.basicOpen u := by
  apply TopologicalSpace.Opens.ext
  ext y
  rw [SetLike.mem_coe, SetLike.mem_coe, Opens.mem_inf, mem_nonvanishingLocus, mem_nonvanishingLocus,
    X.mem_basicOpen u y trivial]
  have hg : (F.presheaf.germ ⊤ y trivial (u • σ) : ↥(F.stalk y)) =
      X.presheaf.germ ⊤ y trivial u • (F.presheaf.germ ⊤ y trivial σ : ↥(F.stalk y)) :=
    germ_smul' F (V := ⊤) (y := y) trivial u σ
  rw [hg]
  constructor
  · intro h
    by_cases hu : IsUnit (X.presheaf.germ ⊤ y trivial u)
    · refine ⟨fun hσ => h ?_, hu⟩
      exact Submodule.smul_mem _ _ hσ
    · exact absurd (Submodule.smul_mem_smul (N := (⊤ : Submodule (X.presheaf.stalk y) (F.stalk y)))
        ((IsLocalRing.mem_maximalIdeal _).mpr hu) Submodule.mem_top) h
  · rintro ⟨hσ, hu⟩ h
    obtain ⟨v, hv⟩ := hu
    refine hσ ?_
    have h2 : (↑v⁻¹ : X.presheaf.stalk y) •
        (X.presheaf.germ ⊤ y trivial u • (F.presheaf.germ ⊤ y trivial σ : ↥(F.stalk y))) ∈
        (IsLocalRing.maximalIdeal (X.presheaf.stalk y)) •
          (⊤ : Submodule (X.presheaf.stalk y) (F.stalk y)) :=
      Submodule.smul_mem _ _ h
    rwa [smul_smul, ← hv, Units.inv_mul, one_smul] at h2

/-- The restriction map of `M|_W` is the restriction map of `M` along `W.ι ''ᵁ O ≤ W.ι ''ᵁ V`
(`restrict_map` is `rfl`; the two `homOfLE`s agree since the category is thin). -/
theorem restrict_res_eq (M : X.Modules) (W : X.Opens) {V O : W.toScheme.Opens} (h : O ≤ V)
    (e : Γ(M.restrict W.ι, V)) :
    ((M.restrict W.ι).res h e : Γ(M, W.ι ''ᵁ O)) =
      M.res (W.ι.image_mono h) (e : Γ(M, W.ι ''ᵁ V)) := by
  show M.presheaf.map (W.ι.opensFunctor.map (homOfLE h)).op e = _
  rw [show W.ι.opensFunctor.map (homOfLE h) = homOfLE (W.ι.image_mono h) from Subsingleton.elim _ _]

/-- For a section `e` of `M|_W` over any open `V`, restricting to `O ≤ V` and then scaling by
`r ∈ Γ(W, O) = Γ(X, W.ι ''ᵁ O)` is `r • e|` computed in `M` over `W.ι ''ᵁ O`
(generalizes `restrict_smul_res` from `V = ⊤` to arbitrary `V`). -/
theorem restrict_smul_res_of_le (M : X.Modules) (W : X.Opens) {V O : W.toScheme.Opens} (h : O ≤ V)
    (e : Γ(M.restrict W.ι, V)) (r : Γ(X, W.ι ''ᵁ O)) :
    ((show Γ(W.toScheme, O) from r) • (M.restrict W.ι).res h e : Γ(M.restrict W.ι, O)) =
      (r • M.res (W.ι.image_mono h) (e : Γ(M, W.ι ''ᵁ V)) : Γ(M, W.ι ''ᵁ O)) := by
  have hs : ∀ y : Γ(M.restrict W.ι, O), (show Γ(W.toScheme, O) from r) • y =
      (((W.ι.appIso O).inv (show Γ(W.toScheme, O) from r) : Γ(X, W.ι ''ᵁ O)) •
        (show Γ(M, W.ι ''ᵁ O) from y) : Γ(M, W.ι ''ᵁ O)) := fun _ ↦ rfl
  have hr : ((W.ι.appIso O).inv (show Γ(W.toScheme, O) from r) : Γ(X, W.ι ''ᵁ O)) = r := by
    rw [Scheme.Opens.ι_appIso]; rfl
  rw [hs, hr, restrict_res_eq]

/-- **Transport of frames along the open immersion `W.ι`**: a section `e` of `M|_W` over `V` is a
frame iff it is a frame as a section of `M` over `W.ι ''ᵁ V`.
`⇒`: every open `U'` inside `W.ι ''ᵁ V` has the form `W.ι ''ᵁ O` (`O := W.ι ⁻¹ᵁ U'`,
`image_preimage_eq_opensRange_inf`), and the two scaling maps agree verbatim by
`restrict_smul_res_of_le`. `⇐`: for `O ≤ V` use `W.ι ''ᵁ O ≤ W.ι ''ᵁ V`. -/
theorem isFrame_restrict_iff (M : X.Modules) (W : X.Opens) (V : W.toScheme.Opens)
    (e : Γ(M.restrict W.ι, V)) :
    IsFrame (M.restrict W.ι) V e ↔ IsFrame M (W.ι ''ᵁ V) (e : Γ(M, W.ι ''ᵁ V)) := by
  constructor
  · intro hR U' hU'
    obtain ⟨O, rfl⟩ : ∃ O : W.toScheme.Opens, U' = W.ι ''ᵁ O :=
      ⟨W.ι ⁻¹ᵁ U', by
        rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
        exact (inf_eq_right.mpr (hU'.trans (image_ι_le W V))).symm⟩
    have hO : O ≤ V := (Scheme.Hom.image_le_image_iff W.ι O V).mp hU'
    have hb := hR O hO
    have hfun := restrict_smul_res_of_le M W hO e
    refine ⟨fun r r' hrr ↦ hb.1 ?_, fun y ↦ ?_⟩
    · exact (hfun r).trans (Eq.trans hrr (hfun r').symm)
    · obtain ⟨r, hr⟩ := hb.2 y
      exact ⟨r, (hfun r).symm.trans hr⟩
  · intro hF O hO
    have hb := hF (W.ι ''ᵁ O) (W.ι.image_mono hO)
    have hfun := restrict_smul_res_of_le M W hO e
    refine ⟨fun r r' hrr ↦ hb.1 ?_, fun y ↦ ?_⟩
    · exact (hfun r).symm.trans (Eq.trans hrr (hfun r'))
    · obtain ⟨r, hr⟩ := hb.2 y
      exact ⟨r, (hfun r).trans hr⟩

/-- **Nonvanishing point of a local section ⟺ frame nearby** (the version of
`frameLocus_eq_nonvanishingLocus` for a section over an open `U`): for `s ∈ Γ(L, U)` and `y ∈ U`,
`s_y ∉ 𝔪_y L_y ⟺ ∃ V, y ∈ V ≤ U ∧ s|_V is a frame`.
`⇒`: take a frame `(W, e)` of `L` at `y` (`W ≤ U`) and write `s|_W = f • e`; `s_y ∉ 𝔪_y L_y`
forces `f_y` to be a unit, so `y ∈ X.basicOpen f`, where `f` is a unit (`isUnit_res_basicOpen`)
and `s` is a frame (`IsFrame.of_isUnit_coord`).
`⇐`: `IsFrame.germ_notMem_maximalIdeal_smul`. -/
theorem germ_notMem_maximalIdeal_smul_iff_exists_isFrame (L : X.Modules) [L.IsLineBundle]
    {U : X.Opens} (s : Γ(L, U)) {y : X} (hy : y ∈ U) :
    (L.presheaf.germ U y hy s : ↥(L.stalk y)) ∉
        (IsLocalRing.maximalIdeal (X.presheaf.stalk y)) •
          (⊤ : Submodule (X.presheaf.stalk y) (L.stalk y)) ↔
      ∃ (V : X.Opens) (hVU : V ≤ U), y ∈ V ∧ IsFrame L V (L.res hVU s) := by
  constructor
  · intro hx
    obtain ⟨W, hWU, hyW, e, hf⟩ := exists_frame_le L hy
    set f : Γ(X, W) := hf.coord le_rfl (L.res hWU s) with hfdef
    have hse : L.res hWU s = f • e := by
      have h := hf.coord_smul_frame le_rfl (L.res hWU s)
      rw [res_self] at h
      exact h.symm
    have hgerm : (L.presheaf.germ U y hy s : ↥(L.stalk y)) =
        X.presheaf.germ W y hyW f • (L.presheaf.germ W y hyW e : ↥(L.stalk y)) := by
      have h0 : L.presheaf.germ W y hyW (L.res hWU s) = L.presheaf.germ U y hy s :=
        TopCat.Presheaf.germ_res_apply _ _ _ _ _
      rw [← h0, hse, germ_smul']
    have hunit : IsUnit (X.presheaf.germ W y hyW f) := by
      by_contra hnu
      refine hx ?_
      rw [hgerm]
      exact Submodule.smul_mem_smul (N := (⊤ : Submodule (X.presheaf.stalk y) (L.stalk y)))
        ((IsLocalRing.mem_maximalIdeal _).mpr hnu) Submodule.mem_top
    set V : X.Opens := X.basicOpen f with hVdef
    have hVW : V ≤ W := X.basicOpen_le f
    have hyV : y ∈ V := (X.mem_basicOpen f y hyW).mpr hunit
    have hfV := hf.restrict hVW
    have hresu : IsUnit (X.presheaf.map (homOfLE hVW).op f) :=
      X.toRingedSpace.isUnit_res_basicOpen f
    have hcoord : hfV.coord le_rfl (L.res hVW (L.res hWU s)) = X.presheaf.map (homOfLE hVW).op f := by
      refine hfV.coord_unique le_rfl _ _ ?_
      rw [res_self, hse, res_smul]
    refine ⟨V, hVW.trans hWU, hyV, ?_⟩
    have h := IsFrame.of_isUnit_coord hfV (by rw [hcoord]; exact hresu)
    rwa [res_res] at h
  · rintro ⟨V, hVU, hyV, hf⟩ hmem
    refine hf.germ_notMem_maximalIdeal_smul hyV ?_
    have h0 : L.presheaf.germ V y hyV (L.res hVU s) = L.presheaf.germ U y hy s :=
      TopCat.Presheaf.germ_res_apply _ _ _ _ _
    rw [h0]
    exact hmem

end AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false in
/-- **Extension of a line bundle section from a basic open (pullback form).**

Statement: `X` quasi-compact quasi-separated, `F` a line bundle on `X`, `u ∈ Γ(X, 𝒪)`,
`W := X.basicOpen u`, `t ∈ Γ(W, F|_W)` (written as a global section of
`(Modules.pullback W.ι).obj F`). Then there is `σ ∈ Γ(X, F)` with `X_σ = W.ι ''ᵁ (W_t)`, i.e. the
nonvanishing locus of `σ` is exactly the image in `X` of the nonvanishing locus of `t` (an open of `W`).

Proof (steps of the proof body).
0. **Pullback form → restriction form.** `ψ := (restrictFunctorIsoPullback W.ι).app F : F|_W ≅ W.ι^*F`,
   `t_R := ψ⁻¹(t)`; nonvanishing loci are invariant under isomorphisms of modules
   (`nonvanishingLocus_iso`), so `(W.ι^*F)_t = (F|_W)_{t_R}`. `Γ(F|_W, ⊤) = Γ(F, W.ι ''ᵁ ⊤)` holds
   by `rfl` (`restrictAppIso = Iso.refl`); write `t' ∈ Γ(F, W.ι ''ᵁ ⊤)` for the same element.
1. **Nonvanishing locus of `𝒪_X`.** `𝒪_X = SheafOfModules.unit` is a line bundle
   (`IsLineBundle.unit`) and the nonvanishing locus of `u` is `X.basicOpen u`
   (`nonvanishingLocus_unit_eq_basicOpen`).
2. **Pointwise description of the image open (the main point).** For `y ∈ X_u`:
   `y ∈ W.ι ''ᵁ (F|_W)_{t_R}` ⟺ there is `y₀ ∈ W` with `ι y₀ = y` and `y₀ ∈ (F|_W)_{t_R}`
   ⟺ (`frameLocus_eq_nonvanishingLocus`) `t_R` is a frame of `F|_W` on a neighbourhood `V` of `y₀`
   ⟺ (`isFrame_restrict_iff`) `t'` is a frame of `F` on `W.ι ''ᵁ V`
   ⟺ (`germ_notMem_maximalIdeal_smul_iff_exists_isFrame`) `t'_y ∉ 𝔪_y F_y`.
3. **Extension in the open-set form.** `exists_section_nonvanishingLocus_inf_eq` with `N := 𝒪_X`,
   `τ := u`, `s := t'|_{X_u}`, `W' := W.ι ''ᵁ (F|_W)_{t_R}` (step 2 provides its hypothesis) gives
   `e` and `σ₀ ∈ Γ(X, F ⊗ 𝒪^{⊗e})` with `X_{σ₀} ⊓ X_u = W'`.
4. **Back to `F`.** `θ : F ⊗ 𝒪^{⊗e} ≅ F` (`tensorIsoTensorObj`, `unitTensorPowIso`,
   `tensorUnitIso`), `σ₁ := θ(σ₀)`, `X_{σ₁} = X_{σ₀}` (`nonvanishingLocus_iso`).
5. **Multiply by `u` to cut off the complement of `X_u`.** `σ := u • σ₁`,
   `X_σ = X_{σ₁} ⊓ X.basicOpen u` (`nonvanishingLocus_smul`) `= W'`. ∎

Edge cases: `X = ∅`: both sides are `⊥`. `u = 0`: `W = ⊥` and the right-hand side is `⊥`; the proof
handles this uniformly. `u` a unit: `W = ⊤`. -/
theorem AlgebraicGeometry.Scheme.Modules.exists_section_nonvanishingLocus_eq_image_basicOpen
    {X : AlgebraicGeometry.Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (F : X.Modules) [F.IsLineBundle] (u : Γ(X, ⊤))
    (t : Γ((AlgebraicGeometry.Scheme.Modules.pullback (X.basicOpen u).ι).obj F, ⊤)) :
    ∃ σ : Γ(F, ⊤), F.nonvanishingLocus σ =
      (X.basicOpen u).ι ''ᵁ
        (((AlgebraicGeometry.Scheme.Modules.pullback (X.basicOpen u).ι).obj F).nonvanishingLocus t) := by
  -- Step 0: pullback form → restriction form (along `restrictFunctorIsoPullback`; the nonvanishing
  -- locus is invariant under isomorphisms)
  let ψ : F.restrict (X.basicOpen u).ι ≅ (Modules.pullback (X.basicOpen u).ι).obj F :=
    (Modules.restrictFunctorIsoPullback (X.basicOpen u).ι).app F
  obtain ⟨tR, htRdef⟩ : ∃ tR : Γ(F.restrict (X.basicOpen u).ι, ⊤), tR = ψ.inv.app ⊤ t := ⟨_, rfl⟩
  have htR : ψ.hom.app ⊤ tR = t := by
    rw [htRdef]
    exact congrArg (fun φ : (Modules.pullback (X.basicOpen u).ι).obj F ⟶ _ => φ.app ⊤ t) ψ.inv_hom_id
  have hP : ((Modules.pullback (X.basicOpen u).ι).obj F).nonvanishingLocus t =
      (F.restrict (X.basicOpen u).ι).nonvanishingLocus tR := by
    rw [← htR]
    exact nonvanishingLocus_iso ψ tR
  -- the section in open-set form, t' ∈ Γ(F, ι ''ᵁ ⊤)
  obtain ⟨t', ht'⟩ : ∃ t' : Γ(F, (X.basicOpen u).ι ''ᵁ ⊤), t' = (tR : Γ(F, (X.basicOpen u).ι ''ᵁ ⊤)) :=
    ⟨_, rfl⟩
  -- Step 1: nonvanishing locus of the structure sheaf = basic open
  have hb : nonvanishingLocus (X := X) (SheafOfModules.unit X.ringCatSheaf) u =
      X.basicOpen u := nonvanishingLocus_unit_eq_basicOpen u
  have hle : nonvanishingLocus (X := X) (SheafOfModules.unit X.ringCatSheaf) u ≤
      (X.basicOpen u).ι ''ᵁ ⊤ := hb.le.trans (X.basicOpen u).ι_image_top.ge
  have hWU : (X.basicOpen u).ι ''ᵁ ((F.restrict (X.basicOpen u).ι).nonvanishingLocus tR) ≤
      nonvanishingLocus (X := X) (SheafOfModules.unit X.ringCatSheaf) u :=
    (image_ι_le _ _).trans hb.ge
  -- Step 2 (main point): points of the image open ⟺ the germ of t' is not in 𝔪_y F_y
  have hW : ∀ (y : X) (hy : y ∈ nonvanishingLocus (X := X) (SheafOfModules.unit X.ringCatSheaf) u),
      y ∈ (X.basicOpen u).ι ''ᵁ ((F.restrict (X.basicOpen u).ι).nonvanishingLocus tR) ↔
        F.presheaf.germ _ y hy (F.res hle t') ∉
          (IsLocalRing.maximalIdeal (X.presheaf.stalk y)) •
            (⊤ : Submodule (X.presheaf.stalk y) (F.stalk y)) := by
    intro y hy
    have hyW : y ∈ X.basicOpen u := hb.le hy
    have hg : F.presheaf.germ _ y hy (F.res hle t') =
        F.presheaf.germ ((X.basicOpen u).ι ''ᵁ ⊤) y (hle hy) t' :=
      TopCat.Presheaf.germ_res_apply _ _ _ _ _
    rw [hg, germ_notMem_maximalIdeal_smul_iff_exists_isFrame F t' (hle hy)]
    constructor
    · rintro ⟨y₀, hy₀, rfl⟩
      have hy₀' : y₀ ∈ (F.restrict (X.basicOpen u).ι).frameLocus tR := by
        rw [MiyaokaMori.Found.CartierBridge.frameLocus_eq_nonvanishingLocus]
        exact hy₀
      obtain ⟨V, hy₀V, hfr⟩ := mem_frameLocus.mp hy₀'
      refine ⟨(X.basicOpen u).ι ''ᵁ V, (X.basicOpen u).ι.image_mono le_top,
        Set.mem_image_of_mem _ hy₀V, ?_⟩
      have h := (isFrame_restrict_iff F (X.basicOpen u) V _).mp hfr
      rw [restrict_res_eq] at h
      rw [ht']
      exact h
    · rintro ⟨V', hV'U, hyV', hfr⟩
      refine ⟨⟨y, hyW⟩, ?_, rfl⟩
      show (⟨y, hyW⟩ : (X.basicOpen u).toScheme) ∈ (F.restrict (X.basicOpen u).ι).nonvanishingLocus tR
      rw [← MiyaokaMori.Found.CartierBridge.frameLocus_eq_nonvanishingLocus]
      refine mem_frameLocus.mpr ⟨(X.basicOpen u).ι ⁻¹ᵁ V', hyV', ?_⟩
      rw [isFrame_restrict_iff, restrict_res_eq]
      have h2 := hfr.restrict ((X.basicOpen u).ι.image_preimage_le V')
      rw [res_res] at h2
      rw [← ht']
      exact h2
  -- Step 3: the open-set form of Stacks 01PW(2)
  obtain ⟨e, σ₀, hσ₀⟩ := exists_section_nonvanishingLocus_inf_eq
    (SheafOfModules.unit X.ringCatSheaf) u F (F.res hle t') _ hWU hW
  rw [hb] at hσ₀
  -- Step 4: F ⊗ 𝒪^{⊗e} ≅ F
  let θ : Modules.tensor F (Modules.tensorPow (SheafOfModules.unit X.ringCatSheaf) e) ≅ F :=
    tensorIsoTensorObj F _ ≪≫
      CategoryTheory.MonoidalCategory.whiskerLeftIso F (unitTensorPowIso X e) ≪≫
      (tensorIsoTensorObj F _).symm ≪≫ tensorUnitIso F
  -- Step 5: σ := u • θ(σ₀)
  refine ⟨u • θ.hom.app ⊤ σ₀, ?_⟩
  rw [nonvanishingLocus_smul, nonvanishingLocus_iso θ σ₀, hσ₀, hP]

end
