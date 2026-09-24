import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorPowCanonicalIso
import MiyaokaMori.AlgebraicGeometry.Modules.Ample.AmpleLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.NonvanishingLocusIsoInvariant
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Ample.Stacks0c4k_IsAmplePullbackIso
import MiyaokaMori.AlgebraicGeometry.Modules.ExtendSectionAcrossBasicOpen
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.Stacks01q1

/-! # Relative ampleness is local on the base (Stacks 01VJ)

Relative ampleness is local on the base (Stacks 01VJ, (1)⇒(3)): if `f : X → S` is quasi-compact,
`N` is a line bundle on `X` and `S` has an affine open cover `{W_i}` such that every `N|_{f⁻¹W_i}` is
ample, then `N|_{f⁻¹V}` is ample for **every** affine open `V` of `S`.

References: Stacks 01VJ (`morphisms-lemma-characterize-relatively-ample`, (1)⇒(3)); Stacks 01VH
(definition). The extension step is `exists_section_nonvanishingLocus_eq_image_basicOpen`
(`Stacks0c4k_RelativelyAmpleLocal_ExtendBasicOpen`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

set_option backward.isDefEq.respectTransparency.types false in
/-- **Stacks 01VJ (1)⇒(3): relative ampleness is local on the base.**

Statement: `f : X ⟶ S` quasi-compact, `N` a line bundle on `X`, `𝒲 ⊆ S.affineOpens` a cover of `S`
(`⊤ = ⨆ i ∈ 𝒲, i`) such that `N|_{f⁻¹ i}` is ample for every `i ∈ 𝒲`. Then `N|_{f⁻¹V}` is ample for
every affine open `V` of `S`. (Here `N|_U` means `(Modules.pullback U.ι).obj N`, and `IsAmple` means:
`f⁻¹V` is quasi-compact and every point has `m > 0`, `s ∈ Γ(N^{⊗m})` with the point in the affine
`X_s`.)

Reference: Stacks 01VJ (1)⇒(3). The proof in Stacks goes through (2), "the canonical map to
`Proj_S(⊕ f_*N^{⊗d})` is an open immersion"; below is a direct argument **avoiding relative Proj**
(extension of sections in the style of Stacks 01PW/01P7, plus basic opens of affine intersections).

Proof sketch (matching the Lean proof step by step). Write `X' := f⁻¹V`, `N' := N|_{X'}`, `P := N^{⊗m}`.

**Step 0 (`X'` is quasi-compact and quasi-separated).** Quasi-compact: `f` quasi-compact and `V`
affine ⇒ `f⁻¹V` quasi-compact (`Scheme.Hom.isCompact_preimage`). Quasi-separated: each piece `f⁻¹i`
(`i ∈ 𝒲`) is a quasi-separated space since `N|_{f⁻¹i}` is ample (`IsAmple.quasiSeparatedSpace`,
Stacks 01PY); `QuasiSeparated` has the affine-target property "the source is a quasi-separated
space" (`HasAffineProperty @QuasiSeparated`) and `𝒲` is an affine open cover, so `f` is
quasi-separated (`HasAffineProperty.of_iSup_eq_top`); `V` is affine, so `X'` is a quasi-separated
space (`quasiSeparatedSpace_of_quasiSeparated (f ∣_ V)`).

**Step 1 (a common basic open).** Take `x ∈ X'` and `i ∈ 𝒲` with `f x ∈ i`. `V`, `i` are affine
opens with `f x ∈ i ⊓ V`, so `exists_basicOpen_le_affine_inter` gives `h ∈ Γ(S, i)`, `h' ∈ Γ(S, V)`
with `D := S.basicOpen h = S.basicOpen h' ∋ f x`, `D ≤ i`, `D ≤ V`.

**Step 2 (`f⁻¹D` as a basic open of `X'`, and the open immersion into `X_i := f⁻¹i`).**
`u' := (X'.ι ≫ f)^♯ h'` (restricted to `⊤`) `∈ Γ(X', 𝒪)`, `W := X'.basicOpen u' = X'.ι⁻¹(f⁻¹D)`
(`Scheme.basicOpen_res`, `Scheme.preimage_basicOpen`). `W ⊆ f⁻¹D ⊆ X_i`, so the image of
`W.ι ≫ X'.ι` lies in the image of `X_i.ι`, giving an open immersion `g : W ⟶ X_i` with
`g ≫ X_i.ι = W.ι ≫ X'.ι` (`IsOpenImmersion.lift`, `lift_fac`).

**Step 3 (ampleness data on `X_i`, pulled back to `W`).** Ampleness of `N|_{X_i}` at `x` gives
`m > 0`, `s ∈ Γ(X_i, (N|_{X_i})^{⊗m})` with `x ∈ L_s := (X_i)_s` affine. Through
`pullbackTensorPowIso`, view `s` as a section `s'` of `(pullback X_i.ι).obj P` (same nonvanishing
locus, `nonvanishingLocus_iso`); pull back along `g` to `g^*s'`, with nonvanishing locus `g⁻¹ L_s`
(`nonvanishingLocus_sectionPullbackAlong`); then through `pullbackComp`,
`pullbackCongr (g ≫ X_i.ι = W.ι ≫ X'.ι)`, `pullbackComp⁻¹` turn it into a section `t` of
`(pullback W.ι).obj ((pullback X'.ι).obj P)`, still with nonvanishing locus `g⁻¹ L_s`.

**Step 4 (extension to `X'`).** `X'` is quasi-compact and quasi-separated and
`F := (pullback X'.ι).obj P` is a line bundle, so `exists_section_nonvanishingLocus_eq_image_basicOpen`
(a nonvanishing-locus form of the extension of Stacks 01PW(2)) gives `σ ∈ Γ(X', F)` with
`X'_σ = W.ι ''ᵁ (g⁻¹ L_s)`. Through `pullbackTensorPowIso X'.ι N m` turn `σ` into a global section `σ'`
of `N'^{⊗m}` with the same nonvanishing locus. Then `(m, σ')` is the required witness at `x`:
* `x ∈ X'_{σ'}`: `x ∈ W` (`f x ∈ D`) and `g ⟨x⟩ = ⟨x⟩ ∈ L_s` (`X_i.ι` injective and
  `g ≫ X_i.ι = W.ι ≫ X'.ι`).
* `X'_{σ'}` is affine: `W.ι ''ᵁ (g⁻¹ L_s)` is affine ⟸ `g⁻¹ L_s` is affine
  (`IsAffineOpen.image_of_isOpenImmersion`) ⟸ `g ''ᵁ (g⁻¹ L_s) = g.opensRange ⊓ L_s` is affine
  (`isAffineOpen_iff_of_isOpenImmersion`, `image_preimage_eq_opensRange_inf`); and
  `g.opensRange = (X_i.ι ≫ f)⁻¹ D = X_i.basicOpen ((X_i.ι ≫ f)^♯ h)` (`opensRange_comp`,
  `preimage_image_eq`, `hW`, `D ≤ V`), so `g.opensRange ⊓ L_s` is the basic open of the function
  `(X_i.ι ≫ f)^♯ h|_{L_s}` on the affine open `L_s` (`Scheme.basicOpen_res`), hence affine
  (`IsAffineOpen.basicOpen`).

Edge cases: `S = ∅` (then `X' = ∅`, both conjuncts trivial); `𝒲 = ∅` is possible only for `S = ∅`;
`X = ∅` is trivial; neither `S` quasi-compact nor `𝒲` finite is needed (the argument is pointwise).

Note: `set_option backward.isDefEq.respectTransparency.types false` lets Mathlib's instance
`HasAffineProperty @QuasiSeparated (fun X _ _ _ ↦ QuasiSeparatedSpace X)` be synthesized (Mathlib's
own uses in `Morphisms/QuasiSeparated.lean` carry the same option; without it not even
`IsZariskiLocalAtTarget @QuasiSeparated` is found). -/
theorem AlgebraicGeometry.isAmple_pullback_preimage_of_isAmple_on_affine_cover
    {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) [AlgebraicGeometry.QuasiCompact f]
    (N : X.Modules) [N.IsLineBundle]
    (𝒲 : Set S.affineOpens) (hcov : (⊤ : S.Opens) = ⨆ i ∈ 𝒲, (i : S.Opens))
    (hN : ∀ i ∈ 𝒲,
      AlgebraicGeometry.IsAmple ((AlgebraicGeometry.Scheme.Modules.pullback (f ⁻¹ᵁ (i : S.Opens)).ι).obj N))
    (V : S.affineOpens) :
    AlgebraicGeometry.IsAmple ((AlgebraicGeometry.Scheme.Modules.pullback (f ⁻¹ᵁ V.1).ι).obj N) := by
  -- Step 0: X' := f⁻¹V is quasi-compact and quasi-separated
  have hcpt : CompactSpace (f ⁻¹ᵁ V.1) :=
    isCompact_iff_compactSpace.mp (f.isCompact_preimage V.2.isCompact)
  have hqsi : ∀ i : 𝒲, QuasiSeparatedSpace (f ⁻¹ᵁ (i.1 : S.Opens)) :=
    fun i => (hN i.1 i.2).quasiSeparatedSpace
  have hcov' : ⨆ i : 𝒲, ((i.1 : S.affineOpens) : S.Opens) = ⊤ := by
    rw [hcov, iSup_subtype]
  have hqsf : AlgebraicGeometry.QuasiSeparated f :=
    AlgebraicGeometry.HasAffineProperty.of_iSup_eq_top (P := @AlgebraicGeometry.QuasiSeparated)
      (fun i : 𝒲 => (i.1 : S.affineOpens)) hcov' hqsi
  have hVaff : AlgebraicGeometry.IsAffine (V.1 : AlgebraicGeometry.Scheme.{u}) := V.2
  have hqs : QuasiSeparatedSpace (f ⁻¹ᵁ V.1) :=
    AlgebraicGeometry.quasiSeparatedSpace_of_quasiSeparated (f ∣_ V.1)
  -- notation
  set XV : X.Opens := f ⁻¹ᵁ V.1 with hXV
  refine ⟨hcpt, fun x => ?_⟩
  -- Step 1: a common basic open D = S.basicOpen h = S.basicOpen h' ∋ f x
  have hfx : f.base x.1 ∈ (V.1 : S.Opens) := x.2
  obtain ⟨i, hi, hfxi⟩ : ∃ i ∈ 𝒲, f.base x.1 ∈ (i : S.Opens) := by
    have h0 : f.base x.1 ∈ (⊤ : S.Opens) := trivial
    rw [hcov] at h0
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp h0
    obtain ⟨hi𝒲, hmem⟩ := TopologicalSpace.Opens.mem_iSup.mp hi
    exact ⟨i, hi𝒲, hmem⟩
  obtain ⟨h, h', hD, hxD⟩ :=
    AlgebraicGeometry.exists_basicOpen_le_affine_inter i.2 V.2 (f.base x.1) ⟨hfxi, hfx⟩
  have hDi : S.basicOpen h ≤ (i : S.Opens) := S.basicOpen_le h
  have hDV : S.basicOpen h' ≤ (V.1 : S.Opens) := S.basicOpen_le h'
  set Xi : X.Opens := f ⁻¹ᵁ (i : S.Opens) with hXi
  -- Step 3 (preparation): u' ∈ Γ(X', ⊤), X'.basicOpen u' = X'.ι⁻¹(f⁻¹D)
  have hVtop : (⊤ : XV.toScheme.Opens) ≤ (XV.ι ≫ f) ⁻¹ᵁ V.1 := fun y _ => y.2
  let u' : Γ(XV.toScheme, ⊤) :=
    XV.toScheme.presheaf.map (CategoryTheory.homOfLE hVtop).op ((XV.ι ≫ f).app V.1 h')
  let W : XV.toScheme.Opens := XV.toScheme.basicOpen u'
  have hW : W = (XV.ι ≫ f) ⁻¹ᵁ S.basicOpen h' := by
    show XV.toScheme.basicOpen u' = _
    rw [AlgebraicGeometry.Scheme.basicOpen_res, ← AlgebraicGeometry.Scheme.preimage_basicOpen,
      top_inf_eq]
  have hmemW : ∀ y : XV.toScheme, y ∈ W ↔ f.base y.1 ∈ S.basicOpen h' := by
    intro y
    rw [hW]
    rfl
  -- Step 2: the open immersion g : W ⟶ Xi (W ⊆ f⁻¹D ⊆ f⁻¹i)
  have hrange : Set.range (W.ι ≫ XV.ι).base ⊆ Set.range Xi.ι.base := by
    rintro _ ⟨y, rfl⟩
    rw [AlgebraicGeometry.Scheme.Opens.range_ι]
    have hy : f.base y.1.1 ∈ S.basicOpen h' := (hmemW y.1).mp y.2
    rw [← hD] at hy
    exact hDi hy
  let g : W.toScheme ⟶ Xi.toScheme := AlgebraicGeometry.IsOpenImmersion.lift Xi.ι (W.ι ≫ XV.ι) hrange
  have hg : g ≫ Xi.ι = W.ι ≫ XV.ι := AlgebraicGeometry.IsOpenImmersion.lift_fac _ _ hrange
  -- the ampleness data
  obtain ⟨m, hm, s, hxs, haff⟩ := (hN i hi).2 ⟨x.1, hfxi⟩
  -- P := N^{⊗m}; move s to (pullback Xi.ι).obj P
  let θi := AlgebraicGeometry.Scheme.Modules.pullbackTensorPowIso Xi.ι N m
  let s' : Γ((AlgebraicGeometry.Scheme.Modules.pullback Xi.ι).obj
      (AlgebraicGeometry.Scheme.Modules.tensorPow N m), ⊤) := θi.inv.app ⊤ s
  have hs' : ((AlgebraicGeometry.Scheme.Modules.pullback Xi.ι).obj
      (AlgebraicGeometry.Scheme.Modules.tensorPow N m)).nonvanishingLocus s' =
      (AlgebraicGeometry.Scheme.Modules.tensorPow
        ((AlgebraicGeometry.Scheme.Modules.pullback Xi.ι).obj N) m).nonvanishingLocus s :=
    AlgebraicGeometry.Scheme.Modules.nonvanishingLocus_iso θi.symm s
  -- pull back along g, then move to (pullback W.ι).obj ((pullback XV.ι).obj P)
  let φ : (AlgebraicGeometry.Scheme.Modules.pullback g).obj
      ((AlgebraicGeometry.Scheme.Modules.pullback Xi.ι).obj
        (AlgebraicGeometry.Scheme.Modules.tensorPow N m)) ≅
      (AlgebraicGeometry.Scheme.Modules.pullback W.ι).obj
        ((AlgebraicGeometry.Scheme.Modules.pullback XV.ι).obj
          (AlgebraicGeometry.Scheme.Modules.tensorPow N m)) :=
    (AlgebraicGeometry.Scheme.Modules.pullbackComp g Xi.ι).app _ ≪≫
      (AlgebraicGeometry.Scheme.Modules.pullbackCongr hg).app _ ≪≫
      ((AlgebraicGeometry.Scheme.Modules.pullbackComp W.ι XV.ι).app _).symm
  let t := φ.hom.app ⊤ (sectionPullbackAlong g s')
  have ht : ((AlgebraicGeometry.Scheme.Modules.pullback W.ι).obj
      ((AlgebraicGeometry.Scheme.Modules.pullback XV.ι).obj
        (AlgebraicGeometry.Scheme.Modules.tensorPow N m))).nonvanishingLocus t =
      g ⁻¹ᵁ (AlgebraicGeometry.Scheme.Modules.tensorPow
        ((AlgebraicGeometry.Scheme.Modules.pullback Xi.ι).obj N) m).nonvanishingLocus s := by
    rw [← hs', ← AlgebraicGeometry.Scheme.Modules.nonvanishingLocus_sectionPullbackAlong g _ s']
    exact AlgebraicGeometry.Scheme.Modules.nonvanishingLocus_iso φ _
  -- Step 3: extend to X'
  obtain ⟨σ, hσ⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_section_nonvanishingLocus_eq_image_basicOpen
      ((AlgebraicGeometry.Scheme.Modules.pullback XV.ι).obj
        (AlgebraicGeometry.Scheme.Modules.tensorPow N m)) u' t
  let θV := AlgebraicGeometry.Scheme.Modules.pullbackTensorPowIso XV.ι N m
  refine ⟨m, hm, θV.hom.app ⊤ σ, ?_, ?_⟩
  · -- x lies in the nonvanishing locus of the witness
    rw [AlgebraicGeometry.Scheme.Modules.nonvanishingLocus_iso θV σ, hσ, ht]
    have hxW : x ∈ W := (hmemW x).mpr (hD ▸ hxD)
    have hgx : g.base ⟨x, hxW⟩ = ⟨x.1, hfxi⟩ := by
      apply Xi.ι.isOpenEmbedding.injective
      have h1 := congrArg (fun k : W.toScheme ⟶ X => k.base ⟨x, hxW⟩) hg
      simp only [AlgebraicGeometry.Scheme.Hom.comp_base, TopCat.comp_app] at h1
      exact h1
    have hmem : (⟨x, hxW⟩ : W.toScheme) ∈ g ⁻¹ᵁ (AlgebraicGeometry.Scheme.Modules.tensorPow
        ((AlgebraicGeometry.Scheme.Modules.pullback Xi.ι).obj N) m).nonvanishingLocus s := by
      change g.base ⟨x, hxW⟩ ∈ (AlgebraicGeometry.Scheme.Modules.tensorPow
        ((AlgebraicGeometry.Scheme.Modules.pullback Xi.ι).obj N) m).nonvanishingLocus s
      rw [hgx]
      exact hxs
    exact Set.mem_image_of_mem _ hmem
  · -- the nonvanishing locus of the witness is affine
    rw [AlgebraicGeometry.Scheme.Modules.nonvanishingLocus_iso θV σ, hσ, ht]
    refine AlgebraicGeometry.IsAffineOpen.image_of_isOpenImmersion ?_ W.ι
    rw [← g.isAffineOpen_iff_of_isOpenImmersion, g.image_preimage_eq_opensRange_inf]
    have hDXV : f ⁻¹ᵁ S.basicOpen h ≤ XV := fun z hz => hDV (hD ▸ hz)
    have h2 : (g ≫ Xi.ι).opensRange = (W.ι ≫ XV.ι).opensRange := by
      apply TopologicalSpace.Opens.ext
      show Set.range (g ≫ Xi.ι).base = Set.range (W.ι ≫ XV.ι).base
      rw [hg]
    have hgr : g.opensRange = (Xi.ι ≫ f) ⁻¹ᵁ S.basicOpen h := by
      rw [← Xi.ι.preimage_image_eq g.opensRange, ← AlgebraicGeometry.Scheme.Hom.opensRange_comp, h2,
        AlgebraicGeometry.Scheme.Hom.opensRange_comp, AlgebraicGeometry.Scheme.Opens.opensRange_ι, hW,
        AlgebraicGeometry.Scheme.Hom.comp_preimage, XV.ι.image_preimage_eq_opensRange_inf,
        AlgebraicGeometry.Scheme.Opens.opensRange_ι, ← hD, inf_eq_right.mpr hDXV]
      rfl
    have hle : (AlgebraicGeometry.Scheme.Modules.tensorPow
        ((AlgebraicGeometry.Scheme.Modules.pullback Xi.ι).obj N) m).nonvanishingLocus s ≤
        (Xi.ι ≫ f) ⁻¹ᵁ (i : S.Opens) := fun z _ => z.2
    have hbo : g.opensRange ⊓ (AlgebraicGeometry.Scheme.Modules.tensorPow
        ((AlgebraicGeometry.Scheme.Modules.pullback Xi.ι).obj N) m).nonvanishingLocus s =
        Xi.toScheme.basicOpen (Xi.toScheme.presheaf.map (CategoryTheory.homOfLE hle).op
          ((Xi.ι ≫ f).app _ h)) := by
      rw [AlgebraicGeometry.Scheme.basicOpen_res, ← AlgebraicGeometry.Scheme.preimage_basicOpen, hgr,
        inf_comm]
    rw [hbo]
    exact haff.basicOpen _

end
