import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.SectionPullbackAlong
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.ZeroSchemeOfSection
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModuleChartPullback

/-! # The zero-scheme ideal sheaf of a section is contained in the kernel iff the pullback vanishes

The ideal sheaf of zeros of a global section `s` of a line bundle is contained in the kernel of a
morphism `h` if and only if the pullback of `s` along `h` is zero:
`idealSheafOfSection L s ≤ h.ker ↔ sectionPullbackAlong h s = 0`.

This is the section-level criterion for "`h` factors through the zero scheme `V(s)`" (Stacks 01WX / 02OR:
functoriality of zero schemes under pullback), used for the scaling action on the cone, for the seed
section and for the vanishing of homogeneous equations along the section given by a tuple.

Route:
* (⇒) No local structure of the pullback is needed: the adjunction unit `η : L ⟶ h_*h^*L` is a morphism
  of `O_X`-modules, the `Γ(X,U)`-action on `h_*h^*L` over `U` is by definition through `h^♯`
  (`IsFrame.unit_app_res_eq_zero`), and then the sheaf axiom for the sheaf `h_*h^*L` on `X`
  (`TopCat.Sheaf.eq_of_locally_eq'`).
* (⇐) The step "pullback preserves frames" uses `pullbackFrameIso_section` (in a frame `e`, the coordinate
  of `h^*s` is `(h|_W)^♯` of the coordinate of `s`), giving
  `IsFrame.app_coord_eq_zero_of_sectionPullbackAlong_eq_zero`; then `IdealSheafData.map_ideal_basicOpen`
  transports the inclusion from affine opens with a frame to all affine opens
  (`le_ker_of_forall_isFrame_affine`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}}

/-- `sectionPullbackAlong h s` is the component at `⊤` of the pullback–pushforward adjunction unit
`η_L : L ⟶ h_*h^*L` (unfolding the definition). -/
theorem sectionPullbackAlong_eq_unit_app (h : Y ⟶ X) {L : X.Modules}
    (s : (L.val.obj (Opposite.op ⊤) : Type u)) :
    sectionPullbackAlong h s =
      Modules.Hom.app ((Modules.pullbackPushforwardAdjunction h).unit.app L) ⊤
        (show Γ(L, ⊤) from s) := rfl

/-- Three restrictions compose to the identity: in the thin category `Opens`, `k₁ ≫ k₂ ≫ k₃ = 𝟙`. -/
private theorem presheaf_map_map_map_eq_self {U V₁ V₂ : Y.Opens} (k₁ : op U ⟶ op V₁)
    (k₂ : op V₁ ⟶ op V₂) (k₃ : op V₂ ⟶ op U) (x : Γ(Y, U)) :
    Y.presheaf.map k₃ (Y.presheaf.map k₂ (Y.presheaf.map k₁ x)) = x := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
    ← Functor.map_comp, Subsingleton.elim (k₁ ≫ k₂ ≫ k₃) (𝟙 _), CategoryTheory.Functor.map_id]
  rfl

/-- The `Γ(X, W)`-action on the pushforward `h_*N` over `W ⊆ X` is by definition through `h^♯`:
`r • x = h^♯(r) • x` (`PresheafOfModules.pushforward` = `restrictScalars`, a definitional equality). -/
theorem Modules.pushforward_smul_def (h : Y ⟶ X) (N : Y.Modules) (W : X.Opens) (r : Γ(X, W))
    (x : Γ((Modules.pushforward h).obj N, W)) :
    r • x = (show Γ(N, h ⁻¹ᵁ W) from h.app W r • (show Γ(N, h ⁻¹ᵁ W) from x)) := rfl

/-- **Local frame form of (⇒)**: `W` carries a frame `e`, `s|_W = c • e` (`c` the frame coordinate). If
`h^♯(c) = 0`, then the adjunction unit `η_L : L ⟶ h_*h^*L` sends `s|_W` to `0` on `W`.

Proof: `η_L` is a morphism of `O_X`-modules, so `η_W(c • e) = c • η_W(e)`; the `Γ(X, W)`-action on `h_*N`
over `W` is by definition (`PresheafOfModules.pushforward` = `restrictScalars` through `h^♯`)
`r • x = h^♯(r) • x`, hence `η_W(s|_W) = h^♯(c) • η_W(e) = 0`. -/
theorem Modules.IsFrame.unit_app_res_eq_zero (h : Y ⟶ X) {L : X.Modules} {W : X.Opens}
    {e : Γ(L, W)} (hf : Modules.IsFrame L W e) (s : Γ(L, ⊤))
    (hc : h.app W (hf.coord le_rfl (L.res le_top s)) = 0) :
    Modules.Hom.app ((Modules.pullbackPushforwardAdjunction h).unit.app L) W (L.res le_top s)
      = 0 := by
  have hs : hf.coord le_rfl (L.res le_top s) • L.res le_rfl e = L.res le_top s :=
    hf.coord_smul_frame le_rfl _
  rw [← hs, Modules.Hom.app_smul, Modules.pushforward_smul_def, hc, zero_smul]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- **Local frame form of (⇐) (pullback preserves frames)**: `W ⊆ X` open, `e` a frame of `L` on `W`, `s` a
global section of `L`, `c :=` the coordinate of `s|_W` in `e`. If `h^*s = 0`, then `h^♯(c) = 0` in
`Γ(Y, h⁻¹W)`.

Proof (the remark after Stacks 01CR + the pullback adjunction; all transports are in `ModuleChartPullback`):
the frame `e` gives a trivialization `φ := hf.restrictIso : L|_W ≅ O_W`. Take the chart `g := h|_W : h⁻¹W → W`
(`morphismRestrict_ι`); `pullbackFrameIso_section` gives `(h^*L)|_{h⁻¹W} ≅ O_{h⁻¹W}` under which
`h^*s|_{h⁻¹W} ↦ g^♯(φ(s|_W))`. When `h^*s = 0` the left side is `0`, so `g^♯(φ(s|_W)) = 0`;
`φ(s|_W)` is the coordinate `c` (`restrictIso_hom_app_restrictAppIso_inv`, coordinates are compatible with
restriction, `coord_map`), and `g^♯ = h^♯` composed with the restriction isomorphism of an equality of opens
(`morphismRestrict_appTop`), which does not affect "`= 0`"; hence `h^♯(c) = 0`. -/
theorem Modules.IsFrame.app_coord_eq_zero_of_sectionPullbackAlong_eq_zero (h : Y ⟶ X)
    {L : X.Modules} {W : X.Opens} {e : Γ(L, W)} (hf : Modules.IsFrame L W e)
    (s : (L.val.obj (Opposite.op ⊤) : Type u)) (hs : sectionPullbackAlong h s = 0) :
    h.app W (hf.coord le_rfl (L.res le_top (show Γ(L, ⊤) from s))) = 0 := by
  have key := AlgebraicGeometry.Scheme.Modules.HomogeneousTupleTwistPullback.pullbackFrameIso_section h (h ⁻¹ᵁ W) W
    (h ∣_ W) (morphismRestrict_ι h W) L hf.restrictIso (show Γ(L, ⊤) from s)
  -- the left-hand side vanishes: h^*s = 0
  have hL : AlgebraicGeometry.Scheme.Modules.HomogeneousTupleTwistPullback.restrictedGlobalSection
      ((Modules.pullback h).obj L) (h ⁻¹ᵁ W)
      (AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback h (show Γ(L, ⊤) from s)) = 0 := by
    unfold AlgebraicGeometry.Scheme.Modules.HomogeneousTupleTwistPullback.restrictedGlobalSection
    rw [show AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback h (show Γ(L, ⊤) from s) = 0 from hs, map_zero,
      map_zero]
  rw [hL, map_zero] at key
  unfold AlgebraicGeometry.Scheme.Modules.HomogeneousTupleTwistPullback.restrictedGlobalSection at key
  rw [hf.restrictIso_hom_app_restrictAppIso_inv] at key
  -- the coordinate on `W.ι ''ᵁ ⊤` is the restriction of the coordinate on `W`
  set c := hf.coord le_rfl (L.res le_top (show Γ(L, ⊤) from s)) with hc
  have hc₀ : hf.coord (Modules.image_ι_le W ⊤)
      (L.presheaf.map (homOfLE (le_top : W.ι ''ᵁ ⊤ ≤ ⊤)).op (show Γ(L, ⊤) from s)) =
      X.presheaf.map (homOfLE (Modules.image_ι_le W ⊤)).op c := by
    have h1 := hf.coord_map (Modules.image_ι_le W ⊤) le_rfl (L.res le_top (show Γ(L, ⊤) from s))
    rw [Modules.res_res] at h1
    exact h1
  rw [hc₀] at key
  have hiso : (W.ι.appIso ⊤).hom (X.presheaf.map (homOfLE (Modules.image_ι_le W ⊤)).op c) =
      (show Γ(W.toScheme, ⊤) from X.presheaf.map (homOfLE (Modules.image_ι_le W ⊤)).op c) := by
    rw [Scheme.Opens.ι_appIso]; rfl
  rw [hiso, morphismRestrict_appTop, CommRingCat.comp_apply] at key
  have hnat := ConcreteCategory.congr_hom (h.naturality (homOfLE (Modules.image_ι_le W ⊤)).op) c
  simp only [CommRingCat.comp_apply] at hnat
  change 0 = Y.presheaf.map (eqToHom (image_morphismRestrict_preimage h W ⊤)).op
    (h.app (W.ι ''ᵁ ⊤) (X.presheaf.map (homOfLE (Modules.image_ι_le W ⊤)).op c)) at key
  rw [hnat] at key
  have hrev : h ⁻¹ᵁ W ≤ (h ⁻¹ᵁ W).ι ''ᵁ ((h ∣_ W) ⁻¹ᵁ ⊤) := by
    rw [image_morphismRestrict_preimage, Scheme.Opens.ι_image_top]
  have := congrArg (Y.presheaf.map (homOfLE hrev).op) key
  rw [map_zero, presheaf_map_map_map_eq_self] at this
  exact this.symm

set_option backward.isDefEq.respectTransparency false in
/-- **Inclusion on an affine open with a frame**: `W` affine, `e` a frame of `L` on `W`, `h^*s = 0` ⇒
`I(W) ⊆ ker(h^♯ : Γ(X,W) → Γ(Y,h⁻¹W))`.

Proof: `I(W)` is generated by the `φ(s|_W)` (`φ : Γ(L,W) →ₗ Γ(X,W)`) (`Ideal.span_le`). `s|_W = c • e`, so
`φ(s|_W) = c · φ(e)` and `h^♯(φ(s|_W)) = h^♯(c) · h^♯(φ(e)) = 0`
(`app_coord_eq_zero_of_sectionPullbackAlong_eq_zero`). -/
theorem idealSheafOfSection_ideal_le_ker_of_isFrame (h : Y ⟶ X) (L : X.Modules) [L.IsLineBundle]
    (s : (L.val.obj (Opposite.op ⊤) : Type u)) (hs : sectionPullbackAlong h s = 0)
    (W : X.affineOpens) {e : Γ(L, W.1)} (hf : Modules.IsFrame L W.1 e) :
    (idealSheafOfSection L s).ideal W ≤ RingHom.ker (h.app W.1).hom := by
  show Ideal.span (Set.range fun φ : Γ(L, W.1) →ₗ[Γ(X, W.1)] Γ(X, W.1) =>
    φ (L.presheaf.map (CategoryTheory.homOfLE le_top).op (show Γ(L, ⊤) from s))) ≤ _
  rw [Ideal.span_le]
  rintro _ ⟨φ, rfl⟩
  rw [SetLike.mem_coe, RingHom.mem_ker]
  set sW : Γ(L, W.1) := L.res le_top (show Γ(L, ⊤) from s) with hsW
  have hc : hf.coord le_rfl sW • L.res le_rfl e = sW := hf.coord_smul_frame le_rfl sW
  show (h.app W.1).hom (φ sW) = 0
  rw [← hc, map_smul, smul_eq_mul, map_mul]
  have h0 := hf.app_coord_eq_zero_of_sectionPullbackAlong_eq_zero h s hs
  rw [show (h.app W.1).hom (hf.coord le_rfl sW) = 0 from h0, zero_mul]

/-- **From affine opens with a frame to all affine opens**: `I` any ideal sheaf on `X`, `L` a line bundle.
If `I(W) ⊆ ker(h^♯_W)` for every affine open `W` carrying a frame, then `I ≤ h.ker`.

Proof: `Hom.ker h = ofIdeals (fun U => ker (h.app U))`, and `le_ofIdeals_iff` reduces the claim to: for
every affine open `U` and every `x ∈ I(U)`, `h^♯_U(x) = 0` in `Γ(Y, h⁻¹U)`. For `p ∈ U` take a frame
neighbourhood `W ≤ U` (`exists_frame_le`), then a basic open `D(g) ∋ p`, `D(g) ≤ W`
(`IsAffineOpen.exists_basicOpen_le`), and restrict the frame to `D(g)`. The `h⁻¹D(g_p)` cover `h⁻¹U` and
`O_Y` is a sheaf (`eq_of_locally_eq'`), so it suffices that
`h^♯_U(x)|_{h⁻¹D(g)} = h^♯_{D(g)}(x|_{D(g)})` (`Hom.naturality`) vanishes; and
`x|_{D(g)} ∈ I(U)·Γ(X, D(g)) = I(D(g))` (`map_ideal_basicOpen`) `⊆ ker h^♯_{D(g)}` (hypothesis). -/
theorem le_ker_of_forall_isFrame_affine (h : Y ⟶ X) (L : X.Modules) [L.IsLineBundle]
    (I : X.IdealSheafData)
    (H : ∀ (W : X.affineOpens) (e : Γ(L, W.1)), Modules.IsFrame L W.1 e →
      I.ideal W ≤ RingHom.ker (h.app W.1).hom) :
    I ≤ h.ker := by
  refine IdealSheafData.le_ofIdeals_iff.mpr fun U x hx => ?_
  rw [RingHom.mem_ker]
  have key : ∀ p : U.1, ∃ g : Γ(X, U.1), p.1 ∈ X.basicOpen g ∧
      ∃ e : Γ(L, X.basicOpen g), Modules.IsFrame L (X.basicOpen g) e := by
    intro p
    obtain ⟨W, hWU, hpW, e, he⟩ := Modules.exists_frame_le L p.2
    obtain ⟨g, hgW, hpg⟩ := U.2.exists_basicOpen_le ⟨p.1, hpW⟩ p.2
    exact ⟨g, hpg, L.res hgW e, he.restrict hgW⟩
  choose g hg e he using key
  refine Y.sheaf.eq_of_locally_eq' (fun p : U.1 => h ⁻¹ᵁ X.basicOpen (g p)) (h ⁻¹ᵁ U.1)
    (fun p => (Opens.map h.base).map (homOfLE (X.basicOpen_le (g p)))) ?_ _ _ fun p => ?_
  · intro y hy
    exact Opens.mem_iSup.mpr ⟨⟨h.base y, hy⟩, hg ⟨h.base y, hy⟩⟩
  · show Y.presheaf.map _ ((h.app U.1).hom x) = Y.presheaf.map _ 0
    rw [map_zero]
    have hnat := ConcreteCategory.congr_hom (h.naturality (homOfLE (X.basicOpen_le (g p))).op) x
    simp only [CommRingCat.comp_apply] at hnat
    refine hnat.symm.trans ?_
    have hmem : X.presheaf.map (homOfLE (X.basicOpen_le (g p))).op x ∈
        I.ideal (X.affineBasicOpen (g p)) := by
      rw [← I.map_ideal_basicOpen U (g p)]
      exact Ideal.mem_map_of_mem _ hx
    exact RingHom.mem_ker.mp (H (X.affineBasicOpen (g p)) (e p) (he p) hmem)

set_option backward.isDefEq.respectTransparency false in
/-- The zero-scheme ideal sheaf is contained in the kernel ⟺ the pullback of the section is zero.

Proof (the section form of Stacks 01WX/02OR): write `I := idealSheafOfSection L s`,
`I(U) =` the ideal generated by `{φ(s|_U) | φ ∈ Hom_{Γ(X,U)}(Γ(L,U), Γ(X,U))}` (definition of
`idealSheafOfSection`). By `IdealSheafData.le_ofIdeals_iff` and the definition of `Hom.ker`, `I ≤ h.ker`
means: for every affine open `U ⊆ X`, `I(U) ⊆ ker(h.app U : Γ(X,U) → Γ(Y, h⁻¹U))`, i.e. `h^♯(φ(s|_U)) = 0`
for every `φ`.
* (⇒) Assume `I ≤ h.ker`. `L` is a line bundle: `X` is covered by affine opens `W` with frames `e_W`
  (`exists_affine_frame_le`), `s|_W = c_W • e_W` with `c_W` the frame coordinate (`IsFrame.coord`). The
  coordinate map is itself a `φ`, so `c_W ∈ I(W) ⊆ ker(h.app W)`, i.e. `h^♯(c_W) = 0`. `η_L : L ⟶ h_*h^*L`
  is the adjunction unit (`sectionPullbackAlong` = the component of `η` at `⊤`), and
  `(h^*s)|_{h⁻¹W} = η_W(s|_W) = η_W(c_W • e_W) = h^♯(c_W) • η_W(e_W) = 0` (`IsFrame.unit_app_res_eq_zero`:
  the scalar action on `h_*N` is by definition through `h^♯`). The `W` cover `X` and `h_*h^*L` is a sheaf
  on `X`, so `h^*s = η_⊤(s) = 0` (`TopCat.Sheaf.eq_of_locally_eq'`).
* (⇐) Assume `h^*s = 0`. By `le_ker_of_forall_isFrame_affine` (`map_ideal_basicOpen` reduces affine opens
  to basic opens with a frame) it suffices to show `I(W) ⊆ ker(h.app W)` for affine opens `W` with a frame
  `e`: the generators are `φ(s|_W) = φ(c • e) = c · φ(e)`, and `h^♯(c) = 0`
  (`IsFrame.app_coord_eq_zero_of_sectionPullbackAlong_eq_zero`: by `pullbackFrameIso_section`, "the
  coordinate of `h^*s` in the pulled-back frame = `(h|_W)^♯` of the coordinate of `s`", and the left side
  is `0`).
Edge cases: for `Y = ∅` both sides hold (`Γ(∅, -)` is the zero ring, `h.ker = ⊤`); for `X = ∅`, `s = 0` and
both sides are trivial; over the zero ring the section groups of `L` are trivial. -/
theorem idealSheafOfSection_le_ker_iff {X Y : AlgebraicGeometry.Scheme.{u}}
    (h : Y ⟶ X) (L : X.Modules) [L.IsLineBundle] (s : (L.val.obj (Opposite.op ⊤) : Type u)) :
    AlgebraicGeometry.Scheme.idealSheafOfSection L s ≤ h.ker ↔ sectionPullbackAlong h s = 0 := by
  constructor
  · intro hI
    have hI' : ∀ U : X.affineOpens,
        (idealSheafOfSection L s).ideal U ≤ RingHom.ker (h.app U.1).hom :=
      IdealSheafData.le_ofIdeals_iff.mp hI
    change Modules.Hom.app ((Modules.pullbackPushforwardAdjunction h).unit.app L) ⊤
        (show Γ(L, ⊤) from s)
      = (0 : Γ((Modules.pushforward h).obj ((Modules.pullback h).obj L), ⊤))
    refine TopCat.Sheaf.eq_of_locally_eq'
      ⟨((Modules.pushforward h).obj ((Modules.pullback h).obj L)).presheaf,
        ((Modules.pushforward h).obj ((Modules.pullback h).obj L)).isSheaf⟩
      (fun W : {W : X.affineOpens // ∃ e : Γ(L, W.1), Modules.IsFrame L W.1 e} => W.1.1) ⊤
      (fun W => homOfLE le_top) ?_ _ _ fun W => ?_
    · intro p _
      obtain ⟨W, hW, -, hpW, e, he⟩ :=
        Modules.exists_affine_frame_le L (U := ⊤) (p := p) trivial
      exact Opens.mem_iSup.mpr ⟨⟨⟨W, hW⟩, e, he⟩, hpW⟩
    · obtain ⟨⟨W, hW⟩, e, he⟩ := W
      have hnat := NatTrans.naturality_apply
        ((Modules.pullbackPushforwardAdjunction h).unit.app L).mapPresheaf
        (homOfLE (le_top : W ≤ ⊤)).op (show Γ(L, ⊤) from s)
      have h0 : Modules.Hom.app ((Modules.pullbackPushforwardAdjunction h).unit.app L) W
          (L.res le_top (show Γ(L, ⊤) from s)) = 0 :=
        he.unit_app_res_eq_zero h _ (RingHom.mem_ker.mp (hI' ⟨W, hW⟩ (Ideal.subset_span
          ⟨(he.coordEquiv le_rfl : Γ(L, W) →ₗ[Γ(X, W)] Γ(X, W)), rfl⟩)))
      show ((Modules.pushforward h).obj ((Modules.pullback h).obj L)).presheaf.map
          (homOfLE (le_top : W ≤ ⊤)).op
          (Modules.Hom.app ((Modules.pullbackPushforwardAdjunction h).unit.app L) ⊤
            (show Γ(L, ⊤) from s))
        = ((Modules.pushforward h).obj ((Modules.pullback h).obj L)).presheaf.map
          (homOfLE (le_top : W ≤ ⊤)).op 0
      rw [map_zero]
      exact hnat.symm.trans h0
  · intro hs
    exact le_ker_of_forall_isFrame_affine h L _
      fun W e hf => idealSheafOfSection_ideal_le_ker_of_isFrame h L s hs W hf

end AlgebraicGeometry.Scheme

end
