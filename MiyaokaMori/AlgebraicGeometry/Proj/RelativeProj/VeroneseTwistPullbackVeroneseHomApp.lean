import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.Stacks0b5j
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.VeroneseTwistPullbackVeroneseComparison

/-! # The Veronese morphism on structure-sheaf sections

Pointwise description of the Veronese morphism `veroneseHom : Proj S ⟶ Proj S^{(d)}` (Stacks 0B5J, glued from the
charts `Spec S_(f) ≅ Spec S^{(d)}_(f^d) → Proj S^{(d)}`, `Stacks0b5j.lean`) on **structure-sheaf
sections**, and the hypotheses of the degree-rescaling comparison morphism (`VeroneseTwistPullbackVeroneseComparison`)
for `φ := veroneseHom`, `ψ := (Proj.veroneseIso).hom = inv veroneseHom`:

* on points, `veroneseHom` is the contraction `𝔭 ↦ 𝔭 ∩ S^{(d)}`
  (`veroneseHom_base_mem_asHomogeneousIdeal`, `Stacks0b5j.lean`), repackaged as
  `veroneseHom_isVeroneseContraction`;
* on sections, `(veroneseHom^# r)(𝔭) = (S^{(d)}_{(𝔭 ∩ S^{(d)})} → S_{(𝔭)}) (r (𝔭 ∩ S^{(d)}))`, compared in the ordinary
  localizations through `HomogeneousLocalization.val` — `veroneseHom_app_val_apply` below (via the basic-open reduction `exists_mem_basicOpen_le` and the chart formula `awayToSection_comp_veroneseHom_appLE`);
* `veroneseIso.hom ∘ veroneseHom = id`, `veroneseHom ∘ veroneseIso.hom = id` on points (`Iso.inv_hom_id`, `hom_inv_id`);
* from these, `IsVeroneseSectionCompatible veroneseHom veroneseIso.hom` (`veroneseIso_hom_isVeroneseSectionCompatible`).

Source: Stacks 0B5J; Mathlib `AlgebraicGeometry/ProjectiveSpectrum/Scheme.lean` (`awayToSection_apply`,
`toSpec_base_apply_eq`) and `Basic.lean` (`awayι`, `basicOpenToSpec_app_top`); Lemma 2.2 of
the paper.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Proj

variable {σ A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℕ) (hd : 0 < d)

/-- `veroneseIso.hom ∘ veroneseHom = id` on points (`veroneseIso.inv = veroneseHom` definitionally). -/
theorem veroneseIso_hom_base_veroneseHom_base (x : AlgebraicGeometry.Proj 𝒜) :
    (AlgebraicGeometry.Proj.veroneseIso 𝒜 d hd).hom.base ((AlgebraicGeometry.Proj.veroneseHom 𝒜 d hd).base x) = x := by
  have e : AlgebraicGeometry.Proj.veroneseHom 𝒜 d hd ≫ (AlgebraicGeometry.Proj.veroneseIso 𝒜 d hd).hom = 𝟙 _ :=
    (AlgebraicGeometry.Proj.veroneseIso 𝒜 d hd).inv_hom_id
  exact congrArg (fun g : AlgebraicGeometry.Proj 𝒜 ⟶ AlgebraicGeometry.Proj 𝒜 => g.base x) e

/-- `veroneseHom ∘ veroneseIso.hom = id` on points. -/
theorem veroneseHom_base_veroneseIso_hom_base (y : AlgebraicGeometry.Proj (veroneseGrading 𝒜 d)) :
    (AlgebraicGeometry.Proj.veroneseHom 𝒜 d hd).base ((AlgebraicGeometry.Proj.veroneseIso 𝒜 d hd).hom.base y) = y := by
  have e : (AlgebraicGeometry.Proj.veroneseIso 𝒜 d hd).hom ≫ AlgebraicGeometry.Proj.veroneseHom 𝒜 d hd = 𝟙 _ :=
    (AlgebraicGeometry.Proj.veroneseIso 𝒜 d hd).hom_inv_id
  exact congrArg (fun g : AlgebraicGeometry.Proj (veroneseGrading 𝒜 d) ⟶ AlgebraicGeometry.Proj (veroneseGrading 𝒜 d) =>
    g.base y) e

/-- `veroneseHom` is pointwise the contraction along `S^{(d)} ↪ S`, in the `IsVeroneseContraction` packaging.
Content: `veroneseHom_base_mem_asHomogeneousIdeal` (`Stacks0b5j.lean`). -/
theorem veroneseHom_isVeroneseContraction :
    IsVeroneseContraction 𝒜 d (AlgebraicGeometry.Proj.veroneseHom 𝒜 d hd) := fun x =>
  Ideal.ext fun a => by
    rw [Ideal.mem_comap]
    exact AlgebraicGeometry.Proj.veroneseHom_base_mem_asHomogeneousIdeal 𝒜 d hd x a

/-- Every point of `Proj ℬ` in an open `U` lies in a basic open `D₊(f) ⊆ U` with `f` homogeneous of
**positive** degree. Proof: `Proj.isBasis_basicOpen` gives `x ∈ D₊(a) ⊆ U` for some `a`;
`basicOpen_eq_iSup_proj` gives a homogeneous component `a_i` with `x ∈ D₊(a_i) ⊆ D₊(a)`; the affine open cover
gives `h ∈ ℬ_n`, `n > 0`, with `x ∈ D₊(h)`; take `f := a_i · h` (`basicOpen_mul`). -/
theorem exists_mem_basicOpen_le {σ' A' : Type u} [CommRing A'] [SetLike σ' A'] [AddSubgroupClass σ' A']
    (ℬ : ℕ → σ') [GradedRing ℬ] (U : (AlgebraicGeometry.Proj ℬ).Opens) (x : AlgebraicGeometry.Proj ℬ)
    (hx : x ∈ U) :
    ∃ (m : ℕ) (f : A'), f ∈ ℬ m ∧ 0 < m ∧ x ∈ AlgebraicGeometry.Proj.basicOpen ℬ f ∧
      AlgebraicGeometry.Proj.basicOpen ℬ f ≤ U := by
  obtain ⟨V, ⟨a, rfl⟩, hxa, haU⟩ :=
    (Opens.isBasis_iff_nbhd.mp (AlgebraicGeometry.Proj.isBasis_basicOpen ℬ)) hx
  have hxa' : x ∈ ⨆ i : ℕ, AlgebraicGeometry.Proj.basicOpen ℬ (GradedRing.proj ℬ i a) := by
    rwa [← AlgebraicGeometry.Proj.basicOpen_eq_iSup_proj]
  obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp hxa'
  have hiU : AlgebraicGeometry.Proj.basicOpen ℬ (GradedRing.proj ℬ i a) ≤ U :=
    (le_iSup (fun i => AlgebraicGeometry.Proj.basicOpen ℬ (GradedRing.proj ℬ i a)) i).trans
      ((AlgebraicGeometry.Proj.basicOpen_eq_iSup_proj ℬ a).ge.trans haU)
  obtain ⟨j, q, hq⟩ := (AlgebraicGeometry.Proj.affineOpenCover ℬ).openCover.exists_eq x
  have hxj : x ∈ AlgebraicGeometry.Proj.basicOpen ℬ j.2.1 := by
    rw [← AlgebraicGeometry.Proj.opensRange_awayι ℬ j.2.1 j.2.2 j.1.pos]
    exact ⟨q, hq⟩
  have hmem : GradedRing.proj ℬ i a ∈ ℬ i := by
    rw [GradedRing.proj_apply]
    exact SetLike.coe_mem _
  refine ⟨i + j.1, GradedRing.proj ℬ i a * j.2.1, SetLike.mul_mem_graded hmem j.2.2,
    Nat.add_pos_right i j.1.pos, ?_, ?_⟩
  · rw [AlgebraicGeometry.Proj.basicOpen_mul]
    exact ⟨hxi, hxj⟩
  · exact (AlgebraicGeometry.Proj.basicOpen_mul ℬ _ _).le.trans (inf_le_left.trans hiU)

/-- **Chart formula** for the Veronese morphism on sections (the analogue of Mathlib
`Proj.awayToSection_comp_appLE` for `Proj.map`): for `f ∈ 𝒜_m`, `m > 0`,
`awayToSection S^{(d)} ⟨f^d⟩ ≫ veroneseHom.appLE (D₊(f^d)) (D₊(f)) = ofHom (veroneseAwayEquiv) ≫ awayToSection S f`.

Proof: the chart identity `awayι 𝒜 f ≫ veroneseHom = Spec.map e ≫ awayι S^{(d)} ⟨f^d⟩` (`awayι_comp_veroneseHom`,
`veroneseChart_eq`) with `awayι = basicOpenIsoSpec.inv ≫ ι` gives, after cancelling the mono `awayι S^{(d)} ⟨f^d⟩`,
`veroneseHom.resLE (D₊(f^d)) (D₊(f)) ≫ basicOpenIsoSpec.hom = basicOpenIsoSpec.hom ≫ Spec.map e`
(`resLE_comp_ι`). Take `appTop` of both sides: `resLE_app_top`, `basicOpenToSpec_app_top`
(`= ΓSpecIso.hom ≫ awayToSection ≫ topIso.inv`) and `ΓSpecIso_naturality` for `(Spec.map e).appTop`; cancel the
iso `ΓSpecIso.hom` on the left and `topIso.inv` on the right. Source: Stacks 0B5J, proof, third paragraph. -/
theorem awayToSection_comp_veroneseHom_appLE {f : A} {m : ℕ} (hf : f ∈ 𝒜 m) (hm : 0 < m) :
    AlgebraicGeometry.Proj.awayToSection (veroneseGrading 𝒜 d)
        (⟨f ^ d, (veronese_pow_mem 𝒜 d hd hf).1⟩ : veroneseSubring 𝒜 d) ≫
      (AlgebraicGeometry.Proj.veroneseHom 𝒜 d hd).appLE
        (AlgebraicGeometry.Proj.basicOpen (veroneseGrading 𝒜 d)
          (⟨f ^ d, (veronese_pow_mem 𝒜 d hd hf).1⟩ : veroneseSubring 𝒜 d))
        (AlgebraicGeometry.Proj.basicOpen 𝒜 f)
        (AlgebraicGeometry.Proj.veroneseHom_preimage_basicOpen 𝒜 d hd f m hf).ge =
    CommRingCat.ofHom (veroneseAwayEquiv 𝒜 d hd hf).toRingHom ≫ AlgebraicGeometry.Proj.awayToSection 𝒜 f := by
  have hg' : (⟨f ^ d, (veronese_pow_mem 𝒜 d hd hf).1⟩ : veroneseSubring 𝒜 d) ∈ veroneseGrading 𝒜 d m :=
    veronese_pow_mem_grading 𝒜 d hd hf
  have hchart : AlgebraicGeometry.Proj.awayι 𝒜 f hf hm ≫ AlgebraicGeometry.Proj.veroneseHom 𝒜 d hd =
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom (veroneseAwayEquiv 𝒜 d hd hf).toRingHom) ≫
        AlgebraicGeometry.Proj.awayι (veroneseGrading 𝒜 d) _ hg' hm :=
    (AlgebraicGeometry.Proj.awayι_comp_veroneseHom 𝒜 d hd ⟨⟨m, hm⟩, ⟨f, hf⟩⟩).trans
      (AlgebraicGeometry.Proj.veroneseChart_eq 𝒜 d hd ⟨⟨m, hm⟩, ⟨f, hf⟩⟩)
  have hA : (AlgebraicGeometry.Proj.veroneseHom 𝒜 d hd).resLE _ _
        (AlgebraicGeometry.Proj.veroneseHom_preimage_basicOpen 𝒜 d hd f m hf).ge ≫
        (AlgebraicGeometry.Proj.basicOpenIsoSpec (veroneseGrading 𝒜 d) _ hg' hm).hom =
      (AlgebraicGeometry.Proj.basicOpenIsoSpec 𝒜 f hf hm).hom ≫
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom (veroneseAwayEquiv 𝒜 d hd hf).toRingHom) := by
    rw [← cancel_mono (AlgebraicGeometry.Proj.awayι (veroneseGrading 𝒜 d) _ hg' hm), Category.assoc,
      Category.assoc, ← hchart, ← AlgebraicGeometry.Proj.basicOpenIsoSpec_inv_ι,
      ← AlgebraicGeometry.Proj.basicOpenIsoSpec_inv_ι]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, AlgebraicGeometry.Scheme.Hom.resLE_comp_ι]
  have hB : ((AlgebraicGeometry.Proj.veroneseHom 𝒜 d hd).resLE _ _
        (AlgebraicGeometry.Proj.veroneseHom_preimage_basicOpen 𝒜 d hd f m hf).ge ≫
        (AlgebraicGeometry.Proj.basicOpenIsoSpec (veroneseGrading 𝒜 d) _ hg' hm).hom).appTop =
      ((AlgebraicGeometry.Proj.basicOpenIsoSpec 𝒜 f hf hm).hom ≫
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom (veroneseAwayEquiv 𝒜 d hd hf).toRingHom)).appTop := by
    rw [hA]
  simp only [AlgebraicGeometry.Scheme.Hom.comp_appTop, AlgebraicGeometry.Scheme.Hom.resLE_app_top, AlgebraicGeometry.Proj.basicOpenIsoSpec_hom,
    AlgebraicGeometry.Proj.basicOpenToSpec_app_top, Category.assoc, Iso.inv_hom_id_assoc,
    AlgebraicGeometry.Scheme.ΓSpecIso_naturality_assoc] at hB
  rw [cancel_epi, ← Category.assoc, ← Category.assoc, cancel_mono] at hB
  exact hB

/-- `veroneseHom : Proj S ⟶ Proj S^{(d)}` acts on structure-sheaf
sections by the fibre maps: for `W ⊆ Proj S^{(d)}` open, `r ∈ Γ(Proj S^{(d)}, W)` (a function `𝔮 ↦ r(𝔮) ∈ S^{(d)}_{(𝔮)}`,
locally a degree-`0` fraction) and `𝔭 ∈ veroneseHom⁻¹ W`, the value of `veroneseHom^# r` at `𝔭`, read in the ordinary
localization `S_𝔭` via `HomogeneousLocalization.val`, is `localRingHom (𝔭 ∩ S^{(d)}) 𝔭 ι (r(𝔭 ∩ S^{(d)}).val)`
(`b/t ↦ b/t`).

Source: Stacks 0B5J (lemma-d-uple), third paragraph of the proof: on `D_+(f)` the isomorphism `S_(f) ≅ S^{(d)}_(f^d)`
is the identity on fractions; Mathlib `ProjectiveSpectrum.Proj.awayToSection_apply` for the pointwise value of the
sections coming from `S_(f)`.

Proof (as formalized; `B := S^{(d)}`, `vH := veroneseHom`, `ι : B → A`):
1. Reduce to a basic open: `exists_mem_basicOpen_le` gives `g ∈ B_k`, `k > 0`, with `vH 𝔭 ∈ D_+(g) ⊆ W`. Put
   `f := ι g ∈ 𝒜_{kd}`; then `⟨f^d⟩ = g^d`, `D_+(⟨f^d⟩) = D_+(g) ⊆ W` (`basicOpen_pow`), and
   `vH⁻¹ D_+(⟨f^d⟩) = D_+(f)` (`veroneseHom_preimage_basicOpen`), so `𝔭 ∈ D_+(f) ⊆ vH⁻¹ W`.
2. Restriction is restriction of functions (`Proj.res_apply`, definitional), and `res ∘ vH.app W = vH.appLE W (D_+ f)
   = vH.appLE (D_+(⟨f^d⟩)) (D_+ f) ∘ res` (`Scheme.Hom.map_appLE`).
3. `awayToSection B ⟨f^d⟩` is surjective (`basicOpenIsoAway`), so `r|_{D_+(⟨f^d⟩)} = awayToSection B ⟨f^d⟩ z`; the chart
   formula `awayToSection_comp_veroneseHom_appLE` gives `(vH^# r)|_{D_+(f)} = awayToSection 𝒜 f (veroneseAwayEquiv z)`.
4. Evaluate at `𝔭` with Mathlib `awayToSection_apply` (both sides are `IsLocalization.map` of the fraction),
   `veroneseAwayEquiv_val` (`(veroneseAwayEquiv z).val = IsLocalization.map ι z.val`), `IsLocalization.map_mk'` and
   `Localization.localRingHom_mk'`: both sides are `mk' b t` with `z = mk ⟨_, b, t, _⟩`. -/
theorem veroneseHom_app_val_apply (W : (AlgebraicGeometry.Proj (veroneseGrading 𝒜 d)).Opens)
    (r : Γ(AlgebraicGeometry.Proj (veroneseGrading 𝒜 d), W))
    (x : (AlgebraicGeometry.Proj.veroneseHom 𝒜 d hd ⁻¹ᵁ W : (AlgebraicGeometry.Proj 𝒜).Opens)) :
    ((show (ProjectiveSpectrum.Proj.structureSheaf 𝒜).1.obj (op (AlgebraicGeometry.Proj.veroneseHom 𝒜 d hd ⁻¹ᵁ W)) from
        (AlgebraicGeometry.Proj.veroneseHom 𝒜 d hd).app W r).1 x).val =
      veroneseFiberMap (veroneseHom_isVeroneseContraction 𝒜 d hd) x.1
        ((show (ProjectiveSpectrum.Proj.structureSheaf (veroneseGrading 𝒜 d)).1.obj (op W) from r).1
          ⟨(AlgebraicGeometry.Proj.veroneseHom 𝒜 d hd).base x.1, x.2⟩).val := by
  obtain ⟨k, g, hg, hk, hxg, hgW⟩ := exists_mem_basicOpen_le (veroneseGrading 𝒜 d) W _ x.2
  have hf : (g : A) ∈ 𝒜 (k * d) := hg.1
  have hkd : 0 < k * d := Nat.mul_pos hk hd
  have hg'eq : (⟨(g : A) ^ d, (veronese_pow_mem 𝒜 d hd hf).1⟩ : veroneseSubring 𝒜 d) = g ^ d :=
    Subtype.ext (SubmonoidClass.coe_pow g d).symm
  have hUW : AlgebraicGeometry.Proj.basicOpen (veroneseGrading 𝒜 d)
      (⟨(g : A) ^ d, (veronese_pow_mem 𝒜 d hd hf).1⟩ : veroneseSubring 𝒜 d) ≤ W := by
    rw [hg'eq, AlgebraicGeometry.Proj.basicOpen_pow _ _ d hd]
    exact hgW
  have hVU : AlgebraicGeometry.Proj.basicOpen 𝒜 (g : A) ≤
      AlgebraicGeometry.Proj.veroneseHom 𝒜 d hd ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen (veroneseGrading 𝒜 d)
        (⟨(g : A) ^ d, (veronese_pow_mem 𝒜 d hd hf).1⟩ : veroneseSubring 𝒜 d) :=
    (AlgebraicGeometry.Proj.veroneseHom_preimage_basicOpen 𝒜 d hd (g : A) (k * d) hf).ge
  have hxV : x.1 ∈ AlgebraicGeometry.Proj.basicOpen 𝒜 (g : A) := by
    rw [← AlgebraicGeometry.Proj.veroneseHom_preimage_basicOpen 𝒜 d hd (g : A) (k * d) hf]
    show (AlgebraicGeometry.Proj.veroneseHom 𝒜 d hd).base x.1 ∈ AlgebraicGeometry.Proj.basicOpen _ _
    rw [hg'eq, AlgebraicGeometry.Proj.basicOpen_pow _ _ d hd]
    exact hxg
  have hVW : AlgebraicGeometry.Proj.basicOpen 𝒜 (g : A) ≤ AlgebraicGeometry.Proj.veroneseHom 𝒜 d hd ⁻¹ᵁ W :=
    hVU.trans fun y hy => hUW hy
  -- the restriction of `r` to `D₊(⟨f^d⟩)` comes from `S^{(d)}_(f^d)`
  obtain ⟨z, hz⟩ := (ConcreteCategory.bijective_of_isIso
    (AlgebraicGeometry.Proj.basicOpenIsoAway (veroneseGrading 𝒜 d) _ (veronese_pow_mem_grading 𝒜 d hd hf) hkd).hom).2
    ((AlgebraicGeometry.Proj (veroneseGrading 𝒜 d)).presheaf.map (homOfLE hUW).op r)
  rw [AlgebraicGeometry.Proj.basicOpenIsoAway_hom] at hz
  -- the restriction of `vH^# r` to `D₊(f)` is `awayToSection 𝒜 f (e z)`
  have hkey : (AlgebraicGeometry.Proj 𝒜).presheaf.map (homOfLE hVW).op
        ((AlgebraicGeometry.Proj.veroneseHom 𝒜 d hd).app W r) =
      AlgebraicGeometry.Proj.awayToSection 𝒜 (g : A) ((veroneseAwayEquiv 𝒜 d hd hf).toRingHom z) := by
    have h1 : (AlgebraicGeometry.Proj 𝒜).presheaf.map (homOfLE hVW).op
        ((AlgebraicGeometry.Proj.veroneseHom 𝒜 d hd).app W r) =
        (AlgebraicGeometry.Proj.veroneseHom 𝒜 d hd).appLE W _ hVW r := rfl
    have h2 : (AlgebraicGeometry.Proj.veroneseHom 𝒜 d hd).appLE W _ hVW r =
        (AlgebraicGeometry.Proj.veroneseHom 𝒜 d hd).appLE _ _ hVU
          ((AlgebraicGeometry.Proj (veroneseGrading 𝒜 d)).presheaf.map (homOfLE hUW).op r) := by
      rw [← CommRingCat.comp_apply, AlgebraicGeometry.Scheme.Hom.map_appLE]
    have h3 : (AlgebraicGeometry.Proj.veroneseHom 𝒜 d hd).appLE _ _ hVU
          (AlgebraicGeometry.Proj.awayToSection (veroneseGrading 𝒜 d) _ z) =
        AlgebraicGeometry.Proj.awayToSection 𝒜 (g : A) ((veroneseAwayEquiv 𝒜 d hd hf).toRingHom z) := by
      have h := congrArg (fun φ => φ z) (awayToSection_comp_veroneseHom_appLE 𝒜 d hd hf hkd)
      exact h
    rw [h1, h2, ← hz, h3]
  have hL : ((show (ProjectiveSpectrum.Proj.structureSheaf 𝒜).1.obj
        (op (AlgebraicGeometry.Proj.veroneseHom 𝒜 d hd ⁻¹ᵁ W)) from
        (AlgebraicGeometry.Proj.veroneseHom 𝒜 d hd).app W r).1 x).val =
      ((show (ProjectiveSpectrum.Proj.structureSheaf 𝒜).1.obj (op (AlgebraicGeometry.Proj.basicOpen 𝒜 (g : A))) from
        (AlgebraicGeometry.Proj 𝒜).presheaf.map (homOfLE hVW).op
          ((AlgebraicGeometry.Proj.veroneseHom 𝒜 d hd).app W r)).1 ⟨x.1, hxV⟩).val := rfl
  have hR : ((show (ProjectiveSpectrum.Proj.structureSheaf (veroneseGrading 𝒜 d)).1.obj (op W) from r).1
        ⟨(AlgebraicGeometry.Proj.veroneseHom 𝒜 d hd).base x.1, x.2⟩).val =
      ((show (ProjectiveSpectrum.Proj.structureSheaf (veroneseGrading 𝒜 d)).1.obj
        (op (AlgebraicGeometry.Proj.basicOpen (veroneseGrading 𝒜 d)
          (⟨(g : A) ^ d, (veronese_pow_mem 𝒜 d hd hf).1⟩ : veroneseSubring 𝒜 d))) from
        (AlgebraicGeometry.Proj (veroneseGrading 𝒜 d)).presheaf.map (homOfLE hUW).op r).1
          ⟨(AlgebraicGeometry.Proj.veroneseHom 𝒜 d hd).base x.1, hVU hxV⟩).val := rfl
  rw [hL, hR, hkey, ← hz]
  erw [ProjectiveSpectrum.Proj.awayToSection_apply, ProjectiveSpectrum.Proj.awayToSection_apply]
  obtain ⟨c, rfl⟩ := HomogeneousLocalization.mk_surjective z
  rw [show (veroneseAwayEquiv 𝒜 d hd hf).toRingHom (HomogeneousLocalization.mk c) =
      HomogeneousLocalization.mk (veroneseAwayEquiv.toNumDen 𝒜 d hd hf c) from rfl,
    HomogeneousLocalization.val_mk, HomogeneousLocalization.val_mk, Localization.mk_eq_mk',
    Localization.mk_eq_mk', IsLocalization.map_mk', IsLocalization.map_mk']
  unfold veroneseFiberMap
  rw [Localization.localRingHom_mk']
  rfl

/-- `ψ := (veroneseIso).hom` is compatible with the fibre maps relative to `φ := veroneseHom`
(hypothesis `happ` of `veroneseTwistHom`): `(veroneseHom ≫ veroneseIso.hom)^# = id`, so
`r(𝔭) = (veroneseHom^# (ψ^# r))(𝔭) = localRingHom ((ψ^# r)(veroneseHom 𝔭))` by `veroneseHom_app_val_apply`. -/
theorem veroneseIso_hom_isVeroneseSectionCompatible :
    IsVeroneseSectionCompatible (AlgebraicGeometry.Proj.veroneseHom 𝒜 d hd)
      (AlgebraicGeometry.Proj.veroneseIso 𝒜 d hd).hom (veroneseIso_hom_base_veroneseHom_base 𝒜 d hd)
      (veroneseHom_isVeroneseContraction 𝒜 d hd) := by
  intro W r x
  have e : AlgebraicGeometry.Proj.veroneseHom 𝒜 d hd ≫ (AlgebraicGeometry.Proj.veroneseIso 𝒜 d hd).hom = 𝟙 _ :=
    (AlgebraicGeometry.Proj.veroneseIso 𝒜 d hd).inv_hom_id
  have hx : x.1 ∈ (AlgebraicGeometry.Proj.veroneseHom 𝒜 d hd ≫ (AlgebraicGeometry.Proj.veroneseIso 𝒜 d hd).hom) ⁻¹ᵁ W := by
    change (AlgebraicGeometry.Proj.veroneseIso 𝒜 d hd).hom.base ((AlgebraicGeometry.Proj.veroneseHom 𝒜 d hd).base x.1) ∈ W
    rw [veroneseIso_hom_base_veroneseHom_base]
    exact x.2
  have h1 : ((AlgebraicGeometry.Proj.veroneseHom 𝒜 d hd ≫ (AlgebraicGeometry.Proj.veroneseIso 𝒜 d hd).hom).app W).hom r =
      ((𝟙 (AlgebraicGeometry.Proj 𝒜) : AlgebraicGeometry.Proj 𝒜 ⟶ AlgebraicGeometry.Proj 𝒜).app W ≫
        (AlgebraicGeometry.Proj 𝒜).presheaf.map (eqToHom (by rw [e])).op).hom r := by
    rw [AlgebraicGeometry.Scheme.Hom.congr_app e W]
  have h2 := congrArg (fun t : (ProjectiveSpectrum.Proj.structureSheaf 𝒜).1.obj
    (op ((AlgebraicGeometry.Proj.veroneseHom 𝒜 d hd ≫ (AlgebraicGeometry.Proj.veroneseIso 𝒜 d hd).hom) ⁻¹ᵁ W)) =>
    (t.1 ⟨x.1, hx⟩).val) h1
  refine Eq.trans ?_ h2
  exact (veroneseHom_app_val_apply 𝒜 d hd ((AlgebraicGeometry.Proj.veroneseIso 𝒜 d hd).hom ⁻¹ᵁ W)
    ((AlgebraicGeometry.Proj.veroneseIso 𝒜 d hd).hom.app W r) ⟨x.1, hx⟩).symm

end AlgebraicGeometry.Proj

end
