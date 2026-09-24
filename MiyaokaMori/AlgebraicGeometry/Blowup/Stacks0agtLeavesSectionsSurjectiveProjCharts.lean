import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.Stacks0agtLeavesSectionsSurjectiveCech
import MiyaokaMori.RingTheory.Stacks0agtLeavesSectionsSurjectiveLaurent
import MiyaokaMori.RingTheory.Stacks0agtLeavesSectionsSurjectiveReesAway

/-! # The two-chart Čech criterion for a scheme covered by `Proj 𝒜` with `D₊(f) ∪ D₊(g) = Proj 𝒜`

`X` a scheme, `ι : Proj 𝒜 ⟶ X` an open immersion with `ι(Proj 𝒜) = X`, `f ∈ 𝒜 d`, `g ∈ 𝒜 e`
(`d, e > 0`) with `D₊(f) ∪ D₊(g) = Proj 𝒜`, and `K` an ideal sheaf on `X` of the form
`K(V) = I₁·Γ(X, V)` for an ideal `I₁ ⊆ Γ(X, ⊤)` (every affine `V`; e.g. `K = (Ĩ).comap b` for
`b : X → Spec A`, by `comap_ideal_eq_map_appLE`). If moreover `𝒜_{(f)}` is generated over `𝒜₀` by
`t = gᵈ/fᵉ` (`hgen`: every element is a polynomial in `t`), then `Γ(X, O_X) → Γ(X, O_X/K)`
(`K.toQuotFamilies`) is surjective.

Proof. The two affine charts `U₁ = ι(D₊(f))`, `U₂ = ι(D₊(g))` cover `X`, their intersection is the
affine `U₁₂ = ι(D₊(fg))` (`Proj.basicOpen_mul`, injectivity of `ι`), and the sections rings are
`𝒜_{(f)}`, `𝒜_{(g)}`, `𝒜_{(fg)}` (`awaySectionsHom`: Mathlib's `awayToSection` followed by `ι.appIso`),
the restrictions being `awayMap` (`presheaf_map_awaySectionsHom`, from Mathlib's
`awayMap_awayToSection` and `appIso_inv_naturality`). Since `𝒜_{(fg)} = 𝒜_{(f)}[1/t]`
(`exists_mul_awayMap_isLocalizationElem_pow_eq`), `t ↦ 1/t'` with `t' = fᵉ/gᵈ ∈ 𝒜_{(g)}`
(`awayMap_isLocalizationElem_mul_awayMap_isLocalizationElem`) and `𝒜_{(f)} = 𝒜₀[t]` (`hgen`), the
Laurent splitting `exists_eq_add_of_localization_of_eval₂_surjective` gives
`Γ(U₁₂) = res Γ(U₁) + res Γ(U₂)`, hence `K(U₁₂) = res K(U₁) + res K(U₂)`
(`exists_mem_map_add_of_forall_exists_eq_add`), which is the hypothesis of the two-chart Čech criterion
`toQuotFamilies_surjective_of_two_affineOpens`.

Source: Stacks 0AGS(3) / 0AGT proof, second paragraph, in the Čech form of
`blowup_regularLocalRing_dimTwo_toQuotFamilies_surjective`; Hartshorne III.4 (Čech cohomology of a
two-element affine cover).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace HomogeneousLocalization
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Proj

variable {σ : Type*} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable {X : AlgebraicGeometry.Scheme.{u}} (ι : Proj 𝒜 ⟶ X) [IsOpenImmersion ι]

/-- `𝒜_{(f)} → Γ(X, ι(D₊(f)))`: Mathlib's `awayToSection` followed by the open-immersion isomorphism
`ι.appIso`. -/
def awaySectionsHom (f : A) : Away 𝒜 f →+* Γ(X, ι ''ᵁ basicOpen 𝒜 f) :=
  (awayToSection 𝒜 f ≫ (ι.appIso (basicOpen 𝒜 f)).inv).hom

/-- `awaySectionsHom` is bijective for `f` homogeneous of positive degree (`basicOpenIsoAway`). -/
theorem awaySectionsHom_bijective {d : ℕ} {f : A} (hf : f ∈ 𝒜 d) (hd : 0 < d) :
    Function.Bijective (awaySectionsHom 𝒜 ι f) := by
  have : IsIso (awayToSection 𝒜 f) := by
    rw [← basicOpenIsoAway_hom 𝒜 f hf hd]; infer_instance
  exact ConcreteCategory.bijective_of_isIso (awayToSection 𝒜 f ≫ (ι.appIso (basicOpen 𝒜 f)).inv)

/-- Restriction along `ι(D₊(x)) ⊆ ι(D₊(f))`, `x = f g`, is `awayMap : 𝒜_{(f)} → 𝒜_{(x)}` under
`awaySectionsHom` (Mathlib's `awayMap_awayToSection` transported along `ι.appIso_inv_naturality`). -/
theorem presheaf_map_awaySectionsHom {e : ℕ} {f g x : A} (hg : g ∈ 𝒜 e) (hx : x = f * g)
    (h : ι ''ᵁ basicOpen 𝒜 x ≤ ι ''ᵁ basicOpen 𝒜 f) (z : Away 𝒜 f) :
    (X.presheaf.map (homOfLE h).op).hom (awaySectionsHom 𝒜 ι f z) =
      awaySectionsHom 𝒜 ι x (awayMap 𝒜 hg hx z) := by
  have h1 := congrArg (fun φ => φ.hom z) (awayMap_awayToSection 𝒜 hg hx)
  have h2 := congrArg (fun φ => φ.hom ((awayToSection 𝒜 f).hom z))
    (ι.appIso_inv_naturality (homOfLE (basicOpen_mono 𝒜 f x ⟨g, hx⟩)).op)
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h1 h2
  show (X.presheaf.map (homOfLE h).op).hom ((ι.appIso _).inv.hom ((awayToSection 𝒜 f).hom z)) =
    (ι.appIso _).inv.hom ((awayToSection 𝒜 x).hom (awayMap 𝒜 hg hx z))
  rw [h1, h2]
  rfl

/-- The chart `ι(D₊(f))` as an affine open of `X` (`f` homogeneous of positive degree). Reducible, so
that `rw` sees through it. -/
abbrev imageBasicOpen {d : ℕ} {f : A} (hf : f ∈ 𝒜 d) (hd : 0 < d) : X.affineOpens :=
  ⟨ι ''ᵁ basicOpen 𝒜 f, (isAffineOpen_basicOpen 𝒜 f hf hd).image_of_isOpenImmersion ι⟩

end AlgebraicGeometry.Proj

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {σ : Type*} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- **Two-chart Čech criterion on a scheme covered by `Proj 𝒜`.** `ι : Proj 𝒜 ⟶ X` an open immersion
onto `X`, `D₊(f) ∪ D₊(g) = Proj 𝒜` (`f ∈ 𝒜 d`, `g ∈ 𝒜 e`, `d, e > 0`), `K(V) = I₁·Γ(X, V)` for every
affine `V`, and `𝒜_{(f)} = 𝒜₀[gᵈ/fᵉ]`. Then `Γ(X, O_X) → Γ(X, O_X/K)` is surjective. -/
theorem toQuotFamilies_surjective_of_proj_two_charts {X : AlgebraicGeometry.Scheme.{u}}
    (K : X.IdealSheafData) (I₁ : Ideal Γ(X, ⊤))
    (hK : ∀ V : X.affineOpens, K.ideal V = I₁.map (X.presheaf.map (homOfLE le_top).op).hom)
    (ι : Proj 𝒜 ⟶ X) [IsOpenImmersion ι] (hι : ι.opensRange = ⊤)
    {d e : ℕ} {f g : A} (hf : f ∈ 𝒜 d) (hg : g ∈ 𝒜 e) (hd : 0 < d) (he : 0 < e)
    (hcov : Proj.basicOpen 𝒜 f ⊔ Proj.basicOpen 𝒜 g = ⊤)
    (hgen : ∀ b : Away 𝒜 f, ∃ p : Polynomial (𝒜 0),
      p.eval₂ (fromZeroRingHom 𝒜 (Submonoid.powers f)) (Away.isLocalizationElem hf hg) = b) :
    Function.Surjective K.toQuotFamilies := by
  have hx : f * g = f * g := rfl
  have hfg : f * g ∈ 𝒜 (d + e) := SetLike.mul_mem_graded hf hg
  have hde : 0 < d + e := Nat.add_pos_left hd e
  -- the two charts and their intersection, all affine (reducible abbreviations)
  have h₁ : Proj.imageBasicOpen 𝒜 ι hfg hde ≤ Proj.imageBasicOpen 𝒜 ι hf hd :=
    ι.image_mono (Proj.basicOpen_mono 𝒜 f (f * g) ⟨g, hx⟩)
  have h₂ : Proj.imageBasicOpen 𝒜 ι hfg hde ≤ Proj.imageBasicOpen 𝒜 ι hg he :=
    ι.image_mono (Proj.basicOpen_mono 𝒜 g (f * g) ⟨f, mul_comm f g⟩)
  have hinf : (Proj.imageBasicOpen 𝒜 ι hf hd).1 ⊓ (Proj.imageBasicOpen 𝒜 ι hg he).1 ≤
      (Proj.imageBasicOpen 𝒜 ι hfg hde).1 := by
    rintro p ⟨⟨q₁, hq₁, rfl⟩, ⟨q₂, hq₂, hq⟩⟩
    obtain rfl : q₂ = q₁ := ι.isOpenEmbedding.injective hq
    refine ⟨q₂, ?_, rfl⟩
    rw [Proj.basicOpen_mul]
    exact ⟨hq₁, hq₂⟩
  have hcov' : (Proj.imageBasicOpen 𝒜 ι hf hd).1 ⊔ (Proj.imageBasicOpen 𝒜 ι hg he).1 = ⊤ := by
    have himg := ι.image_iSup (fun c : Bool => cond c (Proj.basicOpen 𝒜 f) (Proj.basicOpen 𝒜 g))
    simp only [iSup_bool_eq, Bool.cond_true, Bool.cond_false, hcov,
      Scheme.Hom.image_top_eq_opensRange, hι] at himg
    exact himg.symm
  -- Laurent splitting on the sections rings: `Γ(U₁₂) = res Γ(U₁) + res Γ(U₂)`
  have hsum : ∀ w : Γ(X, Proj.imageBasicOpen 𝒜 ι hfg hde),
      ∃ (b₁ : Γ(X, Proj.imageBasicOpen 𝒜 ι hf hd)) (b₂ : Γ(X, Proj.imageBasicOpen 𝒜 ι hg he)),
      w = (X.presheaf.map (homOfLE h₁).op).hom b₁ + (X.presheaf.map (homOfLE h₂).op).hom b₂ := by
    intro w
    obtain ⟨w', rfl⟩ := (Proj.awaySectionsHom_bijective 𝒜 ι hfg hde).2 w
    obtain ⟨b₁, b₂, hw⟩ :=
      MiyaokaMori.LaurentSplitting.exists_eq_add_of_localization_of_eval₂_surjective
        (fromZeroRingHom 𝒜 (Submonoid.powers f)) (fromZeroRingHom 𝒜 (Submonoid.powers g))
        (awayMap 𝒜 hg hx) (awayMap 𝒜 hf (hx.trans (mul_comm f g)))
        (RingHom.ext fun a => by simp only [RingHom.comp_apply, awayMap_fromZeroRingHom])
        (Away.isLocalizationElem hf hg) (Away.isLocalizationElem hg hf)
        (awayMap_isLocalizationElem_mul_awayMap_isLocalizationElem hf hg hx)
        hgen (exists_mul_awayMap_isLocalizationElem_pow_eq hf hg hx hd.ne') w'
    refine ⟨Proj.awaySectionsHom 𝒜 ι f b₁, Proj.awaySectionsHom 𝒜 ι g b₂, ?_⟩
    have hb₁ := Proj.presheaf_map_awaySectionsHom 𝒜 ι hg hx h₁ b₁
    have hb₂ := Proj.presheaf_map_awaySectionsHom 𝒜 ι hf (hx.trans (mul_comm f g)) h₂ b₂
    refine (congrArg _ hw).trans ?_
    rw [map_add, ← hb₁, ← hb₂]
    rfl
  -- the Čech criterion
  refine K.toQuotFamilies_surjective_of_two_affineOpens (Proj.imageBasicOpen 𝒜 ι hf hd)
    (Proj.imageBasicOpen 𝒜 ι hg he) (Proj.imageBasicOpen 𝒜 ι hfg hde) h₁ h₂ hinf hcov' ?_
  intro z hz
  have e₁ : ((X.presheaf.map (homOfLE h₁).op).hom).comp
      (X.presheaf.map (homOfLE (le_top : (Proj.imageBasicOpen 𝒜 ι hf hd).1 ≤ ⊤)).op).hom =
      (X.presheaf.map (homOfLE (le_top : (Proj.imageBasicOpen 𝒜 ι hfg hde).1 ≤ ⊤)).op).hom := by
    rw [← CommRingCat.hom_comp, ← Functor.map_comp]; rfl
  have e₂ : ((X.presheaf.map (homOfLE h₂).op).hom).comp
      (X.presheaf.map (homOfLE (le_top : (Proj.imageBasicOpen 𝒜 ι hg he).1 ≤ ⊤)).op).hom =
      (X.presheaf.map (homOfLE (le_top : (Proj.imageBasicOpen 𝒜 ι hfg hde).1 ≤ ⊤)).op).hom := by
    rw [← CommRingCat.hom_comp, ← Functor.map_comp]; rfl
  rw [hK, ← e₁] at hz
  obtain ⟨c₁, hc₁, c₂, hc₂, hz'⟩ :=
    MiyaokaMori.LaurentSplitting.exists_mem_map_add_of_forall_exists_eq_add
      (X.presheaf.map (homOfLE (le_top : (Proj.imageBasicOpen 𝒜 ι hf hd).1 ≤ ⊤)).op).hom
      (X.presheaf.map (homOfLE (le_top : (Proj.imageBasicOpen 𝒜 ι hg he).1 ≤ ⊤)).op).hom
      (X.presheaf.map (homOfLE h₁).op).hom (X.presheaf.map (homOfLE h₂).op).hom
      (e₁.trans e₂.symm) hsum I₁ z hz
  exact ⟨c₁, (hK _).symm ▸ hc₁, c₂, (hK _).symm ▸ hc₂, hz'⟩

end AlgebraicGeometry.Scheme.IdealSheafData

end
