import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S2WeightedJets.Jets.BasedJetAsSectionFiber
import MiyaokaMori.Paper.S2WeightedJets.Jets.BasedJetOpenRestriction
import MiyaokaMori.Paper.S2WeightedJets.Charts.EtaleBaseChangeJets
import MiyaokaMori.Paper.S2WeightedJets.Charts.JetOfAffineSpace
import MiyaokaMori.Paper.S2WeightedJets.Jets.RelativeJetScheme

/-! # Local coordinates on based jets through an étale chart

An étale chart identifies the jets based at the section, near the section, with the jets of affine
space based at the zero section, and the resulting isomorphism is compatible with the morphisms to
the base.

Source: §2.2 of the paper ("local coordinates on the based jet space", eq. (2.5));
Ein–Mustaţă, *Jet schemes and singularities*, Lemma 2.3, Lemma 2.9, Remark 2.6.

Proof (the top level `relativeJetScheme_etale_chart` is assembled from three lemmas):
1. `relativeJetScheme_restrict_open_over`: based jets near the section restrict to the domain of the
   chart, and the isomorphism lies over `U`; this is `relativeJetScheme.restrict_open_exists_over`
   (Yoneda in `Over U`: `restrictRepresentableBy` + `representableBy` + `uniqueUpToIso`; the jets
   pass through `V` by `jetConstantTerm_surjective`).
2. `relativeJetScheme_etale_based_isPullback`: based jets are the fiber of the unbased jets along the
   section (`relativeJetScheme_isPullback_unbased`); paste with the étale base change of unbased jets
   (`jetScheme_etale_base_change`) by `IsPullback.paste_horiz`, then use `s ≫ φ = 0` to write both
   sides as pullbacks of the same cospan `(jetScheme.proj r (𝔸 ↘ U), 0-section)`;
   `IsPullback.isoIsPullback` gives the isomorphism and `IsPullback.of_horiz_isIso` the pullback
   square along `𝟙 U`.
3. `relativeJetScheme_etale_based_coordinates`: identify the jets of affine space based at the zero
   section with `jetScheme_affineSpace_underlying` and glue the projection equations.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.style.haveILetI false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- **Based jets only see a neighbourhood of the section, over the base** (Ein–Mustaţă, Lemma 2.3 in
its relative, section-based form; §2.2 of the paper: every based jet factors through `𝒵^×`, since its
restriction to `t = 0` is the seed section `s` and a nilpotent thickening does not change the
underlying topological space).

Statement. `J := relativeJetScheme Z s hs r` is the based jet scheme of `Z/C` along `s`, a scheme over `C`.
For `U ⊆ C` open and `V ⊆ Z` open with `s(U) ⊆ V ⊆ π⁻¹U` (and `V → U` affine), the open subscheme
`J.hom ⁻¹ᵁ U` of `J` is isomorphic, **as a scheme over `U`**, to the based jet scheme `J_U` of `V/U` along
`s|_U`. The equation `e.hom ≫ J_U.hom = J.hom ∣_ U` is the compatibility with the structure maps to `U`.
Proof: this is `relativeJetScheme.restrict_open_exists_over`, which
proves it by Yoneda in `Over U`: the open piece `J.hom ⁻¹ᵁ U` represents the based jet functor of `V/U`
(`relativeJetScheme.restrictRepresentableBy`; a based jet over `U` lands in `V` because the constant-term
section is surjective on points, `jetConstantTerm_surjective`), and so does `J_U`
(`relativeJetScheme.representableBy`), hence `Functor.RepresentableBy.uniqueUpToIso` gives an iso over `U`. -/
theorem relativeJetScheme_restrict_open_over {k : Type u} [Field k]
    {C : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (Z : CategoryTheory.Over C) [AlgebraicGeometry.IsAffineHom Z.hom]
    (s : C ⟶ Z.left) (hs : s ≫ Z.hom = CategoryTheory.CategoryStruct.id C)
    (r : ℕ) (U : C.Opens) (V : Z.left.Opens)
    (hsV : U ≤ s ⁻¹ᵁ V) (hVU : V ≤ Z.hom ⁻¹ᵁ U)
    [AlgebraicGeometry.IsAffineHom (Z.hom.resLE U V hVU)] :
    letI : U.toScheme.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨U.ι ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    letI : AlgebraicGeometry.IsAffineHom
        (CategoryTheory.Over.mk (Z.hom.resLE U V hVU)).hom :=
      inferInstanceAs (AlgebraicGeometry.IsAffineHom (Z.hom.resLE U V hVU))
    ∃ e : ((relativeJetScheme (k := k) Z s hs r).hom ⁻¹ᵁ U).toScheme ≅
        (relativeJetScheme (k := k)
          (CategoryTheory.Over.mk (Z.hom.resLE U V hVU))
          (s.resLE V U hsV)
          (relativeJetScheme.restrict_section_over (k := k) Z s hs U V hsV hVU) r).left,
      e.hom ≫ (relativeJetScheme (k := k)
          (CategoryTheory.Over.mk (Z.hom.resLE U V hVU))
          (s.resLE V U hsV)
          (relativeJetScheme.restrict_section_over (k := k) Z s hs U V hsV hVU) r).hom =
        (relativeJetScheme (k := k) Z s hs r).hom ∣_ U := by
  letI : U.toScheme.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨U.ι ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  letI : AlgebraicGeometry.IsAffineHom
      (CategoryTheory.Over.mk (Z.hom.resLE U V hVU)).hom :=
    inferInstanceAs (AlgebraicGeometry.IsAffineHom (Z.hom.resLE U V hVU))
  exact relativeJetScheme.restrict_open_exists_over k Z s hs r U V hsV hVU

/-- **Étale base change for based jets** (Ein–Mustaţă, Lemma 2.9 restricted to jets based at the
section; §2.2 of the paper): if `φ : V → 𝔸^m_U` is étale over `U` and sends the section `s`
to the zero section, then the based jet scheme of `V/U` along `s` is the based jet scheme of `𝔸^m_U/U`
along the zero section, compatibly with the structure maps to `U` (stated as a pullback square along `𝟙 U`).

Proof: `J^s(V/U) = U ×_V J(V/U)` (`relativeJetScheme_isPullback_unbased`), `J(V/U) = V ×_{𝔸} J(𝔸/U)`
(`jetScheme_etale_base_change`); pasting gives `J^s(V/U) = U ×_{𝔸} J(𝔸/U)` along `s ≫ φ = 0`, which is
also `J^0(𝔸/U)` by `relativeJetScheme_isPullback_unbased` for the zero section. Two pullbacks of one
cospan are isomorphic (`IsPullback.isoIsPullback`), and an iso commuting with the maps to `U` is a
pullback square along `𝟙 U` (`IsPullback.of_horiz_isIso`). -/
theorem relativeJetScheme_etale_based_isPullback {k : Type u} [Field k]
    {U V : AlgebraicGeometry.Scheme.{u}}
    [U.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (p : V ⟶ U) [AlgebraicGeometry.IsAffineHom p]
    (s : U ⟶ V) (hs : s ≫ p = CategoryTheory.CategoryStruct.id U)
    (m r : ℕ)
    (φ : V ⟶ AlgebraicGeometry.AffineSpace (ULift.{u} (Fin m)) U)
    (hφ_over : φ ≫
        (AlgebraicGeometry.AffineSpace (ULift.{u} (Fin m)) U ↘ U) = p)
    [AlgebraicGeometry.Etale φ]
    (hφ_s : s ≫ φ = AlgebraicGeometry.AffineSpace.homOfVector
      (CategoryTheory.CategoryStruct.id U) 0) :
    letI : AlgebraicGeometry.IsAffineHom (CategoryTheory.Over.mk p).hom :=
      inferInstanceAs (AlgebraicGeometry.IsAffineHom p)
    letI : AlgebraicGeometry.IsAffineHom
        (CategoryTheory.Over.mk
          (AlgebraicGeometry.AffineSpace (ULift.{u} (Fin m)) U ↘ U)).hom :=
      inferInstanceAs (AlgebraicGeometry.IsAffineHom
        (AlgebraicGeometry.AffineSpace (ULift.{u} (Fin m)) U ↘ U))
    ∃ f : (relativeJetScheme (k := k) (CategoryTheory.Over.mk p) s hs r).left ⟶
        (relativeJetScheme (k := k)
          (CategoryTheory.Over.mk
            (AlgebraicGeometry.AffineSpace (ULift.{u} (Fin m)) U ↘ U))
          (AlgebraicGeometry.AffineSpace.homOfVector
            (CategoryTheory.CategoryStruct.id U) 0) (by simp) r).left,
      CategoryTheory.IsPullback f
        (relativeJetScheme (k := k) (CategoryTheory.Over.mk p) s hs r).hom
        (relativeJetScheme (k := k)
          (CategoryTheory.Over.mk
            (AlgebraicGeometry.AffineSpace (ULift.{u} (Fin m)) U ↘ U))
          (AlgebraicGeometry.AffineSpace.homOfVector
            (CategoryTheory.CategoryStruct.id U) 0) (by simp) r).hom
        (CategoryTheory.CategoryStruct.id U) := by
  letI : AlgebraicGeometry.IsAffineHom (CategoryTheory.Over.mk p).hom :=
    inferInstanceAs (AlgebraicGeometry.IsAffineHom p)
  letI : AlgebraicGeometry.IsAffineHom
      (CategoryTheory.Over.mk
        (AlgebraicGeometry.AffineSpace (ULift.{u} (Fin m)) U ↘ U)).hom :=
    inferInstanceAs (AlgebraicGeometry.IsAffineHom
      (AlgebraicGeometry.AffineSpace (ULift.{u} (Fin m)) U ↘ U))
  -- based jets of `V` along `s` = fibre of the unbased jets over `s`
  have hV := relativeJetScheme_isPullback_unbased (k := k) (CategoryTheory.Over.mk p) s hs r
  -- étale base change for the unbased jets along `φ`
  have hE : CategoryTheory.IsPullback (jetScheme.map (k := k) r φ hφ_over)
      (jetScheme.proj (k := k) r (CategoryTheory.Over.mk p).hom)
      (jetScheme.proj (k := k) r
        (AlgebraicGeometry.AffineSpace (ULift.{u} (Fin m)) U ↘ U)) φ :=
    jetScheme_etale_base_change (k := k) p
      (AlgebraicGeometry.AffineSpace (ULift.{u} (Fin m)) U ↘ U) φ hφ_over r
  -- paste: `J^s(V/U) = U ×_{𝔸} J(𝔸/U)` along `s ≫ φ = 0`
  have hVA := hV.paste_horiz hE
  rw [hφ_s] at hVA
  -- based jets of `𝔸` along the zero section = the same fibre product
  have hA := relativeJetScheme_isPullback_unbased (k := k)
    (CategoryTheory.Over.mk (AlgebraicGeometry.AffineSpace (ULift.{u} (Fin m)) U ↘ U))
    (AlgebraicGeometry.AffineSpace.homOfVector (CategoryTheory.CategoryStruct.id U) 0)
    (by simp) r
  refine ⟨(hVA.isoIsPullback _ _ hA).hom, ?_⟩
  refine CategoryTheory.IsPullback.of_horiz_isIso ⟨?_⟩
  rw [CategoryTheory.Category.comp_id]
  exact hVA.isoIsPullback_hom_snd _ _ hA

/-- Local coordinates on based jets of `V/U` through an étale chart: `J^s(V/U) ≅ 𝔸^{m·r}_U` over `U`
(§2.2 of the paper). Combines `relativeJetScheme_etale_based_isPullback`
with `jetScheme_affineSpace_underlying`. -/
theorem relativeJetScheme_etale_based_coordinates {k : Type u} [Field k]
    {U V : AlgebraicGeometry.Scheme.{u}}
    [U.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (p : V ⟶ U) [AlgebraicGeometry.IsAffineHom p]
    (s : U ⟶ V) (hs : s ≫ p = CategoryTheory.CategoryStruct.id U)
    (m r : ℕ)
    (φ : V ⟶ AlgebraicGeometry.AffineSpace (ULift.{u} (Fin m)) U)
    (hφ_over : φ ≫
        (AlgebraicGeometry.AffineSpace (ULift.{u} (Fin m)) U ↘ U) = p)
    [AlgebraicGeometry.Etale φ]
    (hφ_s : s ≫ φ = AlgebraicGeometry.AffineSpace.homOfVector
      (CategoryTheory.CategoryStruct.id U) 0) :
    letI : AlgebraicGeometry.IsAffineHom (CategoryTheory.Over.mk p).hom :=
      inferInstanceAs (AlgebraicGeometry.IsAffineHom p)
    ∃ e : (relativeJetScheme (k := k) (CategoryTheory.Over.mk p) s hs r).left ≅
        AlgebraicGeometry.AffineSpace (ULift.{u} (Fin m × Fin r)) U,
      e.hom ≫
          (AlgebraicGeometry.AffineSpace (ULift.{u} (Fin m × Fin r)) U ↘ U) =
        (relativeJetScheme (k := k) (CategoryTheory.Over.mk p) s hs r).hom := by
  letI : AlgebraicGeometry.IsAffineHom
      (CategoryTheory.Over.mk
        (AlgebraicGeometry.AffineSpace (ULift.{u} (Fin m)) U ↘ U)).hom :=
    inferInstanceAs (AlgebraicGeometry.IsAffineHom
      (AlgebraicGeometry.AffineSpace (ULift.{u} (Fin m)) U ↘ U))
  obtain ⟨f, hf⟩ := relativeJetScheme_etale_based_isPullback
    (k := k) p s hs m r φ hφ_over hφ_s
  letI : CategoryTheory.IsIso f := hf.isIso_fst_of_isIso
  obtain ⟨e, he⟩ := jetScheme_affineSpace_underlying (k := k) (U := U) m r
  refine ⟨(CategoryTheory.asIso f).trans e, ?_⟩
  rw [CategoryTheory.Iso.trans_hom, CategoryTheory.Category.assoc, he]
  change f ≫ _ = _
  simpa using hf.w

/-- **Local coordinates on the based jet space** (eq. (2.5) of the paper):
on an open `U ⊆ C` carrying an étale chart `φ : V → 𝔸^m_U` (with `s(U) ⊆ V ⊆ π⁻¹U`, `φ` sending `s` to
the zero section), the based jet scheme `J^s_r(Z/C)` restricted to `U` is `𝔸^{m·r}_U`, compatibly with
the projections to `U`. Assembled from `relativeJetScheme_restrict_open_over` and
`relativeJetScheme_etale_based_coordinates`. -/
theorem relativeJetScheme_etale_chart {k : Type u} [Field k]
    {C : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (Z : CategoryTheory.Over C) [AlgebraicGeometry.IsAffineHom Z.hom]
    (s : C ⟶ Z.left)
    (hs : s ≫ Z.hom = CategoryTheory.CategoryStruct.id C)
    [AlgebraicGeometry.IsClosedImmersion s]
    (U : C.Opens) (V : Z.left.Opens)
    (hsV : U ≤ s ⁻¹ᵁ V) (hVU : V ≤ Z.hom ⁻¹ᵁ U)
    (m r : ℕ)
    [AlgebraicGeometry.IsAffineHom (Z.hom.resLE U V hVU)]
    (φ : V.toScheme ⟶
      AlgebraicGeometry.AffineSpace (ULift.{u} (Fin m)) U.toScheme)
    (hφ_over : φ ≫
        (AlgebraicGeometry.AffineSpace (ULift.{u} (Fin m)) U.toScheme ↘ U.toScheme) =
      Z.hom.resLE U V hVU)
    [AlgebraicGeometry.Etale φ]
    (hφ_s : s.resLE V U hsV ≫ φ =
      AlgebraicGeometry.AffineSpace.homOfVector
        (CategoryTheory.CategoryStruct.id U.toScheme) 0) :
    ∃ e : ((relativeJetScheme (k := k) Z s hs r).hom ⁻¹ᵁ U).toScheme ≅
        AlgebraicGeometry.AffineSpace (ULift.{u} (Fin m × Fin r)) U.toScheme,
      e.hom ≫
          (AlgebraicGeometry.AffineSpace
            (ULift.{u} (Fin m × Fin r)) U.toScheme ↘ U.toScheme) =
        (relativeJetScheme (k := k) Z s hs r).hom ∣_ U := by
  letI : U.toScheme.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨U.ι ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  obtain ⟨e₁, he₁⟩ := relativeJetScheme_restrict_open_over
    (k := k) Z s hs r U V hsV hVU
  obtain ⟨e₂, he₂⟩ := relativeJetScheme_etale_based_coordinates
    (k := k) (Z.hom.resLE U V hVU) (s.resLE V U hsV)
      (relativeJetScheme.restrict_section_over (k := k) Z s hs U V hsV hVU)
      m r φ hφ_over hφ_s
  refine ⟨e₁.trans e₂, ?_⟩
  rw [CategoryTheory.Iso.trans_hom, CategoryTheory.Category.assoc, he₂, he₁]

end
