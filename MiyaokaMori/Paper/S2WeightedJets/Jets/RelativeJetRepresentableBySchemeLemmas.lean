import MiyaokaMori.Prelude

/-! # Scheme-theoretic lemmas for the representability of the relative jet functor

General scheme-theoretic lemmas used to prove the proof obligations of `relativeJetScheme.representableBy`
(§2 of the paper, the based jet scheme `J_r^s(Z/C)`; the gluing is Ein–Mustață Prop. 2.2 and Lemma 2.3 in
relative form).
Nothing here mentions jets; everything is about open immersions from affine schemes, `Spec`, `Γ` and
locally directed covers.

* `Opens.SpecMap_ext`: two ring maps `R ⟶ Γ(X, V)` agree as soon as `V.toSpecΓ ≫ Spec.map -` agree.
* `chartSec j` for an open immersion `j : Spec R ⟶ J`: the identification `R ⟶ Γ(J, j.opensRange)`
  (this is the composite used by `relativeJetScheme.chartSections`), characterised by
  `j.opensRange.toSpecΓ ≫ Spec.map (chartSec j) = j.isoOpensRange.inv` (`opensRange_toSpecΓ_SpecMap_chartSec`),
  its naturality along `Spec.map σ ≫ j = j'` (`chartSec_comp_map`), and the computation of
  `g^♯` on a chart in terms of a factorisation `V.ι ≫ g = V.toSpecΓ ≫ Spec.map σ ≫ j` (`chartSec_appLE_of_ι_comp`).
* `Hom.ι_comp_eq_toSpecΓ_SpecMap_appLE_fromSpec`, `Hom.appLE_eq_of_ι_comp_fromSpec`: a morphism into an affine
  open `Spec Γ(Z, U) ≅ U ⊆ Z` restricted to `V` is `V.toSpecΓ ≫ Spec.map (g^♯) ≫ fromSpec`, and conversely
  such a factorisation determines `g^♯`.
* `affinePreimageCover.locallyDirected`, `affinePreimageCover.glue_compat`: the cover of `X` by the preimages
  `g⁻¹U` of the affine opens `U` of `C` (indexed by `C.AffineZariskiSite`, arrows = basic opens) is locally
  directed with transition maps `X.homOfLE`, so a family of morphisms out of the `g⁻¹U` compatible with
  restriction is compatible on all pairwise intersections (the hypothesis of `Scheme.Cover.glueMorphisms`).
  This is Mathlib's `Scheme.OpenCover.glueMorphismsOfLocallyDirected` argument, and the directedness proof is
  the one of Mathlib's instance `(Scheme.AffineZariskiSite.directedCover X).LocallyDirected`, pulled back along `g`.

Source: Stacks 01JJ (gluing morphisms), Mathlib `Mathlib/AlgebraicGeometry/Cover/Directed.lean`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme

/-- Two ring maps `R ⟶ Γ(X, V)` are equal once `V.toSpecΓ ≫ Spec.map -` are equal:
take global sections, `V.toSpecΓ.appTop = ΓSpecIso.hom ≫ topIso.inv` is an isomorphism, and
`ΓSpecIso` is natural. -/
theorem Opens.SpecMap_ext {X : Scheme.{u}} (V : X.Opens) {R : CommRingCat.{u}}
    (τ₁ τ₂ : R ⟶ Γ(X, V))
    (h : V.toSpecΓ ≫ Spec.map τ₁ = V.toSpecΓ ≫ Spec.map τ₂) : τ₁ = τ₂ := by
  have h3 := congrArg (fun φ : V.toScheme ⟶ Spec R => φ.appTop) h
  simp only [Scheme.Hom.comp_appTop, Scheme.Opens.toSpecΓ_appTop] at h3
  rw [← Category.assoc, ← Category.assoc, cancel_mono, ΓSpecIso_naturality, ΓSpecIso_naturality,
    cancel_epi] at h3
  exact h3

/-- For an open immersion `j : Spec R ⟶ J`, the identification `R ⟶ Γ(J, j.opensRange)`:
`R ≅ Γ(Spec R, ⊤) ≅ Γ(j.opensRange, ⊤) ≅ Γ(J, j.opensRange)`. -/
def chartSec {J : Scheme.{u}} {R : CommRingCat.{u}} (j : Spec R ⟶ J) [IsOpenImmersion j] :
    R ⟶ Γ(J, j.opensRange) :=
  (ΓSpecIso R).inv ≫ j.isoOpensRange.inv.appTop ≫ j.opensRange.topIso.hom

/-- Characterisation of `chartSec`: `j.opensRange.toSpecΓ ≫ Spec.map (chartSec j) = j.isoOpensRange.inv`. -/
theorem opensRange_toSpecΓ_SpecMap_chartSec {J : Scheme.{u}} {R : CommRingCat.{u}}
    (j : Spec R ⟶ J) [IsOpenImmersion j] :
    j.opensRange.toSpecΓ ≫ Spec.map (chartSec j) = j.isoOpensRange.inv := by
  unfold chartSec Scheme.Opens.toSpecΓ
  simp only [Spec.map_comp, Category.assoc]
  rw [← Category.assoc (Spec.map _) (Spec.map _), ← Spec.map_comp, Iso.hom_inv_id, Spec.map_id,
    Category.id_comp, ← toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

/-- `j.opensRange.toSpecΓ ≫ Spec.map (chartSec j) ≫ j = j.opensRange.ι`. -/
theorem opensRange_toSpecΓ_SpecMap_chartSec_comp {J : Scheme.{u}} {R : CommRingCat.{u}}
    (j : Spec R ⟶ J) [IsOpenImmersion j] :
    j.opensRange.toSpecΓ ≫ Spec.map (chartSec j) ≫ j = j.opensRange.ι := by
  rw [← Category.assoc, opensRange_toSpecΓ_SpecMap_chartSec, Scheme.Hom.isoOpensRange_inv_comp]

/-- Naturality of `chartSec`: if `j' = Spec.map σ ≫ j` then restricting `chartSec j` to the
smaller chart is `σ` followed by `chartSec j'`. -/
theorem chartSec_comp_map {J : Scheme.{u}} {R R' : CommRingCat.{u}}
    (j : Spec R ⟶ J) [IsOpenImmersion j] (j' : Spec R' ⟶ J) [IsOpenImmersion j']
    (σ : R ⟶ R') (hσ : Spec.map σ ≫ j = j') (hle : j'.opensRange ≤ j.opensRange) :
    chartSec j ≫ J.presheaf.map (homOfLE hle).op = σ ≫ chartSec j' := by
  apply Opens.SpecMap_ext j'.opensRange
  rw [Spec.map_comp, Spec.map_comp, ← Category.assoc, Scheme.Opens.toSpecΓ_SpecMap_presheaf_map,
    Category.assoc, opensRange_toSpecΓ_SpecMap_chartSec, ← Category.assoc,
    opensRange_toSpecΓ_SpecMap_chartSec, ← cancel_mono j, Category.assoc,
    Scheme.Hom.isoOpensRange_inv_comp, Scheme.homOfLE_ι, Category.assoc, hσ,
    Scheme.Hom.isoOpensRange_inv_comp]

/-- If `g : W ⟶ J` restricted to `V` factors through the chart `j` as `V.toSpecΓ ≫ Spec.map σ ≫ j`,
then `g^♯` on the chart, read through `chartSec j`, is `σ`. -/
theorem chartSec_appLE_of_ι_comp {W J : Scheme.{u}} (V : W.Opens) {R : CommRingCat.{u}}
    (j : Spec R ⟶ J) [IsOpenImmersion j] (g : W ⟶ J) (σ : R ⟶ Γ(W, V))
    (hfac : V.ι ≫ g = V.toSpecΓ ≫ Spec.map σ ≫ j)
    (hle : V ≤ g ⁻¹ᵁ j.opensRange) :
    chartSec j ≫ g.appLE j.opensRange V hle = σ := by
  apply Opens.SpecMap_ext V
  rw [Spec.map_comp, ← Category.assoc, Scheme.Opens.toSpecΓ_SpecMap_appLE, Category.assoc,
    opensRange_toSpecΓ_SpecMap_chartSec, ← cancel_mono j, Category.assoc,
    Scheme.Hom.isoOpensRange_inv_comp, Scheme.Hom.resLE_comp_ι, hfac, Category.assoc]

/-- A morphism into `Z` restricted to `V ⊆ g⁻¹U`, `U ⊆ Z` affine, factors through `Spec Γ(Z, U)`
via its own `appLE`. -/
theorem Hom.ι_comp_eq_toSpecΓ_SpecMap_appLE_fromSpec {Y Z : Scheme.{u}} (V : Y.Opens)
    {ZU : Z.Opens} (hU : IsAffineOpen ZU) (g : Y ⟶ Z) (hle : V ≤ g ⁻¹ᵁ ZU) :
    V.ι ≫ g = V.toSpecΓ ≫ Spec.map (g.appLE ZU V hle) ≫ hU.fromSpec := by
  rw [← Category.assoc, Scheme.Opens.toSpecΓ_SpecMap_appLE, Category.assoc,
    IsAffineOpen.toSpecΓ_fromSpec, Scheme.Hom.resLE_comp_ι]

/-- Conversely a factorisation `V.ι ≫ g = V.toSpecΓ ≫ Spec.map σ ≫ fromSpec` determines `g^♯ = σ`. -/
theorem Hom.appLE_eq_of_ι_comp_fromSpec {Y Z : Scheme.{u}} (V : Y.Opens)
    {ZU : Z.Opens} (hU : IsAffineOpen ZU) (g : Y ⟶ Z) (σ : Γ(Z, ZU) ⟶ Γ(Y, V))
    (hfac : V.ι ≫ g = V.toSpecΓ ≫ Spec.map σ ≫ hU.fromSpec)
    (hle : V ≤ g ⁻¹ᵁ ZU) :
    g.appLE ZU V hle = σ := by
  apply Opens.SpecMap_ext V
  have h := (Hom.ι_comp_eq_toSpecΓ_SpecMap_appLE_fromSpec V hU g hle).symm.trans hfac
  rw [← Category.assoc, ← Category.assoc, cancel_mono] at h
  exact h

/-! ## The cover of `X` by the preimages of the affine opens of `C` -/

namespace affinePreimageCover

variable {X C : Scheme.{u}} (g : X ⟶ C) (V : C.AffineZariskiSite → X.Opens)
  (hV : ∀ U, V U = g ⁻¹ᵁ U.1)

include hV in
/-- An arrow `U' ⟶ U` of `C.AffineZariskiSite` (`U'` a basic open of `U`) gives `V U' ≤ V U`. -/
theorem le_of_hom {U U' : C.AffineZariskiSite} (f : U' ⟶ U) : V U' ≤ V U := by
  rw [hV, hV]
  exact (Opens.map g.base).monotone (Scheme.AffineZariskiSite.toOpens_mono f.le)

/-- Directedness of the preimage cover: a point of `g⁻¹U ×_X g⁻¹U'` lies over a point of `U ∩ U'`, which has a
neighbourhood that is a basic open of both `U` and `U'` (`exists_basicOpen_le_affine_inter`, as in Mathlib's
`(directedCover X).LocallyDirected`). -/
theorem directed_aux (U U' : C.AffineZariskiSite) (x : ↑(pullback (V U).ι (V U').ι)) :
    ∃ (k : C.AffineZariskiSite) (hki : k ⟶ U) (hkj : k ⟶ U') (y : (V k).toScheme),
      pullback.lift (X.homOfLE (le_of_hom g V hV hki)) (X.homOfLE (le_of_hom g V hV hkj))
        (by rw [X.homOfLE_ι, X.homOfLE_ι]) y = x := by
  let a : X := (pullback.fst (V U).ι (V U').ι ≫ (V U).ι) x
  have key : ∀ (W : C.AffineZariskiSite) (y : X), y ∈ V W → g y ∈ W.1 := fun W y hy => by
    rw [hV] at hy
    exact hy
  have haU : g a ∈ U.1 := key U _ (pullback.fst (V U).ι (V U').ι x).2
  have haU' : g a ∈ U'.1 := by
    have h1 := key U' _ (pullback.snd (V U).ι (V U').ι x).2
    have h2 : (pullback.fst (V U).ι (V U').ι ≫ (V U).ι) x =
        (pullback.snd (V U).ι (V U').ι ≫ (V U').ι) x := by
      rw [pullback.condition]
    show g ((pullback.fst (V U).ι (V U').ι ≫ (V U).ι) x) ∈ U'.1
    rw [h2]
    exact h1
  obtain ⟨f, f', e, hxf⟩ := exists_basicOpen_le_affine_inter U.2 U'.2 (g a) ⟨haU, haU'⟩
  refine ⟨U.basicOpen f, homOfLE (U.basicOpen_le f),
    eqToHom (Scheme.AffineZariskiSite.toOpens_injective (by exact e)) ≫ homOfLE (U'.basicOpen_le f'),
    ⟨a, by rw [hV]; exact hxf⟩, ?_⟩
  apply (pullback.fst (V U).ι (V U').ι ≫ (V U).ι).isOpenEmbedding.injective
  change (pullback.lift _ _ _ ≫ pullback.fst _ _ ≫ (V U).ι) _ = _
  rw [pullback.lift_fst_assoc, X.homOfLE_ι]
  rfl

set_option warn.classDefReducibility false in
set_option backward.isDefEq.respectTransparency false in
/-- The preimage cover is locally directed, with transition maps `X.homOfLE`
(a `def`, not a global `instance`; users install it locally with `letI`). -/
def locallyDirected (hcov : IsOpenCover V) :
    letI : Category (X.openCoverOfIsOpenCover V hcov).I₀ :=
      inferInstanceAs (Category C.AffineZariskiSite)
    (X.openCoverOfIsOpenCover V hcov).LocallyDirected :=
  letI : Category (X.openCoverOfIsOpenCover V hcov).I₀ :=
    inferInstanceAs (Category C.AffineZariskiSite)
  { trans := fun {_ _} f => X.homOfLE (le_of_hom g V hV f)
    trans_id := fun _ => X.homOfLE_rfl _
    trans_comp := fun _ _ => (X.homOfLE_homOfLE _ _).symm
    w := fun _ => X.homOfLE_ι _
    directed := fun {_ _} x => directed_aux g V hV _ _ x
    property_trans := fun _ => inferInstance }

set_option backward.isDefEq.respectTransparency false in
/-- Gluing compatibility on pairwise intersections for a family of morphisms out of the `V U`
compatible with restriction (`Scheme.OpenCover.glueMorphismsOfLocallyDirected`'s argument). -/
theorem glue_compat (hcov : IsOpenCover V) {Y : Scheme.{u}}
    (φ : ∀ U, (V U).toScheme ⟶ Y)
    (h : ∀ {U U' : C.AffineZariskiSite} (f : U' ⟶ U), X.homOfLE (le_of_hom g V hV f) ≫ φ U = φ U') :
    ∀ U U', pullback.fst ((X.openCoverOfIsOpenCover V hcov).f U)
        ((X.openCoverOfIsOpenCover V hcov).f U') ≫ φ U =
      pullback.snd _ _ ≫ φ U' := by
  intro U U'
  letI inst : Category (X.openCoverOfIsOpenCover V hcov).I₀ :=
    inferInstanceAs (Category C.AffineZariskiSite)
  letI ld : @Cover.LocallyDirected _ _ (X.openCoverOfIsOpenCover V hcov) inst :=
    locallyDirected g V hV hcov
  apply (@Cover.intersectionOfLocallyDirected _ _ (X.openCoverOfIsOpenCover V hcov) inst ld _ _
    U U').hom_ext
  intro k
  rw [Cover.intersectionOfLocallyDirected_f, pullback.lift_fst_assoc, pullback.lift_snd_assoc]
  exact (h k.2.1).trans (h k.2.2).symm

end affinePreimageCover

end AlgebraicGeometry.Scheme

end
