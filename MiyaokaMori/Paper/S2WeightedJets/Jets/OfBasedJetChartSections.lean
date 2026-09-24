import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S2WeightedJets.Jets.RelativeJetRepresentableBy
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.JetThickeningSectionsCoeff

/-! # The morphism of a based jet on chart sections

The `C`-morphism `a = ofBasedJet φ : W → J_r^s(Z/C)` corresponding to a based jet `φ : W ×_k D_r → Z` has, on the
chart `U`, the comorphism `ofBasedJetSections` (`ofBasedJet_appLE_chartSections`); hence `a^♯(d_q b)` is the
`t`-coefficient of order `q + 1` of `φ^♯(b)` (`ofBasedJet_appLE_coeffClass`). The chart image is the preimage of `U`
(`preimage_eq_chartOpen`).
`ofBasedJet_appLE_coeffClass` is assembled from three lemmas:
* `AlgebraicGeometry.Scheme.appLE_isoOpensRange_of_ι_comp` (a general lemma of scheme theory);
* `relativeJetScheme.ι_ofBasedJet` (the defining property of the gluing);
* `relativeJetScheme.ofBasedJetSections_coeffClass` (pure algebra: `BasedJetAlgebra.lift_coeffClass`).
Source: §2 of the paper (the functor of points of `J_k^s`); the construction of Ein–Mustață Prop. 2.2 (chart ring
= Hasse–Schmidt algebra, `d_q b ↦` coefficient of order `q + 1`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Let `W`, `J` be schemes, `V ⊆ W` open, `j : Spec R → J` an open immersion, `g : W → J` and `σ : R → Γ(W, V)` a
ring homomorphism. If `g` factors on `V` through the chart `j` via `σ`, i.e. `V.ι ≫ g = V.toSpecΓ ≫ Spec.map σ ≫ j`,
then the comorphism of `g` on the chart image, composed with "chart ring `→ Γ(J, chart image)`" (global sections of
the inverse of `Spec R ≅ image`), is `σ`.

Proof sketch: let `e := j.isoOpensRange : Spec R ≅ j.opensRange` (`e.hom ≫ j.opensRange.ι = j`). By hypothesis `g`
restricted to `V` lands in `j.opensRange`, and `V.ι ≫ g = (V.toSpecΓ ≫ Spec.map σ ≫ e.hom) ≫ j.opensRange.ι`.
Apply `appLE j.opensRange ⊤` to both sides (`comp_appLE`, `appLE_map`; the `appLE` of `V.ι` is the restriction
`Γ(W, V) ≅ Γ(V, ⊤)`, i.e. `Opens.topIso`); the right side splits by `comp_appTop` into `σ` and the cancellation of
`toSpecΓ` and `ΓSpecIso` (`Scheme.toSpecΓ_appTop` / `ΓSpecIso_naturality`: global sections of `Spec.map σ` sandwiched
between `ΓSpecIso` is `σ`), and `e.hom.appTop` cancels `e.inv.appTop`. -/
theorem AlgebraicGeometry.Scheme.appLE_isoOpensRange_of_ι_comp {W J : AlgebraicGeometry.Scheme.{u}}
    (V : W.Opens) (R : CommRingCat.{u}) (j : AlgebraicGeometry.Spec R ⟶ J) [AlgebraicGeometry.IsOpenImmersion j]
    (g : W ⟶ J) (σ : R ⟶ Γ(W, V))
    (hfac : V.ι ≫ g = V.toSpecΓ ≫ AlgebraicGeometry.Spec.map σ ≫ j)
    (hle : V ≤ g ⁻¹ᵁ j.opensRange) :
    ((AlgebraicGeometry.Scheme.ΓSpecIso R).inv ≫ j.isoOpensRange.inv.appTop ≫ j.opensRange.topIso.hom) ≫
      g.appLE j.opensRange V hle = σ := by
  -- `τ` := "chart ring `→ Γ(J, chart image)`"
  set τ : R ⟶ Γ(J, j.opensRange) :=
    (AlgebraicGeometry.Scheme.ΓSpecIso R).inv ≫ j.isoOpensRange.inv.appTop ≫ j.opensRange.topIso.hom with hτ
  -- (0) key identity: `opensRange.toSpecΓ ≫ Spec.map τ = isoOpensRange.inv`
  --     (unfold `Opens.toSpecΓ`, cancel `topIso`, `toSpecΓ_naturality`, `toSpecΓ ≫ Spec.map ΓSpecIso.inv = 𝟙`)
  have key : j.opensRange.toSpecΓ ≫ AlgebraicGeometry.Spec.map τ = j.isoOpensRange.inv := by
    simp only [hτ, AlgebraicGeometry.Scheme.Opens.toSpecΓ, AlgebraicGeometry.Spec.map_comp,
      CategoryTheory.Category.assoc]
    rw [← AlgebraicGeometry.Spec.map_comp_assoc, CategoryTheory.Iso.hom_inv_id,
      AlgebraicGeometry.Spec.map_id, CategoryTheory.Category.id_comp,
      ← AlgebraicGeometry.Scheme.toSpecΓ_naturality_assoc,
      AlgebraicGeometry.toSpecΓ_SpecMap_ΓSpecIso_inv, CategoryTheory.Category.comp_id]
  -- (1) V.toSpecΓ ≫ Spec.map (τ ≫ g.appLE) ≫ j = V.ι ≫ g (toSpecΓ_SpecMap_appLE + key + resLE_comp_ι)
  have h1 : V.toSpecΓ ≫ AlgebraicGeometry.Spec.map (τ ≫ g.appLE j.opensRange V hle) ≫ j = V.ι ≫ g := by
    simp only [AlgebraicGeometry.Spec.map_comp, CategoryTheory.Category.assoc]
    rw [AlgebraicGeometry.Scheme.Opens.toSpecΓ_SpecMap_appLE_assoc, reassoc_of% key,
      AlgebraicGeometry.Scheme.Hom.isoOpensRange_inv_comp, AlgebraicGeometry.Scheme.Hom.resLE_comp_ι]
  -- (2) cancel the monomorphism `j`
  have h2 : V.toSpecΓ ≫ AlgebraicGeometry.Spec.map (τ ≫ g.appLE j.opensRange V hle) =
      V.toSpecΓ ≫ AlgebraicGeometry.Spec.map σ := by
    have h := h1.trans hfac
    rw [← CategoryTheory.Category.assoc, ← CategoryTheory.Category.assoc,
      CategoryTheory.cancel_mono] at h
    exact h
  -- (3) take global sections: `toSpecΓ.appTop = ΓSpecIso.hom ≫ topIso.inv` is an isomorphism; after
  -- `ΓSpecIso_naturality`, cancel it
  have h3 := congrArg (fun φ : V.toScheme ⟶ AlgebraicGeometry.Spec R => φ.appTop) h2
  simp only [AlgebraicGeometry.Scheme.Hom.comp_appTop, AlgebraicGeometry.Scheme.Opens.toSpecΓ_appTop] at h3
  rw [← CategoryTheory.Category.assoc, ← CategoryTheory.Category.assoc, CategoryTheory.cancel_mono,
    AlgebraicGeometry.Scheme.ΓSpecIso_naturality, AlgebraicGeometry.Scheme.ΓSpecIso_naturality,
    CategoryTheory.cancel_epi] at h3
  exact h3

variable {k : Type u} [Field k] {C : AlgebraicGeometry.Scheme.{u}}
  [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (Z : CategoryTheory.Over C) [AlgebraicGeometry.IsAffineHom Z.hom]
  (s : C ⟶ Z.left) (hs : s ≫ Z.hom = CategoryTheory.CategoryStruct.id C) (r : ℕ)

/-- The defining property of the gluing: `ofBasedJet` restricted to `w⁻¹U` is "Spec adjunction, then
`Spec(ofBasedJetSections)`, then the chart". -/
theorem relativeJetScheme.ι_ofBasedJet (W : CategoryTheory.Over C)
    (φ : (relativeJetFunctor (k := k) Z s hs r).obj (Opposite.op W)) (U : C.AffineZariskiSite) :
    (W.hom ⁻¹ᵁ U.1).ι ≫ (relativeJetScheme.ofBasedJet (k := k) Z s hs r W φ).left =
      (W.hom ⁻¹ᵁ U.1).toSpecΓ ≫
        AlgebraicGeometry.Spec.map (relativeJetScheme.ofBasedJetSections (k := k) Z s hs r W φ U) ≫
        (relativeJetScheme.gluingData Z s hs r).cover.f U := by
  have hl : (relativeJetScheme.ofBasedJet (k := k) Z s hs r W φ).left =
      (W.left.openCoverOfIsOpenCover (fun U : C.AffineZariskiSite => W.hom ⁻¹ᵁ U.1)
        (relativeJetScheme.ofBasedJet_isOpenCover W)).glueMorphisms
      (fun U => (W.hom ⁻¹ᵁ U.1).toSpecΓ ≫
        AlgebraicGeometry.Spec.map (relativeJetScheme.ofBasedJetSections (k := k) Z s hs r W φ U) ≫
        (relativeJetScheme.gluingData Z s hs r).cover.f U)
      (relativeJetScheme.ofBasedJet_glue_compat (k := k) Z s hs r W φ) := rfl
  rw [hl]
  exact AlgebraicGeometry.Scheme.Cover.ι_glueMorphisms
    (W.left.openCoverOfIsOpenCover (fun U : C.AffineZariskiSite => W.hom ⁻¹ᵁ U.1)
      (relativeJetScheme.ofBasedJet_isOpenCover W)) _ _ U

/-- The comorphism of `ofBasedJet` on the chart `U` is `ofBasedJetSections` (on every element of the chart ring). -/
theorem relativeJetScheme.ofBasedJet_appLE_chartSections (W : CategoryTheory.Over C)
    (φ : (relativeJetFunctor (k := k) Z s hs r).obj (Opposite.op W)) (U : C.AffineZariskiSite)
    (hle : W.hom ⁻¹ᵁ U.1 ≤ (relativeJetScheme.ofBasedJet (k := k) Z s hs r W φ).left ⁻¹ᵁ
      relativeJetScheme.chartOpen (k := k) Z s hs r U) :
    relativeJetScheme.chartSections (k := k) Z s hs r U ≫
        (relativeJetScheme.ofBasedJet (k := k) Z s hs r W φ).left.appLE
          (relativeJetScheme.chartOpen (k := k) Z s hs r U) (W.hom ⁻¹ᵁ U.1) hle =
      relativeJetScheme.ofBasedJetSections (k := k) Z s hs r W φ U :=
  @AlgebraicGeometry.Scheme.appLE_isoOpensRange_of_ι_comp _ _ (W.hom ⁻¹ᵁ U.1) _
    ((relativeJetScheme.gluingData Z s hs r).cover.f U)
    (relativeJetScheme.chart_isOpenImmersion Z s hs r U)
    (relativeJetScheme.ofBasedJet (k := k) Z s hs r W φ).left
    (relativeJetScheme.ofBasedJetSections (k := k) Z s hs r W φ U)
    (relativeJetScheme.ι_ofBasedJet Z s hs r W φ U) hle

/-- Pure algebra: `ofBasedJetSections` sends `D_n b` to the `t`-coefficient of order `n` of `φ^♯(b)`
(`BasedJetAlgebra.lift_coeffClass`). -/
theorem relativeJetScheme.ofBasedJetSections_coeffClass (W : CategoryTheory.Over C)
    (φ : (relativeJetFunctor (k := k) Z s hs r).obj (Opposite.op W)) (U : C.AffineZariskiSite)
    (n : ℕ) (hn : n ≤ r) (b : Γ(Z.left, Z.hom ⁻¹ᵁ U.1)) :
    letI : W.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨W.hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    letI := relativeJetScheme.sectionsAlgebra Z U.1
    (relativeJetScheme.ofBasedJetSections (k := k) Z s hs r W φ U).hom
        (BasedJetAlgebra.coeffClass (relativeJetScheme.augmentation Z s hs U.1) r n b) =
      jetThickening.coeff (k := k) r W.left (W.hom ⁻¹ᵁ U.1) n hn
        ((φ.1.appLE (Z.hom ⁻¹ᵁ U.1) (jetThickeningProj (k := k) r W.left ⁻¹ᵁ (W.hom ⁻¹ᵁ U.1))
          (relativeJetScheme.ofBasedJetSections_le (k := k) Z s hs r W φ U)).hom b) := by
  let _ : W.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨W.hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  let _ := relativeJetScheme.sectionsAlgebra Z U.1
  exact BasedJetAlgebra.lift_coeffClass (relativeJetScheme.augmentation Z s hs U.1) r _ _
    (relativeJetScheme.ofBasedJetSections_smul (k := k) Z s hs r W φ U)
    (relativeJetScheme.ofBasedJetSections_epsilon (k := k) Z s hs r W φ U) n hn b

/-- For the `C`-morphism `a = ofBasedJet φ : W → J_r^s(Z/C)` corresponding to a based jet `φ : W ×_k D_r → Z`, on
the jet coordinate `d_q b` of the chart `U`: `a^♯(d_q b)` is the `t`-coefficient of order `q + 1` of `φ^♯(b)`
(coefficients taken through the inverse of `sectionsHom`). Assembled from the three lemmas above. -/
theorem relativeJetScheme.ofBasedJet_appLE_coeffClass
    (W : CategoryTheory.Over C) (φ : (relativeJetFunctor (k := k) Z s hs r).obj (Opposite.op W))
    (U : C.AffineZariskiSite) (q : Fin r) (b : Γ(Z.left, Z.hom ⁻¹ᵁ U.1))
    (hle : W.hom ⁻¹ᵁ U.1 ≤ (relativeJetScheme.ofBasedJet (k := k) Z s hs r W φ).left ⁻¹ᵁ
      relativeJetScheme.chartOpen (k := k) Z s hs r U) :
    letI : W.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨W.hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    letI := relativeJetScheme.sectionsAlgebra Z U.1
    ∀ hφ : jetThickeningProj (k := k) r W.left ⁻¹ᵁ (W.hom ⁻¹ᵁ U.1) ≤ φ.1 ⁻¹ᵁ (Z.hom ⁻¹ᵁ U.1),
    ((relativeJetScheme.ofBasedJet (k := k) Z s hs r W φ).left.appLE
        (relativeJetScheme.chartOpen (k := k) Z s hs r U) (W.hom ⁻¹ᵁ U.1) hle).hom
      ((relativeJetScheme.chartSections (k := k) Z s hs r U).hom
        (BasedJetAlgebra.coeffClass (relativeJetScheme.augmentation Z s hs U.1) r ((q : ℕ) + 1) b)) =
    jetThickening.coeff (k := k) r W.left (W.hom ⁻¹ᵁ U.1) ((q : ℕ) + 1) (Nat.succ_le_of_lt q.2)
      ((φ.1.appLE (Z.hom ⁻¹ᵁ U.1) (jetThickeningProj (k := k) r W.left ⁻¹ᵁ (W.hom ⁻¹ᵁ U.1)) hφ).hom b) := by
  intro hφ
  have h1 := relativeJetScheme.ofBasedJet_appLE_chartSections (k := k) Z s hs r W φ U hle
  have h2 := relativeJetScheme.ofBasedJetSections_coeffClass (k := k) Z s hs r W φ U ((q : ℕ) + 1)
    (Nat.succ_le_of_lt q.2) b
  rw [← h2, ← h1]
  rfl

/-- The chart image is the preimage of `U`: `J_r^s(Z/C)` is glued relatively from `{Spec J_r(B_U, ε_U)}_U` along the
affine opens of `C`, and the `U`-th piece is exactly `toBase⁻¹(U)`
(Mathlib `Scheme.Cover.RelativeGluingData.toBase_preimage_eq_opensRange_ι`). -/
theorem relativeJetScheme.preimage_eq_chartOpen (U : C.AffineZariskiSite) :
    (relativeJetScheme (k := k) Z s hs r).hom ⁻¹ᵁ U.1 = relativeJetScheme.chartOpen (k := k) Z s hs r U :=
  relativeJetScheme.hom_preimage_chartOpen (k := k) Z s hs r U

end
