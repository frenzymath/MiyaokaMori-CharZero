import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S2WeightedJets.Jets.RelativeJetRepresentableByUniversalJet

/-! # Representability of the relative based jet functor

The data making the glued scheme `J_r^s(Z/C)` represent the based jet functor: the universal based jet
`J ×_k D_r → Z` (given chart by chart by the algebraic universal jet, then glued), the map from based jets to
`C`-morphisms `W → J` (take coefficients on each `w⁻¹U`, land in the chart through the `Spec` adjunction, then glue),
the map from `C`-morphisms to based jets, and the two inverse laws (§2 of the paper; the relative version of
Ein–Mustață Prop. 2.2 and Lemma 2.3).

The construction is split over four helper modules:
* `RelativeJetRepresentableBySchemeLemmas`: general lemmas on open immersions from `Spec`, `chartSec`, and the
  locally directed cover of a scheme by the preimages of the affine opens of `C` (`affinePreimageCover.glue_compat`);
* `RelativeJetRepresentableByCharts`: `chartOpen`, `chartSections`, `universalJetSections` and their relation to the
  gluing data (`chart_comp_map`, `chart_comp_hom`, `hom_preimage_chartOpen`, `hom_appLE_chartOpen`, …);
* `RelativeJetRepresentableByCoeff`: `t`-coefficient computations (`coeff_universalJetSections`,
  `coeff_jetThickeningMap_appLE`, the constant-term section, …);
* `RelativeJetRepresentableByUniversalJet`: `universalJet` with `universalJet_glue_compat`, `universalJet_appLE`,
  `universalJet_comp_hom`, `jetConstantTerm_comp_universalJet`.
Here: `ofBasedJetSections`, `ofBasedJet` (with `ofBasedJet_glue_compat`, `ofBasedJet_over`), `toBasedJet`
(with `toBasedJet_prop`), the two inverse laws and `representableBy`.

The proof of the inverse laws (EM08 Prop 2.2, relative version): a `C`-morphism `a : W ⟶ J` restricted to `w⁻¹U`
lands in the chart `J_U = Spec J_r(B_U, ε_U)` and is determined by the ring map `J_r(B_U, ε_U) → Γ(W, w⁻¹U)`,
`d_q b ↦ a^♯(chartSections U (d_q b))`; the based jet `toBasedJet a = (a × 𝟙) ≫ universalJet` has, on `pr⁻¹w⁻¹U`,
`t^n`-coefficients `a^♯(chartSections U (D_n b))` (`toBasedJet_appLE_coeff`), while `ofBasedJet φ` is glued from
`Spec` of `d_q b ↦ (t^{q+1}`-coefficient of `φ^♯ b)` (`ofBasedJetSections_apply_coeffClass`). Both compositions
are then identities by comparing generators (`Ideal.Quotient.ringHom_ext`, `MvPolynomial.ringHom_ext`) resp.
coefficients (`jetThickening.ext_coeff`), locally on the covers `{w⁻¹U}` resp. `{pr⁻¹w⁻¹U}`.

Implementation note: `TruncatedJetRing` is `AdjoinRoot (X^(r+1))`; representatives are taken with
`jetProjection_surjective` (so that `rw` sees `jetProjection … p`, not `Ideal.Quotient.mk (span …) p`), and
`Ideal.Quotient.lift_mk` is rewritten with `erw` (it matches only up to unfolding `AdjoinRoot`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.style.haveILetI false
-- `U.1` for `U : C.AffineZariskiSite` and the cover index `𝒰.I₀` make `rw` motives fail to typecheck under the
-- strict transparency check (Mathlib disables it around `AffineZariskiSite` / locally directed covers too).
set_option backward.isDefEq.respectTransparency false

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
open relativeJetScheme.Charts

noncomputable section

/- The glued scheme `relativeJetScheme` represents `relativeJetFunctor`: the data is the bijection `homEquiv`, both
   directions of which are constructed explicitly. -/


/-- First proof obligation of `ofBasedJetSections` (the open-set inclusion for `appLE`): `pr⁻¹(w⁻¹U) ≤ φ⁻¹(π⁻¹U)`.
Take preimages of `U` on both sides of the based jet condition `φ ≫ Z.hom = pr ≫ W.hom` (in fact an equality). -/

theorem relativeJetScheme.ofBasedJetSections_le {k : Type u} [Field k] {C : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (Z : CategoryTheory.Over C) [AlgebraicGeometry.IsAffineHom Z.hom]
    (s : C ⟶ Z.left) (hs : s ≫ Z.hom = CategoryTheory.CategoryStruct.id C) (r : ℕ)
    (W : CategoryTheory.Over C) (φ : (relativeJetFunctor (k := k) Z s hs r).obj (Opposite.op W))
    (U : C.AffineZariskiSite) :
    letI : W.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨W.hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    jetThickeningProj (k := k) r W.left ⁻¹ᵁ (W.hom ⁻¹ᵁ U.1) ≤ φ.1 ⁻¹ᵁ (Z.hom ⁻¹ᵁ U.1) := by
  letI : W.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨W.hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  intro x hx
  have h : (φ.1 ≫ Z.hom) x = (jetThickeningProj (k := k) r W.left ≫ W.hom) x :=
    congrArg (fun g => g x) φ.2.1
  show (φ.1 ≫ Z.hom) x ∈ U.1
  rw [h]
  exact hx

/-- The comorphism of a based jet on the chart `U` sends the coefficient `π^♯(a)` to `pr^♯(w^♯ a)`
(`φ ≫ Z.hom = pr ≫ W.hom` on sections). -/

theorem relativeJetScheme.ofBasedJetSections_appLE_coeff {k : Type u} [Field k] {C : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (Z : CategoryTheory.Over C) [AlgebraicGeometry.IsAffineHom Z.hom]
    (s : C ⟶ Z.left) (hs : s ≫ Z.hom = CategoryTheory.CategoryStruct.id C) (r : ℕ)
    (W : CategoryTheory.Over C) (φ : (relativeJetFunctor (k := k) Z s hs r).obj (Opposite.op W))
    (U : C.AffineZariskiSite) (a : Γ(C, U.1)) :
    letI : W.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨W.hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    (φ.1.appLE (Z.hom ⁻¹ᵁ U.1) (jetThickeningProj (k := k) r W.left ⁻¹ᵁ (W.hom ⁻¹ᵁ U.1))
        (relativeJetScheme.ofBasedJetSections_le (k := k) Z s hs r W φ U)).hom ((Z.hom.app U.1).hom a) =
      ((jetThickeningProj (k := k) r W.left).app (W.hom ⁻¹ᵁ U.1)).hom ((W.hom.app U.1).hom a) := by
  letI : W.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨W.hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  have h1 := AlgebraicGeometry.Scheme.Hom.comp_appLE φ.1 Z.hom U.1
    (jetThickeningProj (k := k) r W.left ⁻¹ᵁ (W.hom ⁻¹ᵁ U.1))
    (relativeJetScheme.ofBasedJetSections_le (k := k) Z s hs r W φ U)
  have h2 := AlgebraicGeometry.Scheme.Hom.comp_appLE (jetThickeningProj (k := k) r W.left) W.hom U.1
    (jetThickeningProj (k := k) r W.left ⁻¹ᵁ (W.hom ⁻¹ᵁ U.1)) le_rfl
  have h3 := AlgebraicGeometry.Scheme.Hom.appLE_congr_hom φ.2.1 U.1
    (jetThickeningProj (k := k) r W.left ⁻¹ᵁ (W.hom ⁻¹ᵁ U.1))
    (relativeJetScheme.ofBasedJetSections_le (k := k) Z s hs r W φ U) le_rfl
  rw [h1, h2, AlgebraicGeometry.Scheme.Hom.appLE_eq_app] at h3
  exact congrArg (fun g => g.hom a) h3

/-- Second proof obligation of `ofBasedJetSections` (the hypothesis `hψ` of `BasedJetAlgebra.lift`):
`ψ = sectionsHom⁻¹ ∘ φ^♯` is semilinear for `Γ(C,U)`-scalars. Route: `a • b = π^♯(a)·b`; `φ ≫ Z.hom = pr ≫ W.hom` on
sections gives `φ^♯(π^♯ a) = pr^♯(w^♯ a) = sectionsHom(eta(w^♯ a))`, then apply the inverse of `sectionsHom`. -/

theorem relativeJetScheme.ofBasedJetSections_smul {k : Type u} [Field k] {C : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (Z : CategoryTheory.Over C) [AlgebraicGeometry.IsAffineHom Z.hom]
    (s : C ⟶ Z.left) (hs : s ≫ Z.hom = CategoryTheory.CategoryStruct.id C) (r : ℕ)
    (W : CategoryTheory.Over C) (φ : (relativeJetFunctor (k := k) Z s hs r).obj (Opposite.op W))
    (U : C.AffineZariskiSite) :
    letI : W.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨W.hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    letI := relativeJetScheme.sectionsAlgebra Z U.1
    ∀ (a : Γ(C, U.1)) (b : Γ(Z.left, Z.hom ⁻¹ᵁ U.1)),
      ((RingEquiv.ofBijective _ (jetThickening.sectionsHom_bijective (k := k) r W.left
          (W.hom ⁻¹ᵁ U.1))).symm.toRingHom.comp
        (φ.1.appLE (Z.hom ⁻¹ᵁ U.1) (jetThickeningProj (k := k) r W.left ⁻¹ᵁ (W.hom ⁻¹ᵁ U.1))
          (relativeJetScheme.ofBasedJetSections_le (k := k) Z s hs r W φ U)).hom) (a • b) =
        MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.eta r ((W.hom.app U.1).hom a) *
          ((RingEquiv.ofBijective _ (jetThickening.sectionsHom_bijective (k := k) r W.left
          (W.hom ⁻¹ᵁ U.1))).symm.toRingHom.comp
        (φ.1.appLE (Z.hom ⁻¹ᵁ U.1) (jetThickeningProj (k := k) r W.left ⁻¹ᵁ (W.hom ⁻¹ᵁ U.1))
          (relativeJetScheme.ofBasedJetSections_le (k := k) Z s hs r W φ U)).hom) b := by
  letI : W.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨W.hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  letI := relativeJetScheme.sectionsAlgebra Z U.1
  intro a b
  simp only [RingHom.comp_apply]
  rw [Algebra.smul_def, map_mul, map_mul]
  congr 1
  show (RingEquiv.ofBijective _ (jetThickening.sectionsHom_bijective (k := k) r W.left
    (W.hom ⁻¹ᵁ U.1))).symm _ = _
  rw [RingEquiv.symm_apply_eq]
  show (φ.1.appLE (Z.hom ⁻¹ᵁ U.1) (jetThickeningProj (k := k) r W.left ⁻¹ᵁ (W.hom ⁻¹ᵁ U.1))
      (relativeJetScheme.ofBasedJetSections_le (k := k) Z s hs r W φ U)).hom ((Z.hom.app U.1).hom a) =
    jetThickening.sectionsHom (k := k) r W.left (W.hom ⁻¹ᵁ U.1)
      (MiyaokaMori.Jet.jetProjection _ r (Polynomial.C ((W.hom.app U.1).hom a)))
  rw [relativeJetScheme.ofBasedJetSections_appLE_coeff]
  unfold jetThickening.sectionsHom
  rw [MiyaokaMori.Jet.lift_jetProjection, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]

/-- Third proof obligation of `ofBasedJetSections` (the hypothesis `hε` of `BasedJetAlgebra.lift`): the constant term
of `ψ(b)` is `w^♯(ε_U b)`. Route: `epsilon ∘ sectionsHom⁻¹` is the pullback along the constant-term section
`jetConstantTerm` (on `C a` by `ct ≫ pr = 𝟙`, on `t` by `jetBaseZero^♯(t) = 0`), then use the based jet condition
`jetConstantTerm ≫ φ = W.hom ≫ s` on sections. -/

theorem relativeJetScheme.ofBasedJetSections_epsilon {k : Type u} [Field k] {C : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (Z : CategoryTheory.Over C) [AlgebraicGeometry.IsAffineHom Z.hom]
    (s : C ⟶ Z.left) (hs : s ≫ Z.hom = CategoryTheory.CategoryStruct.id C) (r : ℕ)
    (W : CategoryTheory.Over C) (φ : (relativeJetFunctor (k := k) Z s hs r).obj (Opposite.op W))
    (U : C.AffineZariskiSite) :
    letI : W.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨W.hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    letI := relativeJetScheme.sectionsAlgebra Z U.1
    ∀ b : Γ(Z.left, Z.hom ⁻¹ᵁ U.1),
      MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.epsilon r
          (((RingEquiv.ofBijective _ (jetThickening.sectionsHom_bijective (k := k) r W.left
          (W.hom ⁻¹ᵁ U.1))).symm.toRingHom.comp
        (φ.1.appLE (Z.hom ⁻¹ᵁ U.1) (jetThickeningProj (k := k) r W.left ⁻¹ᵁ (W.hom ⁻¹ᵁ U.1))
          (relativeJetScheme.ofBasedJetSections_le (k := k) Z s hs r W φ U)).hom) b) =
        (W.hom.app U.1).hom (relativeJetScheme.augmentation Z s hs U.1 b) := by
  letI : W.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨W.hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  letI := relativeJetScheme.sectionsAlgebra Z U.1
  intro b
  simp only [RingHom.comp_apply]
  have hE : ∀ y, MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.epsilon r
      ((RingEquiv.ofBijective _ (jetThickening.sectionsHom_bijective (k := k) r W.left
        (W.hom ⁻¹ᵁ U.1))).symm y) =
      ((jetConstantTerm (k := k) r W.left).appLE _ (W.hom ⁻¹ᵁ U.1)
        (jetConstantTerm_le (k := k) r W.left (W.hom ⁻¹ᵁ U.1))).hom y := by
    intro y
    obtain ⟨p, rfl⟩ := (RingEquiv.ofBijective _ (jetThickening.sectionsHom_bijective (k := k) r W.left
      (W.hom ⁻¹ᵁ U.1))).surjective y
    rw [RingEquiv.symm_apply_apply]
    exact (jetConstantTerm_sectionsHom (k := k) r W.left (W.hom ⁻¹ᵁ U.1) p).symm
  refine (hE _).trans ?_
  have h1 := AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE (jetConstantTerm (k := k) r W.left) φ.1
    (Z.hom ⁻¹ᵁ U.1) (jetThickeningProj (k := k) r W.left ⁻¹ᵁ (W.hom ⁻¹ᵁ U.1)) (W.hom ⁻¹ᵁ U.1)
    (relativeJetScheme.ofBasedJetSections_le (k := k) Z s hs r W φ U)
    (jetConstantTerm_le (k := k) r W.left (W.hom ⁻¹ᵁ U.1))
  have hsle : U.1 ≤ s ⁻¹ᵁ (Z.hom ⁻¹ᵁ U.1) := by
    rw [← AlgebraicGeometry.Scheme.Hom.comp_preimage, hs]; rfl
  have h2 := AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE W.hom s
    (Z.hom ⁻¹ᵁ U.1) U.1 (W.hom ⁻¹ᵁ U.1) hsle le_rfl
  have h3 := AlgebraicGeometry.Scheme.Hom.appLE_congr_hom φ.2.2 (Z.hom ⁻¹ᵁ U.1) (W.hom ⁻¹ᵁ U.1)
    ((jetConstantTerm_le (k := k) r W.left (W.hom ⁻¹ᵁ U.1)).trans
      ((TopologicalSpace.Opens.map (jetConstantTerm (k := k) r W.left).base).map (CategoryTheory.homOfLE
        (relativeJetScheme.ofBasedJetSections_le (k := k) Z s hs r W φ U))).le)
    (le_rfl.trans ((TopologicalSpace.Opens.map W.hom.base).map (CategoryTheory.homOfLE hsle)).le)
  rw [← h1, ← h2, AlgebraicGeometry.Scheme.Hom.appLE_eq_app] at h3
  exact congrArg (fun g => g.hom b) h3

/-- The comorphism of the inverse direction on the chart `U`: a based jet `φ : W ×_k D_r → Z` gives
`B_U → Γ(W ×_k D_r, pr⁻¹ w⁻¹U) ≅ Γ(W, w⁻¹U)[t]/(t^{r+1})` (the latter is the inverse of `jetThickening.sectionsHom`,
bijective by `sectionsHom_bijective`), and taking coefficients gives `J_r(B_U, ε_U) → Γ(W, w⁻¹U)`. -/

noncomputable def relativeJetScheme.ofBasedJetSections {k : Type u} [Field k] {C : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (Z : CategoryTheory.Over C) [AlgebraicGeometry.IsAffineHom Z.hom]
    (s : C ⟶ Z.left) (hs : s ≫ Z.hom = CategoryTheory.CategoryStruct.id C) (r : ℕ)
    (W : CategoryTheory.Over C) (φ : (relativeJetFunctor (k := k) Z s hs r).obj (Opposite.op W))
    (U : C.AffineZariskiSite) :
    relativeJetScheme.chartRing Z s hs r U.1 ⟶ Γ(W.left, W.hom ⁻¹ᵁ U.1) :=
  letI : W.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨W.hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  letI := relativeJetScheme.sectionsAlgebra Z U.1
  CommRingCat.ofHom (BasedJetAlgebra.lift (relativeJetScheme.augmentation Z s hs U.1) r
    (W.hom.app U.1).hom
    ((RingEquiv.ofBijective _ (jetThickening.sectionsHom_bijective (k := k) r W.left
        (W.hom ⁻¹ᵁ U.1))).symm.toRingHom.comp
      (φ.1.appLE (Z.hom ⁻¹ᵁ U.1) (jetThickeningProj (k := k) r W.left ⁻¹ᵁ (W.hom ⁻¹ᵁ U.1))
        (relativeJetScheme.ofBasedJetSections_le (k := k) Z s hs r W φ U)).hom)
    (relativeJetScheme.ofBasedJetSections_smul (k := k) Z s hs r W φ U)
    (relativeJetScheme.ofBasedJetSections_epsilon (k := k) Z s hs r W φ U))

section OfBasedJet

variable {k : Type u} [Field k] {C : AlgebraicGeometry.Scheme.{u}}
  [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (Z : CategoryTheory.Over C) [AlgebraicGeometry.IsAffineHom Z.hom]
  (s : C ⟶ Z.left) (hs : s ≫ Z.hom = CategoryTheory.CategoryStruct.id C) (r : ℕ)

/-- `ofBasedJetSections` on a coefficient: `algebraMap c ↦ w^♯ c` (`BasedJetAlgebra.lift` on `C c`). -/
theorem relativeJetScheme.ofBasedJetSections_apply_algebraMap (W : CategoryTheory.Over C)
    (φ : (relativeJetFunctor (k := k) Z s hs r).obj (Opposite.op W)) (U : C.AffineZariskiSite) (c : Γ(C, U.1)) :
    letI := relativeJetScheme.sectionsAlgebra Z U.1
    (relativeJetScheme.ofBasedJetSections (k := k) Z s hs r W φ U).hom
        (algebraMap Γ(C, U.1) (BasedJetAlgebra (relativeJetScheme.augmentation Z s hs U.1) r) c) =
      (W.hom.app U.1).hom c := by
  show MvPolynomial.eval₂Hom _ _ (MvPolynomial.C c) = _
  rw [MvPolynomial.eval₂Hom_C]

/-- `ofBasedJetSections` on the generator `D_n b`: the `t^n`-coefficient of `φ^♯ b` (`BasedJetAlgebra.lift_coeffClass`). -/
theorem relativeJetScheme.ofBasedJetSections_apply_coeffClass (W : CategoryTheory.Over C)
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
  letI : W.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨W.hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  letI := relativeJetScheme.sectionsAlgebra Z U.1
  exact BasedJetAlgebra.lift_coeffClass (relativeJetScheme.augmentation Z s hs U.1) r _ _
    (relativeJetScheme.ofBasedJetSections_smul (k := k) Z s hs r W φ U)
    (relativeJetScheme.ofBasedJetSections_epsilon (k := k) Z s hs r W φ U) n hn b

/-- First proof obligation of `ofBasedJet`: `{w⁻¹U}` (`U` ranging over the affine opens of `C`) covers `W` (the
preimage along `w` of the affine open cover of `C`). -/

theorem relativeJetScheme.ofBasedJet_isOpenCover (W : CategoryTheory.Over C) :
    TopologicalSpace.IsOpenCover (fun U : C.AffineZariskiSite => W.hom ⁻¹ᵁ U.1) :=
  TopologicalSpace.IsOpenCover.comap
    (show TopologicalSpace.IsOpenCover (fun U : C.AffineZariskiSite => U.1) from
      AlgebraicGeometry.iSup_affineOpens_eq_top C) W.hom.base.1

/-- The piece of `ofBasedJet φ` on `w⁻¹U`: `toSpecΓ ≫ Spec (ofBasedJetSections U) ≫ chart U`. -/
noncomputable def relativeJetScheme.ofBasedJetPiece (W : CategoryTheory.Over C)
    (φ : (relativeJetFunctor (k := k) Z s hs r).obj (Opposite.op W)) (U : C.AffineZariskiSite) :
    (W.hom ⁻¹ᵁ U.1).toScheme ⟶ (relativeJetScheme (k := k) Z s hs r).left :=
  (W.hom ⁻¹ᵁ U.1).toSpecΓ ≫
    AlgebraicGeometry.Spec.map (relativeJetScheme.ofBasedJetSections (k := k) Z s hs r W φ U) ≫
    relativeJetScheme.chart (k := k) Z s hs r U

/-- Naturality of `ofBasedJetSections` in `U`: restricting to a basic open `V ⊆ U` is the transition map of
the chart rings followed by `ofBasedJetSections V`. On coefficients this is the naturality of `w^♯`; on the
generators `D_n b` it is the naturality of the `t`-coefficients (`jetThickening.coeff_restrict`) and of `φ^♯`. -/
theorem relativeJetScheme.ofBasedJetSections_comp_map (W : CategoryTheory.Over C)
    (φ : (relativeJetFunctor (k := k) Z s hs r).obj (Opposite.op W)) {U V : C.AffineZariskiSite} (f : V ⟶ U) :
    relativeJetScheme.ofBasedJetSections (k := k) Z s hs r W φ U ≫
        W.left.presheaf.map (CategoryTheory.homOfLE
          (AlgebraicGeometry.Scheme.affinePreimageCover.le_of_hom W.hom
            (fun U : C.AffineZariskiSite => W.hom ⁻¹ᵁ U.1) (fun _ => rfl) f)).op =
      (relativeJetScheme.chartFunctor Z s hs r).map f.op ≫
        relativeJetScheme.ofBasedJetSections (k := k) Z s hs r W φ V := by
  letI : W.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨W.hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  letI := relativeJetScheme.sectionsAlgebra Z U.1
  letI := relativeJetScheme.sectionsAlgebra Z V.1
  have hUV : V.1 ≤ U.1 := AlgebraicGeometry.Scheme.AffineZariskiSite.toOpens_mono f.le
  have hW : W.hom ⁻¹ᵁ V.1 ≤ W.hom ⁻¹ᵁ U.1 := (TopologicalSpace.Opens.map W.hom.base).monotone hUV
  have hZ : Z.hom ⁻¹ᵁ V.1 ≤ Z.hom ⁻¹ᵁ U.1 := (TopologicalSpace.Opens.map Z.hom.base).monotone hUV
  have hβ := relativeJetScheme.chartFunctor_smul Z hUV
  have hε : ∀ b : Γ(Z.left, Z.hom ⁻¹ᵁ U.1),
      relativeJetScheme.augmentation Z s hs V.1 ((Z.left.presheaf.map (CategoryTheory.homOfLE hZ).op).hom b) =
        (C.presheaf.map (CategoryTheory.homOfLE hUV).op).hom (relativeJetScheme.augmentation Z s hs U.1 b) :=
    fun b => congrArg (fun ψ : Γ(Z.left, Z.hom ⁻¹ᵁ U.1) ⟶ Γ(C, V.1) => CommRingCat.Hom.hom ψ b)
      (relativeJetScheme.augmentation_naturality Z s hs hUV)
  apply CommRingCat.hom_ext
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro c
    show (W.left.presheaf.map (CategoryTheory.homOfLE hW).op).hom
        ((relativeJetScheme.ofBasedJetSections (k := k) Z s hs r W φ U).hom
          (algebraMap Γ(C, U.1) (BasedJetAlgebra (relativeJetScheme.augmentation Z s hs U.1) r) c)) =
      (relativeJetScheme.ofBasedJetSections (k := k) Z s hs r W φ V).hom
        (BasedJetAlgebra.map _ _ r _ _ hβ hε
          (algebraMap Γ(C, U.1) (BasedJetAlgebra (relativeJetScheme.augmentation Z s hs U.1) r) c))
    rw [BasedJetAlgebra.map_algebraMap, relativeJetScheme.ofBasedJetSections_apply_algebraMap,
      relativeJetScheme.ofBasedJetSections_apply_algebraMap]
    exact (congrArg (fun ψ : Γ(C, U.1) ⟶ Γ(W.left, W.hom ⁻¹ᵁ V.1) => ψ.hom c)
      (W.hom.naturality (CategoryTheory.homOfLE hUV).op)).symm
  · rintro ⟨q, b⟩
    have hq : Ideal.Quotient.mk (BasedJetAlgebra.relations (relativeJetScheme.augmentation Z s hs U.1) r)
        (MvPolynomial.X (q, b)) =
        BasedJetAlgebra.coeffClass (relativeJetScheme.augmentation Z s hs U.1) r (q.1 + 1) b :=
      (BasedJetAlgebra.coeffClass_succ _ r q.1 q.2 b).symm
    show (W.left.presheaf.map (CategoryTheory.homOfLE hW).op).hom
        ((relativeJetScheme.ofBasedJetSections (k := k) Z s hs r W φ U).hom
          (Ideal.Quotient.mk _ (MvPolynomial.X (q, b)))) =
      (relativeJetScheme.ofBasedJetSections (k := k) Z s hs r W φ V).hom
        (BasedJetAlgebra.map _ _ r _ _ hβ hε (Ideal.Quotient.mk _ (MvPolynomial.X (q, b))))
    rw [hq, BasedJetAlgebra.map_coeffClass, relativeJetScheme.ofBasedJetSections_apply_coeffClass _ _ _ _ _ _ _ _
      (Nat.succ_le_of_lt q.2), relativeJetScheme.ofBasedJetSections_apply_coeffClass _ _ _ _ _ _ _ _
      (Nat.succ_le_of_lt q.2), ← jetThickening.coeff_restrict (k := k) r W.left hW]
    congr 1
    rw [← CategoryTheory.comp_apply, AlgebraicGeometry.Scheme.Hom.appLE_map,
      ← CategoryTheory.comp_apply, AlgebraicGeometry.Scheme.Hom.map_appLE]

/-- The pieces of `ofBasedJet φ` are compatible with restriction to a basic open `V ⊆ U`. -/
theorem relativeJetScheme.ofBasedJet_piece_restrict (W : CategoryTheory.Over C)
    (φ : (relativeJetFunctor (k := k) Z s hs r).obj (Opposite.op W)) {U V : C.AffineZariskiSite} (f : V ⟶ U) :
    W.left.homOfLE (AlgebraicGeometry.Scheme.affinePreimageCover.le_of_hom W.hom
        (fun U : C.AffineZariskiSite => W.hom ⁻¹ᵁ U.1) (fun _ => rfl) f) ≫
      relativeJetScheme.ofBasedJetPiece (k := k) Z s hs r W φ U =
    relativeJetScheme.ofBasedJetPiece (k := k) Z s hs r W φ V := by
  unfold relativeJetScheme.ofBasedJetPiece
  rw [← CategoryTheory.Category.assoc, ← AlgebraicGeometry.Scheme.Opens.toSpecΓ_SpecMap_presheaf_map,
    ← relativeJetScheme.chart_comp_map (k := k) Z s hs r f]
  simp only [CategoryTheory.Category.assoc]
  congr 1
  rw [← AlgebraicGeometry.Spec.map_comp_assoc, ← AlgebraicGeometry.Spec.map_comp_assoc,
    relativeJetScheme.ofBasedJetSections_comp_map]

/-- Second proof obligation of `ofBasedJet` (compatibility on overlaps): the morphisms on the `w⁻¹U` obtained from
`ofBasedJetSections` through the chart into `J` agree on `w⁻¹U ∩ w⁻¹U'`. Proof: `{w⁻¹U}` is the preimage cover under
`W.hom` of the affine opens of `C`, which is locally directed (`affinePreimageCover.glue_compat`), so it suffices to
check compatibility with restriction to basic opens `V ⊆ U` (`ofBasedJet_piece_restrict`: naturality of
`ofBasedJetSections` in `U`). -/

theorem relativeJetScheme.ofBasedJet_glue_compat (W : CategoryTheory.Over C)
    (φ : (relativeJetFunctor (k := k) Z s hs r).obj (Opposite.op W)) :
    ∀ U U' : C.AffineZariskiSite,
      CategoryTheory.Limits.pullback.fst
          ((W.left.openCoverOfIsOpenCover (fun U : C.AffineZariskiSite => W.hom ⁻¹ᵁ U.1)
            (relativeJetScheme.ofBasedJet_isOpenCover W)).f U)
          ((W.left.openCoverOfIsOpenCover (fun U : C.AffineZariskiSite => W.hom ⁻¹ᵁ U.1)
            (relativeJetScheme.ofBasedJet_isOpenCover W)).f U') ≫
        ((W.hom ⁻¹ᵁ U.1).toSpecΓ ≫
          AlgebraicGeometry.Spec.map (relativeJetScheme.ofBasedJetSections (k := k) Z s hs r W φ U) ≫
          (relativeJetScheme.gluingData Z s hs r).cover.f U) =
      CategoryTheory.Limits.pullback.snd
          ((W.left.openCoverOfIsOpenCover (fun U : C.AffineZariskiSite => W.hom ⁻¹ᵁ U.1)
            (relativeJetScheme.ofBasedJet_isOpenCover W)).f U)
          ((W.left.openCoverOfIsOpenCover (fun U : C.AffineZariskiSite => W.hom ⁻¹ᵁ U.1)
            (relativeJetScheme.ofBasedJet_isOpenCover W)).f U') ≫
        ((W.hom ⁻¹ᵁ U'.1).toSpecΓ ≫
          AlgebraicGeometry.Spec.map (relativeJetScheme.ofBasedJetSections (k := k) Z s hs r W φ U') ≫
          (relativeJetScheme.gluingData Z s hs r).cover.f U') :=
  AlgebraicGeometry.Scheme.affinePreimageCover.glue_compat W.hom
    (fun U : C.AffineZariskiSite => W.hom ⁻¹ᵁ U.1) (fun _ => rfl)
    (relativeJetScheme.ofBasedJet_isOpenCover W)
    (relativeJetScheme.ofBasedJetPiece (k := k) Z s hs r W φ)
    (fun f => relativeJetScheme.ofBasedJet_piece_restrict (k := k) Z s hs r W φ f)

/-- The glued morphism restricted to `w⁻¹U` is the piece (`Cover.ι_glueMorphisms`). -/
theorem relativeJetScheme.ι_glued_ofBasedJet (W : CategoryTheory.Over C)
    (φ : (relativeJetFunctor (k := k) Z s hs r).obj (Opposite.op W)) (U : C.AffineZariskiSite) :
    (W.hom ⁻¹ᵁ U.1).ι ≫
      ((W.left.openCoverOfIsOpenCover (fun U : C.AffineZariskiSite => W.hom ⁻¹ᵁ U.1)
            (relativeJetScheme.ofBasedJet_isOpenCover W)).glueMorphisms
        (fun U => (W.hom ⁻¹ᵁ U.1).toSpecΓ ≫
          AlgebraicGeometry.Spec.map (relativeJetScheme.ofBasedJetSections (k := k) Z s hs r W φ U) ≫
          (relativeJetScheme.gluingData Z s hs r).cover.f U)
        (relativeJetScheme.ofBasedJet_glue_compat (k := k) Z s hs r W φ)) =
    (W.hom ⁻¹ᵁ U.1).toSpecΓ ≫
      AlgebraicGeometry.Spec.map (relativeJetScheme.ofBasedJetSections (k := k) Z s hs r W φ U) ≫
      (relativeJetScheme.gluingData Z s hs r).cover.f U :=
  AlgebraicGeometry.Scheme.Cover.ι_glueMorphisms
    (W.left.openCoverOfIsOpenCover (fun U : C.AffineZariskiSite => W.hom ⁻¹ᵁ U.1)
      (relativeJetScheme.ofBasedJet_isOpenCover W)) _ _ U

/-- The glued morphism lies over `C`, on `w⁻¹U`: `chart U ≫ (J ⟶ C) = Spec (coefficient map) ≫ U.fromSpec`
and `coefficientMap ≫ ofBasedJetSections U = w^♯` (`lift` on coefficients is `w^♯`). -/
theorem relativeJetScheme.ι_glued_ofBasedJet_comp_hom (W : CategoryTheory.Over C)
    (φ : (relativeJetFunctor (k := k) Z s hs r).obj (Opposite.op W)) (U : C.AffineZariskiSite) :
    (W.hom ⁻¹ᵁ U.1).ι ≫
      ((W.left.openCoverOfIsOpenCover (fun U : C.AffineZariskiSite => W.hom ⁻¹ᵁ U.1)
            (relativeJetScheme.ofBasedJet_isOpenCover W)).glueMorphisms
        (fun U => (W.hom ⁻¹ᵁ U.1).toSpecΓ ≫
          AlgebraicGeometry.Spec.map (relativeJetScheme.ofBasedJetSections (k := k) Z s hs r W φ U) ≫
          (relativeJetScheme.gluingData Z s hs r).cover.f U)
        (relativeJetScheme.ofBasedJet_glue_compat (k := k) Z s hs r W φ)) ≫
      (relativeJetScheme (k := k) Z s hs r).hom =
    (W.hom ⁻¹ᵁ U.1).ι ≫ W.hom := by
  letI := relativeJetScheme.sectionsAlgebra Z U.1
  rw [← CategoryTheory.Category.assoc, relativeJetScheme.ι_glued_ofBasedJet,
    AlgebraicGeometry.Scheme.Hom.ι_comp_eq_toSpecΓ_SpecMap_appLE_fromSpec (W.hom ⁻¹ᵁ U.1) U.2 W.hom le_rfl,
    AlgebraicGeometry.Scheme.Hom.appLE_eq_app]
  simp only [CategoryTheory.Category.assoc]
  rw [relativeJetScheme.chart_comp_hom (k := k) Z s hs r U, ← AlgebraicGeometry.Spec.map_comp_assoc]
  congr 3
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  exact relativeJetScheme.ofBasedJetSections_apply_algebraMap (k := k) Z s hs r W φ U c

/-- Third proof obligation of `ofBasedJet` (`Over.homMk`): the glued morphism lies over `C`. Proof: check on the cover
`{w⁻¹U}` (`Cover.hom_ext`, `ι_glueMorphisms`); the chart `Spec J_r(B_U,ε_U) → J → C` is `Spec` of the coefficient map
`Γ(C,U) → J_r(B_U,ε_U)` followed by `U ↪ C`, and `lift` on coefficients is `ρ = w^♯` (`lift ∘ algebraMap = ρ`). -/

theorem relativeJetScheme.ofBasedJet_over (W : CategoryTheory.Over C)
    (φ : (relativeJetFunctor (k := k) Z s hs r).obj (Opposite.op W)) :
    ((W.left.openCoverOfIsOpenCover (fun U : C.AffineZariskiSite => W.hom ⁻¹ᵁ U.1)
            (relativeJetScheme.ofBasedJet_isOpenCover W)).glueMorphisms
        (fun U => (W.hom ⁻¹ᵁ U.1).toSpecΓ ≫
          AlgebraicGeometry.Spec.map (relativeJetScheme.ofBasedJetSections (k := k) Z s hs r W φ U) ≫
          (relativeJetScheme.gluingData Z s hs r).cover.f U)
        (relativeJetScheme.ofBasedJet_glue_compat (k := k) Z s hs r W φ)) ≫ (relativeJetScheme (k := k) Z s hs r).hom = W.hom :=
  (W.left.openCoverOfIsOpenCover (fun U : C.AffineZariskiSite => W.hom ⁻¹ᵁ U.1)
    (relativeJetScheme.ofBasedJet_isOpenCover W)).hom_ext _ _
    (fun U => relativeJetScheme.ι_glued_ofBasedJet_comp_hom (k := k) Z s hs r W φ U)

end OfBasedJet

/-- From a based jet to a `C`-morphism `W → J`: on the open cover `{w⁻¹U}` of `W`, land in the chart
`Spec J_r(B_U, ε_U)` through the `Spec` adjunction, then glue. -/

noncomputable def relativeJetScheme.ofBasedJet {k : Type u} [Field k] {C : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (Z : CategoryTheory.Over C) [AlgebraicGeometry.IsAffineHom Z.hom]
    (s : C ⟶ Z.left) (hs : s ≫ Z.hom = CategoryTheory.CategoryStruct.id C) (r : ℕ)
    (W : CategoryTheory.Over C) (φ : (relativeJetFunctor (k := k) Z s hs r).obj (Opposite.op W)) :
    W ⟶ relativeJetScheme (k := k) Z s hs r :=
  CategoryTheory.Over.homMk
    ((W.left.openCoverOfIsOpenCover (fun U : C.AffineZariskiSite => W.hom ⁻¹ᵁ U.1)
        (relativeJetScheme.ofBasedJet_isOpenCover W)).glueMorphisms
      (fun U => (W.hom ⁻¹ᵁ U.1).toSpecΓ ≫
        AlgebraicGeometry.Spec.map (relativeJetScheme.ofBasedJetSections (k := k) Z s hs r W φ U) ≫
        (relativeJetScheme.gluingData Z s hs r).cover.f U)
      (relativeJetScheme.ofBasedJet_glue_compat (k := k) Z s hs r W φ))
    (relativeJetScheme.ofBasedJet_over (k := k) Z s hs r W φ)

/-- The proof obligation of `toBasedJet` (the subtype condition): the pullback of the universal jet along `a` is again
a based jet. Proof: the universal jet satisfies both conditions (`universalJet_comp_hom`:
`universalJet ≫ Z.hom = pr ≫ J.hom`; `jetConstantTerm_comp_universalJet`:
`jetConstantTerm ≫ universalJet = J.hom ≫ s`), and they transport along `a` by the naturality of `jetThickeningMap` with
respect to `pr` and `jetConstantTerm` (`jetThickeningMap_proj`, `jetConstantTerm_naturality`) and `Over.w a`. -/

theorem relativeJetScheme.toBasedJet_prop {k : Type u} [Field k] {C : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (Z : CategoryTheory.Over C) [AlgebraicGeometry.IsAffineHom Z.hom]
    (s : C ⟶ Z.left) (hs : s ≫ Z.hom = CategoryTheory.CategoryStruct.id C) (r : ℕ)
    (W : CategoryTheory.Over C) (a : W ⟶ relativeJetScheme (k := k) Z s hs r) :
    letI : W.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨W.hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    letI : (relativeJetScheme (k := k) Z s hs r).left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨(relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    haveI : a.left.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨CategoryTheory.Over.w_assoc a _⟩
    (jetThickeningMap (k := k) r a.left ≫ relativeJetScheme.universalJet (k := k) Z s hs r) ≫ Z.hom =
        jetThickeningProj (k := k) r W.left ≫ W.hom ∧
      jetConstantTerm (k := k) r W.left ≫
          (jetThickeningMap (k := k) r a.left ≫ relativeJetScheme.universalJet (k := k) Z s hs r) =
        W.hom ≫ s := by
  letI : W.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨W.hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  letI : (relativeJetScheme (k := k) Z s hs r).left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨(relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  haveI : a.left.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨CategoryTheory.Over.w_assoc a _⟩
  constructor
  · rw [CategoryTheory.Category.assoc, relativeJetScheme.universalJet_comp_hom,
      ← CategoryTheory.Category.assoc, jetThickeningMap_proj, CategoryTheory.Category.assoc,
      CategoryTheory.Over.w]
  · rw [← CategoryTheory.Category.assoc, jetConstantTerm_naturality, CategoryTheory.Category.assoc,
      relativeJetScheme.jetConstantTerm_comp_universalJet_eq, ← CategoryTheory.Category.assoc,
      CategoryTheory.Over.w]

/-- From a `C`-morphism `a : W → J` to a based jet: the pullback of the universal jet along `a`. -/

noncomputable def relativeJetScheme.toBasedJet {k : Type u} [Field k] {C : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (Z : CategoryTheory.Over C) [AlgebraicGeometry.IsAffineHom Z.hom]
    (s : C ⟶ Z.left) (hs : s ≫ Z.hom = CategoryTheory.CategoryStruct.id C) (r : ℕ)
    (W : CategoryTheory.Over C) (a : W ⟶ relativeJetScheme (k := k) Z s hs r) :
    (relativeJetFunctor (k := k) Z s hs r).obj (Opposite.op W) :=
  letI : W.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨W.hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  letI : (relativeJetScheme (k := k) Z s hs r).left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨(relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  haveI : a.left.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨CategoryTheory.Over.w_assoc a _⟩
  ⟨jetThickeningMap (k := k) r a.left ≫ relativeJetScheme.universalJet (k := k) Z s hs r,
    relativeJetScheme.toBasedJet_prop (k := k) Z s hs r W a⟩

section Inverses

variable {k : Type u} [Field k] {C : AlgebraicGeometry.Scheme.{u}}
  [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (Z : CategoryTheory.Over C) [AlgebraicGeometry.IsAffineHom Z.hom]
  (s : C ⟶ Z.left) (hs : s ≫ Z.hom = CategoryTheory.CategoryStruct.id C) (r : ℕ)

/-- A `C`-morphism `a : W ⟶ J` maps `w⁻¹U` into the chart `J_U = (J ⟶ C)⁻¹U`. -/
theorem relativeJetScheme.over_preimage_le (W : CategoryTheory.Over C)
    (a : W ⟶ relativeJetScheme (k := k) Z s hs r) (U : C.AffineZariskiSite) :
    W.hom ⁻¹ᵁ U.1 ≤ a.left ⁻¹ᵁ relativeJetScheme.chartOpen (k := k) Z s hs r U := by
  rw [← relativeJetScheme.hom_preimage_chartOpen, ← AlgebraicGeometry.Scheme.Hom.comp_preimage,
    CategoryTheory.Over.w]

/-- `pr⁻¹(w⁻¹U) ≤ (a × 𝟙)⁻¹(pr⁻¹J_U)`. -/
theorem relativeJetScheme.proj_preimage_le_jetThickeningMap_preimage (W : CategoryTheory.Over C)
    (a : W ⟶ relativeJetScheme (k := k) Z s hs r) (U : C.AffineZariskiSite) :
    letI : W.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨W.hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    letI : (relativeJetScheme (k := k) Z s hs r).left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨(relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    haveI : a.left.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨CategoryTheory.Over.w_assoc a _⟩
    jetThickeningProj (k := k) r W.left ⁻¹ᵁ (W.hom ⁻¹ᵁ U.1) ≤
      jetThickeningMap (k := k) r a.left ⁻¹ᵁ (jetThickeningProj (k := k) r (relativeJetScheme (k := k) Z s hs r).left ⁻¹ᵁ
        relativeJetScheme.chartOpen (k := k) Z s hs r U) := by
  letI : W.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨W.hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  letI : (relativeJetScheme (k := k) Z s hs r).left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨(relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  haveI : a.left.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨CategoryTheory.Over.w_assoc a _⟩
  intro x hx
  show (jetThickeningMap (k := k) r a.left ≫ jetThickeningProj (k := k) r _) x ∈
    relativeJetScheme.chartOpen (k := k) Z s hs r U
  rw [jetThickeningMap_proj]
  exact relativeJetScheme.over_preimage_le (k := k) Z s hs r W a U hx

/-- The `t^n`-coefficient of the based jet `toBasedJet a = (a × 𝟙) ≫ universalJet` on `pr⁻¹w⁻¹U`, applied to
`b ∈ Γ(Z, π⁻¹U)`, is `a^♯ (chartSections U (D_n b))`: `(a × 𝟙)^♯` acts coefficientwise by `a^♯`
(`coeff_jetThickeningMap_appLE`) and `universalJet^♯ = universalJetSections U` has coefficients
`chartSections U (D_n b)` (`universalJet_appLE`, `coeff_universalJetSections`). -/
theorem relativeJetScheme.toBasedJet_appLE_coeff (W : CategoryTheory.Over C)
    (a : W ⟶ relativeJetScheme (k := k) Z s hs r) (U : C.AffineZariskiSite) (n : ℕ) (hn : n ≤ r)
    (b : Γ(Z.left, Z.hom ⁻¹ᵁ U.1)) :
    letI : W.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨W.hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    letI := relativeJetScheme.sectionsAlgebra Z U.1
    jetThickening.coeff (k := k) r W.left (W.hom ⁻¹ᵁ U.1) n hn
        (((relativeJetScheme.toBasedJet (k := k) Z s hs r W a).1.appLE (Z.hom ⁻¹ᵁ U.1)
          (jetThickeningProj (k := k) r W.left ⁻¹ᵁ (W.hom ⁻¹ᵁ U.1))
          (relativeJetScheme.ofBasedJetSections_le (k := k) Z s hs r W
            (relativeJetScheme.toBasedJet (k := k) Z s hs r W a) U)).hom b) =
      (a.left.appLE (relativeJetScheme.chartOpen (k := k) Z s hs r U) (W.hom ⁻¹ᵁ U.1)
          (relativeJetScheme.over_preimage_le (k := k) Z s hs r W a U)).hom
        ((relativeJetScheme.chartSections (k := k) Z s hs r U).hom
          (BasedJetAlgebra.coeffClass (relativeJetScheme.augmentation Z s hs U.1) r n b)) := by
  letI : W.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨W.hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  letI : (relativeJetScheme (k := k) Z s hs r).left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨(relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  haveI : a.left.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨CategoryTheory.Over.w_assoc a _⟩
  letI := relativeJetScheme.sectionsAlgebra Z U.1
  show jetThickening.coeff (k := k) r W.left (W.hom ⁻¹ᵁ U.1) n hn
    (((jetThickeningMap (k := k) r a.left ≫ relativeJetScheme.universalJet (k := k) Z s hs r).appLE
      (Z.hom ⁻¹ᵁ U.1) (jetThickeningProj (k := k) r W.left ⁻¹ᵁ (W.hom ⁻¹ᵁ U.1)) _).hom b) = _
  rw [← AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE (jetThickeningMap (k := k) r a.left)
    (relativeJetScheme.universalJet (k := k) Z s hs r) (Z.hom ⁻¹ᵁ U.1)
    (jetThickeningProj (k := k) r (relativeJetScheme (k := k) Z s hs r).left ⁻¹ᵁ
      relativeJetScheme.chartOpen (k := k) Z s hs r U)
    (jetThickeningProj (k := k) r W.left ⁻¹ᵁ (W.hom ⁻¹ᵁ U.1))
    (relativeJetScheme.universalJet_preimage_le (k := k) Z s hs r U)
    (relativeJetScheme.proj_preimage_le_jetThickeningMap_preimage (k := k) Z s hs r W a U),
    CommRingCat.hom_comp, RingHom.comp_apply,
    jetThickening.coeff_jetThickeningMap_appLE (k := k) r a.left
      (relativeJetScheme.chartOpen (k := k) Z s hs r U) (W.hom ⁻¹ᵁ U.1)
      (relativeJetScheme.over_preimage_le (k := k) Z s hs r W a U) _ n hn,
    relativeJetScheme.universalJet_appLE_chartOpen, CommRingCat.hom_ofHom,
    relativeJetScheme.coeff_universalJetSections]

/-- `ofBasedJet φ` restricted to `w⁻¹U` is the piece `toSpecΓ ≫ Spec (ofBasedJetSections U) ≫ chart U`. -/
theorem relativeJetScheme.ι_ofBasedJet_left (W : CategoryTheory.Over C)
    (φ : (relativeJetFunctor (k := k) Z s hs r).obj (Opposite.op W)) (U : C.AffineZariskiSite) :
    (W.hom ⁻¹ᵁ U.1).ι ≫ (relativeJetScheme.ofBasedJet (k := k) Z s hs r W φ).left =
      (W.hom ⁻¹ᵁ U.1).toSpecΓ ≫
        AlgebraicGeometry.Spec.map (relativeJetScheme.ofBasedJetSections (k := k) Z s hs r W φ U) ≫
        relativeJetScheme.chart (k := k) Z s hs r U :=
  relativeJetScheme.ι_glued_ofBasedJet (k := k) Z s hs r W φ U

/-- `(ofBasedJet φ)^♯` on the chart `J_U`, read through `chartSections U`, is `ofBasedJetSections U φ`. -/
theorem relativeJetScheme.chartSections_comp_ofBasedJet_appLE (W : CategoryTheory.Over C)
    (φ : (relativeJetFunctor (k := k) Z s hs r).obj (Opposite.op W)) (U : C.AffineZariskiSite) :
    relativeJetScheme.chartSections (k := k) Z s hs r U ≫
        (relativeJetScheme.ofBasedJet (k := k) Z s hs r W φ).left.appLE
          (relativeJetScheme.chartOpen (k := k) Z s hs r U) (W.hom ⁻¹ᵁ U.1)
          (relativeJetScheme.over_preimage_le (k := k) Z s hs r W _ U) =
      relativeJetScheme.ofBasedJetSections (k := k) Z s hs r W φ U :=
  AlgebraicGeometry.Scheme.chartSec_appLE_of_ι_comp (W.hom ⁻¹ᵁ U.1) (relativeJetScheme.chart (k := k) Z s hs r U)
    _ _ (relativeJetScheme.ι_ofBasedJet_left (k := k) Z s hs r W φ U) _

/-- `{pr⁻¹(w⁻¹U)}` covers `W ×_k D_r`. -/
theorem relativeJetScheme.proj_preimage_isOpenCover (W : CategoryTheory.Over C) :
    letI : W.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨W.hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    TopologicalSpace.IsOpenCover (fun U : C.AffineZariskiSite =>
      jetThickeningProj (k := k) r W.left ⁻¹ᵁ (W.hom ⁻¹ᵁ U.1)) :=
  letI : W.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨W.hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  (relativeJetScheme.ofBasedJet_isOpenCover W).comap (jetThickeningProj (k := k) r W.left).base.1

/-- `toBasedJet (ofBasedJet φ) = φ` on `pr⁻¹(w⁻¹U)`: both factor through `Spec Γ(Z, π⁻¹U)` and the comodule
maps have the same `t`-coefficients (`toBasedJet_appLE_coeff`, `chartSections_comp_ofBasedJet_appLE`,
`ofBasedJetSections_apply_coeffClass`). -/
theorem relativeJetScheme.ι_toBasedJet_ofBasedJet (W : CategoryTheory.Over C)
    (φ : (relativeJetFunctor (k := k) Z s hs r).obj (Opposite.op W)) (U : C.AffineZariskiSite) :
    letI : W.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨W.hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    (jetThickeningProj (k := k) r W.left ⁻¹ᵁ (W.hom ⁻¹ᵁ U.1)).ι ≫
        (relativeJetScheme.toBasedJet (k := k) Z s hs r W (relativeJetScheme.ofBasedJet (k := k) Z s hs r W φ)).1 =
      (jetThickeningProj (k := k) r W.left ⁻¹ᵁ (W.hom ⁻¹ᵁ U.1)).ι ≫ φ.1 := by
  letI : W.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨W.hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  letI := relativeJetScheme.sectionsAlgebra Z U.1
  rw [AlgebraicGeometry.Scheme.Hom.ι_comp_eq_toSpecΓ_SpecMap_appLE_fromSpec _ (U.2.preimage Z.hom) _
      (relativeJetScheme.ofBasedJetSections_le (k := k) Z s hs r W _ U),
    AlgebraicGeometry.Scheme.Hom.ι_comp_eq_toSpecΓ_SpecMap_appLE_fromSpec _ (U.2.preimage Z.hom) _
      (relativeJetScheme.ofBasedJetSections_le (k := k) Z s hs r W φ U)]
  congr 3
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro b
  apply jetThickening.ext_coeff
  intro n hn
  rw [relativeJetScheme.toBasedJet_appLE_coeff, ← relativeJetScheme.ofBasedJetSections_apply_coeffClass
    (k := k) Z s hs r W φ U n hn b, ← relativeJetScheme.chartSections_comp_ofBasedJet_appLE (k := k) Z s hs r W φ U]
  rfl

/-- The `right_inv` obligation of `representableBy`: `toBasedJet ∘ ofBasedJet = id`. Proof: after `Subtype.ext`,
check on the cover `{pr⁻¹w⁻¹U}` of `W ×_k D_r` (`ι_toBasedJet_ofBasedJet`). -/

theorem relativeJetScheme.representableBy_right_inv (W : CategoryTheory.Over C) :
    Function.RightInverse (relativeJetScheme.ofBasedJet (k := k) Z s hs r W)
      (relativeJetScheme.toBasedJet (k := k) Z s hs r W) := by
  letI : W.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨W.hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  intro φ
  apply Subtype.ext
  exact ((jetThickening (k := k) r W.left).openCoverOfIsOpenCover
    (fun U : C.AffineZariskiSite => jetThickeningProj (k := k) r W.left ⁻¹ᵁ (W.hom ⁻¹ᵁ U.1))
    (relativeJetScheme.proj_preimage_isOpenCover (k := k) r W)).hom_ext _ _
    (fun U => relativeJetScheme.ι_toBasedJet_ofBasedJet (k := k) Z s hs r W φ U)

/-- `ofBasedJet (toBasedJet a) = a` on `w⁻¹U`: both factor through the chart `Spec J_r(B_U, ε_U)` and the
comodule maps agree on the generators (`ofBasedJetSections_apply_algebraMap` with `hom_appLE_chartOpen`;
`ofBasedJetSections_apply_coeffClass` with `toBasedJet_appLE_coeff`). -/
theorem relativeJetScheme.ι_ofBasedJet_toBasedJet (W : CategoryTheory.Over C)
    (a : W ⟶ relativeJetScheme (k := k) Z s hs r) (U : C.AffineZariskiSite) :
    (W.hom ⁻¹ᵁ U.1).ι ≫
        (relativeJetScheme.ofBasedJet (k := k) Z s hs r W (relativeJetScheme.toBasedJet (k := k) Z s hs r W a)).left =
      (W.hom ⁻¹ᵁ U.1).ι ≫ a.left := by
  letI : W.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨W.hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  letI := relativeJetScheme.sectionsAlgebra Z U.1
  rw [relativeJetScheme.ι_ofBasedJet_left,
    ← AlgebraicGeometry.Scheme.Hom.resLE_comp_ι a.left (relativeJetScheme.over_preimage_le (k := k) Z s hs r W a U),
    relativeJetScheme.chartOpen_ι_eq, ← AlgebraicGeometry.Scheme.Opens.toSpecΓ_SpecMap_appLE_assoc]
  congr 1
  rw [← AlgebraicGeometry.Spec.map_comp_assoc]
  congr 2
  apply CommRingCat.hom_ext
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro c
    show (relativeJetScheme.ofBasedJetSections (k := k) Z s hs r W _ U).hom
        (algebraMap Γ(C, U.1) (BasedJetAlgebra (relativeJetScheme.augmentation Z s hs U.1) r) c) =
      (a.left.appLE (relativeJetScheme.chartOpen (k := k) Z s hs r U) (W.hom ⁻¹ᵁ U.1)
          (relativeJetScheme.over_preimage_le (k := k) Z s hs r W a U)).hom
        ((relativeJetScheme.chartSections (k := k) Z s hs r U).hom
          (((relativeJetScheme.coefficientMap Z s hs r).app (Opposite.op U)).hom c))
    rw [relativeJetScheme.ofBasedJetSections_apply_algebraMap, ← relativeJetScheme.hom_appLE_chartOpen_apply,
      ← CategoryTheory.comp_apply, AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE,
      AlgebraicGeometry.Scheme.Hom.appLE_congr_hom (CategoryTheory.Over.w a) U.1 (W.hom ⁻¹ᵁ U.1) _ le_rfl,
      AlgebraicGeometry.Scheme.Hom.appLE_eq_app]
  · rintro ⟨q, b⟩
    have hq : Ideal.Quotient.mk (BasedJetAlgebra.relations (relativeJetScheme.augmentation Z s hs U.1) r)
        (MvPolynomial.X (q, b)) =
        BasedJetAlgebra.coeffClass (relativeJetScheme.augmentation Z s hs U.1) r (q.1 + 1) b :=
      (BasedJetAlgebra.coeffClass_succ _ r q.1 q.2 b).symm
    show (relativeJetScheme.ofBasedJetSections (k := k) Z s hs r W _ U).hom
        (Ideal.Quotient.mk _ (MvPolynomial.X (q, b))) =
      (a.left.appLE (relativeJetScheme.chartOpen (k := k) Z s hs r U) (W.hom ⁻¹ᵁ U.1)
          (relativeJetScheme.over_preimage_le (k := k) Z s hs r W a U)).hom
        ((relativeJetScheme.chartSections (k := k) Z s hs r U).hom
          (Ideal.Quotient.mk _ (MvPolynomial.X (q, b))))
    rw [hq, relativeJetScheme.ofBasedJetSections_apply_coeffClass (k := k) Z s hs r W _ U (q.1 + 1)
      (Nat.succ_le_of_lt q.2) b, relativeJetScheme.toBasedJet_appLE_coeff]

/-- The `left_inv` obligation of `representableBy`: `ofBasedJet ∘ toBasedJet = id`. Proof (relative version of
Ein–Mustață Prop. 2.2): after `Over.OverMorphism.ext`, check on the cover `{w⁻¹U}` of `W`
(`ι_ofBasedJet_toBasedJet`). -/

theorem relativeJetScheme.representableBy_left_inv (W : CategoryTheory.Over C) :
    Function.LeftInverse (relativeJetScheme.ofBasedJet (k := k) Z s hs r W)
      (relativeJetScheme.toBasedJet (k := k) Z s hs r W) := by
  intro a
  apply CategoryTheory.Over.OverMorphism.ext
  exact (W.left.openCoverOfIsOpenCover (fun U : C.AffineZariskiSite => W.hom ⁻¹ᵁ U.1)
    (relativeJetScheme.ofBasedJet_isOpenCover W)).hom_ext _ _
    (fun U => relativeJetScheme.ι_ofBasedJet_toBasedJet (k := k) Z s hs r W a U)

end Inverses

/-- Functoriality of `jetThickeningMap` with respect to composition. -/

private theorem jetThickeningMap_comp_aux {k : Type u} [Field k] (r : ℕ) {A B D : AlgebraicGeometry.Scheme.{u}}
    [A.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] [B.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [D.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (g : A ⟶ B) (h : B ⟶ D)
    [g.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [h.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [(g ≫ h).IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))] :
    jetThickeningMap (k := k) r (g ≫ h) =
      jetThickeningMap (k := k) r g ≫ jetThickeningMap (k := k) r h := by
  delta jetThickeningMap jetThickening
  apply CategoryTheory.Limits.pullback.hom_ext
  · rw [CategoryTheory.Category.assoc, CategoryTheory.Limits.pullback.lift_fst, CategoryTheory.Limits.pullback.lift_fst, CategoryTheory.Limits.pullback.lift_fst_assoc, CategoryTheory.Category.assoc]
  · rw [CategoryTheory.Category.assoc, CategoryTheory.Limits.pullback.lift_snd, CategoryTheory.Limits.pullback.lift_snd, CategoryTheory.Limits.pullback.lift_snd_assoc, CategoryTheory.Category.assoc,
      CategoryTheory.Category.comp_id, CategoryTheory.Category.comp_id, CategoryTheory.Category.comp_id]

/-- The `homEquiv_comp` obligation of `representableBy` (naturality in `W`): `toBasedJet (f ≫ a) = F.map f (toBasedJet a)`,
i.e. the functoriality of `jetThickeningMap` with respect to composition (composition of `pullback.map`). -/

theorem relativeJetScheme.representableBy_homEquiv_comp {k : Type u} [Field k] {C : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (Z : CategoryTheory.Over C) [AlgebraicGeometry.IsAffineHom Z.hom]
    (s : C ⟶ Z.left) (hs : s ≫ Z.hom = CategoryTheory.CategoryStruct.id C) (r : ℕ)
    {W W' : CategoryTheory.Over C} (f : W ⟶ W') (a : W' ⟶ relativeJetScheme (k := k) Z s hs r) :
    relativeJetScheme.toBasedJet (k := k) Z s hs r W (f ≫ a) =
      (relativeJetFunctor (k := k) Z s hs r).map f.op
        (relativeJetScheme.toBasedJet (k := k) Z s hs r W' a) := by
  letI : W.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨W.hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  letI : W'.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨W'.hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  letI : (relativeJetScheme (k := k) Z s hs r).left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨(relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  haveI : a.left.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨CategoryTheory.Over.w_assoc a _⟩
  haveI : f.left.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨CategoryTheory.Over.w_assoc f _⟩
  haveI : (f ≫ a).left.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨CategoryTheory.Over.w_assoc (f ≫ a) _⟩
  apply Subtype.ext
  show jetThickeningMap (k := k) r (f ≫ a).left ≫ relativeJetScheme.universalJet (k := k) Z s hs r =
    jetThickeningMap (k := k) r f.left ≫
      (jetThickeningMap (k := k) r a.left ≫ relativeJetScheme.universalJet (k := k) Z s hs r)
  rw [← CategoryTheory.Category.assoc]
  congr 1
  exact jetThickeningMap_comp_aux (k := k) r f.left a.left

/-- `J_r^s(Z/C)` represents the based jet functor: both directions of the bijection are constructions, and the inverse
laws and naturality are the relative version of Ein–Mustață Prop. 2.2. -/

noncomputable def relativeJetScheme.representableBy {k : Type u} [Field k] {C : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (Z : CategoryTheory.Over C) [AlgebraicGeometry.IsAffineHom Z.hom]
    (s : C ⟶ Z.left) (hs : s ≫ Z.hom = CategoryTheory.CategoryStruct.id C) (r : ℕ) :
    (relativeJetFunctor (k := k) Z s hs r).RepresentableBy (relativeJetScheme (k := k) Z s hs r) where
  homEquiv {W} :=
    { toFun := relativeJetScheme.toBasedJet (k := k) Z s hs r W
      invFun := relativeJetScheme.ofBasedJet (k := k) Z s hs r W
      left_inv := relativeJetScheme.representableBy_left_inv (k := k) Z s hs r W
      right_inv := relativeJetScheme.representableBy_right_inv (k := k) Z s hs r W }
  homEquiv_comp := relativeJetScheme.representableBy_homEquiv_comp (k := k) Z s hs r

end
