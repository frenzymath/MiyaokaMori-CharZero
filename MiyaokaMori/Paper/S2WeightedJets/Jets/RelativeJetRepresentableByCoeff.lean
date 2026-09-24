import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetAlgebraCoaction
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetConstantTerm
import MiyaokaMori.Paper.S2WeightedJets.Jets.RelativeJetFunctor
import MiyaokaMori.Paper.S2WeightedJets.Jets.RelativeJetRepresentableByCharts
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.JetThickeningSectionsCoeff

/-! # Representability of the relative jet functor: coefficient computations

Everything about morphisms into the affine charts of `Z` and `J_r^s(Z/C)` is decided by comparing the
`t`-coefficients of functions on the thickening `W ×_k D_r` (`jetThickening.coeff`, `jetThickening.ext_coeff`).
This module collects the coefficient formulas used by the proof obligations of the representability theorem:

* `jetThickening.appLE_jetThickeningMap_sectionsHom`, `jetThickening.coeff_jetThickeningMap_appLE`:
  `(g × 𝟙)^♯` acts on `Γ(W, V)[t]/(t^{r+1})` coefficientwise by `g^♯` (a restatement of
  `jetThickening.sectionsHom_jetThickeningMap`, which lives downstream, hence reproved);
* `jetThickening.coeff_proj_app`: coefficients of a pulled-back function `pr^♯ a` (`a` in degree 0);
* `jetConstantTerm_sectionsHom`, `jetConstantTerm_appLE_eq_coeff_zero`: the constant-term section
  `W ⟶ W ×_k D_r` takes the coefficient of `t^0`;
* `relativeJetScheme.coeff_universalJetSections`: the `t^n`-coefficient of the universal jet of `b` on the chart
  `U` is `chartSections U (D_n b)`; consequences: restriction to a basic open (`universalJetSections_restrict`),
  the coefficients `π^♯ a` (`universalJetSections_algebraMap`), and the constant term (`jetConstantTerm_appLE_universalJetSections`).

References: §2 of the paper (the based relative jet scheme); Ein–Mustață, Prop. 2.2 (the universal jet
`b ↦ Σ D_n b tⁿ`).

Implementation note: `TruncatedJetRing` is `AdjoinRoot (X^(r+1))`; representatives are taken with
`jetProjection_surjective` (so that `rw` sees `jetProjection … p`, not `Ideal.Quotient.mk (span …) p`), and
`Ideal.Quotient.lift_mk` is rewritten with `erw` (it matches only up to unfolding `AdjoinRoot`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.style.haveILetI false
-- `U.1` for `U : C.AffineZariskiSite` (a `def` wrapping a subtype) makes `rw` motives fail to typecheck under
-- the strict transparency check (Mathlib disables it around `AffineZariskiSite` too).
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section


/-! ## `(g × 𝟙)^♯` on truncated polynomials -/

section JetThickeningMap

variable {k : Type u} [Field k] (r : ℕ) {W W' : AlgebraicGeometry.Scheme.{u}}
  [W.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] [W'.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
  (g : W' ⟶ W) [g.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))]

/-- `pr⁻¹(g⁻¹V) ≤ (g × 𝟙)⁻¹(pr⁻¹V)` (from `(g × 𝟙) ≫ pr = pr ≫ g`). -/
theorem jetThickening.preimage_le_jetThickeningMap_preimage (V : W.Opens) :
    jetThickeningProj (k := k) r W' ⁻¹ᵁ (g ⁻¹ᵁ V) ≤
      jetThickeningMap (k := k) r g ⁻¹ᵁ (jetThickeningProj (k := k) r W ⁻¹ᵁ V) := by
  intro x hx
  show (jetThickeningMap (k := k) r g ≫ jetThickeningProj (k := k) r W) x ∈ V
  rw [jetThickeningMap_proj]
  exact hx

/-- `(g × 𝟙)^♯` is natural for `sectionsHom`: `(g × 𝟙)^♯ (sectionsHom_V p) = sectionsHom_{g⁻¹V} (g^♯ p)`
(coefficientwise). Both sides are ring homomorphisms out of `Γ(W,V)[t]/(t^{r+1})`; check on constants
(`(g × 𝟙) ≫ pr = pr ≫ g`) and on `t` (`(g × 𝟙) ≫ snd = snd`). -/
theorem jetThickening.appLE_jetThickeningMap_sectionsHom (V : W.Opens)
    (p : MiyaokaMori.Jet.TruncatedJetRing Γ(W, V) r)
    (hle : jetThickeningProj (k := k) r W' ⁻¹ᵁ (g ⁻¹ᵁ V) ≤
      jetThickeningMap (k := k) r g ⁻¹ᵁ (jetThickeningProj (k := k) r W ⁻¹ᵁ V)) :
    ((jetThickeningMap (k := k) r g).appLE _ _ hle).hom
        (jetThickening.sectionsHom (k := k) r W V p) =
      jetThickening.sectionsHom (k := k) r W' (g ⁻¹ᵁ V)
        (MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.map r (g.app V).hom p) := by
  obtain ⟨p, rfl⟩ := MiyaokaMori.Jet.jetProjection_surjective _ _ p
  rw [MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.map_projection]
  unfold jetThickening.sectionsHom
  rw [MiyaokaMori.Jet.lift_jetProjection, MiyaokaMori.Jet.lift_jetProjection]
  simp only [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_map]
  rw [Polynomial.hom_eval₂]
  congr 1
  · ext a
    have h1 := AlgebraicGeometry.Scheme.Hom.comp_appLE (jetThickeningMap (k := k) r g)
      (jetThickeningProj (k := k) r W) V
      (jetThickeningProj (k := k) r W' ⁻¹ᵁ (g ⁻¹ᵁ V)) hle
    have h2 := AlgebraicGeometry.Scheme.Hom.comp_appLE (jetThickeningProj (k := k) r W') g V
      (jetThickeningProj (k := k) r W' ⁻¹ᵁ (g ⁻¹ᵁ V)) le_rfl
    have h3 := AlgebraicGeometry.Scheme.Hom.appLE_congr_hom (jetThickeningMap_proj (k := k) r g) V
      (jetThickeningProj (k := k) r W' ⁻¹ᵁ (g ⁻¹ᵁ V)) hle le_rfl
    rw [h1, h2] at h3
    have h4 := congrArg (fun φ : Γ(W, V) ⟶ Γ(jetThickening (k := k) r W',
      jetThickeningProj (k := k) r W' ⁻¹ᵁ (g ⁻¹ᵁ V)) => φ.hom a) h3
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h4
    rw [AlgebraicGeometry.Scheme.Hom.appLE_eq_app] at h4
    exact h4
  · have h1 := AlgebraicGeometry.Scheme.Hom.map_appLE (jetThickeningMap (k := k) r g) hle
      (CategoryTheory.homOfLE (le_top : jetThickeningProj (k := k) r W ⁻¹ᵁ V ≤ ⊤)).op
    have h2 := congrArg (fun φ : Γ(jetThickening (k := k) r W, ⊤) ⟶
      Γ(jetThickening (k := k) r W', jetThickeningProj (k := k) r W' ⁻¹ᵁ (g ⁻¹ᵁ V)) =>
        φ.hom (jetThickening.parameter (k := k) r W)) h1
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h2
    rw [h2]
    unfold jetThickening.parameter
    have h3 := AlgebraicGeometry.Scheme.Hom.comp_appLE (jetThickeningMap (k := k) r g)
      (CategoryTheory.Limits.pullback.snd (W ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
        (jetBase k r ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) ⊤
      (jetThickeningProj (k := k) r W' ⁻¹ᵁ (g ⁻¹ᵁ V)) le_top
    have h4 := AlgebraicGeometry.Scheme.Hom.appLE_congr_hom (jetThickeningMap_snd (k := k) r g) ⊤
      (jetThickeningProj (k := k) r W' ⁻¹ᵁ (g ⁻¹ᵁ V)) le_top le_top
    rw [h3] at h4
    have h5 := congrArg (fun φ : Γ(jetBase k r, ⊤) ⟶
      Γ(jetThickening (k := k) r W', jetThickeningProj (k := k) r W' ⁻¹ᵁ (g ⁻¹ᵁ V)) =>
        φ.hom ((AlgebraicGeometry.Scheme.ΓSpecIso
          (CommRingCat.of (MiyaokaMori.RingTheory.GlobalTruncatedParameter k r))).inv.hom
            (MiyaokaMori.Jet.jetProjection k r Polynomial.X))) h4
    simp only [CommRingCat.hom_comp] at h5
    exact h5.trans rfl

/-- Coefficientwise form, for any open `V' ≤ g⁻¹V` of `W'`:
`coeff n ((g × 𝟙)^♯ x) = g^♯ (coeff n x)` on `pr⁻¹V'`. -/
theorem jetThickening.coeff_jetThickeningMap_appLE (V : W.Opens) (V' : W'.Opens) (hV' : V' ≤ g ⁻¹ᵁ V)
    (hle : jetThickeningProj (k := k) r W' ⁻¹ᵁ V' ≤
      jetThickeningMap (k := k) r g ⁻¹ᵁ (jetThickeningProj (k := k) r W ⁻¹ᵁ V))
    (n : ℕ) (hn : n ≤ r) (x : Γ(jetThickening (k := k) r W, jetThickeningProj (k := k) r W ⁻¹ᵁ V)) :
    jetThickening.coeff (k := k) r W' V' n hn (((jetThickeningMap (k := k) r g).appLE _ _ hle).hom x) =
      (g.appLE V V' hV').hom (jetThickening.coeff (k := k) r W V n hn x) := by
  obtain ⟨p, rfl⟩ := (jetThickening.sectionsHom_bijective (k := k) r W V).2 x
  have hle' : jetThickeningProj (k := k) r W' ⁻¹ᵁ V' ≤ jetThickeningProj (k := k) r W' ⁻¹ᵁ (g ⁻¹ᵁ V) :=
    fun _ hx => hV' hx
  have h1 : (jetThickeningMap (k := k) r g).appLE _ _ hle =
      (jetThickeningMap (k := k) r g).appLE _ _
        (jetThickening.preimage_le_jetThickeningMap_preimage (k := k) r g V) ≫
        (jetThickening (k := k) r W').presheaf.map (CategoryTheory.homOfLE hle').op := by
    rw [AlgebraicGeometry.Scheme.Hom.appLE_map]
  rw [h1, CommRingCat.hom_comp, RingHom.comp_apply,
    jetThickening.appLE_jetThickeningMap_sectionsHom (k := k) r g V p,
    ← jetThickening.sectionsHom_restrict (k := k) r W' hV', jetThickening.coeff_sectionsHom,
    jetThickening.coeff_sectionsHom, MiyaokaMori.Jet.TruncatedJetRing.coeff_map,
    MiyaokaMori.Jet.TruncatedJetRing.coeff_map, AlgebraicGeometry.Scheme.Hom.appLE, CommRingCat.hom_comp,
    RingHom.comp_apply]

end JetThickeningMap

/-! ## Coefficients of pulled-back functions and the constant term -/

section ConstantTermAux

variable {k : Type u} [Field k] (r : ℕ) (W : AlgebraicGeometry.Scheme.{u})
  [W.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]

/-- `pr^♯ a = sectionsHom (eta a)`. -/
theorem jetThickening.proj_app_eq_sectionsHom (V : W.Opens) (a : Γ(W, V)) :
    ((jetThickeningProj (k := k) r W).app V).hom a =
      jetThickening.sectionsHom (k := k) r W V (MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.eta r a) := by
  rw [MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.eta_apply]
  unfold jetThickening.sectionsHom
  rw [MiyaokaMori.Jet.lift_jetProjection, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]

/-- Coefficients of `pr^♯ a`: `a` in degree `0`, `0` otherwise. -/
theorem jetThickening.coeff_proj_app (V : W.Opens) (n : ℕ) (hn : n ≤ r) (a : Γ(W, V)) :
    jetThickening.coeff (k := k) r W V n hn (((jetThickeningProj (k := k) r W).app V).hom a) =
      if n = 0 then a else 0 := by
  rw [jetThickening.proj_app_eq_sectionsHom, jetThickening.coeff_sectionsHom]
  show (Polynomial.C a).coeff n = _
  rw [Polynomial.coeff_C]

theorem jetConstantTerm_proj : jetConstantTerm (k := k) r W ≫ jetThickeningProj (k := k) r W = CategoryTheory.CategoryStruct.id W := by
  delta jetConstantTerm jetThickeningProj jetThickening
  exact CategoryTheory.Limits.pullback.lift_fst _ _ _

theorem jetConstantTerm_snd : jetConstantTerm (k := k) r W ≫
    (CategoryTheory.Limits.pullback.snd (W ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
      (jetBase k r ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) =
    (W ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) ≫ jetBaseZero k r := by
  delta jetConstantTerm jetThickening
  exact CategoryTheory.Limits.pullback.lift_snd _ _ _

theorem jetConstantTerm_le (V : W.Opens) :
    V ≤ jetConstantTerm (k := k) r W ⁻¹ᵁ (jetThickeningProj (k := k) r W ⁻¹ᵁ V) := by
  intro x hx
  have h : (jetConstantTerm (k := k) r W ≫ jetThickeningProj (k := k) r W) x = x := by
    rw [jetConstantTerm_proj]; rfl
  show (jetConstantTerm (k := k) r W ≫ jetThickeningProj (k := k) r W) x ∈ V
  rw [h]; exact hx

theorem jetConstantTerm_parameter (V : W.Opens) :
    ((jetConstantTerm (k := k) r W).appLE ⊤ V le_top).hom (jetThickening.parameter (k := k) r W) = 0 := by
  have h1 := AlgebraicGeometry.Scheme.Hom.comp_appLE (jetConstantTerm (k := k) r W)
    (CategoryTheory.Limits.pullback.snd (W ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
      (jetBase k r ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) ⊤ V le_top
  have h2 := AlgebraicGeometry.Scheme.Hom.comp_appLE
    (W ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) (jetBaseZero k r) ⊤ V le_top
  have h3 := AlgebraicGeometry.Scheme.Hom.appLE_congr_hom (jetConstantTerm_snd (k := k) r W) ⊤ V le_top le_top
  rw [h1, h2] at h3
  have h4 := congrArg (fun g => g.hom ((AlgebraicGeometry.Scheme.ΓSpecIso
    (CommRingCat.of (MiyaokaMori.RingTheory.GlobalTruncatedParameter k r))).inv.hom
      (MiyaokaMori.Jet.jetProjection k r Polynomial.X))) h3
  have nat := AlgebraicGeometry.Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.epsilon (R := k) r))
  have nat' := congrArg (fun g => g.hom (MiyaokaMori.Jet.jetProjection k r Polynomial.X)) nat
  have e0 : MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.epsilon (R := k) r
      (MiyaokaMori.Jet.jetProjection k r Polynomial.X) = 0 := by
    rw [MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.epsilon_projection, Polynomial.eval_X]
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h4 nat'
  rw [e0, map_zero] at nat'
  refine h4.trans ?_
  have : ((jetBaseZero k r).app ⊤).hom ((AlgebraicGeometry.Scheme.ΓSpecIso
      (CommRingCat.of (MiyaokaMori.RingTheory.GlobalTruncatedParameter k r))).inv.hom
        (MiyaokaMori.Jet.jetProjection k r Polynomial.X)) = 0 := nat'.symm
  exact (congrArg (fun y => (AlgebraicGeometry.Scheme.Hom.appLE (W ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
    (jetBaseZero k r ⁻¹ᵁ ⊤) V le_top).hom y) this).trans (map_zero _)

/-- The constant-term section and `sectionsHom`: `ct^♯ ∘ sectionsHom = epsilon`. -/
theorem jetConstantTerm_sectionsHom (V : W.Opens) (p : MiyaokaMori.Jet.TruncatedJetRing Γ(W, V) r) :
    ((jetConstantTerm (k := k) r W).appLE (jetThickeningProj (k := k) r W ⁻¹ᵁ V) V
        (jetConstantTerm_le (k := k) r W V)).hom (jetThickening.sectionsHom (k := k) r W V p) =
      MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.epsilon r p := by
  suffices h : (((jetConstantTerm (k := k) r W).appLE (jetThickeningProj (k := k) r W ⁻¹ᵁ V) V
        (jetConstantTerm_le (k := k) r W V)).hom.comp (jetThickening.sectionsHom (k := k) r W V)) =
      MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.epsilon r from congrArg (fun f => f p) h
  apply Ideal.Quotient.ringHom_ext
  apply Polynomial.ringHom_ext
  · intro a
    show ((jetConstantTerm (k := k) r W).appLE _ V _).hom
      (jetThickening.sectionsHom (k := k) r W V (MiyaokaMori.Jet.jetProjection _ r (Polynomial.C a))) =
      MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.epsilon r (MiyaokaMori.Jet.jetProjection _ r (Polynomial.C a))
    rw [MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.epsilon_projection, Polynomial.eval_C]
    unfold jetThickening.sectionsHom
    rw [MiyaokaMori.Jet.lift_jetProjection, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
    have h1 := AlgebraicGeometry.Scheme.Hom.comp_appLE (jetConstantTerm (k := k) r W)
      (jetThickeningProj (k := k) r W) V V (jetConstantTerm_le (k := k) r W V)
    have hle : V ≤ (CategoryTheory.CategoryStruct.id W : W ⟶ W) ⁻¹ᵁ V := le_rfl
    have h3 := AlgebraicGeometry.Scheme.Hom.appLE_congr_hom (jetConstantTerm_proj (k := k) r W) V V
      (jetConstantTerm_le (k := k) r W V) hle
    have hid : AlgebraicGeometry.Scheme.Hom.appLE (CategoryTheory.CategoryStruct.id W) V V hle = CategoryTheory.CategoryStruct.id _ := by
      simp only [AlgebraicGeometry.Scheme.Hom.appLE, AlgebraicGeometry.Scheme.Hom.id_app]
      exact W.presheaf.map_id _
    rw [h1] at h3
    exact congrArg (fun g => g.hom a) (h3.trans hid)
  · show ((jetConstantTerm (k := k) r W).appLE _ V _).hom
      (jetThickening.sectionsHom (k := k) r W V (MiyaokaMori.Jet.jetProjection _ r Polynomial.X)) =
      MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.epsilon r (MiyaokaMori.Jet.jetProjection _ r Polynomial.X)
    rw [MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.epsilon_projection, Polynomial.eval_X]
    unfold jetThickening.sectionsHom
    rw [MiyaokaMori.Jet.lift_jetProjection, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X,
      ← CategoryTheory.comp_apply, AlgebraicGeometry.Scheme.Hom.map_appLE]
    exact jetConstantTerm_parameter (k := k) r W V

/-- The constant-term section takes the `t^0`-coefficient. -/
theorem jetConstantTerm_appLE_eq_coeff_zero (V : W.Opens)
    (x : Γ(jetThickening (k := k) r W, jetThickeningProj (k := k) r W ⁻¹ᵁ V)) :
    ((jetConstantTerm (k := k) r W).appLE (jetThickeningProj (k := k) r W ⁻¹ᵁ V) V
        (jetConstantTerm_le (k := k) r W V)).hom x =
      jetThickening.coeff (k := k) r W V 0 (Nat.zero_le r) x := by
  obtain ⟨p, rfl⟩ := (jetThickening.sectionsHom_bijective (k := k) r W V).2 x
  rw [jetConstantTerm_sectionsHom, jetThickening.coeff_sectionsHom,
    MiyaokaMori.Jet.TruncatedJetRing.epsilon_eq_coeff_zero]

end ConstantTermAux

/-! ## Coefficients of the universal jet on a chart -/

section UniversalJetSections

variable {k : Type u} [Field k] {C : AlgebraicGeometry.Scheme.{u}}
  [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (Z : CategoryTheory.Over C) [AlgebraicGeometry.IsAffineHom Z.hom]
  (s : C ⟶ Z.left) (hs : s ≫ Z.hom = CategoryTheory.CategoryStruct.id C) (r : ℕ)

/-- The `t^n`-coefficient of the universal jet of `b` on the chart `U` is `chartSections U (D_n b)`. -/
theorem relativeJetScheme.coeff_universalJetSections (U : C.AffineZariskiSite) (n : ℕ) (hn : n ≤ r)
    (b : Γ(Z.left, Z.hom ⁻¹ᵁ U.1)) :
    letI : (relativeJetScheme (k := k) Z s hs r).left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨(relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    letI := relativeJetScheme.sectionsAlgebra Z U.1
    jetThickening.coeff (k := k) r (relativeJetScheme (k := k) Z s hs r).left
        (relativeJetScheme.chartOpen (k := k) Z s hs r U) n hn
        (relativeJetScheme.universalJetSections (k := k) Z s hs r U b) =
      (relativeJetScheme.chartSections (k := k) Z s hs r U).hom
        (BasedJetAlgebra.coeffClass (relativeJetScheme.augmentation Z s hs U.1) r n b) := by
  letI : (relativeJetScheme (k := k) Z s hs r).left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨(relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  letI := relativeJetScheme.sectionsAlgebra Z U.1
  unfold relativeJetScheme.universalJetSections
  rw [RingHom.comp_apply, RingHom.comp_apply, jetThickening.coeff_sectionsHom,
    MiyaokaMori.Jet.TruncatedJetRing.coeff_map]
  exact congrArg _ (BasedJetAlgebra.coeff_universalJet _ r n hn b)

/-- `universalJetSections` is compatible with restriction to a basic open `V ⊆ U`. -/
theorem relativeJetScheme.universalJetSections_restrict {U V : C.AffineZariskiSite} (f : V ⟶ U)
    (b : Γ(Z.left, Z.hom ⁻¹ᵁ U.1)) :
    letI : (relativeJetScheme (k := k) Z s hs r).left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨(relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    ((jetThickening (k := k) r (relativeJetScheme (k := k) Z s hs r).left).presheaf.map
        (CategoryTheory.homOfLE (show
          jetThickeningProj (k := k) r (relativeJetScheme (k := k) Z s hs r).left ⁻¹ᵁ
              relativeJetScheme.chartOpen (k := k) Z s hs r V ≤
            jetThickeningProj (k := k) r (relativeJetScheme (k := k) Z s hs r).left ⁻¹ᵁ
              relativeJetScheme.chartOpen (k := k) Z s hs r U from
          fun _ hx => relativeJetScheme.chartOpen_mono (k := k) Z s hs r f hx)).op).hom
      (relativeJetScheme.universalJetSections (k := k) Z s hs r U b) =
    relativeJetScheme.universalJetSections (k := k) Z s hs r V
      ((Z.left.presheaf.map (CategoryTheory.homOfLE
        (show Z.hom ⁻¹ᵁ V.1 ≤ Z.hom ⁻¹ᵁ U.1 from
          (TopologicalSpace.Opens.map Z.hom.base).monotone
            (AlgebraicGeometry.Scheme.AffineZariskiSite.toOpens_mono f.le))).op).hom b) := by
  letI : (relativeJetScheme (k := k) Z s hs r).left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨(relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  letI := relativeJetScheme.sectionsAlgebra Z U.1
  letI := relativeJetScheme.sectionsAlgebra Z V.1
  apply jetThickening.ext_coeff
  intro n hn
  rw [jetThickening.coeff_restrict (k := k) r _ (relativeJetScheme.chartOpen_mono (k := k) Z s hs r f),
    relativeJetScheme.coeff_universalJetSections, relativeJetScheme.coeff_universalJetSections,
    relativeJetScheme.chartSections_map_apply (k := k) Z s hs r f]
  congr 1
  exact BasedJetAlgebra.map_coeffClass (relativeJetScheme.augmentation Z s hs U.1)
    (relativeJetScheme.augmentation Z s hs V.1) r _ _
    (relativeJetScheme.chartFunctor_smul Z
      (AlgebraicGeometry.Scheme.AffineZariskiSite.toOpens_mono f.le))
    (fun b => congrArg (fun φ : Γ(Z.left, Z.hom ⁻¹ᵁ U.1) ⟶ Γ(C, V.1) =>
      CommRingCat.Hom.hom φ b) (relativeJetScheme.augmentation_naturality Z s hs
        (AlgebraicGeometry.Scheme.AffineZariskiSite.toOpens_mono f.le))) n b

/-- The universal jet of a coefficient `π^♯ a` is the pulled-back coefficient `pr^♯ (chartSections U (a))`. -/
theorem relativeJetScheme.universalJetSections_algebraMap (U : C.AffineZariskiSite) (a : Γ(C, U.1)) :
    letI : (relativeJetScheme (k := k) Z s hs r).left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨(relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    relativeJetScheme.universalJetSections (k := k) Z s hs r U ((Z.hom.app U.1).hom a) =
      ((jetThickeningProj (k := k) r (relativeJetScheme (k := k) Z s hs r).left).app
          (relativeJetScheme.chartOpen (k := k) Z s hs r U)).hom
        ((relativeJetScheme.chartSections (k := k) Z s hs r U).hom
          (((relativeJetScheme.coefficientMap Z s hs r).app (Opposite.op U)).hom a)) := by
  letI : (relativeJetScheme (k := k) Z s hs r).left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨(relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  letI := relativeJetScheme.sectionsAlgebra Z U.1
  apply jetThickening.ext_coeff
  intro n hn
  rw [relativeJetScheme.coeff_universalJetSections, jetThickening.coeff_proj_app]
  have h : (Z.hom.app U.1).hom a = algebraMap Γ(C, U.1) Γ(Z.left, Z.hom ⁻¹ᵁ U.1) a := rfl
  rw [h, Algebra.algebraMap_eq_smul_one, BasedJetAlgebra.coeffClass_smul _ r n hn,
    BasedJetAlgebra.coeffClass_one _ r n hn]
  split_ifs
  · rw [mul_one]; rfl
  · rw [mul_zero, map_zero]

/-- The constant term of the universal jet of `b` is `ε_U b` (as a coefficient on the chart). -/
theorem relativeJetScheme.jetConstantTerm_appLE_universalJetSections (U : C.AffineZariskiSite)
    (b : Γ(Z.left, Z.hom ⁻¹ᵁ U.1)) :
    letI : (relativeJetScheme (k := k) Z s hs r).left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨(relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    letI := relativeJetScheme.sectionsAlgebra Z U.1
    ((jetConstantTerm (k := k) r (relativeJetScheme (k := k) Z s hs r).left).appLE
        (jetThickeningProj (k := k) r (relativeJetScheme (k := k) Z s hs r).left ⁻¹ᵁ
          relativeJetScheme.chartOpen (k := k) Z s hs r U)
        (relativeJetScheme.chartOpen (k := k) Z s hs r U)
        (jetConstantTerm_le (k := k) r _ _)).hom
      (relativeJetScheme.universalJetSections (k := k) Z s hs r U b) =
    (relativeJetScheme.chartSections (k := k) Z s hs r U).hom
      (((relativeJetScheme.coefficientMap Z s hs r).app (Opposite.op U)).hom
        (relativeJetScheme.augmentation Z s hs U.1 b)) := by
  letI : (relativeJetScheme (k := k) Z s hs r).left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨(relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  letI := relativeJetScheme.sectionsAlgebra Z U.1
  rw [jetConstantTerm_appLE_eq_coeff_zero, relativeJetScheme.coeff_universalJetSections,
    BasedJetAlgebra.coeffClass_zero_order]
  rfl

end UniversalJetSections

end
