import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.TruncatedJetAlgebraSectionsGermExt

/-! # Generic evaluation of `𝒜(W)` in a frame: `𝒜(W) → K(C̃)[t]/(t^{κ+1})`, `r • μ^{⊗n} ↦ γ^n · r(η) · t^n`
(helper for Lemma 3.1 of the paper)

In a frame `μ` of `L^{-1}` on `W ∋ η`, `𝒜(W) ≅ 𝒪(W)[t]/(t^{κ+1})` (`quotToSections`, bijective);
composing its inverse with the coefficientwise germ `𝒪(W) → K := K(C̃)` and the substitution `t ↦ γ t`
(`TruncatedJetRing.rescale`) gives the ring map `genericEval : 𝒜(W) → K[t]/(t^{κ+1})`. Its `t^n`-coefficient
on `x` is `γ^n · (coordinate of π_n x in μ^{⊗n})(η)` (`coeff_genericEval`); equivalently, if
`(π_n x)_η = a • (μ^{⊗n})_η` then the coefficient is `γ^n · a` (`coeff_genericEval_of_germ_smul`). For
`γ ≠ 0` it is injective (`genericEval_injective`): the coefficients recover the germs of all pieces, which
determine `x` (`sectionsRing_ext_of_germ`).

-/
set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace truncatedJetAlgebra

open AlgebraicGeometry.Scheme.Modules

variable {k : Type u} [Field k] {Ct : SmoothProjectiveCurve k} (L : LineBundle Ct.toVariety)
  {W : Ct.toScheme.Opens} (hηW : genericPoint Ct.toScheme ∈ W)
  {μ : Γ((L.zpow (-1)).toModules, W)} (hμ : IsFrame (L.zpow (-1)).toModules W μ) (κ : ℕ)

/-- The inverse of `quotToSections μ : 𝒪(W)[t]/(t^{κ+1}) → 𝒜(W)` (a frame `μ` makes it bijective). -/
def sectionsToQuot : (truncatedJetAlgebra L κ).sectionsRing W →+* MiyaokaMori.Jet.TruncatedJetRing Γ(Ct.toScheme, W) κ :=
  (RingEquiv.ofBijective _ (quotToSections_bijective L W μ κ hμ)).symm.toRingHom

theorem sectionsToQuot_quotToSections (y : MiyaokaMori.Jet.TruncatedJetRing Γ(Ct.toScheme, W) κ) :
    sectionsToQuot L hμ κ (quotToSections L W μ κ y) = y :=
  (RingEquiv.ofBijective _ (quotToSections_bijective L W μ κ hμ)).symm_apply_apply y

variable (γ : Ct.toScheme.functionField)

/-- **Generic evaluation in the frame `μ` with scale `γ`**: `𝒜(W) → K[t]/(t^{κ+1})`,
`r • μ^{⊗n} ↦ γ^n · r(η) · t^n`. -/
def genericEval : (truncatedJetAlgebra L κ).sectionsRing W →+* MiyaokaMori.Jet.TruncatedJetRing Ct.toScheme.functionField κ :=
  (MiyaokaMori.Jet.TruncatedJetRing.rescale κ γ).comp
    ((MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.map κ (Ct.toScheme.presheaf.germ W (genericPoint Ct.toScheme) hηW).hom).comp
      (sectionsToQuot L hμ κ))

/-- The `t^n`-coefficient of `genericEval x` is `γ^n · (coord_{μ^{⊗n}} (π_n x))(η)`. -/
theorem coeff_genericEval (x : (truncatedJetAlgebra L κ).sectionsRing W) (n : ℕ) (hn : n ≤ κ) :
    MiyaokaMori.Jet.TruncatedJetRing.coeff κ n hn (genericEval L hηW hμ κ γ x) =
      γ ^ n * Ct.toScheme.presheaf.germ W (genericPoint Ct.toScheme) hηW
        ((framePow_isFrame L W μ hμ n).coord le_rfl
          ((CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
            ⟨n, Nat.lt_succ_of_le hn⟩).app W x)) := by
  obtain ⟨y, hy⟩ := (quotToSections_bijective L W μ κ hμ).2 x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hinv : sectionsToQuot L hμ κ x = MiyaokaMori.Jet.jetProjection _ κ p := by
    rw [← hy]; exact sectionsToQuot_quotToSections L hμ κ _
  have hπ : (CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
      ⟨n, Nat.lt_succ_of_le hn⟩).app W x = p.coeff n • framePow L W μ n := by
    rw [← hy, quotToSections_mk]
    exact π_polyToSections L W μ κ p ⟨n, Nat.lt_succ_of_le hn⟩
  have hc : (framePow_isFrame L W μ hμ n).coord le_rfl
      ((CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
        ⟨n, Nat.lt_succ_of_le hn⟩).app W x) = p.coeff n := by
    apply (framePow_isFrame L W μ hμ n).coord_unique
    rw [res_self, hπ]
  rw [hc]
  unfold genericEval
  rw [RingHom.comp_apply, RingHom.comp_apply, hinv, MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.map_projection,
    MiyaokaMori.Jet.TruncatedJetRing.rescale_projection, MiyaokaMori.Jet.TruncatedJetRing.coeff_jetProjection,
    Polynomial.comp_C_mul_X_coeff, Polynomial.coeff_map, _root_.mul_comm]

/-- The constant term of `genericEval x` is the germ of the weight-`0` piece `π₀ x = r ∈ 𝒪(W)`
(`μ^{⊗0} = 1`, so the coordinate of `π₀ x` is `π₀ x` itself). -/
theorem coeff_zero_genericEval (x : (truncatedJetAlgebra L κ).sectionsRing W) (r : Γ(Ct.toScheme, W))
    (h : (CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
      ⟨0, Nat.succ_pos κ⟩).app W x = r) :
    MiyaokaMori.Jet.TruncatedJetRing.coeff κ 0 (Nat.zero_le κ) (genericEval L hηW hμ κ γ x) =
      Ct.toScheme.presheaf.germ W (genericPoint Ct.toScheme) hηW r := by
  rw [coeff_genericEval L hηW hμ κ γ x 0 (Nat.zero_le κ), _root_.pow_zero, _root_.one_mul]
  congr 1
  apply (framePow_isFrame L W μ hμ 0).coord_unique
  rw [res_self, framePow_zero, h]
  show r • (1 : Γ(Ct.toScheme, W)) = r
  rw [smul_eq_mul, mul_one]

/-- If `(π_n x)_η = a • (μ^{⊗n})_η` then the `t^n`-coefficient of `genericEval x` is `γ^n · a`. -/
theorem coeff_genericEval_of_germ_smul (x : (truncatedJetAlgebra L κ).sectionsRing W) (n : ℕ) (hn : n ≤ κ)
    (a : Ct.toScheme.functionField)
    (h : (truncatedJetAlgebra.piece L n).presheaf.germ W (genericPoint Ct.toScheme) hηW
        ((CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
          ⟨n, Nat.lt_succ_of_le hn⟩).app W x) =
      a • ((truncatedJetAlgebra.piece L n).presheaf.germ W (genericPoint Ct.toScheme) hηW (framePow L W μ n) :
        (truncatedJetAlgebra.piece L n).stalk (genericPoint Ct.toScheme))) :
    MiyaokaMori.Jet.TruncatedJetRing.coeff κ n hn (genericEval L hηW hμ κ γ x) = γ ^ n * a := by
  rw [coeff_genericEval L hηW hμ κ γ x n hn]
  congr 1
  have F := framePow_isFrame L W μ hμ n
  set z := (CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
    ⟨n, Nat.lt_succ_of_le hn⟩).app W x with hz
  have hx : F.coord le_rfl z • framePow L W μ n = z := by
    have := F.coord_smul_frame le_rfl z; rwa [res_self] at this
  rw [← hx, germ_smul'] at h
  have h0 : (Ct.toScheme.presheaf.germ W (genericPoint Ct.toScheme) hηW (F.coord le_rfl z) - a) •
      ((truncatedJetAlgebra.piece L n).presheaf.germ W (genericPoint Ct.toScheme) hηW (framePow L W μ n) :
        (truncatedJetAlgebra.piece L n).stalk (genericPoint Ct.toScheme)) = 0 := by
    rw [sub_smul, h, sub_self]
  exact sub_eq_zero.mp (F.germ_smul_eq_zero hηW _ h0)

/-- **`genericEval` is injective for `γ ≠ 0`** (the coefficients recover the germs of the pieces, which
determine an element of `𝒜(W)`). -/
theorem genericEval_injective [AlgebraicGeometry.IsIntegral Ct.toScheme] (hγ : γ ≠ 0) :
    Function.Injective (genericEval L hηW hμ κ γ) := by
  intro x y hxy
  apply sectionsRing_ext_of_germ L hηW hμ κ
  intro q
  have h1 := coeff_genericEval L hηW hμ κ γ x q (Nat.le_of_lt_succ q.2)
  have h2 := coeff_genericEval L hηW hμ κ γ y q (Nat.le_of_lt_succ q.2)
  rw [hxy, h2] at h1
  have h3 := mul_left_cancel₀ (pow_ne_zero (q : ℕ) hγ) h1
  have F := framePow_isFrame L W μ hμ q
  have hx : F.coord le_rfl ((CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
      ⟨(q : ℕ), Nat.lt_succ_of_le (Nat.le_of_lt_succ q.2)⟩).app W x) • framePow L W μ q =
      (CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q) q).app W x := by
    have := F.coord_smul_frame le_rfl ((CategoryTheory.Limits.biproduct.π
      (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q) q).app W x)
    rwa [res_self] at this
  have hy : F.coord le_rfl ((CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
      ⟨(q : ℕ), Nat.lt_succ_of_le (Nat.le_of_lt_succ q.2)⟩).app W y) • framePow L W μ q =
      (CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q) q).app W y := by
    have := F.coord_smul_frame le_rfl ((CategoryTheory.Limits.biproduct.π
      (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q) q).app W y)
    rwa [res_self] at this
  rw [← hx, ← hy, germ_smul', germ_smul', h3]

end truncatedJetAlgebra

end
