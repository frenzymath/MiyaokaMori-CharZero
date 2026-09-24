import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.LocalJetGenericEvaluation
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.AffineJetGenericPointCoefficients
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.JetNeighborhoodPointOfRingHom
import MiyaokaMori.AlgebraicGeometry.Morphisms.ThickeningFunctionsOfTruncatedJet
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.LocalJetGluing

/-! # The generic point `θ : D → p_L⁻¹(W)` of a framed local jet, and `θ ≫ g_Ψ = Θ`
(step 2 of the proof of Lemma 3.1 of the paper)

Fix an affine `W ∋ η_{C̃}`, a frame `μ₀` of `L^{-1}` on `W` and `γ₀ ∈ K(C̃)ˣ`. The ring map
`θ^♯ : 𝒜(W) → Γ(D, ⊤)`, `D := Spec κ(η) ×_k D_κ`, is the generic evaluation in the frame `μ₀` with scale
`γ₀` (`genericEval`, `r • μ₀^{⊗n} ↦ γ₀^n r(η) t^n`) followed by `K(C̃) ≅ κ(η) ≅ Γ(Spec κ(η), ⊤)` and
`K[t]/(t^{κ+1}) → Γ(D, ⊤)` (`evalToThickening`); it is injective (`genericPointRingHom_injective`), and
`θ := pointOfRingHom θ^♯ : D → p_L⁻¹(W)` is the corresponding point.

**Main statement** (`pointOfRingHom_localJet_eq_genericBasedJet`): for a ring map `Ψ : B_V → 𝒜(W)` with constant
term `s^♯` and positive pieces of generic value `γ^{-(q+1)} (d_q c)(ĵ)` in a section `μ` of `L^{-1}` (with the
frame relation `γ₀^{-n} (μ₀^{⊗n})_η = γ^{-n} (μ^{⊗n})_η`; neither `μ` being a frame nor `γ ≠ 0` is needed),
`θ ≫ g_Ψ = Θ`, the based jet of `ĵ`
(`genericBasedJet`). Proof: both are morphisms from the affine `D` landing in `π⁻¹V`, so it suffices to
compare ring maps on `B_V` (`isAffine_hom_ext_of_appLE`, `LocalJetGluing`); `(θ ≫ g_Ψ)^♯ = Ψ ≫ θ^♯` (`pointOfRingHom_localJet_appLE`),
and coefficientwise (`jetThickening.ext_coeff`): the `t^0`-coefficient is `(ρ^♯ s^♯ c)(η)` on both sides
(`coeff_zero_genericEval`, `coeff_zero_genericBasedJet`) and the `t^{q+1}`-coefficient is
`γ₀^{q+1} · γ₀^{-(q+1)} (d_q c)(ĵ) = (d_q c)(ĵ)` on both sides (`coeff_genericEval_of_germ_smul` with the frame
relation, `coeff_genericBasedJet`).

-/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace jetNeighborhood

variable {k : Type u} [Field k] {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}
  (f : C.toScheme ⟶ X.toScheme) [MMSetup f] (κ : ℕ) (ρ : FiniteCover k C)

/-- `K(C̃) → Γ(Spec κ(η), ⊤)`: the residue map followed by `ΓSpecIso⁻¹`. -/
def genericResidueHom : ρ.source.toScheme.functionField →+* Γ((genericOver ρ).left, ⊤) :=
  ((AlgebraicGeometry.Scheme.ΓSpecIso (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme))).inv.hom).comp
    (ρ.source.toScheme.residue (genericPoint ρ.source.toScheme)).hom

theorem genericResidueHom_injective : Function.Injective (genericResidueHom ρ) := by
  haveI : AlgebraicGeometry.IsIntegral ρ.source.toScheme := ρ.source.isIntegral
  have h1 : ∀ z : ρ.source.toScheme.functionField, ρ.source.toScheme.functionFieldIsoResidueField.inv.hom
      ((AlgebraicGeometry.Scheme.ΓSpecIso (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme))).hom.hom
        (genericResidueHom ρ z)) = z := by
    intro z
    show ρ.source.toScheme.functionFieldIsoResidueField.inv.hom
      ((AlgebraicGeometry.Scheme.ΓSpecIso (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme))).hom.hom
        ((AlgebraicGeometry.Scheme.ΓSpecIso (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme))).inv.hom
          ((ρ.source.toScheme.residue (genericPoint ρ.source.toScheme)).hom z))) = z
    rw [CategoryTheory.Iso.inv_hom_id_apply]
    exact CategoryTheory.Iso.hom_inv_id_apply ρ.source.toScheme.functionFieldIsoResidueField z
  intro a b hab
  rw [← h1 a, ← h1 b, hab]

variable (L : LineBundle ρ.source.toVariety)
  {W : ρ.source.toScheme.Opens} (hηW : genericPoint ρ.source.toScheme ∈ W)
  {μ₀ : Γ((L.zpow (-1)).toModules, W)} (hμ₀ : AlgebraicGeometry.Scheme.Modules.IsFrame (L.zpow (-1)).toModules W μ₀)
  (γ₀ : ρ.source.toScheme.functionField)

/-- `⊤ ≤ pr⁻¹⊤` in `D`. -/
theorem top_le_proj_preimage_top :
    letI := genericOverInst ρ
    (⊤ : (jetThickening (k := k) κ (genericOver ρ).left).Opens) ≤
      jetThickeningProj (k := k) κ (genericOver ρ).left ⁻¹ᵁ ⊤ :=
  fun _ _ => trivial

/-- **The ring map `θ^♯ : 𝒜(W) → Γ(D, ⊤)`** of the generic point in the frame `μ₀` with scale `γ₀`. -/
def genericPointRingHom :
    letI := genericOverInst ρ
    CommRingCat.of ((truncatedJetAlgebra L κ).sectionsRing W) ⟶ Γ(jetThickening (k := k) κ (genericOver ρ).left, ⊤) :=
  letI := genericOverInst ρ
  CommRingCat.ofHom ((jetThickening.evalToThickening k κ (genericOver ρ).left _ (genericResidueHom ρ)).comp
      (truncatedJetAlgebra.genericEval L hηW hμ₀ κ γ₀)) ≫
    (jetThickening (k := k) κ (genericOver ρ).left).presheaf.map (homOfLE (top_le_proj_preimage_top κ ρ)).op

theorem genericPointRingHom_injective (hγ₀ : γ₀ ≠ 0) :
    Function.Injective (genericPointRingHom κ ρ L hηW hμ₀ γ₀).hom := by
  letI := genericOverInst ρ
  haveI : AlgebraicGeometry.IsIntegral ρ.source.toScheme := ρ.source.isIntegral
  have hres : Function.Injective ((jetThickening (k := k) κ (genericOver ρ).left).presheaf.map
      (homOfLE (top_le_proj_preimage_top κ ρ)).op).hom := by
    intro a b hab
    have h := congrArg ((jetThickening (k := k) κ (genericOver ρ).left).presheaf.map
      (homOfLE (le_top : jetThickeningProj (k := k) κ (genericOver ρ).left ⁻¹ᵁ ⊤ ≤ ⊤)).op).hom hab
    rw [← RingHom.comp_apply, ← RingHom.comp_apply, ← CommRingCat.hom_comp, ← Functor.map_comp,
      show ((homOfLE (top_le_proj_preimage_top κ ρ)).op ≫ (homOfLE (le_top :
        jetThickeningProj (k := k) κ (genericOver ρ).left ⁻¹ᵁ ⊤ ≤ ⊤)).op) = 𝟙 _ from Subsingleton.elim _ _,
      CategoryTheory.Functor.map_id] at h
    exact h
  intro a b hab
  exact (jetThickening.evalToThickening_injective k κ (genericOver ρ).left _ (genericResidueHom ρ)
    (genericResidueHom_injective ρ)).comp
    (truncatedJetAlgebra.genericEval_injective L hηW hμ₀ κ γ₀ hγ₀) (hres hab)

variable (ĵ : AlgebraicGeometry.Spec (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme)) ⟶
    (relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).left)
  (hĵ : ĵ ≫ (relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom =
    ρ.source.toScheme.fromSpecResidueField (genericPoint ρ.source.toScheme) ≫ ρ.hom)

/-- `D` is affine (a fibre product of affine schemes). -/
theorem isAffine_genericThickening :
    letI := genericOverInst ρ
    AlgebraicGeometry.IsAffine (jetThickening (k := k) κ (genericOver ρ).left) := by
  letI := genericOverInst ρ
  haveI : AlgebraicGeometry.IsAffine (genericOver ρ).left :=
    AlgebraicGeometry.isAffine_Spec (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme))
  haveI : AlgebraicGeometry.IsAffine (jetBase k κ) :=
    AlgebraicGeometry.isAffine_Spec (CommRingCat.of (MiyaokaMori.RingTheory.GlobalTruncatedParameter k κ))
  unfold jetThickening
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- **`θ ≫ g_Ψ = Θ`** for a framed local jet `Ψ` with the generic values of `ĵ`. -/
theorem pointOfRingHom_localJet_eq_genericBasedJet (hγ₀ : γ₀ ≠ 0) (hW : AlgebraicGeometry.IsAffineOpen W)
    {V : C.toScheme.Opens} (hV : AlgebraicGeometry.IsAffineOpen V)
    (hĵV : (⊤ : (AlgebraicGeometry.Spec (ρ.source.toScheme.residueField (genericPoint ρ.source.toScheme))).Opens) ≤
      ĵ ⁻¹ᵁ ((relativeJetScheme (k := k) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).hom ⁻¹ᵁ V))
    (hWV : W ≤ ρ.hom ⁻¹ᵁ V) {μ : Γ((L.zpow (-1)).toModules, W)} (γ : ρ.source.toScheme.functionField)
    (hfr : ∀ n : ℕ,
      γ₀ ^ (-(n : ℤ)) • ((truncatedJetAlgebra.piece L n).presheaf.germ W (genericPoint ρ.source.toScheme) hηW
          (truncatedJetAlgebra.framePow L W μ₀ n) : (truncatedJetAlgebra.piece L n).stalk (genericPoint ρ.source.toScheme)) =
      γ ^ (-(n : ℤ)) • ((truncatedJetAlgebra.piece L n).presheaf.germ W (genericPoint ρ.source.toScheme) hηW
          (truncatedJetAlgebra.framePow L W μ n) : (truncatedJetAlgebra.piece L n).stalk (genericPoint ρ.source.toScheme)))
    (Ψ : Γ((MMSetup.cone f).left, (MMSetup.cone f).hom ⁻¹ᵁ V) ⟶
      CommRingCat.of ((truncatedJetAlgebra L κ).sectionsRing W))
    (hzero : ∀ c : Γ((MMSetup.cone f).left, (MMSetup.cone f).hom ⁻¹ᵁ V),
      (CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
          ⟨0, Nat.succ_pos κ⟩).app W (Ψ.hom c) =
        (ρ.hom.appLE V W hWV).hom
          (((MMSetup.seed f).1.appLE ((MMSetup.cone f).hom ⁻¹ᵁ V) V
            (relativeJetScheme.section_preimage_le (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 V)).hom c))
    (hgen : ∀ (q : Fin κ) (c : Γ((MMSetup.cone f).left, (MMSetup.cone f).hom ⁻¹ᵁ V)),
      ((truncatedJetAlgebra.piece L ((q : ℕ) + 1)).presheaf.germ W (genericPoint ρ.source.toScheme) hηW
          ((CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
            ⟨(q : ℕ) + 1, Nat.succ_lt_succ q.2⟩).app W (Ψ.hom c)) :
        (truncatedJetAlgebra.piece L ((q : ℕ) + 1)).stalk (genericPoint ρ.source.toScheme)) =
      (γ ^ (-((q : ℕ) + 1 : ℤ)) * affineJetCoeff f κ ρ ĵ hV hĵV ((q : ℕ) + 1) c) •
        ((truncatedJetAlgebra.piece L ((q : ℕ) + 1)).presheaf.germ W (genericPoint ρ.source.toScheme) hηW
          (truncatedJetAlgebra.framePow L W μ ((q : ℕ) + 1)) :
        (truncatedJetAlgebra.piece L ((q : ℕ) + 1)).stalk (genericPoint ρ.source.toScheme))) :
    letI := genericOverInst ρ
    pointOfRingHom κ ρ L hW (genericPointRingHom κ ρ L hηW hμ₀ γ₀) ≫ localJet f κ ρ L hV hW Ψ =
      (genericBasedJet f κ ρ ĵ hĵ).1 := by
  letI := genericOverInst ρ
  haveI : AlgebraicGeometry.IsIntegral ρ.source.toScheme := ρ.source.isIntegral
  haveI := isAffine_genericThickening κ ρ
  have hΘle : (⊤ : (jetThickening (k := k) κ (genericOver ρ).left).Opens) ≤
      (genericBasedJet f κ ρ ĵ hĵ).1 ⁻¹ᵁ ((MMSetup.cone f).hom ⁻¹ᵁ V) :=
    fun x _ => genericBasedJet_le f κ ρ ĵ hĵ hV hĵV (show x ∈ jetThickeningProj (k := k) κ (genericOver ρ).left ⁻¹ᵁ ⊤ from trivial)
  apply isAffine_hom_ext_of_appLE (cone_preimage_isAffineOpen f hV)
    (top_le_pointOfRingHom_localJet_preimage f κ ρ L hW (genericPointRingHom κ ρ L hηW hμ₀ γ₀) hV Ψ) hΘle
  rw [pointOfRingHom_localJet_appLE,
    ← AlgebraicGeometry.Scheme.Hom.appLE_map (genericBasedJet f κ ρ ĵ hĵ).1 (genericBasedJet_le f κ ρ ĵ hĵ hV hĵV)
      (homOfLE (top_le_proj_preimage_top κ ρ)).op]
  show Ψ ≫ CommRingCat.ofHom ((jetThickening.evalToThickening k κ (genericOver ρ).left _ (genericResidueHom ρ)).comp
      (truncatedJetAlgebra.genericEval L hηW hμ₀ κ γ₀)) ≫
    (jetThickening (k := k) κ (genericOver ρ).left).presheaf.map (homOfLE (top_le_proj_preimage_top κ ρ)).op = _
  rw [← Category.assoc]
  congr 1
  ext c
  apply jetThickening.ext_coeff (k := k) κ (genericOver ρ).left ⊤
  intro n hn
  show jetThickening.coeff (k := k) κ (genericOver ρ).left ⊤ n hn
    (jetThickening.evalToThickening k κ (genericOver ρ).left _ (genericResidueHom ρ)
      (truncatedJetAlgebra.genericEval L hηW hμ₀ κ γ₀ (Ψ.hom c))) = _
  rw [jetThickening.coeff_evalToThickening]
  cases n with
  | zero =>
    rw [coeff_zero_genericBasedJet f κ ρ ĵ hĵ hV hĵV hηW hWV c,
      truncatedJetAlgebra.coeff_zero_genericEval L hηW hμ₀ κ γ₀ (Ψ.hom c) _ (hzero c)]
    rfl
  | succ q =>
    have hq : q < κ := Nat.lt_of_succ_le hn
    rw [coeff_genericBasedJet f κ ρ ĵ hĵ hV hĵV (q + 1) hn c]
    -- the germ of the `(q+1)`-piece of `Ψ c` in the reference frame `μ₀`
    have hg := hgen ⟨q, hq⟩ c
    have hf := hfr (q + 1)
    have hg' : (truncatedJetAlgebra.piece L (q + 1)).presheaf.germ W (genericPoint ρ.source.toScheme) hηW
        ((CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
          ⟨q + 1, Nat.lt_succ_of_le hn⟩).app W (Ψ.hom c)) =
        (γ₀ ^ (-((q + 1 : ℕ) : ℤ)) * affineJetCoeff f κ ρ ĵ hV hĵV (q + 1) c) •
          ((truncatedJetAlgebra.piece L (q + 1)).presheaf.germ W (genericPoint ρ.source.toScheme) hηW
            (truncatedJetAlgebra.framePow L W μ₀ (q + 1)) :
          (truncatedJetAlgebra.piece L (q + 1)).stalk (genericPoint ρ.source.toScheme)) := by
      have hcast : ((q : ℕ) + 1 : ℤ) = ((q + 1 : ℕ) : ℤ) := by push_cast; rfl
      rw [hcast] at hg
      rw [hg, mul_comm, mul_smul, mul_comm, mul_smul, hf]
    rw [truncatedJetAlgebra.coeff_genericEval_of_germ_smul L hηW hμ₀ κ γ₀ (Ψ.hom c) (q + 1) hn _ hg',
      ← mul_assoc, zpow_neg, zpow_natCast, mul_inv_cancel₀ (pow_ne_zero _ hγ₀), one_mul]
    rfl

end jetNeighborhood

end
