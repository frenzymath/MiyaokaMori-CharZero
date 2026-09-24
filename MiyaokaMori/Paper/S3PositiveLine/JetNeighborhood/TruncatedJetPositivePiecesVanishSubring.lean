import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.JetChartTrivialization_Basis
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleNonvanishingLocus

/-! # Sections of the truncated jet algebra whose positive pieces vanish at a point form a subring
(proof of Lemma 3.1 of the paper)

In a frame `μ` of `L^{-1}` on `V`, `𝒜(V) = O(V)[t]/(t^{κ+1})` (`polyToSections`, module
`JetChartTrivialization_Basis`) with `π_q (polyToSections p) = p.coeff q • μ^{⊗q}`. The condition
"`germ_y (π_q h) ∈ 𝔪_y • ⊤` for all `1 ≤ q ≤ κ`" (`PositivePiecesVanishAt`) therefore reads
"`germ_y (p.coeff q) ∈ 𝔪_y` for all `1 ≤ q ≤ κ`", which contains the constants and is closed under `+`
and `*` (`Polynomial.coeff_mul`: in every term of `coeff (p * p') q = ∑_{i+j=q} coeff p i * coeff p' j`
with `q ≥ 1` one factor has positive index). This is the shared step (3)/(4) of
`BasedJet.pieceSection_germ_mem_of_forall_isZeroAt` and `BasedJet.weightComponent_germ_mem_of_forall_pieceSection`,
used for `BasedJet.normalizedTupleNowhereZero_of_unit_coefficient`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace truncatedJetAlgebra

variable {k : Type u} [Field k] {Ct : SmoothProjectiveCurve k} (L : LineBundle Ct.toVariety)
  (κ : ℕ) {V : Ct.toScheme.Opens} {y : Ct.toScheme} (hy : y ∈ V)

/-- `h ∈ 𝒜(V)` has all its positive pieces vanishing at `y ∈ V`: for every `q` with `1 ≤ q ≤ κ` the germ at
`y` of `π_q h ∈ Γ(V, M^{⊗q})` lies in `𝔪_y • ⊤`. -/
def PositivePiecesVanishAt (h : (truncatedJetAlgebra L κ).sectionsRing V) : Prop :=
  ∀ q : Fin (κ + 1), 1 ≤ (q : ℕ) →
    (truncatedJetAlgebra.piece L q).presheaf.germ V y hy
        ((CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q) q).app V h) ∈
      (IsLocalRing.maximalIdeal (Ct.toScheme.presheaf.stalk y)) •
        (⊤ : Submodule (Ct.toScheme.presheaf.stalk y) ((truncatedJetAlgebra.piece L q).presheaf.stalk y))

variable (μ : Γ((L.zpow (-1)).toModules, V))

include μ in
/-- Constants have all positive pieces vanishing (they have no positive pieces at all); the frame section
`μ` is used only to write `sectionsUnit r = polyToSections (C r)`. -/
theorem positivePiecesVanishAt_sectionsUnit (r : Γ(Ct.toScheme, V)) :
    PositivePiecesVanishAt L κ hy ((truncatedJetAlgebra L κ).sectionsUnit V r) := by
  intro q hq
  rw [← polyToSections_C L V μ κ r, π_polyToSections, Polynomial.coeff_C,
    if_neg (by omega : (q : ℕ) ≠ 0), zero_smul, map_zero]
  exact Submodule.zero_mem _

variable (hμ : AlgebraicGeometry.Scheme.Modules.IsFrame (L.zpow (-1)).toModules V μ)
include hμ

/-- Germ criterion in the frame `μ^{⊗q}`: `germ_y (c • μ^{⊗q}) ∈ 𝔪_y • ⊤ ↔ germ_y c ∈ 𝔪_y`. -/
theorem germ_smul_framePow_mem_iff (q : ℕ) (c : Γ(Ct.toScheme, V)) :
    (truncatedJetAlgebra.piece L q).presheaf.germ V y hy (c • framePow L V μ q) ∈
        (IsLocalRing.maximalIdeal (Ct.toScheme.presheaf.stalk y)) •
          (⊤ : Submodule (Ct.toScheme.presheaf.stalk y) ((truncatedJetAlgebra.piece L q).presheaf.stalk y)) ↔
      Ct.toScheme.presheaf.germ V y hy c ∈ IsLocalRing.maximalIdeal (Ct.toScheme.presheaf.stalk y) := by
  rw [AlgebraicGeometry.Scheme.Modules.germ_smul']
  constructor
  · intro h
    by_contra hc
    have hu : IsUnit (Ct.toScheme.presheaf.germ V y hy c) := IsLocalRing.notMem_maximalIdeal.mp hc
    obtain ⟨u, hu⟩ := hu
    have h2 := Submodule.smul_mem _ (↑u⁻¹ : Ct.toScheme.presheaf.stalk y) h
    rw [smul_smul, ← hu, Units.inv_mul, one_smul] at h2
    exact (framePow_isFrame L V μ hμ q).germ_notMem_maximalIdeal_smul hy h2
  · intro h
    exact Submodule.smul_mem_smul h Submodule.mem_top

theorem PositivePiecesVanishAt.add {h₁ h₂ : (truncatedJetAlgebra L κ).sectionsRing V}
    (H₁ : PositivePiecesVanishAt L κ hy h₁) (H₂ : PositivePiecesVanishAt L κ hy h₂) :
    PositivePiecesVanishAt L κ hy (h₁ + h₂) := by
  obtain ⟨p₁, rfl⟩ := polyToSections_surjective L V μ κ hμ h₁
  obtain ⟨p₂, rfl⟩ := polyToSections_surjective L V μ κ hμ h₂
  intro q hq
  have e₁ := H₁ q hq
  have e₂ := H₂ q hq
  rw [π_polyToSections, germ_smul_framePow_mem_iff L hy μ hμ] at e₁ e₂
  rw [← map_add, π_polyToSections, germ_smul_framePow_mem_iff L hy μ hμ, Polynomial.coeff_add, map_add]
  exact Ideal.add_mem _ e₁ e₂

/-- Products: `coeff (p₁ p₂) q = ∑_{i+j=q} coeff p₁ i · coeff p₂ j`, and for `q ≥ 1` one of `i, j` is `≥ 1`. -/
theorem PositivePiecesVanishAt.mul {h₁ h₂ : (truncatedJetAlgebra L κ).sectionsRing V}
    (H₁ : PositivePiecesVanishAt L κ hy h₁) (H₂ : PositivePiecesVanishAt L κ hy h₂) :
    PositivePiecesVanishAt L κ hy (h₁ * h₂) := by
  obtain ⟨p₁, rfl⟩ := polyToSections_surjective L V μ κ hμ h₁
  obtain ⟨p₂, rfl⟩ := polyToSections_surjective L V μ κ hμ h₂
  have key : ∀ (p : Polynomial Γ(Ct.toScheme, V)), PositivePiecesVanishAt L κ hy (polyToSections L V μ κ p) →
      ∀ q : Fin (κ + 1), 1 ≤ (q : ℕ) →
        Ct.toScheme.presheaf.germ V y hy (p.coeff q) ∈ IsLocalRing.maximalIdeal (Ct.toScheme.presheaf.stalk y) := by
    intro p H q hq
    have := H q hq
    rw [π_polyToSections, germ_smul_framePow_mem_iff L hy μ hμ] at this
    exact this
  intro q hq
  rw [← map_mul, π_polyToSections, germ_smul_framePow_mem_iff L hy μ hμ, Polynomial.coeff_mul, map_sum]
  refine Ideal.sum_mem _ fun x hx => ?_
  rw [Finset.mem_antidiagonal] at hx
  rw [map_mul]
  by_cases h0 : x.1 = 0
  · have hx2 : x.2 = (q : ℕ) := by omega
    refine Ideal.mul_mem_left _ _ ?_
    have := key p₂ H₂ ⟨x.2, by omega⟩ (by simp only; omega)
    simpa using this
  · refine Ideal.mul_mem_right _ _ ?_
    have := key p₁ H₁ ⟨x.1, by omega⟩ (by simp only; omega)
    simpa using this

end truncatedJetAlgebra

end
