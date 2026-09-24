import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.JetChartTrivialization_Basis

/-! # Sections of the pieces `L^{-n}` and of `𝒜` over `W ∋ η` are determined by their germs at `η`
(helper for Lemma 3.1 of the paper)

On the integral curve `C̃`, a section of the line bundle `L^{-n}` over an open `W` containing the generic
point `η` is determined by its germ at `η`: in a frame `μ^{⊗n}` it is `r • μ^{⊗n}` with `r ∈ 𝒪(W)`, the germ
of `μ^{⊗n}` is a basis of the stalk, and `𝒪(W) → 𝒪_η = K(C̃)` is injective (`germ_injective_of_isIntegral`).
Hence an element of `𝒜(W) = ⊕_{q ≤ κ} L^{-q}(W)` is determined by the germs of its pieces
(`biproduct_sections_total`).

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
  [AlgebraicGeometry.IsIntegral Ct.toScheme]
  {W : Ct.toScheme.Opens} (hηW : genericPoint Ct.toScheme ∈ W)

section Frame

variable {μ : Γ((L.zpow (-1)).toModules, W)} (hμ : IsFrame (L.zpow (-1)).toModules W μ)
include hμ

/-- **Germ-injectivity of the frame coordinate**: if `r • μ^{⊗n}` and `r' • μ^{⊗n}` have the same germ
at `η`, then `r = r'` (`germ_smul'`, `IsFrame.germ_smul_eq_zero`, `germ_injective_of_isIntegral`). -/
theorem eq_of_germ_smul_framePow_eq (n : ℕ) {r r' : Γ(Ct.toScheme, W)}
    (h : (truncatedJetAlgebra.piece L n).presheaf.germ W (genericPoint Ct.toScheme) hηW (r • framePow L W μ n) =
      (truncatedJetAlgebra.piece L n).presheaf.germ W (genericPoint Ct.toScheme) hηW (r' • framePow L W μ n)) :
    r = r' := by
  rw [germ_smul', germ_smul'] at h
  have h0 : (Ct.toScheme.presheaf.germ W (genericPoint Ct.toScheme) hηW r -
      Ct.toScheme.presheaf.germ W (genericPoint Ct.toScheme) hηW r') •
      ((truncatedJetAlgebra.piece L n).presheaf.germ W (genericPoint Ct.toScheme) hηW (framePow L W μ n) :
        (truncatedJetAlgebra.piece L n).stalk (genericPoint Ct.toScheme)) = 0 := by
    rw [sub_smul, h, sub_self]
  have h1 := (framePow_isFrame L W μ hμ n).germ_smul_eq_zero hηW _ h0
  have h2 : Ct.toScheme.presheaf.germ W (genericPoint Ct.toScheme) hηW r =
      Ct.toScheme.presheaf.germ W (genericPoint Ct.toScheme) hηW r' := sub_eq_zero.mp h1
  exact AlgebraicGeometry.germ_injective_of_isIntegral Ct.toScheme (genericPoint Ct.toScheme) hηW h2

/-- **A section of `L^{-n}` over `W ∋ η` is determined by its germ at `η`** (in the presence of a frame). -/
theorem piece_section_ext_of_germ (n : ℕ) {x y : Γ(truncatedJetAlgebra.piece L n, W)}
    (h : (truncatedJetAlgebra.piece L n).presheaf.germ W (genericPoint Ct.toScheme) hηW x =
      (truncatedJetAlgebra.piece L n).presheaf.germ W (genericPoint Ct.toScheme) hηW y) : x = y := by
  have F := framePow_isFrame L W μ hμ n
  have hx : F.coord le_rfl x • framePow L W μ n = x := by
    have := F.coord_smul_frame le_rfl x; rwa [res_self] at this
  have hy : F.coord le_rfl y • framePow L W μ n = y := by
    have := F.coord_smul_frame le_rfl y; rwa [res_self] at this
  rw [← hx, ← hy] at h ⊢
  rw [eq_of_germ_smul_framePow_eq L hηW hμ n h]

variable (κ : ℕ)

/-- **An element of `𝒜(W)` is determined by the germs of its pieces at `η`** (`biproduct_sections_total`). -/
theorem sectionsRing_ext_of_germ {x y : (truncatedJetAlgebra L κ).sectionsRing W}
    (h : ∀ q : Fin (κ + 1),
      (truncatedJetAlgebra.piece L q).presheaf.germ W (genericPoint Ct.toScheme) hηW
          ((CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q) q).app W x) =
        (truncatedJetAlgebra.piece L q).presheaf.germ W (genericPoint Ct.toScheme) hηW
          ((CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q) q).app W y)) :
    x = y := by
  rw [biproduct_sections_total (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q) W x,
    biproduct_sections_total (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q) W y]
  refine Finset.sum_congr rfl fun q _ => ?_
  congr 1
  exact piece_section_ext_of_germ L hηW hμ q (h q)

end Frame

variable (κ : ℕ)

omit [AlgebraicGeometry.IsIntegral Ct.toScheme] in
/-- **An element of `𝒜(W)` with prescribed constant term and vanishing positive pieces is a constant**:
`x = sectionsUnit W r` when `π₀ x = r` and `π_{q+1} x = 0` for all `q < κ` (`biproduct_sections_total`,
`sectionsUnit_mul_tau` at `q = 0`). -/
theorem eq_sectionsUnit_of_pieces (x : (truncatedJetAlgebra L κ).sectionsRing W) (r : Γ(Ct.toScheme, W))
    (h0 : (CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
      ⟨0, Nat.succ_pos κ⟩).app W x = r)
    (hpos : ∀ q : Fin κ,
      (CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
        ⟨(q : ℕ) + 1, Nat.succ_lt_succ q.2⟩).app W x = 0) :
    x = (truncatedJetAlgebra L κ).sectionsUnit W r := by
  classical
  have hunit : (truncatedJetAlgebra L κ).sectionsUnit W r =
      (CategoryTheory.Limits.biproduct.ι (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
        ⟨0, Nat.succ_pos κ⟩).app W r := by
    have h := sectionsUnit_mul_tau L W (0 : Γ((L.zpow (-1)).toModules, W)) κ r ⟨0, Nat.succ_pos κ⟩
    rw [tau_zero, mul_one] at h
    rw [h]
    show (CategoryTheory.Limits.biproduct.ι (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
      ⟨0, Nat.succ_pos κ⟩).app W (r • (1 : Γ(Ct.toScheme, W))) = _
    rw [smul_eq_mul, mul_one]
  rw [hunit, biproduct_sections_total (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q) W x,
    Finset.sum_eq_single (⟨0, Nat.succ_pos κ⟩ : Fin (κ + 1))]
  · rw [h0]
  · intro q _ hq
    have hq' : (q : ℕ) ≠ 0 := fun h => hq (Fin.ext h)
    have hqeq : q = ⟨(⟨(q : ℕ) - 1, by omega⟩ : Fin κ) + 1, Nat.succ_lt_succ (by omega)⟩ := Fin.ext (by
      show (q : ℕ) = (q : ℕ) - 1 + 1
      omega)
    rw [hqeq, hpos ⟨(q : ℕ) - 1, by omega⟩, map_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

end truncatedJetAlgebra

end
