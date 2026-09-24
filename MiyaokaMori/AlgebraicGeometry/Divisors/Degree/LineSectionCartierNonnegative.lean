import MiyaokaMori.AlgebraicGeometry.Divisors.RationalSections.LineRationalSectionCartier
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierFiniteSupport

/-!
# Nonnegative Cartier coefficients of a regular line section

For a global regular section of the same line module, any actual Cartier presentation of
its generic germ has nonnegative coefficients. The coordinate in the chosen local frame
is an element of the actual stalk; its canonical function-field image is the presentation's
local equation. Its order is a nonnegative module length at codimension one.

This uses the specified presentation and its actual frames, without invoking presentation
existence or change-of-section results. It applies to singular integral locally Noetherian
schemes and does not assume a DVR or properness. Presentation existence and independence of
the resulting degree remain separate obligations in the nonzero-section degree argument.

Sources: the proofs of Lemma 3.1 and Theorem 4.2 of the paper
(nonnegativity of the degree of a nonzero coefficient); Stacks Project `divisors.tex`,
`definition-order-vanishing` and `definition-order-vanishing-meromorphic`.
-/

open AlgebraicGeometry CategoryTheory AlgebraicGeometry AlgebraicGeometry.Divisors AlgebraicGeometry.Proj AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Divisors.LineGenericCoordinates

universe u

namespace AlgebraicGeometry.Divisors.LineSectionCartierNonnegative

variable {k : Type u} [Field k] {X : SchemeOver k}

section Local

variable [IsIntegral X.scheme] [IsLocallyNoetherian X.scheme] {M : X.scheme.Modules}

/-- Every coefficient of a Cartier presentation of a global regular section is nonnegative. -/
theorem coefficient_nonneg (s : Γ(M, ⊤))
    (P : LineCartierPresentation X M (M.presheaf.germ ⊤ (genericPoint X.scheme) (by simp) s))
    (x : X.scheme) : 0 ≤ P.cartier.coefficient x := by
  by_cases hx : Order.coheight x = 1
  · let i := P.cartier.indexAt x
    have hxi : x ∈ P.cartier.opens i := P.cartier.indexAt_mem x
    have hU : Nonempty (P.cartier.opens i) := ⟨⟨x, hxi⟩⟩
    let a := lineStalkEquivOfTrivialization X.scheme M (P.cartier.opens i)
      ⟨x, hxi⟩ (P.frame i) (M.presheaf.germ ⊤ x (by simp) s)
    have heq : P.cartier.equation i =
        algebraMap (X.scheme.presheaf.stalk x) X.scheme.functionField a := by
      rw [P.equation_eq i hU]
      have h := lineStalkEquivOfTrivialization_toGenericFiber X.scheme M
        (P.cartier.opens i) (P.frame i) ⟨x, hxi⟩
        (genericPoint_mem_of_nonempty X.scheme (P.cartier.opens i) hU)
        (M.presheaf.germ ⊤ x (by simp) s)
      simpa only [moduleStalkToGenericFiber_germ, genericCoordinate, a] using! h
    have ha : a ≠ 0 := by
      intro hz
      apply P.cartier.equation_ne_zero i
      rw [heq, hz, map_zero]
    have : Ring.KrullDimLE 1 (X.scheme.presheaf.stalk x) := krullDimLE_of_coheight_le hx.le
    rw [P.cartier.coefficient_eq_ord x hx]
    apply (Scheme.le_ord_iff hx (P.cartier.equation_ne_zero i)).2
    change 1 ≤ Ring.ordFrac (X.scheme.presheaf.stalk x) (P.cartier.equation i)
    rw [heq]
    exact Ring.ordFrac_ge_one_of_ne_zero ha
  · rw [P.cartier.coefficient_eq_zero_of_coheight_ne_one x hx]

end Local

variable [IsIntegral X.scheme] {M : X.scheme.Modules}

/-- The actual residue-weighted zero-cycle degree of a regular section's presentation is
nonnegative on a proper integral curve. -/
theorem degree_nonneg [IsNoetherian X.scheme] [IsProper X.toBase]
    (hdim : topologicalKrullDim X.scheme ≤ 1) (s : Γ(M, ⊤))
    (P : LineCartierPresentation X M (M.presheaf.germ ⊤ (genericPoint X.scheme) (by simp) s)) :
    0 ≤ Intersection.rawZeroCycleDegree X.toBase (P.cartier.zeroCycle hdim) := by
  rw [Intersection.rawZeroCycleDegree_eq_sum]
  apply Finset.sum_nonneg
  intro x hx
  exact mul_nonneg (coefficient_nonneg s P x) (Int.natCast_nonneg _)

end AlgebraicGeometry.Divisors.LineSectionCartierNonnegative
