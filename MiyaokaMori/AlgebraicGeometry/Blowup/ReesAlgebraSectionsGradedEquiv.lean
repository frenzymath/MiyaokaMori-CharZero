import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Blowup.ReesAlgebraSheafAffineSections

/-! # Sections of the Rees algebra sheaf on an affine open

On an affine open `U = Spec A` the graded sections ring `⊕ₙ Γ(U, Iⁿ)` of the Rees algebra sheaf
`I.reesAlgebra` is the Rees algebra `⊕ₙ Jⁿ Xⁿ ⊆ A[X]` of `J = I(U)`, as graded rings and
compatibly with the structure maps from `A = Γ(X, U)`.

Source: Stacks 01OG (definition of the blowup: on `Spec A` the sheaf `⊕ Iⁿ` is the Rees algebra
`⊕ Jⁿ`), used in Stacks 0804.

This is the special case `ψ = RingEquiv.refl`, `J = I(U)` of
`exists_reesAlgebra_sectionsRing_equiv_of_ringEquiv`, which builds the graded ring isomorphism
`(sₙ)ₙ ↦ ∑ₙ ψ(sₙ) Xⁿ` by `DirectSum.toSemiring` from the piece maps and the multiplication formula
`coe_reesAlgebra_sectionsGMul`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- **Sections of the Rees algebra sheaf on an affine open are the Rees algebra of `I(U)`**, as
graded rings, compatibly with the unit `Γ(X, U) → ⊕ₙ Γ(U, Iⁿ)` and `A → ⊕ₙ Jⁿ Xⁿ`.

Source: Stacks 01OG / 0804 (on `U = Spec A` the quasi-coherent graded algebra `⊕ Iⁿ` has sections
`⊕ Jⁿ`, `J = I(U)`, with the obvious multiplication).

**Proof.** This is `exists_reesAlgebra_sectionsRing_equiv_of_ringEquiv` with
`ψ := RingEquiv.refl Γ(X, U)` and `J := I.ideal U` (the hypothesis `x ∈ I(U) ↔ ψ x ∈ J` is
`Iff.rfl`). That proof runs, with `S := I.reesAlgebra`, `A := Γ(X, U)`, `J := I.ideal U`:
1. **Pieces.** `Γ(U, I.pow n) = { s ∈ A | ∀ affine V ≤ U, s|_V ∈ I(V)^n } = J^n` as subsets of `A`
   (`mem_powSubmodule_affine_iff`, equivalently `mem_powSubmodule_iff_of_isAffineOpen`, via Mathlib's
   `IdealSheafData.ideal_le_comap_ideal` / `map_ideal`).
2. **The ring map.** `e := DirectSum.toSemiring (fun n => reesPieceToReesAlgebra n)`, with
   `reesPieceToReesAlgebra n : Γ(U, Iⁿ) →+ Rees J`, `s ↦ s Xⁿ` (`reesAlgebra.monomial_mem`). Its
   `n`-th coefficient is the `n`-th component (`coeff_reesSectionsToReesAlgebra`), so `e` is injective
   (`DirectSum.ext` + coefficients) and surjective (`DirectSum.mk` on the polynomial's support).
3. **Multiplicativity.** `of m a * of n b = of (m+n) (sectionsGMul a b)` (`DirectSum.of_mul_of`) and
   `(sectionsGMul a b).1 = a.1 * b.1` (`coe_reesAlgebra_sectionsGMul`, which unwinds
   `powMul = liftPow (powMulToUnit)` on `tensorSections` through the localized monoidal structure), so
   `e (of m a * of n b) = monomial (m+n) (ab) = monomial m a * monomial n b`
   (`Polynomial.monomial_mul_monomial`); `e 1 = monomial 0 1 = 1` (`monoidalUnitIso_hom_app`).
4. **Grading.** `mem_sectionsGrading_iff_reesSectionsRingEquiv`: (→) `e (of m a)` is a monomial of
   degree `m` (`MiyaokaMori.RingTheory.ReesAlgebra.mem_grading_iff`); (←) `e (of m (component m x)) = e x` by
   `MiyaokaMori.RingTheory.ReesAlgebra.eq_monomial_of_mem` + the coefficient formula, then injectivity and
   `GradedQCAlgebra.mem_sectionsGrading_iff`.
5. **Unit.** `sectionsUnitHom U r = of 0 (S.one.app U r)` (rfl) and `(S.one.app U r).1 = r`
   (`monoidalUnitIso_hom_app`), so `e (sectionsUnitHom U r) = monomial 0 r = algebraMap A (Rees J) r`
   (`reesSectionsRingEquiv_sectionsUnitHom`).

Edge cases: `U = ∅` (`A = 0`, both rings trivial); `I = ⊥` (`J^n = 0` for `n ≥ 1`, both sides are
`A` in degree `0`); `I = ⊤` (both sides `A[X]`) — all covered by the general argument. -/
theorem AlgebraicGeometry.Scheme.IdealSheafData.exists_reesAlgebra_sectionsRing_equiv
    {X : AlgebraicGeometry.Scheme.{u}} (I : X.IdealSheafData) (U : X.affineOpens) :
    ∃ e : I.reesAlgebra.sectionsRing (U : X.Opens) ≃+* _root_.reesAlgebra (I.ideal U),
      (∀ (m : ℕ) (x : I.reesAlgebra.sectionsRing (U : X.Opens)),
        x ∈ I.reesAlgebra.sectionsGrading (U : X.Opens) m ↔ e x ∈ Ideal.reesGrading (I.ideal U) m) ∧
      ∀ r : Γ(X, (U : X.Opens)),
        e (I.reesAlgebra.sectionsUnitHom (U : X.Opens) r) =
          algebraMap Γ(X, (U : X.Opens)) (_root_.reesAlgebra (I.ideal U)) r :=
  I.exists_reesAlgebra_sectionsRing_equiv_of_ringEquiv U (RingEquiv.refl _) (I.ideal U)
    (fun _ => Iff.rfl)

end
