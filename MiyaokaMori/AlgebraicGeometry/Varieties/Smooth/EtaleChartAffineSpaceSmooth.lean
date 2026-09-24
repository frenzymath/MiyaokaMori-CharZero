import MiyaokaMori.Prelude

/-! # Affine space is smooth of relative dimension `n`

`𝔸^n_S → S` is smooth of relative dimension `n`: the polynomial algebra `R[X_1..X_n]` has a
submersive presentation with no relations (the Jacobian is the empty determinant `1`), so it is
standard smooth of relative dimension `n`; `𝔸^n_S` is the base change of `Spec ℤ[X_1..X_n] → Spec ℤ`
along `S → Spec ℤ`, and the property is stable under base change. Used for the étale chart
(`A^{n+1}_U → U` is smooth of relative dimension `n+1`).

Source: Stacks 00T7 (polynomial algebras are standard smooth).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace Algebra

/-- The polynomial algebra `R[X_i : i ∈ ι]` has the pre-submersive presentation with generators
`X_i` and no relations. -/
noncomputable def PreSubmersivePresentation.mvPolynomial (R : Type u) [CommRing R] (ι : Type v) :
    PreSubmersivePresentation R (MvPolynomial ι R) ι PEmpty.{1} where
  toGenerators := Generators.mvPolynomial R ι
  relation := PEmpty.elim
  span_range_relation_eq_ker := by
    rw [Set.range_eq_empty, Ideal.span_empty, Generators.ker_mvPolynomial]
  map := PEmpty.elim
  map_inj := fun a => a.elim

@[simp]
lemma PreSubmersivePresentation.mvPolynomial_jacobian (R : Type u) [CommRing R] (ι : Type v) :
    (PreSubmersivePresentation.mvPolynomial R ι).jacobian = 1 := by
  rw [PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det, Matrix.det_isEmpty, map_one]

/-- The polynomial algebra `R[X_i : i ∈ ι]` has the submersive presentation with generators `X_i`
and no relations (the Jacobian is the empty determinant `1`). -/
noncomputable def SubmersivePresentation.mvPolynomial (R : Type u) [CommRing R] (ι : Type v) :
    SubmersivePresentation R (MvPolynomial ι R) ι PEmpty.{1} where
  __ := PreSubmersivePresentation.mvPolynomial R ι
  jacobian_isUnit := by
    rw [PreSubmersivePresentation.mvPolynomial_jacobian]
    exact isUnit_one

/-- A polynomial algebra in finitely many variables is standard smooth of relative dimension the
number of variables. -/
theorem IsStandardSmoothOfRelativeDimension.mvPolynomial (R : Type u) [CommRing R] (ι : Type v)
    [Finite ι] : IsStandardSmoothOfRelativeDimension (Nat.card ι) R (MvPolynomial ι R) :=
  (SubmersivePresentation.mvPolynomial R ι).isStandardSmoothOfRelativeDimension
    (by simp [Presentation.dimension])

end Algebra

set_option backward.isDefEq.respectTransparency false in
/-- **Affine space is smooth of relative dimension `n` over its base.**
`𝔸(ULift (Fin n); S) ↘ S` is `pullback.fst (terminal.from S) (terminal.from (Spec ℤ[X_1..X_n]))`,
so by stability under base change (`smoothOfRelativeDimension_isStableUnderBaseChange`) it suffices
that `Spec ℤ[X_1..X_n] ⟶ ⊤_ Scheme` is smooth of relative dimension `n`. That morphism is
`Spec.map (ℤ → ℤ[X]) ≫ (Spec ℤ ⟶ ⊤_)`, the second factor an isomorphism (`Spec ℤ` is terminal,
`specULiftZIsTerminal`), so by `HasRingHomProperty.Spec_iff` it reduces to the ring map
`ℤ → ℤ[X_1..X_n]` being (locally) standard smooth of relative dimension `n`
(`Algebra.IsStandardSmoothOfRelativeDimension.mvPolynomial`, `Nat.card (ULift (Fin n)) = n`).

Toolchain note: `backward.isDefEq.respectTransparency` is switched off as in Mathlib, so that the
`RespectsIso` instance of `SmoothOfRelativeDimension n` is found. -/
theorem AlgebraicGeometry.AffineSpace.smoothOfRelativeDimension_over (n : ℕ)
    (S : AlgebraicGeometry.Scheme.{u}) :
    AlgebraicGeometry.SmoothOfRelativeDimension n
      (AlgebraicGeometry.AffineSpace (ULift.{u} (Fin n)) S ↘ S) := by
  have hbc : MorphismProperty.IsStableUnderBaseChange (@AlgebraicGeometry.SmoothOfRelativeDimension.{u} n) :=
    AlgebraicGeometry.smoothOfRelativeDimension_isStableUnderBaseChange n
  show AlgebraicGeometry.SmoothOfRelativeDimension n (pullback.fst (terminal.from S)
    (terminal.from (AlgebraicGeometry.Spec (CommRingCat.of (MvPolynomial (ULift.{u} (Fin n)) (ULift.{u} ℤ))))))
  apply MorphismProperty.pullback_fst
  have e : terminal.from (AlgebraicGeometry.Spec (CommRingCat.of (MvPolynomial (ULift.{u} (Fin n)) (ULift.{u} ℤ)))) =
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom
        (algebraMap (ULift.{u} ℤ) (MvPolynomial (ULift.{u} (Fin n)) (ULift.{u} ℤ)))) ≫
        terminal.from (AlgebraicGeometry.Spec (CommRingCat.of (ULift.{u} ℤ))) := by
    simp
  have hiso : IsIso (terminal.from (AlgebraicGeometry.Spec (CommRingCat.of (ULift.{u} ℤ)))) :=
    ⟨⟨AlgebraicGeometry.specULiftZIsTerminal.from _,
      AlgebraicGeometry.specULiftZIsTerminal.hom_ext _ _, terminalIsTerminal.hom_ext _ _⟩⟩
  rw [e, MorphismProperty.cancel_right_of_respectsIso (P := @AlgebraicGeometry.SmoothOfRelativeDimension.{u} n),
    AlgebraicGeometry.HasRingHomProperty.Spec_iff (P := @AlgebraicGeometry.SmoothOfRelativeDimension.{u} n)]
  refine RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ ?_
  rw [CommRingCat.hom_ofHom, RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
  have := Algebra.IsStandardSmoothOfRelativeDimension.mvPolynomial (ULift.{u} ℤ) (ULift.{u} (Fin n))
  simpa [Nat.card_eq_fintype_card] using this

end
