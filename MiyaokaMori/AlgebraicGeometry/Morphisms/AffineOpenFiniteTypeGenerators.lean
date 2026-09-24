import MiyaokaMori.Prelude

/-! # Finite generation of the sections of an affine open over a field

Let `V` be a scheme locally of finite type over a field `k` and `U ⊆ V` an affine open. Then `Γ(U, O)` is
generated as a `k`-algebra (through the structure morphism) by finitely many elements
`t_1, …, t_m ∈ Γ(V, U)`: the polynomial map `k[y_1,…,y_m] → Γ(U, O)`, `y_i ↦ t_i`, is surjective.

Proof: `U.ι ≫ (V ↘ Spec k)` is locally of finite type (open immersion followed by a morphism locally of
finite type), `U` and `Spec k` are affine, so `Γ(Spec k) → Γ(U)` is a ring map of finite type (Mathlib
`HasRingHomProperty.appTop`); composing with the isomorphism `k ≅ Γ(Spec k)` keeps finite type;
`Algebra.FiniteType.iff_quotient_mvPolynomial''` gives the surjection `k[y_1..y_m] → Γ(U)`, whose values at
the `y_i` are the generators.

Source: Stacks 01T0 (affine characterization of locally of finite type).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- **Finite generation of the coordinate ring of an affine open** of a scheme locally of finite type
over a field `k`: there are `t_1, …, t_m ∈ Γ(V, U)` with `k[y_1,…,y_m] → Γ(U, O)`, `y_i ↦ t_i`
surjective (the `k`-algebra structure is the one through the structure morphism, written as in
`projectivizationChartEval`). -/
theorem AlgebraicGeometry.exists_surjective_eval₂Hom_of_isAffineOpen (k : Type u) [Field k]
    (V : AlgebraicGeometry.Scheme.{u}) [V.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.LocallyOfFiniteType (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k))]
    (U : V.Opens) (hU : AlgebraicGeometry.IsAffineOpen U) :
    ∃ (m : ℕ) (t : Fin m → Γ(V, U)),
      Function.Surjective (MvPolynomial.eval₂Hom
        ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
          (U.ι ≫ (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k))).appTop).hom
        (fun i => U.topIso.inv.hom (t i))) := by
  have : AlgebraicGeometry.IsAffine U.toScheme := hU
  set c : CommRingCat.of k ⟶ Γ(U.toScheme, ⊤) :=
    (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
      (U.ι ≫ (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k))).appTop with hc
  have hft : c.hom.FiniteType := by
    have h1 : ((U.ι ≫ (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k))).appTop).hom.FiniteType :=
      AlgebraicGeometry.HasRingHomProperty.appTop (P := @AlgebraicGeometry.LocallyOfFiniteType)
        (U.ι ≫ (V ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) inferInstance
    have h2 : ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv).hom.FiniteType :=
      RingHom.FiniteType.of_surjective _
        (ConcreteCategory.bijective_of_isIso
          (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv).2
    exact h1.comp h2
  let _ : Algebra k Γ(U.toScheme, ⊤) := c.hom.toAlgebra
  have hFT : Algebra.FiniteType k Γ(U.toScheme, ⊤) := hft
  obtain ⟨m, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hFT
  refine ⟨m, fun i => U.topIso.hom.hom (f (MvPolynomial.X i)), ?_⟩
  intro y
  obtain ⟨p, rfl⟩ := hf y
  refine ⟨p, ?_⟩
  have hfa : f p = MvPolynomial.aeval (fun i => f (MvPolynomial.X i)) p := by
    conv_lhs => rw [MvPolynomial.aeval_unique f]
    rfl
  have hfun : (fun i => U.topIso.inv.hom (U.topIso.hom.hom (f (MvPolynomial.X i)))) =
      fun i => f (MvPolynomial.X i) := by
    funext i
    exact CategoryTheory.Iso.hom_inv_id_apply U.topIso _
  rw [hfun, hfa, MvPolynomial.aeval_eq_eval₂Hom, RingHom.algebraMap_toAlgebra]

end
