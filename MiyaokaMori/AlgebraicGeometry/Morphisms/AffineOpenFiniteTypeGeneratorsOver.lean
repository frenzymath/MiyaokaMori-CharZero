import MiyaokaMori.Prelude

/-! # Finite generation of the sections of an affine open over a base ring

`f : V → Spec R` locally of finite type, `U ⊆ V` affine open ⇒ `Γ(U, O)` is generated as an `R`-algebra
(through `f`) by finitely many `t_1, …, t_m ∈ Γ(V, U)`: `R[y_1..y_m] → Γ(U, O)`, `y_i ↦ t_i` surjective.

Ring version of `exists_surjective_eval₂Hom_of_isAffineOpen`
(`AffineOpenFiniteTypeGenerators.lean`, stated for `V ↘ Spec k` with `k` a field); the proof
is the same word for word — `U.ι ≫ f` is locally of finite type, `U` and `Spec R` are affine, so
`Γ(Spec R) → Γ(U)` is of finite type (Mathlib `HasRingHomProperty.appTop`), and
`Algebra.FiniteType.iff_quotient_mvPolynomial''` gives the surjection.

Source: Stacks 01T0/01T1.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- **Finite generation of the coordinate ring of an affine open** of a scheme locally of finite type
over a ring `R` (via `f : V → Spec R`): there are `t_1, …, t_m ∈ Γ(V, U)` with `R[y_1,…,y_m] → Γ(U, O)`,
`y_i ↦ t_i` surjective (the `R`-algebra structure is `ΓSpecIso.inv ≫ (U.ι ≫ f).appTop`, as in
`projectivizationChartEvalOver`). -/
theorem AlgebraicGeometry.exists_surjective_eval₂Hom_of_isAffineOpen_over {R : Type u} [CommRing R]
    {V : AlgebraicGeometry.Scheme.{u}} (f : V ⟶ AlgebraicGeometry.Spec (CommRingCat.of R))
    [AlgebraicGeometry.LocallyOfFiniteType f]
    (U : V.Opens) (hU : AlgebraicGeometry.IsAffineOpen U) :
    ∃ (m : ℕ) (t : Fin m → Γ(V, U)),
      Function.Surjective (MvPolynomial.eval₂Hom
        ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (U.ι ≫ f).appTop).hom
        (fun i => U.topIso.inv.hom (t i))) := by
  have : AlgebraicGeometry.IsAffine U.toScheme := hU
  set c : CommRingCat.of R ⟶ Γ(U.toScheme, ⊤) :=
    (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (U.ι ≫ f).appTop with hc
  have hft : c.hom.FiniteType := by
    have h1 : ((U.ι ≫ f).appTop).hom.FiniteType :=
      AlgebraicGeometry.HasRingHomProperty.appTop (P := @AlgebraicGeometry.LocallyOfFiniteType)
        (U.ι ≫ f) inferInstance
    have h2 : ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of R)).inv).hom.FiniteType :=
      RingHom.FiniteType.of_surjective _
        (ConcreteCategory.bijective_of_isIso
          (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of R)).inv).2
    exact h1.comp h2
  let _ : Algebra R Γ(U.toScheme, ⊤) := c.hom.toAlgebra
  have hFT : Algebra.FiniteType R Γ(U.toScheme, ⊤) := hft
  obtain ⟨m, g, hg⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp hFT
  refine ⟨m, fun i => U.topIso.hom.hom (g (MvPolynomial.X i)), ?_⟩
  intro y
  obtain ⟨p, rfl⟩ := hg y
  refine ⟨p, ?_⟩
  have hga : g p = MvPolynomial.aeval (fun i => g (MvPolynomial.X i)) p := by
    conv_lhs => rw [MvPolynomial.aeval_unique g]
    rfl
  have hfun : (fun i => U.topIso.inv.hom (U.topIso.hom.hom (g (MvPolynomial.X i)))) =
      fun i => g (MvPolynomial.X i) := by
    funext i
    exact CategoryTheory.Iso.hom_inv_id_apply U.topIso _
  rw [hfun, hga, MvPolynomial.aeval_eq_eval₂Hom, RingHom.algebraMap_toAlgebra]

end
