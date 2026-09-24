import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveLineStandardChart
import MiyaokaMori.Paper.S3PositiveLine.Realization.ProjectivizationMinors
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.PullbackUnit

/-! # Polynomials as functions on `A¹`, transport of trivializations, and a `congr` lemma

Glue for the fiber polynomial extension: polynomials as functions on `A¹`,
transport of a trivialization along a factorization, and a `congr` lemma for
`projectivizationMorphism`.

* `affineLinePolynomial k f` is the polynomial `f ∈ k[t]` regarded as a global function on
  `A¹_k = Spec k[t]` (through `AffineSpace.SpecIso` and `ΓSpecIso`); `polynomialSection O f`
  is by definition its restriction to the open `O`
  (`polynomialSection_eq_appTop`, `rfl`).
* `exists_unit_trivialization_of_comp`: a trivialization `τ₀ : i^*N ≅ O_F` of a pulled-back module
  transports along any `f : S ⟶ F` to a trivialization of `(f ≫ i)^*N ≅ O_S`, and on global sections
  `τ (f ≫ i)^*s = f^♯ (τ₀ (i^*s))` (Mathlib `pullbackComp`, `pullbackObjUnitToUnit`;
  `AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback_comp_inv`, `pullback_unit`).
* `projectivizationMorphism_congr_sections`: the projectivization only depends on the tuple
  (the nowhere-vanishing proof is a `Prop`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The polynomial `f ∈ k[t]` as a global function on `A¹_k` (`t ↦ X ⟨0⟩ ∈ k[X_{ULift (Fin 1)}]`,
then `ΓSpecIso⁻¹` and the chart `AffineSpace.SpecIso`). `polynomialSection O f` is its restriction
to `O` (`polynomialSection_eq_appTop`). -/
noncomputable def affineLinePolynomial (k : Type u) [Field k] (f : Polynomial k) :
    Γ(AlgebraicGeometry.Scheme.affineLineOver (AlgebraicGeometry.Spec (CommRingCat.of k)), ⊤) :=
  (AlgebraicGeometry.AffineSpace.SpecIso (ULift.{u} (Fin 1)) (CommRingCat.of k)).hom.appTop.hom
    ((AlgebraicGeometry.Scheme.ΓSpecIso
        (CommRingCat.of (MvPolynomial (ULift.{u} (Fin 1)) k))).inv.hom
      (Polynomial.aeval (MvPolynomial.X ⟨0⟩ : MvPolynomial (ULift.{u} (Fin 1)) k) f))

/-- `polynomialSection O f` is the restriction of the global function `affineLinePolynomial k f`. -/
theorem polynomialSection_eq_appTop {k : Type u} [Field k]
    (O : (AlgebraicGeometry.Scheme.affineLineOver (AlgebraicGeometry.Spec (CommRingCat.of k))).Opens)
    (f : Polynomial k) :
    polynomialSection O f = O.ι.appTop.hom (affineLinePolynomial k f) := rfl

theorem affineLinePolynomial_zero (k : Type u) [Field k] : affineLinePolynomial k 0 = 0 := by
  unfold affineLinePolynomial
  simp only [map_zero]
  rfl

theorem polynomialSection_zero {k : Type u} [Field k]
    (O : (AlgebraicGeometry.Scheme.affineLineOver (AlgebraicGeometry.Spec (CommRingCat.of k))).Opens) :
    polynomialSection O (0 : Polynomial k) = 0 := by
  rw [polynomialSection_eq_appTop, affineLinePolynomial_zero]
  exact map_zero _

/-- **Transport of a trivialization along a factorization.** If `τ₀ : i^*N ≅ O_F` and `f ≫ i = j`,
then `j^*N ≅ O_S` by `τ := (pullbackComp f i)⁻¹ ≪≫ f^*τ₀ ≪≫ (f^*O_F ≅ O_S)`, and on global sections
`τ (j^*s) = f^♯ (τ₀ (i^*s))`. -/
theorem exists_unit_trivialization_of_comp {S F T : AlgebraicGeometry.Scheme.{u}} (f : S ⟶ F) (i : F ⟶ T)
    (N : T.Modules)
    (τ₀ : (AlgebraicGeometry.Scheme.Modules.pullback i).obj N ≅ SheafOfModules.unit F.ringCatSheaf)
    (j : S ⟶ T) (hj : f ≫ i = j) :
    ∃ τ : (AlgebraicGeometry.Scheme.Modules.pullback j).obj N ≅ SheafOfModules.unit S.ringCatSheaf,
      ∀ s : (N.val.obj (Opposite.op ⊤) : Type u),
        τ.hom.app ⊤ (sectionPullbackAlong j s) =
          f.appTop.hom (τ₀.hom.app ⊤ (sectionPullbackAlong i s)) := by
  subst hj
  refine ⟨(((AlgebraicGeometry.Scheme.Modules.pullbackComp f i).app N).symm ≪≫
      (AlgebraicGeometry.Scheme.Modules.pullback f).mapIso τ₀) ≪≫
      AlgebraicGeometry.Scheme.Modules.pullbackUnitIso f, fun s => ?_⟩
  have h1 := AlgebraicGeometry.Scheme.Modules.pullbackComp_symm_trans_mapIso_app_top f i τ₀ s
  have h2 := AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback_unit f (τ₀.hom.app ⊤ (sectionPullbackAlong i s))
  change (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso f).hom.app ⊤
    ((((AlgebraicGeometry.Scheme.Modules.pullbackComp f i).app N).symm ≪≫
      (AlgebraicGeometry.Scheme.Modules.pullback f).mapIso τ₀).hom.app ⊤
        (sectionPullbackAlong (f ≫ i) s)) = _
  exact (congrArg (fun x => (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso f).hom.app ⊤ x) h1).trans h2

/-- The projectivization depends only on the tuple of sections (the nowhere-vanishing witness is a
proposition). -/
theorem projectivizationMorphism_congr_sections {k : Type u} [Field k]
    {V : AlgebraicGeometry.Scheme.{u}} [V.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (M : V.Modules) [M.IsLineBundle] {N : ℕ}
    {P P' : Fin (N + 1) → (M.val.obj (Opposite.op ⊤) : Type u)} (h : P = P')
    (hP : ∀ v : V, ∃ ℓ, ¬ IsZeroAt (P ℓ) v) (hP' : ∀ v : V, ∃ ℓ, ¬ IsZeroAt (P' ℓ) v) :
    projectivizationMorphism (k := k) M P hP = projectivizationMorphism (k := k) M P' hP' := by
  subst h
  rfl

end
