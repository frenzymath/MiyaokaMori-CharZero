import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.Cech.CechComplexAlternating
import MiyaokaMori.AlgebraicGeometry.Cohomology.Cech.CechComplexBaseChange
import MiyaokaMori.Algebra.CochainComplexToTopComplex
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.CoherentSheaf
import MiyaokaMori.AlgebraicGeometry.Modules.Flat.FlatFamilyRestrictAffineBase
import MiyaokaMori.AlgebraicGeometry.Cohomology.Coherent.Stacks02o6

/-! # Finiteness of the cohomology of the alternating Čech complex

Let `A` be a Noetherian ring, `f : X → Spec A` proper, `M` coherent and flat over `A`, and `U_1..U_n`
affine opens covering `X`. Then every cohomology module `H^i(Č_alt(U, M))` of the alternating Čech
complex (viewed as a complex of `A`-modules via `A → Γ(X, O_X)`) is a finite `A`-module.

Proof sketch:
1. Base change of the Čech complex with `A' = A`, `φ = 𝟙`:
   `H^i(X ×_A Spec A, pr₁^*M) ≃ₗ[A] H^i((extendScalars 𝟙) K)` for `i ∈ ℕ`.
2. The second projection `X ×_A Spec A → Spec A` is the base change of `f`, hence proper; `pr₁^*M` is
   coherent (`isCoherent_pullback`); Stacks 02O6 ⇒ the left side is a finite `A`-module.
3. `(extendScalars 𝟙).obj N ≃ₗ[A] A ⊗[A] N ≃ₗ[A] N` (`extendScalarsEquiv` followed by
   `TensorProduct.lid`), naturally in `N`; the middle homology is invariant under isomorphisms of
   three-term diagrams (`midHomology_of_equiv`, `homology_sc'_fin`), so `H^i(K)` is finite.
4. For `i < 0`, `K^i = 0` and the homology vanishes.

Source: Stacks 01XD + 02O6; Hartshorne III.4.5 + III.5.2.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-- `(extendScalars 𝟙).obj N ≃ₗ N`, naturally in `N`. -/
private def extendScalarsIdEquiv {R : Type u} [CommRing R] (N : ModuleCat.{u} R) :
    ((ModuleCat.extendScalars (algebraMap R R)).obj N) ≃ₗ[R] N :=
  (ModuleCat.extendScalarsEquiv (R := R) (S := R) N).trans (TensorProduct.lid R N)

private theorem extendScalarsIdEquiv_naturality {R : Type u} [CommRing R] {N N' : ModuleCat.{u} R}
    (g : N ⟶ N') (x : (ModuleCat.extendScalars (algebraMap R R)).obj N) :
    extendScalarsIdEquiv N' (((ModuleCat.extendScalars (algebraMap R R)).map g).hom x)
      = g.hom (extendScalarsIdEquiv N x) := by
  unfold extendScalarsIdEquiv
  simp only [LinearEquiv.trans_apply]
  rw [ModuleCat.extendScalarsEquiv_naturality]
  generalize ModuleCat.extendScalarsEquiv (S := R) N x = y
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a m => simp
  | add y z hy hz => simp only [map_add, hy, hz]

theorem AlgebraicGeometry.cechComplexAlt_homology_finite {A : CommRingCat.{u}} [IsNoetherianRing A]
    {X : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ AlgebraicGeometry.Spec A) [AlgebraicGeometry.IsProper f]
    {n : ℕ} (U : Fin n → X.Opens) (hU : ∀ i, AlgebraicGeometry.IsAffineOpen (U i)) (hcov : ⨆ i, U i = ⊤)
    (M : X.Modules) [M.IsCoherent]
    (hM : AlgebraicGeometry.Scheme.Modules.ModuleRelativeFlatness.FlatOver f M) (i : ℤ) :
    Module.Finite A ((((ModuleCat.restrictScalars
        ((AlgebraicGeometry.Scheme.ΓSpecIso A).inv ≫ f.appTop).hom).mapHomologicalComplex _).obj
      (AlgebraicGeometry.Scheme.Modules.cechComplexAlt U M)).homology i) := by
  have : M.IsQuasicoherent := AlgebraicGeometry.Scheme.Modules.IsCoherent.quasicoherent
  obtain ⟨-, hbdd, hiso⟩ := AlgebraicGeometry.cechComplexAlt_computes_baseChange f U hU hcov M hM
  generalize ((ModuleCat.restrictScalars
        ((AlgebraicGeometry.Scheme.ΓSpecIso A).inv ≫ f.appTop).hom).mapHomologicalComplex _).obj
      (AlgebraicGeometry.Scheme.Modules.cechComplexAlt U M) = K at hbdd hiso ⊢
  by_cases hi : i < 0
  · have := ModuleCat.isZero_iff_subsingleton.mp
      ((HomologicalComplex.exactAt_iff_isZero_homology _ _).mp
        (HomologicalComplex.ExactAt.of_isZero (hbdd i (Or.inl hi))))
    infer_instance
  · obtain ⟨k, rfl⟩ : ∃ k : ℕ, i = (k : ℤ) := ⟨i.toNat, by omega⟩
    let _ : (pullback f (AlgebraicGeometry.Spec.map (𝟙 A))).Over (AlgebraicGeometry.Spec A) :=
      ⟨pullback.snd f (AlgebraicGeometry.Spec.map (𝟙 A))⟩
    obtain ⟨e⟩ := hiso A (𝟙 A) k
    have : ((AlgebraicGeometry.Scheme.Modules.pullback (pullback.fst f
        (AlgebraicGeometry.Spec.map (𝟙 A)))).obj M).IsCoherent :=
      AlgebraicGeometry.Scheme.Modules.isCoherent_pullback _ M
    have hfin := AlgebraicGeometry.finite_sheafCohomology_of_isProper
      (pullback.snd f (AlgebraicGeometry.Spec.map (𝟙 A)))
      ((AlgebraicGeometry.Scheme.Modules.pullback (pullback.fst f
        (AlgebraicGeometry.Spec.map (𝟙 A)))).obj M) k
    have h1 : Module.Finite A ((((ModuleCat.extendScalars (𝟙 A : A ⟶ A).hom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K).homology (k : ℤ)) := Module.Finite.equiv e
    obtain ⟨f1, -⟩ := TopCx.homology_sc'_fin (((ModuleCat.extendScalars
      (𝟙 A : A ⟶ A).hom).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
      ((k : ℤ) - 1) k ((k : ℤ) + 1) (by ring) rfl
    obtain ⟨f2, -⟩ := TopCx.homology_sc'_fin K ((k : ℤ) - 1) k ((k : ℤ) + 1) (by ring) rfl
    obtain ⟨f3, -⟩ := LinearMap.midHomology_of_equiv
      ((((ModuleCat.extendScalars (𝟙 A : A ⟶ A).hom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K).d ((k : ℤ) - 1) k).hom
      ((((ModuleCat.extendScalars (𝟙 A : A ⟶ A).hom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K).d k ((k : ℤ) + 1)).hom
      (K.d ((k : ℤ) - 1) k).hom (K.d k ((k : ℤ) + 1)).hom
      (extendScalarsIdEquiv _) (extendScalarsIdEquiv _) (extendScalarsIdEquiv _)
      (fun x => extendScalarsIdEquiv_naturality _ x) (fun x => extendScalarsIdEquiv_naturality _ x)
    exact f2.mpr (f3.mp (f1.mp h1))

end
