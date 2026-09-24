import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.Cech.CechComplexAlternating
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedQcAlgebraPullback
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPullbackQuasicoherent
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.QcPullbackAffineSections
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.QuasicoherentAffineLocal
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafCohomologyModule
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModuleSheafStalkStmt
import MiyaokaMori.AlgebraicGeometry.Cohomology.Cech.Stacks01x9
import MiyaokaMori.AlgebraicGeometry.Cohomology.Vanishing.Stacks01xb
import MiyaokaMori.AlgebraicGeometry.Cohomology.Cech.Stacks01ew
import MiyaokaMori.AlgebraicGeometry.Modules.Flat.Stacks01u4
import MiyaokaMori.AlgebraicGeometry.Cohomology.Cech.CechLeray
import MiyaokaMori.AlgebraicGeometry.Cohomology.Cech.CechBaseChangeIso
import MiyaokaMori.AlgebraicGeometry.Cohomology.Cech.CechBaseChangeLeaves
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.PullbackSectionsAffine
import MiyaokaMori.AlgebraicGeometry.Modules.Flat.SectionsFlatOfFlatOver
import MiyaokaMori.Algebra.RestrictScalarsHomology

/-! # The Čech complex computes cohomology after base change

Let `f : X → Spec A` be separated, `U_1..U_n` affine opens covering `X`, and `F` quasi-coherent and
flat over `A`. Then the terms of the alternating Čech complex `K^•` are flat `A`-modules, nonzero only
in degrees `0..n−1`, and for every `A → A'` the cohomology of `K^• ⊗_A A'` is isomorphic
(`A'`-linearly) to `H^i(X_{A'}, F_{A'})`.

Source: Stacks 01XD (statement), 01XL/01XM, 01U4; the proof follows the dimension shifting of
Hartshorne III.4.5 (p. 222), using only the alternating Čech complex (no spectral sequence).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- **Stacks 01XD (alternating complex version)**: `X` separated over an affine base, `U` a finite
affine open cover, `M` quasi-coherent ⇒ `H^i(X, M) ≃ Ȟ^i_alt(U, M)`, `Γ(X, O_X)`-linearly. Immediate
from Leray (`sheafCohomology_equiv_cechAlt_homology`) and affine vanishing (Stacks 01XB); no
Noetherian hypothesis. -/
theorem AlgebraicGeometry.sheafCohomology_equiv_cechAlt_of_isSeparated {A : CommRingCat.{u}}
    {X : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ AlgebraicGeometry.Spec A) [AlgebraicGeometry.IsSeparated f]
    {n : ℕ} (U : Fin n → X.Opens) (hU : ∀ i, AlgebraicGeometry.IsAffineOpen (U i)) (hcov : ⨆ i, U i = ⊤)
    (M : X.Modules) [M.IsQuasicoherent] (i : ℕ) :
    Nonempty (AlgebraicGeometry.sheafCohomology X M i ≃ₗ[Γ(X, ⊤)]
      ((AlgebraicGeometry.Scheme.Modules.cechComplexAlt U M).homology ((i : ℕ) : ℤ))) :=
  AlgebraicGeometry.Scheme.Modules.sheafCohomology_equiv_cechAlt_homology U hcov i M
    fun _ σ p hp => sheafCohomology'_affineOpen_vanishing M
      (AlgebraicGeometry.Scheme.Modules.isAffineOpen_iInf_of_isSeparated f (fun k => U (σ k))
        (fun k => hU (σ k))) p hp

/-- **Cohomology after base change is computed by `K^• ⊗_A A'`** (Stacks 01XD + 02KG; the first
paragraph of the proofs of Hartshorne III.4.5 + III.9.3). Flatness of `M` over `A` is not needed. -/
theorem AlgebraicGeometry.cechComplexAlt_baseChange_cohomology {A : CommRingCat.{u}}
    {X : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ AlgebraicGeometry.Spec A) [AlgebraicGeometry.IsSeparated f]
    {n : ℕ} (U : Fin n → X.Opens) (hU : ∀ i, AlgebraicGeometry.IsAffineOpen (U i)) (hcov : ⨆ i, U i = ⊤)
    (M : X.Modules) [M.IsQuasicoherent] (A' : CommRingCat.{u}) (φ : A ⟶ A') (i : ℕ) :
    letI : (CategoryTheory.Limits.pullback f (AlgebraicGeometry.Spec.map φ)).Over (AlgebraicGeometry.Spec A') :=
      ⟨CategoryTheory.Limits.pullback.snd f (AlgebraicGeometry.Spec.map φ)⟩
    Nonempty (AlgebraicGeometry.sheafCohomology
        (CategoryTheory.Limits.pullback f (AlgebraicGeometry.Spec.map φ))
        ((AlgebraicGeometry.Scheme.Modules.pullback
          (CategoryTheory.Limits.pullback.fst f (AlgebraicGeometry.Spec.map φ))).obj M) i
      ≃ₗ[A'] (((ModuleCat.extendScalars φ.hom).mapHomologicalComplex _).obj
        (((ModuleCat.restrictScalars
          ((AlgebraicGeometry.Scheme.ΓSpecIso A).inv ≫ f.appTop).hom).mapHomologicalComplex _).obj
        (AlgebraicGeometry.Scheme.Modules.cechComplexAlt U M))).homology (i : ℤ)) := by
  have haff : ∀ (q : ℕ) (σ : Fin (q + 1) ↪o Fin n),
      AlgebraicGeometry.IsAffineOpen (⨅ k, U (σ k)) := fun q σ =>
    AlgebraicGeometry.Scheme.Modules.isAffineOpen_iInf_of_isSeparated f (fun k => U (σ k))
      (fun k => hU (σ k))
  let _ : (CategoryTheory.Limits.pullback f (AlgebraicGeometry.Spec.map φ)).Over
      (AlgebraicGeometry.Spec A') :=
    ⟨CategoryTheory.Limits.pullback.snd f (AlgebraicGeometry.Spec.map φ)⟩
  have : AlgebraicGeometry.IsAffineHom
      (CategoryTheory.Limits.pullback.fst f (AlgebraicGeometry.Spec.map φ)) :=
    AlgebraicGeometry.Scheme.Modules.isAffineHom_pullback_fst_spec f φ
  -- the pullback of the cover is a cover
  have hcov' : ⨆ i, (CategoryTheory.Limits.pullback.fst f (AlgebraicGeometry.Spec.map φ)) ⁻¹ᵁ U i
      = ⊤ := by
    have h := congrArg
      (fun W => (CategoryTheory.Limits.pullback.fst f (AlgebraicGeometry.Spec.map φ)) ⁻¹ᵁ W) hcov
    simpa [AlgebraicGeometry.Scheme.Hom.preimage_iSup] using h
  -- finite intersections of the pulled-back cover are affine; quasi-coherent sheaves are acyclic there
  -- (Stacks 01XB)
  have hacyc : ∀ (q : ℕ) (σ : Fin (q + 1) ↪o Fin n) (p : ℕ), 0 < p →
      Subsingleton (((AlgebraicGeometry.Scheme.Modules.pullback
        (CategoryTheory.Limits.pullback.fst f (AlgebraicGeometry.Spec.map φ))).obj
          M).toAddCommGrpSheaf.H' p
        (⨅ k, (CategoryTheory.Limits.pullback.fst f (AlgebraicGeometry.Spec.map φ)) ⁻¹ᵁ
          U (σ k))) := by
    intro q σ p hp
    refine sheafCohomology'_affineOpen_vanishing _ ?_ p hp
    rw [← AlgebraicGeometry.Scheme.Modules.preimage_iInf_eq]
    exact (haff q σ).preimage _
  -- Leray (alternating complex version, Hartshorne III.4.5)
  obtain ⟨r⟩ := AlgebraicGeometry.Scheme.Modules.sheafCohomology_equiv_cechAlt_homology
    (fun i => (CategoryTheory.Limits.pullback.fst f (AlgebraicGeometry.Spec.map φ)) ⁻¹ᵁ U i)
    hcov' i _ hacyc
  -- `K ⊗_A A'` ≅ the Čech complex of the pulled-back cover (as a complex of `A'`-modules)
  obtain ⟨χ⟩ := AlgebraicGeometry.Scheme.Modules.cechBaseChange_complex_iso
    (CategoryTheory.Limits.pullback.fst f (AlgebraicGeometry.Spec.map φ))
    ((AlgebraicGeometry.Scheme.ΓSpecIso A).inv ≫ f.appTop).hom
    ((AlgebraicGeometry.Scheme.ΓSpecIso A').inv ≫
      (CategoryTheory.Limits.pullback.snd f (AlgebraicGeometry.Spec.map φ)).appTop).hom
    φ.hom U (AlgebraicGeometry.Scheme.Modules.appTop_comp_structure_eq f φ) M
    (fun p σ => AlgebraicGeometry.Scheme.Modules.isIso_transpose_pullbackSectionsLinear_of_affine
      f φ M _ (haff p σ) _ _
      (AlgebraicGeometry.Scheme.Modules.preimage_iInf_eq _ fun k => U (σ k)).symm)
  exact ModuleCat.nonempty_linearEquiv_homology_of_restrictScalars_iso _ _ _ χ (i : ℤ)
    (fun _ _ => rfl) r


theorem AlgebraicGeometry.cechComplexAlt_computes_baseChange {A : CommRingCat.{u}}
    {X : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ AlgebraicGeometry.Spec A) [AlgebraicGeometry.IsSeparated f]
    {n : ℕ} (U : Fin n → X.Opens) (hU : ∀ i, AlgebraicGeometry.IsAffineOpen (U i)) (hcov : ⨆ i, U i = ⊤)
    (M : X.Modules) [M.IsQuasicoherent] (hM : AlgebraicGeometry.Scheme.Modules.ModuleRelativeFlatness.FlatOver f M) :
    -- restrict scalars along `A ≅ Γ(Spec A, ⊤) → Γ(X, ⊤)` (global sections of `f`) to view the Čech
    -- complex as a complex of `A`-modules
    let K := ((ModuleCat.restrictScalars
        ((AlgebraicGeometry.Scheme.ΓSpecIso A).inv ≫ f.appTop).hom).mapHomologicalComplex _).obj
      (AlgebraicGeometry.Scheme.Modules.cechComplexAlt U M)
    (∀ p, Module.Flat A (K.X p)) ∧ (∀ p, (p < 0 ∨ (n : ℤ) ≤ p) → CategoryTheory.Limits.IsZero (K.X p)) ∧
    ∀ (A' : CommRingCat.{u}) (φ : A ⟶ A') (i : ℕ),
      -- the base change `X_{A'} := X ×_{Spec A} Spec A'` is an `A'`-scheme via the second projection
      -- (this gives the `A'`-module structure on cohomology)
      letI : (CategoryTheory.Limits.pullback f (AlgebraicGeometry.Spec.map φ)).Over (AlgebraicGeometry.Spec A') :=
        ⟨CategoryTheory.Limits.pullback.snd f (AlgebraicGeometry.Spec.map φ)⟩
      Nonempty (AlgebraicGeometry.sheafCohomology
          (CategoryTheory.Limits.pullback f (AlgebraicGeometry.Spec.map φ))
          ((AlgebraicGeometry.Scheme.Modules.pullback
            (CategoryTheory.Limits.pullback.fst f (AlgebraicGeometry.Spec.map φ))).obj M) i
        ≃ₗ[A'] (((ModuleCat.extendScalars φ.hom).mapHomologicalComplex _).obj K).homology (i : ℤ)) := by
  intro K
  have haff : ∀ (q : ℕ) (σ : Fin (q + 1) ↪o Fin n),
      AlgebraicGeometry.IsAffineOpen (⨅ k, U (σ k)) := fun q σ =>
    AlgebraicGeometry.Scheme.Modules.isAffineOpen_iInf_of_isSeparated f (fun k => U (σ k))
      (fun k => hU (σ k))
  refine ⟨fun p => ?_, fun p hp => ?_, fun A' φ i =>
    AlgebraicGeometry.cechComplexAlt_baseChange_cohomology f U hU hcov M A' φ i⟩
  · -- (1) the terms are flat
    cases p with
    | ofNat q =>
      exact AlgebraicGeometry.Scheme.Modules.flat_restrictScalars_pi _ _ fun σ =>
        AlgebraicGeometry.Scheme.Modules.sectionsOverTop_flat_of_isFlatOver f M hM _ (haff q σ)
    | negSucc k =>
      haveI : Subsingleton ↑(K.X (Int.negSucc k)) := inferInstanceAs (Subsingleton PUnit)
      infer_instance
  · -- (2) zero outside degrees `0..n−1`
    cases p with
    | ofNat q =>
      have hq : n ≤ q := by
        rcases hp with hp | hp
        · exact absurd hp (by simp)
        · exact Int.ofNat_le.mp hp
      show CategoryTheory.Limits.IsZero ((ModuleCat.restrictScalars
        ((AlgebraicGeometry.Scheme.ΓSpecIso A).inv ≫ f.appTop).hom).obj
        (AlgebraicGeometry.Scheme.Modules.cechTermAlt U M q))
      exact Functor.map_isZero _
        (AlgebraicGeometry.Scheme.Modules.cechTermAlt_isZero_of_le U M q hq)
    | negSucc k =>
      show CategoryTheory.Limits.IsZero ((ModuleCat.restrictScalars
        ((AlgebraicGeometry.Scheme.ΓSpecIso A).inv ≫ f.appTop).hom).obj
        (ModuleCat.of Γ(X, ⊤) PUnit))
      exact Functor.map_isZero _ (ModuleCat.isZero_of_subsingleton (ModuleCat.of Γ(X, ⊤) PUnit))

end
