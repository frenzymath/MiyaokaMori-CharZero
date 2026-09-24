import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.Coherent.Stacks01xt

/-! # Finiteness of the cohomology of twists over a Noetherian ring (Stacks 01XT)

Stacks 01XT, finiteness, over a Noetherian ring: `R` Noetherian, `P^N_R = ProjectiveSpaceOver N R`,
`O(d) = projectiveSpaceOverTwist R N d`. Then every
`H^q(P^N_R, O(d))` is a finite `R`-module (for the `R`-structure `sheafCohomology.moduleOver` of the
structure morphism `P^N_R → Spec R`).

This is the ring form of the field statement `finiteDimensional_sheafCohomology_projectiveSpaceTwist`
(`Stacks01xt.lean`). The assembly there is already stated over an arbitrary ring up to the `Field`
section (`Stacks01xtAux.exists_leray` — Leray for the standard affine cover — is over `R`); the `Field`
section only used the field through `isNoetherian_of_isNoetherianRing_of_finite k`. So this module is
that section with `k ↦ R`, `[IsNoetherianRing R]` added exactly where the Noetherian hypothesis is used.
It depends on the same inputs as the field case: `ProjectiveSpaceOver.exists_cechFamily_equiv_laurent`
and `LaurentCech.finite_ker_δ_zero`, `LaurentCech.finite_homology_succ`, all stated over an arbitrary
ring.

Route (Stacks 01XT, first paragraph; Hartshorne III.5.1): Leray for the alternating Čech complex of the
standard affine cover `D_+(T_i)` gives `H^q(P^N_R, O(d)) ≃ Ȟ^q_alt(U, O(d))`, `Γ(P^N_R, O)`-linearly.
Under the term-wise isomorphisms `e` the alternating Čech complex is the Laurent–Čech complex
`LaurentCech.Cochain R N d`, whose `ker δ^0` and `H^{q+1}` are finite `R`-modules. The `R`-structures
are matched through `ModuleCat.restrictScalars` along `R → Γ(P^N_R, O)`.

Source: Stacks 01XT (coherent-lemma-cohomology-projective-space-over-ring); Hartshorne III.5.1;
EGA III 2.1.12.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace Stacks01xtOverRing

open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

attribute [local instance] MvPolynomial.gradedAlgebra

variable (R : Type u) [CommRing R] (N : ℕ) (d : ℤ)

/-- The ring map `R → Γ(P^N_R, O)` through which `R` acts on everything (the one in
`sheafCohomology.moduleOver`). -/
def baseHom : R →+* Γ(ProjectiveSpaceOver N R, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
    (ProjectiveSpaceOver N R ↘ Spec (CommRingCat.of R)).appTop).hom

theorem scalar_eq (V : (ProjectiveSpaceOver N R).Opens) (r : R) :
    ProjectiveSpaceOver.scalar N R V r =
      ((ProjectiveSpaceOver N R).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom (baseHom R N r) := rfl

/-- The term-wise isomorphisms between the Čech terms of `O(d)` and the Laurent–Čech terms. -/
abbrev TermEquiv : Type u := ∀ (p : ℕ) (σ : Fin (p + 1) ↪o Fin (N + 1)),
  Γ(projectiveSpaceOverTwist R N d, ⨅ j, ProjectiveSpaceOver.chart N R (σ j)) ≃+
    LaurentCech.Term R N d (LaurentCech.V N p σ)

variable {R N d}

/-- Compatibility with the Čech face restrictions. -/
abbrev FaceCompat (e : TermEquiv R N d) : Prop :=
  ∀ (p : ℕ) (τ : Fin (p + 2) ↪o Fin (N + 1)) (k' : Fin (p + 2))
    (x : Γ(projectiveSpaceOverTwist R N d, ⨅ j, ProjectiveSpaceOver.chart N R ((CechAltAlg.face τ k') j))),
    e (p + 1) τ ((projectiveSpaceOverTwist R N d).presheaf.map
      (homOfLE (cech_face_le (ProjectiveSpaceOver.chart N R) τ k')).op x) =
      LaurentCech.res d (LaurentCech.hface N p τ k') (e p (CechAltAlg.face τ k') x)

/-- `R`-linearity. -/
abbrev ScalarCompat (e : TermEquiv R N d) : Prop :=
  ∀ (p : ℕ) (σ : Fin (p + 1) ↪o Fin (N + 1)) (r : R)
    (x : Γ(projectiveSpaceOverTwist R N d, ⨅ j, ProjectiveSpaceOver.chart N R (σ j))),
    e p σ (ProjectiveSpaceOver.scalar N R (⨅ j, ProjectiveSpaceOver.chart N R (σ j)) r • x) = r • e p σ x

variable (R N d) in
/-- The `p`-th alternating Čech term of `O(d)` on the standard cover, as an `R`-module along `baseHom`. -/
abbrev CechTermR (p : ℕ) : Type u :=
  ((ModuleCat.restrictScalars (baseHom R N)).obj
    (cechTermAlt (ProjectiveSpaceOver.chart N R) (projectiveSpaceOverTwist R N d) p))

variable (R N d) in
/-- The family of Čech terms `σ ↦ Γ(O(d), U_σ)` (as `Γ(P^N, O)`-modules) whose product is `cechTermAlt`. -/
abbrev Fam (p : ℕ) : (Fin (p + 1) ↪o Fin (N + 1)) → ModuleCat.{u} Γ(ProjectiveSpaceOver N R, ⊤) :=
  fun σ => (projectiveSpaceOverTwist R N d).sectionsOverTop (⨅ j, ProjectiveSpaceOver.chart N R (σ j))

/-- `C^p_alt(U, O(d)) → LaurentCech.Cochain R N d p`, `x ↦ (σ ↦ e p σ (x_σ))`, `R`-linear for the
`R`-structure restricted along `baseHom`. -/
def toLaurent (e : TermEquiv R N d) (hlin : ScalarCompat e) (p : ℕ) :
    CechTermR R N d p →ₗ[R] LaurentCech.Cochain R N d p where
  toFun x := fun σ => e p σ (cechToFamily (ProjectiveSpaceOver.chart N R) (projectiveSpaceOverTwist R N d) p x σ)
  map_add' x y := by
    funext σ
    exact (congrArg (e p σ) (map_add (Pi.π (Fam R N d p) σ).hom x y)).trans (map_add (e p σ) _ _)
  map_smul' r x := by
    funext σ
    exact (congrArg (e p σ) (_root_.map_smul (Pi.π (Fam R N d p) σ).hom (baseHom R N r) x)).trans
      (hlin p σ r _)

theorem toLaurent_apply (e : TermEquiv R N d) (hlin : ScalarCompat e) (p : ℕ) (x : CechTermR R N d p)
    (σ : Fin (p + 1) ↪o Fin (N + 1)) :
    toLaurent e hlin p x σ =
      e p σ (cechToFamily (ProjectiveSpaceOver.chart N R) (projectiveSpaceOverTwist R N d) p x σ) := rfl

theorem toLaurent_bijective (e : TermEquiv R N d) (hlin : ScalarCompat e) (p : ℕ) :
    Function.Bijective (toLaurent e hlin p) := by
  constructor
  · intro x y hxy
    apply (cechToFamily_bijective (ProjectiveSpaceOver.chart N R) (projectiveSpaceOverTwist R N d) p).1
    funext σ
    exact (e p σ).injective (congrFun hxy σ)
  · intro s
    obtain ⟨x, hx⟩ := (cechToFamily_bijective (ProjectiveSpaceOver.chart N R)
      (projectiveSpaceOverTwist R N d) p).2 (fun σ => (e p σ).symm (s σ))
    refine ⟨x, ?_⟩
    funext σ
    show e p σ (cechToFamily (ProjectiveSpaceOver.chart N R) (projectiveSpaceOverTwist R N d) p x σ) = s σ
    rw [hx]
    exact (e p σ).apply_symm_apply _

/-- The `R`-linear isomorphism `C^p_alt(U, O(d)) ≃ LaurentCech.Cochain R N d p`. -/
def toLaurentEquiv (e : TermEquiv R N d) (hlin : ScalarCompat e) (p : ℕ) :
    CechTermR R N d p ≃ₗ[R] LaurentCech.Cochain R N d p :=
  LinearEquiv.ofBijective _ (toLaurent_bijective e hlin p)

/-- Compatibility with the differentials (face compatibility + `cechFamilyD_eq_δ`). -/
theorem toLaurent_d (e : TermEquiv R N d) (he : FaceCompat e) (hlin : ScalarCompat e) (p : ℕ)
    (x : CechTermR R N d p) :
    toLaurentEquiv e hlin (p + 1) (((ModuleCat.restrictScalars (baseHom R N)).map
        (cechDiffAlt (ProjectiveSpaceOver.chart N R) (projectiveSpaceOverTwist R N d) p)).hom x) =
      LaurentCech.δ R N d p (toLaurentEquiv e hlin p x) := by
  have h1 := cechToFamily_diff (ProjectiveSpaceOver.chart N R) (projectiveSpaceOverTwist R N d) p x
  have h2 := ProjectiveSpaceOver.cechFamilyD_eq_δ R N d e he p
    (cechToFamily (ProjectiveSpaceOver.chart N R) (projectiveSpaceOverTwist R N d) p x)
  show (fun τ => e (p + 1) τ (cechToFamily (ProjectiveSpaceOver.chart N R) (projectiveSpaceOverTwist R N d) (p + 1)
    ((cechDiffAlt (ProjectiveSpaceOver.chart N R) (projectiveSpaceOverTwist R N d) p).hom x) τ)) =
    LaurentCech.δ R N d p
      (fun σ => e p σ (cechToFamily (ProjectiveSpaceOver.chart N R) (projectiveSpaceOverTwist R N d) p x σ))
  rw [h1]
  exact h2

variable (R N d)

/-- `H^0(P^N_R, O(d))` embeds `R`-linearly into `ker δ^0` of the Laurent–Čech complex. -/
theorem exists_injective_zero :
    ∃ F : sheafCohomology (ProjectiveSpaceOver N R) (projectiveSpaceOverTwist R N d) 0 →ₗ[R]
      LinearMap.ker (LaurentCech.δ R N d 0), Function.Injective F := by
  obtain ⟨e, he, hlin⟩ := ProjectiveSpaceOver.exists_cechFamily_equiv_laurent R N d
  obtain ⟨r⟩ := Stacks01xtAux.exists_leray N R d 0
  let C := cechComplexAlt (ProjectiveSpaceOver.chart N R) (projectiveSpaceOverTwist R N d)
  let L := ((ModuleCat.restrictScalars (baseHom R N)).mapHomologicalComplex (ComplexShape.up ℤ)).obj C
  obtain ⟨E⟩ := ModuleCat.nonempty_linearEquiv_homology_of_restrictScalars_iso (baseHom R N) C L
    (Iso.refl _) ((0 : ℕ) : ℤ) (fun _ _ => rfl) r
  have hz : IsZero (L.X (-1)) :=
    @ModuleCat.isZero_of_subsingleton _ _ (L.X (-1)) (inferInstanceAs (Subsingleton PUnit))
  obtain ⟨a, -, -⟩ := CochainComplex.exists_homologyZero_equiv_ker (𝟙 L) hz hz
  have hd : L.d 0 1 = (ModuleCat.restrictScalars (baseHom R N)).map
      (cechDiffAlt (ProjectiveSpaceOver.chart N R) (projectiveSpaceOverTwist R N d) 0) := by
    rw [Functor.mapHomologicalComplex_obj_d]
    exact congrArg _ (cechComplexAlt_d _ _ 0)
  let G : LinearMap.ker (L.d 0 1).hom →ₗ[R] LinearMap.ker (LaurentCech.δ R N d 0) :=
    ((toLaurentEquiv e hlin 0).toLinearMap.comp (LinearMap.ker (L.d 0 1).hom).subtype).codRestrict _
      (fun x => by
        obtain ⟨y, hy⟩ := x
        have hy' : ((ModuleCat.restrictScalars (baseHom R N)).map
            (cechDiffAlt (ProjectiveSpaceOver.chart N R) (projectiveSpaceOverTwist R N d) 0)).hom y = 0 := by
          rw [← hd]
          exact hy
        have h := toLaurent_d e he hlin 0 y
        rw [hy', map_zero] at h
        exact LinearMap.mem_ker.2 h.symm)
  have hG : Function.Injective G :=
    (LinearMap.injective_codRestrict_iff _).2
      ((toLaurentEquiv e hlin 0).injective.comp (Submodule.injective_subtype _))
  exact ⟨G ∘ₗ a.toLinearMap ∘ₗ E.toLinearMap, hG.comp (a.injective.comp E.injective)⟩

/-- `H^0(P^N_R, O(d))` is a finite `R`-module for `R` Noetherian (`ker δ^0` is finite). -/
theorem finite_zero [IsNoetherianRing R] :
    Module.Finite R (sheafCohomology (ProjectiveSpaceOver N R) (projectiveSpaceOverTwist R N d) 0) := by
  obtain ⟨F, hF⟩ := exists_injective_zero R N d
  have := LaurentCech.finite_ker_δ_zero R N d
  have := isNoetherian_of_isNoetherianRing_of_finite R (LinearMap.ker (LaurentCech.δ R N d 0))
  exact Module.Finite.of_injective F hF

/-- `H^{q+1}(P^N_R, O(d))` is a finite `R`-module (through Leray and the term-wise isomorphisms). -/
theorem finite_succ (q : ℕ) :
    Module.Finite R (sheafCohomology (ProjectiveSpaceOver N R) (projectiveSpaceOverTwist R N d) (q + 1)) := by
  obtain ⟨e, he, hlin⟩ := ProjectiveSpaceOver.exists_cechFamily_equiv_laurent R N d
  obtain ⟨r⟩ := Stacks01xtAux.exists_leray N R d (q + 1)
  let C := cechComplexAlt (ProjectiveSpaceOver.chart N R) (projectiveSpaceOverTwist R N d)
  let L := ((ModuleCat.restrictScalars (baseHom R N)).mapHomologicalComplex (ComplexShape.up ℤ)).obj C
  obtain ⟨E⟩ := ModuleCat.nonempty_linearEquiv_homology_of_restrictScalars_iso (baseHom R N) C L
    (Iso.refl _) (((q + 1 : ℕ)) : ℤ) (fun _ _ => rfl) r
  have hfin : Module.Finite R (L.homology (((q + 1 : ℕ)) : ℤ)) := by
    obtain ⟨h1, -⟩ := TopCx.homology_sc'_fin L ((q : ℕ) : ℤ) (((q + 1 : ℕ)) : ℤ) (((q + 1 + 1 : ℕ)) : ℤ)
      (by push_cast; ring) (by push_cast; ring)
    rw [h1]
    have hd1 : L.d ((q : ℕ) : ℤ) (((q + 1 : ℕ)) : ℤ) = (ModuleCat.restrictScalars (baseHom R N)).map
        (cechDiffAlt (ProjectiveSpaceOver.chart N R) (projectiveSpaceOverTwist R N d) q) := by
      rw [Functor.mapHomologicalComplex_obj_d]
      exact congrArg _ (cechComplexAlt_d _ _ q)
    have hd2 : L.d (((q + 1 : ℕ)) : ℤ) (((q + 1 + 1 : ℕ)) : ℤ) = (ModuleCat.restrictScalars (baseHom R N)).map
        (cechDiffAlt (ProjectiveSpaceOver.chart N R) (projectiveSpaceOverTwist R N d) (q + 1)) := by
      rw [Functor.mapHomologicalComplex_obj_d]
      exact congrArg _ (cechComplexAlt_d _ _ (q + 1))
    rw [hd1, hd2]
    obtain ⟨h2, -⟩ := LinearMap.midHomology_of_equiv (R := R) _ _ (LaurentCech.δ R N d q)
      (LaurentCech.δ R N d (q + 1)) (toLaurentEquiv e hlin q) (toLaurentEquiv e hlin (q + 1))
      (toLaurentEquiv e hlin (q + 1 + 1)) (toLaurent_d e he hlin q) (toLaurent_d e he hlin (q + 1))
    obtain ⟨E3⟩ := LinearMap.nonempty_midHomology_equiv_map_mkQ (LaurentCech.δ R N d q)
      (LaurentCech.δ R N d (q + 1))
    have := LaurentCech.finite_homology_succ R N d q
    exact h2.2 (Module.Finite.equiv E3.symm)
  exact Module.Finite.equiv E.symm

/-- **Stacks 01XT over a Noetherian ring, finiteness**: every `H^q(P^N_R, O(d))` is a finite `R`-module.
Assembled from Leray, the term-wise Laurent isomorphisms and the Laurent–Čech finiteness results. -/
theorem finite_sheafCohomology_twist [IsNoetherianRing R] (q : ℕ) :
    Module.Finite R (sheafCohomology (ProjectiveSpaceOver N R) (projectiveSpaceOverTwist R N d) q) := by
  cases q with
  | zero => exact finite_zero R N d
  | succ q => exact finite_succ R N d q

end Stacks01xtOverRing

end
