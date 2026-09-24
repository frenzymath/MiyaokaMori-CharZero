import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafCohomologyModule
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.SerreTwistProjectiveSpace
import MiyaokaMori.AlgebraicGeometry.Cohomology.Vanishing.Stacks01xb
import MiyaokaMori.AlgebraicGeometry.Cohomology.Cech.CechLeray
import MiyaokaMori.AlgebraicGeometry.Cohomology.ProjectiveSpaceCechLaurent
import MiyaokaMori.AlgebraicGeometry.Cohomology.Cech.LaurentCechCohomology
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpaceOverTwist
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.LocallyFreeQuasicoherent
import MiyaokaMori.Algebra.CochainComplexToTopComplex
import MiyaokaMori.Algebra.RestrictScalarsHomology

/-! # Cohomology of twists on projective space (Stacks 01XT)

Cohomology of the twisting sheaves on projective space (Stacks 01XT, EGA III 2.1.12): every
`H^q(P^N_k, O(d))` is a finite-dimensional `k`-vector space (for `q = 0`, `d ≥ 0` it is the space of
homogeneous polynomials of degree `d`; for `q = N`, `d < 0` it is given by Laurent monomials; otherwise
it vanishes).

Source: Stacks 01XT.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-! ## Assembly

Route (Stacks 01XT, first paragraph; Hartshorne III.5.1): the standard affine cover `U_i = D_+(T_i)` of `P^N_k`
has affine finite intersections (`D_+(∏ T_{σ j})`), `O(d)` is quasi-coherent (a line bundle), so higher
cohomology vanishes on every `U_σ` (Stacks 01XB) and Leray for the alternating Čech complex gives
`H^q(P^N, O(d)) ≃ Ȟ^q_alt(U, O(d))`, `Γ(P^N, O)`-linearly. Under the term-wise isomorphisms `e` of
`ProjectiveSpaceCechLaurent.lean` the alternating Čech complex is the Laurent–Čech complex
`LaurentCech.Cochain k N d`, whose cohomology is computed in `LaurentCechCohomology.lean`:
* vanishing in degree `q + 1` unless `q + 1 = N ∧ d ≤ -N-1`: `ProjectiveSpaceOver.subsingleton_cechComplexAlt_homology_succ`;
* degree `0`, `d < 0`, `N ≥ 1`: `ker δ^0 = S_d = 0`;
* finiteness: `ker δ^0` and `H^{p+1}` are finite `k`-modules; the `k`-structures are matched through
  `ModuleCat.restrictScalars` along `k → Γ(P^N, O)` (the same ring map as `sheafCohomology.moduleOver`),
  `homology_sc'_fin` and `LinearMap.midHomology_of_equiv`.
`N = 0` never reaches the `H^0` computation: the hypotheses of the vanishing theorem force `q ≥ 1` there.
-/

/-- `ker g ⧸ (im f ∩ ker g) ≃ (ker g).map (im f).mkQ` (the two encodings of the middle cohomology). -/
theorem LinearMap.nonempty_midHomology_equiv_map_mkQ {R : Type u} [CommRing R] {U V W : Type v}
    [AddCommGroup U] [AddCommGroup V] [AddCommGroup W] [Module R U] [Module R V] [Module R W]
    (f : U →ₗ[R] V) (g : V →ₗ[R] W) :
    Nonempty (LinearMap.midHomology f g ≃ₗ[R] (LinearMap.ker g).map (LinearMap.range f).mkQ) := by
  let h : LinearMap.ker g →ₗ[R] V ⧸ LinearMap.range f :=
    (LinearMap.range f).mkQ ∘ₗ (LinearMap.ker g).subtype
  have hker : LinearMap.ker h = (LinearMap.range f).submoduleOf (LinearMap.ker g) := by
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
    rfl
  have hrange : LinearMap.range h = (LinearMap.ker g).map (LinearMap.range f).mkQ := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  exact ⟨((Submodule.quotEquivOfEq _ _ hker.symm).trans h.quotKerEquivRange).trans
    (LinearEquiv.ofEq _ _ hrange)⟩


namespace Stacks01xtAux

open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

attribute [local instance] MvPolynomial.gradedAlgebra

section StandardCover

variable {σ A : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- `D_+(∏_{i ∈ s} f_i) = ⋂_{i ∈ s} D_+(f_i)` (Mathlib `Proj.basicOpen_mul`, `Proj.basicOpen_one`). -/
theorem proj_basicOpen_finset_prod {ι : Type*} (s : Finset ι) (f : ι → A) :
    Proj.basicOpen 𝒜 (∏ i ∈ s, f i) = s.inf (fun i => Proj.basicOpen 𝒜 (f i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Proj.basicOpen_one]
  | insert a s ha ih => rw [Finset.prod_insert ha, Proj.basicOpen_mul, ih, Finset.inf_insert]

end StandardCover

variable (N : ℕ) (R : Type u) [CommRing R]

/-- `⋂_j D_+(T_{τ j}) = D_+(∏_j T_{τ j})`. -/
theorem iInf_chart_eq {p : ℕ} (τ : Fin (p + 1) ↪o Fin (N + 1)) :
    (⨅ j, ProjectiveSpaceOver.chart N R (τ j)) =
      Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (∏ j, MvPolynomial.X (τ j)) := by
  rw [proj_basicOpen_finset_prod, Finset.inf_univ_eq_iInf]
  rfl

/-- Finite intersections of the standard charts are affine (`∏_j T_{τ j}` is homogeneous of degree `p + 1 > 0`). -/
theorem isAffineOpen_iInf_chart {p : ℕ} (τ : Fin (p + 1) ↪o Fin (N + 1)) :
    IsAffineOpen (⨅ j, ProjectiveSpaceOver.chart N R (τ j)) := by
  rw [iInf_chart_eq]
  refine Proj.isAffineOpen_basicOpen _ _ (m := p + 1) ?_ (Nat.succ_pos p)
  rw [MvPolynomial.mem_homogeneousSubmodule]
  have h := MvPolynomial.IsHomogeneous.prod Finset.univ
    (fun j : Fin (p + 1) => (MvPolynomial.X (τ j) : MvPolynomial (Fin (N + 1)) R)) (fun _ => 1)
    (fun j _ => MvPolynomial.isHomogeneous_X R (τ j))
  simpa using h

/-- `O(d)` is quasi-coherent (it is a line bundle: `projectiveSpaceOverTwist_isLineBundle`). -/
theorem twist_isQuasicoherent (d : ℤ) : (projectiveSpaceOverTwist R N d).IsQuasicoherent :=
  IsLineBundle.isQuasicoherent _

/-- Higher cohomology of `O(d)` vanishes on every finite intersection of charts (Stacks 01XB). -/
theorem hPrime_vanishing (d : ℤ) (q : ℕ) (τ : Fin (q + 1) ↪o Fin (N + 1)) (p : ℕ) (hp : 0 < p) :
    Subsingleton ((projectiveSpaceOverTwist R N d).toAddCommGrpSheaf.H' p
      (⨅ j, ProjectiveSpaceOver.chart N R (τ j))) := by
  have := twist_isQuasicoherent N R d
  exact sheafCohomology'_affineOpen_vanishing _ (isAffineOpen_iInf_chart N R τ) p hp

/-- Leray: `H^q(P^N_R, O(d)) ≃ Ȟ^q_alt(standard cover, O(d))`, `Γ(P^N_R, O)`-linearly. -/
theorem exists_leray (d : ℤ) (q : ℕ) :
    Nonempty (sheafCohomology (ProjectiveSpaceOver N R) (projectiveSpaceOverTwist R N d) q
      ≃ₗ[Γ(ProjectiveSpaceOver N R, ⊤)]
      ((cechComplexAlt (ProjectiveSpaceOver.chart N R) (projectiveSpaceOverTwist R N d)).homology
        ((q : ℕ) : ℤ))) :=
  sheafCohomology_equiv_cechAlt_homology (ProjectiveSpaceOver.chart N R) (ProjectiveSpaceOver.iSup_chart N R)
    q _ (fun q τ p hp => hPrime_vanishing N R d q τ p hp)

section Field

variable (k : Type u) [Field k] (N : ℕ) (d : ℤ)

/-- The ring map `k → Γ(P^N_k, O)` through which `k` acts on everything (the one in `sheafCohomology.moduleOver`). -/
def baseHom : k →+* Γ(ProjectiveSpaceOver N k, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
    (ProjectiveSpaceOver N k ↘ Spec (CommRingCat.of k)).appTop).hom

theorem scalar_eq (V : (ProjectiveSpaceOver N k).Opens) (r : k) :
    ProjectiveSpaceOver.scalar N k V r =
      ((ProjectiveSpaceOver N k).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom (baseHom k N r) := rfl

/-- The term-wise isomorphisms between the Čech terms of `O(d)` and the Laurent–Čech terms. -/
abbrev TermEquiv : Type u := ∀ (p : ℕ) (σ : Fin (p + 1) ↪o Fin (N + 1)),
  Γ(projectiveSpaceOverTwist k N d, ⨅ j, ProjectiveSpaceOver.chart N k (σ j)) ≃+
    LaurentCech.Term k N d (LaurentCech.V N p σ)

variable {k N d}

/-- Compatibility with the Čech face restrictions. -/
abbrev FaceCompat (e : TermEquiv k N d) : Prop :=
  ∀ (p : ℕ) (τ : Fin (p + 2) ↪o Fin (N + 1)) (k' : Fin (p + 2))
    (x : Γ(projectiveSpaceOverTwist k N d, ⨅ j, ProjectiveSpaceOver.chart N k ((CechAltAlg.face τ k') j))),
    e (p + 1) τ ((projectiveSpaceOverTwist k N d).presheaf.map
      (homOfLE (cech_face_le (ProjectiveSpaceOver.chart N k) τ k')).op x) =
      LaurentCech.res d (LaurentCech.hface N p τ k') (e p (CechAltAlg.face τ k') x)

/-- `k`-linearity. -/
abbrev ScalarCompat (e : TermEquiv k N d) : Prop :=
  ∀ (p : ℕ) (σ : Fin (p + 1) ↪o Fin (N + 1)) (r : k)
    (x : Γ(projectiveSpaceOverTwist k N d, ⨅ j, ProjectiveSpaceOver.chart N k (σ j))),
    e p σ (ProjectiveSpaceOver.scalar N k (⨅ j, ProjectiveSpaceOver.chart N k (σ j)) r • x) = r • e p σ x

variable (k N d) in
/-- The `p`-th alternating Čech term of `O(d)` on the standard cover, as a `k`-module along `baseHom`. -/
abbrev CechTermK (p : ℕ) : Type u :=
  ((ModuleCat.restrictScalars (baseHom k N)).obj
    (cechTermAlt (ProjectiveSpaceOver.chart N k) (projectiveSpaceOverTwist k N d) p))

variable (k N d) in
/-- The family of Čech terms `σ ↦ Γ(O(d), U_σ)` (as `Γ(P^N, O)`-modules) whose product is `cechTermAlt`. -/
abbrev Fam (p : ℕ) : (Fin (p + 1) ↪o Fin (N + 1)) → ModuleCat.{u} Γ(ProjectiveSpaceOver N k, ⊤) :=
  fun σ => (projectiveSpaceOverTwist k N d).sectionsOverTop (⨅ j, ProjectiveSpaceOver.chart N k (σ j))

/-- `C^p_alt(U, O(d)) → LaurentCech.Cochain k N d p`, `x ↦ (σ ↦ e p σ (x_σ))`, `k`-linear for the
`k`-structure restricted along `baseHom`. -/
def toLaurent (e : TermEquiv k N d) (hlin : ScalarCompat e) (p : ℕ) :
    CechTermK k N d p →ₗ[k] LaurentCech.Cochain k N d p where
  toFun x := fun σ => e p σ (cechToFamily (ProjectiveSpaceOver.chart N k) (projectiveSpaceOverTwist k N d) p x σ)
  map_add' x y := by
    funext σ
    exact (congrArg (e p σ) (map_add (Pi.π (Fam k N d p) σ).hom x y)).trans (map_add (e p σ) _ _)
  map_smul' r x := by
    funext σ
    exact (congrArg (e p σ) (_root_.map_smul (Pi.π (Fam k N d p) σ).hom (baseHom k N r) x)).trans
      (hlin p σ r _)

theorem toLaurent_apply (e : TermEquiv k N d) (hlin : ScalarCompat e) (p : ℕ) (x : CechTermK k N d p)
    (σ : Fin (p + 1) ↪o Fin (N + 1)) :
    toLaurent e hlin p x σ =
      e p σ (cechToFamily (ProjectiveSpaceOver.chart N k) (projectiveSpaceOverTwist k N d) p x σ) := rfl

theorem toLaurent_bijective (e : TermEquiv k N d) (hlin : ScalarCompat e) (p : ℕ) :
    Function.Bijective (toLaurent e hlin p) := by
  constructor
  · intro x y hxy
    apply (cechToFamily_bijective (ProjectiveSpaceOver.chart N k) (projectiveSpaceOverTwist k N d) p).1
    funext σ
    exact (e p σ).injective (congrFun hxy σ)
  · intro s
    obtain ⟨x, hx⟩ := (cechToFamily_bijective (ProjectiveSpaceOver.chart N k)
      (projectiveSpaceOverTwist k N d) p).2 (fun σ => (e p σ).symm (s σ))
    refine ⟨x, ?_⟩
    funext σ
    show e p σ (cechToFamily (ProjectiveSpaceOver.chart N k) (projectiveSpaceOverTwist k N d) p x σ) = s σ
    rw [hx]
    exact (e p σ).apply_symm_apply _

/-- The `k`-linear isomorphism `C^p_alt(U, O(d)) ≃ LaurentCech.Cochain k N d p`. -/
def toLaurentEquiv (e : TermEquiv k N d) (hlin : ScalarCompat e) (p : ℕ) :
    CechTermK k N d p ≃ₗ[k] LaurentCech.Cochain k N d p :=
  LinearEquiv.ofBijective _ (toLaurent_bijective e hlin p)

/-- Compatibility with the differentials (face compatibility + `cechFamilyD_eq_δ`). -/
theorem toLaurent_d (e : TermEquiv k N d) (he : FaceCompat e) (hlin : ScalarCompat e) (p : ℕ)
    (x : CechTermK k N d p) :
    toLaurentEquiv e hlin (p + 1) (((ModuleCat.restrictScalars (baseHom k N)).map
        (cechDiffAlt (ProjectiveSpaceOver.chart N k) (projectiveSpaceOverTwist k N d) p)).hom x) =
      LaurentCech.δ k N d p (toLaurentEquiv e hlin p x) := by
  have h1 := cechToFamily_diff (ProjectiveSpaceOver.chart N k) (projectiveSpaceOverTwist k N d) p x
  have h2 := ProjectiveSpaceOver.cechFamilyD_eq_δ k N d e he p
    (cechToFamily (ProjectiveSpaceOver.chart N k) (projectiveSpaceOverTwist k N d) p x)
  show (fun τ => e (p + 1) τ (cechToFamily (ProjectiveSpaceOver.chart N k) (projectiveSpaceOverTwist k N d) (p + 1)
    ((cechDiffAlt (ProjectiveSpaceOver.chart N k) (projectiveSpaceOverTwist k N d) p).hom x) τ)) =
    LaurentCech.δ k N d p
      (fun σ => e p σ (cechToFamily (ProjectiveSpaceOver.chart N k) (projectiveSpaceOverTwist k N d) p x σ))
  rw [h1]
  exact h2

variable (k N d)

/-- `H^0(P^N_k, O(d))` embeds `k`-linearly into `ker δ^0` of the Laurent–Čech complex. -/
theorem exists_injective_zero :
    ∃ F : sheafCohomology (ProjectiveSpaceOver N k) (projectiveSpaceOverTwist k N d) 0 →ₗ[k]
      LinearMap.ker (LaurentCech.δ k N d 0), Function.Injective F := by
  obtain ⟨e, he, hlin⟩ := ProjectiveSpaceOver.exists_cechFamily_equiv_laurent k N d
  obtain ⟨r⟩ := exists_leray N k d 0
  let C := cechComplexAlt (ProjectiveSpaceOver.chart N k) (projectiveSpaceOverTwist k N d)
  let L := ((ModuleCat.restrictScalars (baseHom k N)).mapHomologicalComplex (ComplexShape.up ℤ)).obj C
  obtain ⟨E⟩ := ModuleCat.nonempty_linearEquiv_homology_of_restrictScalars_iso (baseHom k N) C L
    (Iso.refl _) ((0 : ℕ) : ℤ) (fun _ _ => rfl) r
  have hz : IsZero (L.X (-1)) :=
    @ModuleCat.isZero_of_subsingleton _ _ (L.X (-1)) (inferInstanceAs (Subsingleton PUnit))
  obtain ⟨a, -, -⟩ := CochainComplex.exists_homologyZero_equiv_ker (𝟙 L) hz hz
  have hd : L.d 0 1 = (ModuleCat.restrictScalars (baseHom k N)).map
      (cechDiffAlt (ProjectiveSpaceOver.chart N k) (projectiveSpaceOverTwist k N d) 0) := by
    rw [Functor.mapHomologicalComplex_obj_d]
    exact congrArg _ (cechComplexAlt_d _ _ 0)
  let G : LinearMap.ker (L.d 0 1).hom →ₗ[k] LinearMap.ker (LaurentCech.δ k N d 0) :=
    ((toLaurentEquiv e hlin 0).toLinearMap.comp (LinearMap.ker (L.d 0 1).hom).subtype).codRestrict _
      (fun x => by
        obtain ⟨y, hy⟩ := x
        have hy' : ((ModuleCat.restrictScalars (baseHom k N)).map
            (cechDiffAlt (ProjectiveSpaceOver.chart N k) (projectiveSpaceOverTwist k N d) 0)).hom y = 0 := by
          rw [← hd]
          exact hy
        have h := toLaurent_d e he hlin 0 y
        rw [hy', map_zero] at h
        exact LinearMap.mem_ker.2 h.symm)
  have hG : Function.Injective G :=
    (LinearMap.injective_codRestrict_iff _).2
      ((toLaurentEquiv e hlin 0).injective.comp (Submodule.injective_subtype _))
  exact ⟨G ∘ₗ a.toLinearMap ∘ₗ E.toLinearMap, hG.comp (a.injective.comp E.injective)⟩

/-- `H^0(P^N_k, O(d))` is finite-dimensional (`ker δ^0` is finite). -/
theorem finite_zero :
    Module.Finite k (sheafCohomology (ProjectiveSpaceOver N k) (projectiveSpaceOverTwist k N d) 0) := by
  obtain ⟨F, hF⟩ := exists_injective_zero k N d
  have := LaurentCech.finite_ker_δ_zero k N d
  have := isNoetherian_of_isNoetherianRing_of_finite k (LinearMap.ker (LaurentCech.δ k N d 0))
  exact Module.Finite.of_injective F hF

/-- `H^0(P^N_k, O(d)) = 0` for `d < 0`, `N ≥ 1` (`ker δ^0 = S_d`, and `S_d = 0` for `d < 0`). -/
theorem subsingleton_zero (hd : d < 0) (hN : 1 ≤ N) :
    Subsingleton (sheafCohomology (ProjectiveSpaceOver N k) (projectiveSpaceOverTwist k N d) 0) := by
  obtain ⟨F, hF⟩ := exists_injective_zero k N d
  have hker : Subsingleton (LinearMap.ker (LaurentCech.δ k N d 0)) := by
    have key : ∀ s : LinearMap.ker (LaurentCech.δ k N d 0), s = 0 := by
      intro s
      obtain ⟨a, ha, hs⟩ := (LaurentCech.δ_zero_eq_zero_iff k N hN d s.1).1 s.2
      have hpoly : LaurentCech.polyPiece k N d = ⊥ := by
        rw [LaurentCech.polyPiece, if_neg (not_le.mpr hd)]
      rw [hpoly, Submodule.mem_bot] at ha
      apply Subtype.ext
      funext σ
      apply Subtype.ext
      rw [hs σ, ha, map_zero]
      rfl
    exact ⟨fun s t => (key s).trans (key t).symm⟩
  exact hF.subsingleton

/-- `H^{q+1}(P^N_k, O(d))` is finite-dimensional (through Leray and the term-wise isomorphisms). -/
theorem finite_succ (q : ℕ) :
    Module.Finite k (sheafCohomology (ProjectiveSpaceOver N k) (projectiveSpaceOverTwist k N d) (q + 1)) := by
  obtain ⟨e, he, hlin⟩ := ProjectiveSpaceOver.exists_cechFamily_equiv_laurent k N d
  obtain ⟨r⟩ := exists_leray N k d (q + 1)
  let C := cechComplexAlt (ProjectiveSpaceOver.chart N k) (projectiveSpaceOverTwist k N d)
  let L := ((ModuleCat.restrictScalars (baseHom k N)).mapHomologicalComplex (ComplexShape.up ℤ)).obj C
  obtain ⟨E⟩ := ModuleCat.nonempty_linearEquiv_homology_of_restrictScalars_iso (baseHom k N) C L
    (Iso.refl _) (((q + 1 : ℕ)) : ℤ) (fun _ _ => rfl) r
  have hfin : Module.Finite k (L.homology (((q + 1 : ℕ)) : ℤ)) := by
    obtain ⟨h1, -⟩ := TopCx.homology_sc'_fin L ((q : ℕ) : ℤ) (((q + 1 : ℕ)) : ℤ) (((q + 1 + 1 : ℕ)) : ℤ)
      (by push_cast; ring) (by push_cast; ring)
    rw [h1]
    have hd1 : L.d ((q : ℕ) : ℤ) (((q + 1 : ℕ)) : ℤ) = (ModuleCat.restrictScalars (baseHom k N)).map
        (cechDiffAlt (ProjectiveSpaceOver.chart N k) (projectiveSpaceOverTwist k N d) q) := by
      rw [Functor.mapHomologicalComplex_obj_d]
      exact congrArg _ (cechComplexAlt_d _ _ q)
    have hd2 : L.d (((q + 1 : ℕ)) : ℤ) (((q + 1 + 1 : ℕ)) : ℤ) = (ModuleCat.restrictScalars (baseHom k N)).map
        (cechDiffAlt (ProjectiveSpaceOver.chart N k) (projectiveSpaceOverTwist k N d) (q + 1)) := by
      rw [Functor.mapHomologicalComplex_obj_d]
      exact congrArg _ (cechComplexAlt_d _ _ (q + 1))
    rw [hd1, hd2]
    obtain ⟨h2, -⟩ := LinearMap.midHomology_of_equiv (R := k) _ _ (LaurentCech.δ k N d q)
      (LaurentCech.δ k N d (q + 1)) (toLaurentEquiv e hlin q) (toLaurentEquiv e hlin (q + 1))
      (toLaurentEquiv e hlin (q + 1 + 1)) (toLaurent_d e he hlin q) (toLaurent_d e he hlin (q + 1))
    obtain ⟨E3⟩ := LinearMap.nonempty_midHomology_equiv_map_mkQ (LaurentCech.δ k N d q)
      (LaurentCech.δ k N d (q + 1))
    have := LaurentCech.finite_homology_succ k N d q
    exact h2.2 (Module.Finite.equiv E3.symm)
  exact Module.Finite.equiv E.symm

end Field

end Stacks01xtAux


/-- Stacks 01XT, finiteness: every `H^q(P^N_k, O(d))` is a finite-dimensional `k`-vector space.
Assembled from Leray, the term-wise Laurent isomorphisms and the Laurent–Čech computation (see above). -/
theorem finiteDimensional_sheafCohomology_projectiveSpaceTwist {k : Type u} [Field k] (N : ℕ) (d : ℤ) (q : ℕ) :
    FiniteDimensional k (AlgebraicGeometry.sheafCohomology (ProjectiveSpace N k) (projectiveSpaceTwist k N d) q) := by
  cases q with
  | zero => exact Stacks01xtAux.finite_zero k N d
  | succ q => exact Stacks01xtAux.finite_succ k N d q

/-- Stacks 01XT, vanishing: `H^q(P^N, O(d))` is nonzero only for `q = 0`, `d ≥ 0` (homogeneous
polynomials of degree `d`) and `q = N`, `d ≤ −N−1` (the degree-`d` part of the Laurent monomials
`1/(T_0⋯T_N)·k[1/T_i]`, empty for `d > −N−1`); it vanishes in all other cases. -/

theorem subsingleton_sheafCohomology_projectiveSpaceTwist {k : Type u} [Field k] (N : ℕ) (d : ℤ) (q : ℕ)
    (h0 : ¬ (q = 0 ∧ 0 ≤ d)) (hN : ¬ (q = N ∧ d ≤ -((N : ℤ) + 1))) :
    Subsingleton (AlgebraicGeometry.sheafCohomology (ProjectiveSpace N k) (projectiveSpaceTwist k N d) q) := by
  cases q with
  | zero =>
    have hd : d < 0 := by
      by_contra h
      exact h0 ⟨rfl, not_lt.1 h⟩
    have hN1 : 1 ≤ N := by
      by_contra h
      have hN0 : N = 0 := by omega
      subst hN0
      exact hN ⟨rfl, by omega⟩
    exact Stacks01xtAux.subsingleton_zero k N d hd hN1
  | succ q =>
    obtain ⟨r⟩ := Stacks01xtAux.exists_leray N k d (q + 1)
    have := ProjectiveSpaceOver.subsingleton_cechComplexAlt_homology_succ k N d q hN
    exact r.toEquiv.subsingleton

end
