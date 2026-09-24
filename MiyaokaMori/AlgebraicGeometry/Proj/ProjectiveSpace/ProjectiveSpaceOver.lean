import MiyaokaMori.Prelude

/-! # Projective space over a commutative ring

The `N`-dimensional projective space `P^N_R := Proj R[T₀, …, T_N]` over a commutative ring `R`
(standard total-degree grading), its structure morphism `P^N_R → Spec R`, the `Over` instance, the
isomorphism `R ≃+* (R[T])₀`, and the properness of the structure morphism.

This is the one definition of `P^N`: the versions over a field, `ProjectiveSpace N k` and
`ProjectiveSpace.toSpecBase N k`, are `abbrev`s of the two definitions here at `R := k`, and the
`Over` instance over a field is `ProjectiveSpaceOver.over N k`.

Source: Stacks 01ND (Constructions, Definition 27.13.2: `P^n_R = Proj R[T₀, …, T_n]`); properness
Stacks 01NE / 01WC.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The `N`-dimensional projective space `P^N_R = Proj R[T₀,…,T_N]` over a commutative ring `R`
(Stacks 01ND). Over the zero ring it is the empty scheme; for `N = 0` it is isomorphic to `Spec R`.
Over a field, `ProjectiveSpace N k` is an `abbrev` of this definition at `R := k`. -/
noncomputable def ProjectiveSpaceOver (N : ℕ) (R : Type u) [CommRing R] : AlgebraicGeometry.Scheme.{u} :=
  AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)

/-- `R ≃+* (R[x_σ])₀`: the degree-zero homogeneous part consists exactly of the constants. -/
noncomputable def MvPolynomial.homogeneousSubmoduleZeroRingEquiv (σ : Type*) (R : Type*) [CommRing R] :
    (MvPolynomial.homogeneousSubmodule σ R 0) ≃+* R :=
  (RingEquiv.ofBijective (algebraMap R (MvPolynomial.homogeneousSubmodule σ R 0))
    ⟨fun a b h => MvPolynomial.C_injective σ R (congrArg Subtype.val h),
     fun p => by
      obtain ⟨p, hp⟩ := p
      have hp' : p ∈ (1 : Submodule R (MvPolynomial σ R)) := by
        rwa [← MvPolynomial.homogeneousSubmodule_zero]
      obtain ⟨r, hr⟩ := Submodule.mem_one.1 hp'
      exact ⟨r, Subtype.ext hr⟩⟩).symm

/-- The structure morphism `P^N_R → Spec R`: Mathlib's `Proj.toSpecZero` (with target `Spec 𝒜₀`)
followed by `Spec (R → 𝒜₀)`. -/
noncomputable def ProjectiveSpaceOver.toSpecBase (N : ℕ) (R : Type u) [CommRing R] :
    ProjectiveSpaceOver N R ⟶ AlgebraicGeometry.Spec (CommRingCat.of R) :=
  AlgebraicGeometry.Proj.toSpecZero (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) ≫
    AlgebraicGeometry.Spec.map (CommRingCat.ofHom
      (algebraMap R (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R 0)))

/-- `P^N_R` as a scheme over `Spec R`. Over a field `ProjectiveSpace N k` is an `abbrev` of
`ProjectiveSpaceOver N k`, so this is also the (unique) instance of `(ProjectiveSpace N k).Over (Spec k)`. -/
noncomputable instance ProjectiveSpaceOver.over (N : ℕ) (R : Type u) [CommRing R] :
    (ProjectiveSpaceOver N R).Over (AlgebraicGeometry.Spec (CommRingCat.of R)) :=
  ⟨ProjectiveSpaceOver.toSpecBase N R⟩

theorem ProjectiveSpaceOver.over_hom (N : ℕ) (R : Type u) [CommRing R] :
    (ProjectiveSpaceOver N R ↘ AlgebraicGeometry.Spec (CommRingCat.of R)) =
      ProjectiveSpaceOver.toSpecBase N R := rfl

/-! ## Properness of the structure morphism (Stacks 01NE; properness of Mathlib's `Proj.toSpecZero`
together with `R ≃ 𝒜₀`) -/

/-- `R → (R[T₀..T_N])₀` is bijective (the constants are exactly the degree-zero homogeneous part).
This holds for every commutative ring, including the zero ring. -/
theorem ProjectiveSpaceOver.algebraMap_zero_bijective (N : ℕ) (R : Type u) [CommRing R] :
    Function.Bijective (algebraMap R (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R 0)) :=
  (MvPolynomial.homogeneousSubmoduleZeroRingEquiv (Fin (N + 1)) R).symm.bijective

/-- The structure morphism `P^N_R → Spec R` is proper. Stated as a `theorem` rather than a global
`instance`; use `haveI := …` when needed. The global instance `ProjectiveSpace.isProper_toSpecBase`
over a field is its value at `R := k`. -/
theorem ProjectiveSpaceOver.isProper_toSpecBase (N : ℕ) (R : Type u) [CommRing R] :
    AlgebraicGeometry.IsProper
      (ProjectiveSpaceOver N R ↘ AlgebraicGeometry.Spec (CommRingCat.of R)) := by
  have : IsScalarTower R (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R 0)
      (MvPolynomial (Fin (N + 1)) R) :=
    IsScalarTower.of_algebraMap_eq (R := R)
      (S := MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R 0)
      (A := MvPolynomial (Fin (N + 1)) R) fun _ ↦ rfl
  have : Algebra.FiniteType (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R 0)
      (MvPolynomial (Fin (N + 1)) R) :=
    Algebra.FiniteType.of_restrictScalars_finiteType R
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R 0) _
  have : IsIso (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
      (algebraMap R (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R 0)))) :=
    AlgebraicGeometry.isIso_SpecMap_iff.mpr (ProjectiveSpaceOver.algebraMap_zero_bijective N R)
  change AlgebraicGeometry.IsProper
    (AlgebraicGeometry.Proj.toSpecZero (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) ≫ _)
  infer_instance

/-- The standard open subsets `D₊(T_i)` (`i = 0..N`), the affine open cover used for the alternating
Čech complex. -/
noncomputable def ProjectiveSpaceOver.chart (N : ℕ) (R : Type u) [CommRing R] (i : Fin (N + 1)) :
    (ProjectiveSpaceOver N R).Opens :=
  AlgebraicGeometry.Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
    (MvPolynomial.X i)

/-- The `D₊(T_i)` cover `P^N_R` (the `T_i` generate `R[T]` over `𝒜₀ = R`). -/
theorem ProjectiveSpaceOver.iSup_chart (N : ℕ) (R : Type u) [CommRing R] :
    ⨆ i : Fin (N + 1), ProjectiveSpaceOver.chart N R i = ⊤ := by
  apply AlgebraicGeometry.Proj.iSup_basicOpen_eq_top'
  · exact fun i ↦ ⟨1, MvPolynomial.isHomogeneous_X R i⟩
  · apply top_unique
    intro p hp
    clear hp
    induction p using MvPolynomial.induction_on with
    | C r =>
      exact (Algebra.adjoin (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R 0)
        (Set.range (MvPolynomial.X : Fin (N + 1) → MvPolynomial (Fin (N + 1)) R))).algebraMap_mem
          ⟨MvPolynomial.C r, MvPolynomial.isHomogeneous_C (Fin (N + 1)) r⟩
    | add p q hp hq => exact Subalgebra.add_mem _ hp hq
    | mul_X p i hp =>
      exact Subalgebra.mul_mem _ hp (Algebra.subset_adjoin (Set.mem_range_self i))

/-- `D₊(T_i)` is an affine open (Mathlib `Proj.isAffineOpen_basicOpen`). -/
theorem ProjectiveSpaceOver.isAffineOpen_chart (N : ℕ) (R : Type u) [CommRing R] (i : Fin (N + 1)) :
    AlgebraicGeometry.IsAffineOpen (ProjectiveSpaceOver.chart N R i) :=
  AlgebraicGeometry.Proj.isAffineOpen_basicOpen
    (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i)
    ((MvPolynomial.mem_homogeneousSubmodule 1 _).mpr (MvPolynomial.isHomogeneous_X R i)) (by decide)

end
