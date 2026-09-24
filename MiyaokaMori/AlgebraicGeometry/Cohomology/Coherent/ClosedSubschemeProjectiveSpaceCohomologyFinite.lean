import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpaceOver
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.CoherentSheaf
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafCohomologyModule
import MiyaokaMori.AlgebraicGeometry.Cohomology.Coherent.ProjectiveSpaceCohomologyFiniteNoetherianRing
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.Stacks01y6
import MiyaokaMori.AlgebraicGeometry.Cohomology.Pushforward.SheafCohomologyClosedImmersionFiniteOver

/-! # Finiteness of cohomology for closed subschemes of projective space

Stacks 0B5T(3) / Hartshorne III.5.2(a) for closed subschemes of projective space over a Noetherian ring:
`R` Noetherian, `j : Z → P^n_R` a closed immersion, `F` coherent on `Z` ⇒ every `H^i(Z, F)` is a finite
`R`-module. This is the "affine case" of Stacks 02O4, to which 02O4 reduces.

Assembled from
* Stacks 01Y6 (`isCoherent_pushforward_of_isFinite`): `j_*F` is coherent on the locally Noetherian
  `P^n_R` (closed immersions are finite, Mathlib instance);
* Stacks 02UV: `H^i(Z, F) ≃ H^i(P^n_R, j_*F)`, `R`-linearly (the `R`-structures are
  `sheafCohomology.moduleOver` for `Z → P^n_R → Spec R` and `P^n_R → Spec R`); here we need the
  direction "finite on `P^n_R` ⇒ finite on `Z`",
  `finite_sheafCohomology_of_finite_pushforward_of_isClosedImmersion` below;
* Stacks 01YS(3) over a Noetherian ring (`ProjectiveSpaceCohomologyFiniteNoetherianRing.lean`);
* `P^n_R := ProjectiveSpaceOver n R` is locally Noetherian (`ProjectiveSpaceOver.isLocallyNoetherian`
  below: `R[T]_0 = R` (`ProjectiveSpaceOver.algebraMap_zero_bijective`) is Noetherian and `R[T]` is of
  finite type over it, so `Proj.toSpecZero` is of finite type over a Noetherian scheme).

Source: Stacks 0B5T (coherent-lemma-coherent-proper-ample) part (3), proof; Stacks 02O4, proof;
Hartshorne III.5.2(a).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

namespace AlgebraicGeometry

/-- `K`-finiteness of cohomology *ascends* along a closed immersion of `K`-schemes (the converse of
`finite_sheafCohomology_pushforward_of_isClosedImmersion`): `H^p(X, i_*M)` finite ⇒ `H^p(Z, M)` finite.
Proof: the 02UV isomorphism `sheafCohomologyClosedImmersionAddEquivOver` is `K`-linear
(`sheafCohomologyClosedImmersionAddEquivOver_smul`), so its inverse is a `K`-linear equivalence and
`Module.Finite.equiv` applies. -/
theorem Scheme.Modules.finite_sheafCohomology_of_finite_pushforward_of_isClosedImmersion
    {K : Type u} [CommRing K] {Z X : Scheme.{u}} [Z.Over (Spec (CommRingCat.of K))]
    [X.Over (Spec (CommRingCat.of K))] (i : Z ⟶ X) [IsClosedImmersion i]
    [i.IsOver (Spec (CommRingCat.of K))] (M : Z.Modules) (p : ℕ)
    [Module.Finite K (sheafCohomology X ((Scheme.Modules.pushforward i).obj M) p)] :
    Module.Finite K (sheafCohomology Z M p) :=
  let e : sheafCohomology Z M p ≃ₗ[K] sheafCohomology X ((Scheme.Modules.pushforward i).obj M) p :=
    { Scheme.Modules.sheafCohomologyClosedImmersionAddEquivOver i M p with
      map_smul' := Scheme.Modules.sheafCohomologyClosedImmersionAddEquivOver_smul i M p }
  Module.Finite.equiv e.symm

/-- `R[T]_0` is Noetherian when `R` is (`R → R[T]_0` is bijective, `ProjectiveSpaceOver.algebraMap_zero_bijective`). Not a global instance. -/
theorem _root_.ProjectiveSpaceOver.isNoetherianRing_zero (n : ℕ) (R : Type u) [CommRing R]
    [IsNoetherianRing R] : IsNoetherianRing (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R 0) :=
  isNoetherianRing_of_surjective R _ (algebraMap R (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R 0))
    (ProjectiveSpaceOver.algebraMap_zero_bijective n R).surjective

/-- `R → R[T]_0 → R[T]` is a scalar tower (both structure maps are the inclusion of constants).
Not a global instance; same proof as inside `ProjectiveSpaceOver.isProper_toSpecBase`. -/
theorem _root_.ProjectiveSpaceOver.isScalarTower_zero (n : ℕ) (R : Type u) [CommRing R] :
    IsScalarTower R (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R 0) (MvPolynomial (Fin (n + 1)) R) :=
  IsScalarTower.of_algebraMap_eq (S := MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R 0) fun _ => rfl

/-- `R[T_0, …, T_n]` is of finite type over its degree-zero part (it is of finite type over `R`, and
`R → R[T]_0 → R[T]` is a scalar tower). Not a global instance. -/
theorem _root_.ProjectiveSpaceOver.finiteType_zero (n : ℕ) (R : Type u) [CommRing R] :
    Algebra.FiniteType (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R 0) (MvPolynomial (Fin (n + 1)) R) :=
  haveI := ProjectiveSpaceOver.isScalarTower_zero n R
  Algebra.FiniteType.of_restrictScalars_finiteType R (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R 0)
    (MvPolynomial (Fin (n + 1)) R)

/-- `P^n_R` is locally Noetherian for `R` Noetherian (Stacks 01YS, proof, first line; Stacks 01T6):
`Proj.toSpecZero : P^n_R → Spec R[T]_0` is locally of finite type (Mathlib, `R[T]` of finite type over
`R[T]_0`) and `Spec R[T]_0` is Noetherian. Not a global instance. -/
theorem _root_.ProjectiveSpaceOver.isLocallyNoetherian (n : ℕ) (R : Type u) [CommRing R]
    [IsNoetherianRing R] : IsLocallyNoetherian (ProjectiveSpaceOver n R) := by
  have := ProjectiveSpaceOver.finiteType_zero n R
  have := ProjectiveSpaceOver.isNoetherianRing_zero n R
  -- the two instances are synthesised on fully elaborated types and passed explicitly
  -- (implicit synthesis inside `exact` fails here because the universe of `Proj.toSpecZero` is not yet fixed)
  have hLFT : LocallyOfFiniteType
      (Proj.toSpecZero (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)) := by infer_instance
  have hN : IsLocallyNoetherian
      (Spec (CommRingCat.of (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R 0))) := by infer_instance
  exact @LocallyOfFiniteType.isLocallyNoetherian _ _
    (Proj.toSpecZero (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)) hLFT hN

/-- **Finiteness of cohomology for closed subschemes of projective space** (Stacks 0B5T(3), Hartshorne
III.5.2(a)): `R` Noetherian, `j : Z → P^n_R` a closed immersion, `F` coherent on `Z` ⇒ `H^i(Z, F)` is a
finite `R`-module, for the `R`-structure `sheafCohomology.moduleOver` given by
`Z → P^n_R → Spec R` (`letI : Z.Over (Spec R) := ⟨j ≫ ProjectiveSpaceOver.toSpecBase n R⟩`).

Proof: `P^n_R` is locally Noetherian (`ProjectiveSpaceOver.isLocallyNoetherian`),
so `j_*F` is coherent (Stacks 01Y6, `isCoherent_pushforward_of_isFinite`; closed immersions are finite);
`H^i(P^n_R, j_*F)` is finite over `R` (Stacks 01YS(3) over `R`,
`finite_sheafCohomology_projectiveSpaceOver_of_isNoetherianRing`); and `H^i(Z, F) ≃ H^i(P^n_R, j_*F)`
`R`-linearly (Stacks 02UV, `finite_sheafCohomology_of_finite_pushforward_of_isClosedImmersion`; `j` is a
morphism over `Spec R` by construction of the `Over` structure on `Z`).

Edge cases: `Z = ∅` (all `H^i = 0`); `R = 0` (`P^n_R = ∅`); `n = 0` (`Z` a closed subscheme of `Spec R`,
`H^0 = Γ` a finite module, `H^{>0} = 0`). -/
theorem finite_sheafCohomology_of_isClosedImmersion_projectiveSpaceOver
    {R : Type u} [CommRing R] [IsNoetherianRing R] {n : ℕ} {Z : Scheme.{u}}
    (j : Z ⟶ ProjectiveSpaceOver n R) [IsClosedImmersion j] (F : Z.Modules) [F.IsCoherent]
    (i : ℕ) :
    letI : Z.Over (Spec (CommRingCat.of R)) := ⟨j ≫ ProjectiveSpaceOver.toSpecBase n R⟩
    Module.Finite R (sheafCohomology Z F i) := by
  let _ : Z.Over (Spec (CommRingCat.of R)) := ⟨j ≫ ProjectiveSpaceOver.toSpecBase n R⟩
  have : j.IsOver (Spec (CommRingCat.of R)) := ⟨rfl⟩
  have := ProjectiveSpaceOver.isLocallyNoetherian n R
  have : ((Scheme.Modules.pushforward j).obj F).IsCoherent :=
    Scheme.Modules.isCoherent_pushforward_of_isFinite j F
  have : Module.Finite R (sheafCohomology (ProjectiveSpaceOver n R)
      ((Scheme.Modules.pushforward j).obj F) i) :=
    finite_sheafCohomology_projectiveSpaceOver_of_isNoetherianRing n
      ((Scheme.Modules.pushforward j).obj F) i
  exact Scheme.Modules.finite_sheafCohomology_of_finite_pushforward_of_isClosedImmersion j F i

end AlgebraicGeometry

end
