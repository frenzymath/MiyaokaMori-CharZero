import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpaceOver
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpaceOverTwist
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpaceOverCoherentQuotientTwists
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.ModulesBiproductLocallyFree
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.CoherentSheaf
import MiyaokaMori.AlgebraicGeometry.Cohomology.Vanishing.GrothendieckVanishing
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafCohomologyModule
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafCohomologyTopLinearEquiv
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafCohomologyLinearLongExact
import MiyaokaMori.AlgebraicGeometry.Cohomology.Coherent.SheafCohomologyFiniteTwoOutOfThree
import MiyaokaMori.AlgebraicGeometry.Cohomology.Coherent.Stacks01xtOverRing
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.Stacks01xz
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.Stacks01y1
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.Stacks01ic

/-! # Finiteness of cohomology on projective space over a Noetherian ring

Stacks 01YS(3) over a Noetherian ring: `R` Noetherian, `F` coherent on `P^n_R` ⇒ every `H^i(P^n_R, F)` is a
finite `R`-module. This is the Noetherian-ring form of `finiteDimensional_sheafCohomology_projectiveSpace`
(stated over a field in `Stacks01ys.lean`); it is the base case needed by Stacks 02O4 (via closed
subschemes of projective space), and through 02O4 by the dévissage generator of 02O6.

The proof is the field proof of `Stacks01ys.lean` with `k ↦ R`; the only field-specific inputs were the
twist finiteness (Stacks 01XT) and the presentation by twists (Stacks 01YS(1)), whose ring versions are
`Stacks01xtOverRing.finite_sheafCohomology_twist` and `exists_epi_biproduct_twists_projectiveSpaceOver`.

`P^n_R` is the scheme `ProjectiveSpaceOver n R`, which carries the API: charts, twists, ampleness,
properness and the global `Over (Spec R)` instance.

Source: Stacks 01YS (coherent-lemma-coherent-projective), part (3); Hartshorne III.5.2(a).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

namespace ProjectiveSpaceOverRingCohomology

open AlgebraicGeometry

variable {X : Scheme.{u}}

/-! ### Generalities on `H^n` (copied from `Stacks01ys.lean`, which cannot be imported here: it is the
field case that should eventually be derived from this module). -/

/-- `H^n` is additive in the morphism: the zero morphism induces the zero map. -/
theorem sheafCohomology_map_zero (M N : X.Modules) (n : ℕ) :
    sheafCohomology.map (0 : M ⟶ N) n = 0 := by
  apply LinearMap.ext
  intro x
  rw [sheafCohomology.map_apply]
  have h0 : Scheme.Modules.toAddCommGrpSheafMap (0 : M ⟶ N) = 0 :=
    Functor.map_zero (SheafOfModules.toSheaf X.ringCatSheaf) M N
  rw [h0]
  have h := Sheaf.H.map_add_apply (0 : M.toAddCommGrpSheaf ⟶ N.toAddCommGrpSheaf) 0 x
  rw [add_zero] at h
  exact (add_left_cancel ((add_zero _).trans h)).symm

/-- `H^n` is additive in the morphism. -/
theorem sheafCohomology_map_add {M N : X.Modules} (f g : M ⟶ N) (n : ℕ) :
    sheafCohomology.map (f + g) n = sheafCohomology.map f n + sheafCohomology.map g n := by
  apply LinearMap.ext
  intro x
  rw [LinearMap.add_apply, sheafCohomology.map_apply, sheafCohomology.map_apply,
    sheafCohomology.map_apply]
  have h : Scheme.Modules.toAddCommGrpSheafMap (f + g) =
      Scheme.Modules.toAddCommGrpSheafMap f + Scheme.Modules.toAddCommGrpSheafMap g :=
    Functor.map_add (SheafOfModules.toSheaf X.ringCatSheaf)
  rw [h]
  exact Sheaf.H.map_add_apply _ _ x

/-- `H^n` of a finite sum of morphisms is the sum of the induced maps. -/
theorem sheafCohomology_map_sum {M N : X.Modules} {ι : Type*} (s : Finset ι) (f : ι → (M ⟶ N))
    (n : ℕ) :
    sheafCohomology.map (∑ j ∈ s, f j) n = ∑ j ∈ s, sheafCohomology.map (f j) n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [sheafCohomology_map_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, sheafCohomology_map_add, ih]

/-- Finiteness of the cohomology of a finite biproduct: `H^n(⊕ F_j)` injects `R`-linearly into
`∏_j H^n(F_j)` via the projections (left inverse `Σ_j H^n(ι_j)`, from `biproduct.total`), and a finite
product of finite modules over a Noetherian ring is finite. -/
theorem sheafCohomology_finite_biproduct (R : Type u) [CommRing R] [IsNoetherianRing R]
    [X.Over (Spec (CommRingCat.of R))] {ι : Type} [Fintype ι] (F : ι → X.Modules) (n : ℕ)
    [hF : ∀ j, Module.Finite R (sheafCohomology X (F j) n)] :
    Module.Finite R (sheafCohomology X (⨁ F) n) := by
  classical
  have : ∀ j, _root_.IsNoetherian R (sheafCohomology X (F j) n) :=
    fun j => isNoetherian_of_isNoetherianRing_of_finite R _
  have : _root_.IsNoetherian R (∀ j, sheafCohomology X (F j) n) := isNoetherian_pi
  let φ : sheafCohomology X (⨁ F) n →ₗ[R] (∀ j, sheafCohomology X (F j) n) :=
    LinearMap.pi fun j => sheafCohomology.mapOver R (biproduct.π F j) n
  refine Module.Finite.of_injective φ ?_
  have key : ∀ z : sheafCohomology X (⨁ F) n,
      z = ∑ j, sheafCohomology.map (biproduct.ι F j) n
        (sheafCohomology.map (biproduct.π F j) n z) := by
    intro z
    have h := congrArg (fun ψ : sheafCohomology X (⨁ F) n →ₗ[Γ(X, ⊤)] sheafCohomology X (⨁ F) n
      => ψ z) (sheafCohomology_map_sum Finset.univ
        (fun j => biproduct.π F j ≫ biproduct.ι F j) n)
    rw [biproduct.total, sheafCohomology.map_id, LinearMap.id_apply, LinearMap.sum_apply] at h
    refine h.trans (Finset.sum_congr rfl fun j _ => ?_)
    rw [sheafCohomology.map_comp, LinearMap.comp_apply]
  intro x y hxy
  refine (key x).trans ((Finset.sum_congr rfl fun j _ => ?_).trans (key y).symm)
  have hj := congr_fun hxy j
  simp only [φ, LinearMap.pi_apply, sheafCohomology.mapOver_apply] at hj
  rw [hj]

/-- Vanishing above the size of an affine cover (Grothendieck/Čech, Stacks 01XI via
`sheafCohomology'_vanishing_of_affine_cover`), transported from `H'(⊤)` to `sheafCohomology`. -/
theorem sheafCohomology_subsingleton_of_affine_cover_le
    [IsAffineHom (pullback.diagonal (terminal.from X))] (M : X.Modules) [M.IsQuasicoherent]
    (t : ℕ) (U : Fin t → X.Opens) (hU : ∀ i, IsAffineOpen (U i)) (hcov : ⨆ i, U i = ⊤) (n : ℕ)
    (hn : t ≤ n) : Subsingleton (sheafCohomology X M n) := by
  have h := sheafCohomology'_vanishing_of_affine_cover M t U hU n hn
  rw [hcov] at h
  exact Equiv.subsingleton (sheafCohomologyTopLinearEquiv M n).symm.toEquiv

/-! ### `P^N_R` is Noetherian and semi-separated -/

/-- `P^N_R` is locally Noetherian for `R` Noetherian (Stacks 01YS, proof, first line): `R[T]` is of
finite type over `R[T]_0` (scalar tower `R → R[T]_0 → R[T]`), so `Proj.toSpecZero` is locally of finite
type, and `R[T]_0` is Noetherian as a quotient of `R` (`R → R[T]_0` is bijective,
`ProjectiveSpaceOver.algebraMap_zero_bijective`). Not a global instance. -/
theorem isLocallyNoetherian (R : Type u) [CommRing R] [IsNoetherianRing R] (N : ℕ) :
    IsLocallyNoetherian (ProjectiveSpaceOver N R) := by
  have : IsScalarTower R (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R 0)
      (MvPolynomial (Fin (N + 1)) R) :=
    IsScalarTower.of_algebraMap_eq (R := R)
      (S := MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R 0)
      (A := MvPolynomial (Fin (N + 1)) R) fun _ ↦ rfl
  have : Algebra.FiniteType (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R 0)
      (MvPolynomial (Fin (N + 1)) R) :=
    Algebra.FiniteType.of_restrictScalars_finiteType R
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R 0) _
  have : IsNoetherianRing (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R 0) :=
    isNoetherianRing_of_surjective R _
      (algebraMap R (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R 0))
      (ProjectiveSpaceOver.algebraMap_zero_bijective N R).2
  change IsLocallyNoetherian (Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R))
  exact LocallyOfFiniteType.isLocallyNoetherian
    (Proj.toSpecZero (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R))

/-- `P^N_R` is semi-separated: the diagonal of `P^N_R → pt` is affine (`P^N_R` is proper, hence
separated, over the affine `Spec R`). -/
theorem isAffineHom_diagonal_terminal (R : Type u) [CommRing R] (N : ℕ) :
    IsAffineHom (pullback.diagonal (terminal.from (ProjectiveSpaceOver N R))) := by
  have := ProjectiveSpaceOver.isProper_toSpecBase N R
  have : IsSeparated (terminal.from (ProjectiveSpaceOver N R)) := by
    rw [← terminal.comp_from (ProjectiveSpaceOver N R ↘ Spec (CommRingCat.of R))]
    infer_instance
  infer_instance

/-- A finite direct sum of twists on `P^N_R` is coherent (locally free of finite type on a locally
Noetherian scheme, Stacks 01XZ). -/
theorem biproduct_twist_isCoherent (R : Type u) [CommRing R] [IsNoetherianRing R] (N : ℕ) {r : ℕ}
    (d : Fin r → ℤ) : (⨁ fun j => projectiveSpaceOverTwist R N (d j)).IsCoherent := by
  have := isLocallyNoetherian R N
  exact Scheme.Modules.isCoherent_of_isLocallyFree _

/-! ### The descending induction (Stacks 01YS, proof of (3)) -/

/-- **Stacks 01YS(3) over a Noetherian ring**, in the `ProjectiveSpaceOver` spelling: `R` Noetherian,
`F` coherent on `P^N_R` ⇒ `H^i(P^N_R, F)` is a finite `R`-module.

Proof (descending induction, exactly as `finiteDimensional_sheafCohomology_projectiveSpace`). Fix a finite
affine open cover `U_1, …, U_t` of the quasi-compact `P^N_R`. Since `P^N_R` is semi-separated,
`H^i(P^N_R, M) = 0` for every quasi-coherent `M` and `i ≥ t`. Claim(d): for every coherent `M` and every
`i` with `t ≤ i + d`, `H^i(M)` is finite. `d = 0`: vanishing. `d → d + 1`: choose an epimorphism
`p : E := ⊕_j O(d_j) → M` (01YS(1) over `R`); `E` is coherent (locally free of finite type on a Noetherian
scheme, 01XZ), `K = ker p` is quasi-coherent (01IC) hence coherent (01Y1). The `R`-linear exact segment
`H^i(E) → H^i(M) → H^{i+1}(K)` (`range_mapOver_g_eq_ker_δOver`), finiteness of `H^i(E)` (biproduct + 01XT
over `R`) and of `H^{i+1}(K)` (Claim(d)), and Noetherian two-out-of-three
(`Module.Finite.of_range_eq_ker_of_isNoetherianRing`) give the claim. Claim(t) with `M = F` finishes. -/
theorem finite_sheafCohomology_of_isCoherent (R : Type u) [CommRing R] [IsNoetherianRing R] (N : ℕ)
    (F : (ProjectiveSpaceOver N R).Modules) [F.IsCoherent] (i : ℕ) :
    Module.Finite R (sheafCohomology (ProjectiveSpaceOver N R) F i) := by
  classical
  have := isLocallyNoetherian R N
  have := ProjectiveSpaceOver.compactSpace N R
  have := isAffineHom_diagonal_terminal R N
  obtain ⟨t, U, hU, hcov⟩ := exists_finite_affineOpen_cover (ProjectiveSpaceOver N R)
  have main : ∀ (d : ℕ) (M : (ProjectiveSpaceOver N R).Modules) [M.IsCoherent] (i : ℕ), t ≤ i + d →
      Module.Finite R (sheafCohomology (ProjectiveSpaceOver N R) M i) := by
    intro d
    induction d with
    | zero =>
      intro M _ i hi
      have : M.IsQuasicoherent := Scheme.Modules.IsCoherent.quasicoherent
      have := sheafCohomology_subsingleton_of_affine_cover_le M t U hU hcov i (by omega)
      infer_instance
    | succ d ih =>
      intro M _ i hi
      obtain ⟨r, dd, p, hp⟩ := exists_epi_biproduct_twists_projectiveSpaceOver R N M
      have hEcoh : (⨁ fun j => projectiveSpaceOverTwist R N (dd j)).IsCoherent :=
        biproduct_twist_isCoherent R N dd
      have hMqc : M.IsQuasicoherent := Scheme.Modules.IsCoherent.quasicoherent
      have hEqc : (⨁ fun j => projectiveSpaceOverTwist R N (dd j)).IsQuasicoherent :=
        Scheme.Modules.IsCoherent.quasicoherent
      have hKqc : (kernel p).IsQuasicoherent := (Scheme.Modules.isQuasicoherent_kernel p).1
      have hKcoh : (kernel p).IsCoherent := Scheme.Modules.isCoherent_of_mono (kernel.ι p)
      let S : ShortComplex (ProjectiveSpaceOver N R).Modules :=
        ShortComplex.mk (kernel.ι p) p (kernel.condition p)
      have hS : S.ShortExact := { exact := ShortComplex.exact_kernel p }
      have hTw : ∀ j, Module.Finite R (sheafCohomology (ProjectiveSpaceOver N R)
          (projectiveSpaceOverTwist R N (dd j)) i) :=
        fun j => Stacks01xtOverRing.finite_sheafCohomology_twist R N (dd j) i
      have hE : Module.Finite R (sheafCohomology (ProjectiveSpaceOver N R) S.X₂ i) :=
        sheafCohomology_finite_biproduct R _ i
      have hK : Module.Finite R (sheafCohomology (ProjectiveSpaceOver N R) S.X₁ (i + 1)) :=
        ih (kernel p) (i + 1) (by omega)
      exact Module.Finite.of_range_eq_ker_of_isNoetherianRing
        (sheafCohomology.mapOver R S.g i)
        (sheafCohomology.δOver hS i (i + 1) rfl R)
        (sheafCohomology.range_mapOver_g_eq_ker_δOver hS i (i + 1) rfl R)
  exact main t F i (by omega)

end ProjectiveSpaceOverRingCohomology

/-- **Finiteness of cohomology on projective space over a Noetherian ring** (Stacks 01YS(3); Hartshorne
III.5.2(a)), `ProjectiveSpaceOver` spelling. `R` a Noetherian ring, `P := P^n_R = Proj R[T_0, …, T_n]`
(`ProjectiveSpaceOver n R`), `F` coherent on `P`. Then `H^i(P, F)` is a finite
`R`-module for every `i`; the `R`-module structure is `sheafCohomology.moduleOver` for the structure
morphism `ProjectiveSpaceOver.toSpecBase n R : P → Spec R` (global instance `ProjectiveSpaceOver.over`).
Proof: `ProjectiveSpaceOverRingCohomology.finite_sheafCohomology_of_isCoherent` (descending induction,
Stacks 01YS proof of (3); see its docstring and the module docstring).

**Edge cases.** `n = 0`: `P = Spec R`, coherent = finite `R`-module, `H^0 = Γ`, `H^i = 0` for `i > 0`.
`R` the zero ring: `P = ∅`, everything is `0`. `F = 0`: all `H^i = 0`. `R` a field: this is
`finiteDimensional_sheafCohomology_projectiveSpace` (Stacks 01YS over a field), whose statement is the
`Module.Finite k` form of this one for the same scheme and the same module structure
(`ProjectiveSpace N k = ProjectiveSpaceOver N k` and the two `Over` instances are `rfl`). -/
theorem AlgebraicGeometry.finite_sheafCohomology_projectiveSpaceOver_of_isNoetherianRing
    {R : Type u} [CommRing R] [IsNoetherianRing R] (n : ℕ)
    (F : (ProjectiveSpaceOver n R).Modules) [F.IsCoherent] (i : ℕ) :
    Module.Finite R (AlgebraicGeometry.sheafCohomology (ProjectiveSpaceOver n R) F i) :=
  ProjectiveSpaceOverRingCohomology.finite_sheafCohomology_of_isCoherent R n F i

end
