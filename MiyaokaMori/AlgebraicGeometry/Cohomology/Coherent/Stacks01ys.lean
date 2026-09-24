import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpaceCoherentQuotientTwists
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.ModulesBiproductLocallyFree
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpace
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpaceStructureMorphism
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.CoherentSheaf
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.SerreTwistProjectiveSpace
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.SerreTwistIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafCohomologyModule
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafCohomologyLinearLongExact
import MiyaokaMori.AlgebraicGeometry.Cohomology.Coherent.ProjectiveSpaceCohomologyFiniteNoetherianRing
import MiyaokaMori.AlgebraicGeometry.Cohomology.Coherent.SheafCohomologyFiniteTwoOutOfThree
import MiyaokaMori.AlgebraicGeometry.Cohomology.Coherent.Stacks01xt
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.Stacks01xz
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.Stacks01y1
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.Stacks01ic

/-! # Cohomology of coherent sheaves on projective space over a field (Stacks 01YS)

Cohomology of coherent sheaves on projective space (Stacks 01YS(3)): for a coherent sheaf `F` on `P^n_k`
over a field `k`, every `H^i(P^n_k, F)` is a finite-dimensional `k`-vector space.

Source: Stacks 01YS (coherent-lemma-coherent-projective), parts (1)–(3) with `R = k`.

## Relation to the Noetherian-ring version

The same theorem over a Noetherian ring `R` is
`AlgebraicGeometry.finite_sheafCohomology_projectiveSpaceOver_of_isNoetherianRing`
(`ProjectiveSpaceCohomologyFiniteNoetherianRing.lean`); for `R = k` its statement is definitionally the
one below (`ProjectiveSpace N k = ProjectiveSpaceOver N k` and `ProjectiveSpace.over_eq_over` are `rfl`).
The general `H^n` helpers used below (`ProjectiveSpaceOverRingCohomology.sheafCohomology_map_zero /
_map_add / _map_sum / _finite_biproduct / _subsingleton_of_affine_cover_le`) live in that module.

## Proof (as formalized here; descending induction, Stacks 01YS third paragraph)

Let X = P^N_k. Fix once and for all a finite affine open cover U_1, …, U_t of X
(`AlgebraicGeometry.exists_finite_affineOpen_cover`; X is quasi-compact because it is proper over
Spec k). X is separated over the affine base Spec k, so the diagonal is affine and the Čech/Mayer–Vietoris
vanishing `sheafCohomology'_vanishing_of_affine_cover` gives H^n(X, M) = 0 for every quasi-coherent M
and every n ≥ t (`ProjectiveSpaceOverRingCohomology.sheafCohomology_subsingleton_of_affine_cover_le`).

Claim(d): for every coherent M and every i with t ≤ i + d, H^i(X, M) is a finite k-module.
* d = 0: i ≥ t, so H^i(X, M) = 0.
* d → d + 1: by 01YS(1) (`exists_epi_biproduct_twists_projectiveSpace`) choose an epimorphism
  p : E := ⊕_{j<r} O(d_j) → M. E is locally free of finite type, hence coherent (01XZ); its
  kernel K is quasi-coherent (01IC) and, as a quasi-coherent submodule of a coherent module on a
  locally Noetherian scheme, coherent (01Y1). The short exact sequence 0 → K → E → M → 0 gives the
  k-linear exact segment H^i(E) → H^i(M) → H^{i+1}(K)
  (`sheafCohomology.range_mapOver_g_eq_ker_δOver`). H^i(E) is finite: H^i(⊕ F_j) injects k-linearly
  into ∏_j H^i(F_j) via the projections (left inverse Σ_j H^i(ι_j), from `biproduct.total` and the
  additivity of H^i in the morphism; `ProjectiveSpaceOverRingCohomology.sheafCohomology_finite_biproduct`),
  and each H^i(X, O(d_j)) is finite (01XT). H^{i+1}(K) is finite by Claim(d) since t ≤ (i+1) + d.
  Over the Noetherian ring k the middle term of an exact sequence with finite ends is finite
  (`Module.Finite.of_range_eq_ker_of_isNoetherianRing`).
Claim(t) with M = G gives the theorem.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- **Stacks 01YS(3)** over a field: every cohomology group of a coherent sheaf on `P^N_k` is
finite-dimensional. Proof: descending induction, see the module docstring. -/
theorem finiteDimensional_sheafCohomology_projectiveSpace {k : Type u} [Field k] (N : ℕ)
    (G : (ProjectiveSpace N k).Modules) [G.IsCoherent] (i : ℕ) :
    FiniteDimensional k (AlgebraicGeometry.sheafCohomology (ProjectiveSpace N k) G i) := by
  classical
  have : AlgebraicGeometry.IsLocallyNoetherian (ProjectiveSpace N k) :=
    AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian
      (ProjectiveSpace N k ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
  have : CompactSpace (ProjectiveSpace N k) :=
    AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace
      (ProjectiveSpace N k ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
  have : AlgebraicGeometry.IsSeparated (terminal.from (ProjectiveSpace N k)) := by
    rw [← terminal.comp_from (ProjectiveSpace N k ↘ AlgebraicGeometry.Spec (CommRingCat.of k))]
    infer_instance
  have : AlgebraicGeometry.IsAffineHom (pullback.diagonal (terminal.from (ProjectiveSpace N k))) :=
    inferInstance
  obtain ⟨t, U, hU, hcov⟩ := AlgebraicGeometry.exists_finite_affineOpen_cover (ProjectiveSpace N k)
  have main : ∀ (d : ℕ) (M : (ProjectiveSpace N k).Modules) [M.IsCoherent] (i : ℕ), t ≤ i + d →
      Module.Finite k (AlgebraicGeometry.sheafCohomology (ProjectiveSpace N k) M i) := by
    intro d
    induction d with
    | zero =>
      intro M _ i hi
      have : M.IsQuasicoherent := AlgebraicGeometry.Scheme.Modules.IsCoherent.quasicoherent
      have := ProjectiveSpaceOverRingCohomology.sheafCohomology_subsingleton_of_affine_cover_le M t U
        hU hcov i (by omega)
      infer_instance
    | succ d ih =>
      intro M _ i hi
      obtain ⟨r, dd, p, hp⟩ := exists_epi_biproduct_twists_projectiveSpace N M
      have hEcoh : (⨁ fun j => projectiveSpaceTwist k N (dd j)).IsCoherent :=
        AlgebraicGeometry.Scheme.Modules.isCoherent_of_isLocallyFree _
      have hMqc : M.IsQuasicoherent := AlgebraicGeometry.Scheme.Modules.IsCoherent.quasicoherent
      have hEqc : (⨁ fun j => projectiveSpaceTwist k N (dd j)).IsQuasicoherent :=
        AlgebraicGeometry.Scheme.Modules.IsCoherent.quasicoherent
      have hKqc : (kernel p).IsQuasicoherent :=
        (AlgebraicGeometry.Scheme.Modules.isQuasicoherent_kernel p).1
      have hKcoh : (kernel p).IsCoherent :=
        AlgebraicGeometry.Scheme.Modules.isCoherent_of_mono (kernel.ι p)
      let S : ShortComplex (ProjectiveSpace N k).Modules :=
        ShortComplex.mk (kernel.ι p) p (kernel.condition p)
      have hS : S.ShortExact := { exact := ShortComplex.exact_kernel p }
      have hTw : ∀ j, Module.Finite k (AlgebraicGeometry.sheafCohomology (ProjectiveSpace N k)
          (projectiveSpaceTwist k N (dd j)) i) :=
        fun j => finiteDimensional_sheafCohomology_projectiveSpaceTwist N (dd j) i
      have hE : Module.Finite k (AlgebraicGeometry.sheafCohomology (ProjectiveSpace N k) S.X₂ i) :=
        ProjectiveSpaceOverRingCohomology.sheafCohomology_finite_biproduct k _ i
      have hK : Module.Finite k
          (AlgebraicGeometry.sheafCohomology (ProjectiveSpace N k) S.X₁ (i + 1)) :=
        ih (kernel p) (i + 1) (by omega)
      exact Module.Finite.of_range_eq_ker_of_isNoetherianRing
        (AlgebraicGeometry.sheafCohomology.mapOver k S.g i)
        (AlgebraicGeometry.sheafCohomology.δOver hS i (i + 1) rfl k)
        (AlgebraicGeometry.sheafCohomology.range_mapOver_g_eq_ker_δOver hS i (i + 1) rfl k)
  exact main t G i (by omega)

-- the `k`-structure comes from the `Over (Spec k)` instance of projective space via `sheafCohomology.moduleOver`

end
