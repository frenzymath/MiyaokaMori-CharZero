import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpaceTwistTensor
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpaceStructureMorphism
import MiyaokaMori.AlgebraicGeometry.Cohomology.Vanishing.GrothendieckVanishing
import MiyaokaMori.AlgebraicGeometry.Modules.Stacks0892_TensorPowIsos

/-! # Auxiliary facts on projective space for Serre vanishing

Two small facts about `P^N_k` used in the proof of Serre vanishing (Stacks 0B5T(4)) on projective space
(`Stacks0b5tProjectiveSpace.lean`):

1. **Čech bound** `sheafCohomology_projectiveSpace_subsingleton_of_lt`: for a quasi-coherent module `M`
   on `P^N_k` and `p > N`, `H^p(P^N, M) = 0`. Proof: `P^N` is separated over `Spec k`, hence
   semi-separated (its diagonal is affine, so intersections of affine opens are affine), and it is covered
   by the `N + 1` affine opens `D_+(x_i)` (Mathlib `Proj.isAffineOpen_basicOpen`, cover
   `projectiveSpace_iSup_basicOpen_X`); the Mayer–Vietoris induction of `GrothendieckVanishing.lean`
   (`sheafCohomology'_vanishing_of_affine_cover`) then gives `H^p = 0` for `p ≥ N + 1`.
   This uses the affine-cover bound instead of the Noetherian-dimension bound of Stacks 02UZ.

2. **Tensor powers of `O(1)`** `projectiveSpaceTwist_tensorPow_one`: `O(1)^{⊗n} ≅ O(n)`.
   Induction on `n`: `n = 0` is `O_X ≅ O(0)` (`projectiveSpaceTwist_zero_iso_unit`, proved here from
   `O(0) ⊗ O(0) ≅ O(0)` and the fact that `− ⊗ O(0)` is an autoequivalence), and `n + 1` uses
   `O(n) ⊗ O(1) ≅ O(n + 1)` (`projectiveSpaceTwist_tensor`).

Source: Stacks 0B5T (proof of (4)), 01XS; the paper uses Serre vanishing in the proof of
Proposition 3.2.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry CategoryTheory.MonoidalCategory

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

/-- `P^N_k` is semi-separated: the diagonal of `P^N → pt` is affine (it is separated over `Spec k`). -/
theorem ProjectiveSpace.isAffineHom_diagonal_terminal (k : Type u) [Field k] (N : ℕ) :
    AlgebraicGeometry.IsAffineHom (pullback.diagonal (terminal.from (ProjectiveSpace N k))) := by
  haveI : AlgebraicGeometry.IsSeparated (terminal.from (ProjectiveSpace N k)) := by
    rw [← terminal.comp_from (ProjectiveSpace N k ↘ AlgebraicGeometry.Spec (CommRingCat.of k))]
    infer_instance
  infer_instance

/-- **Čech bound on `P^N`**: quasi-coherent cohomology vanishes above `N` (Stacks 01XS, via the affine
cover by the `N + 1` standard opens). -/
theorem AlgebraicGeometry.sheafCohomology_projectiveSpace_subsingleton_of_lt {k : Type u} [Field k]
    (N : ℕ) (M : (ProjectiveSpace N k).Modules) [M.IsQuasicoherent] (p : ℕ) (hp : N < p) :
    Subsingleton (CategoryTheory.Sheaf.H M.toAddCommGrpSheaf p) := by
  haveI := ProjectiveSpace.isAffineHom_diagonal_terminal k N
  have h := sheafCohomology'_vanishing_of_affine_cover M (N + 1)
    (fun i : Fin (N + 1) => AlgebraicGeometry.Proj.basicOpen (AlgebraicGeometry.Proj.projectiveGrading k N)
      (MvPolynomial.X i))
    (fun i => AlgebraicGeometry.Proj.isAffineOpen_basicOpen (AlgebraicGeometry.Proj.projectiveGrading k N)
      (MvPolynomial.X i)
      ((MvPolynomial.mem_homogeneousSubmodule 1 _).mpr (MvPolynomial.isHomogeneous_X k i))
      (by decide : 0 < 1)) p hp
  have hcov : (⨆ i : Fin (N + 1), AlgebraicGeometry.Proj.basicOpen (AlgebraicGeometry.Proj.projectiveGrading k N)
      (MvPolynomial.X i) : (ProjectiveSpace N k).Opens) = ⊤ := projectiveSpace_iSup_basicOpen_X k N
  rw [hcov] at h
  exact Equiv.subsingleton
    (CategoryTheory.Sheaf.H'TopAddEquiv _ isTerminalTop M.toAddCommGrpSheaf p).symm.toEquiv

/-- `O(0) ≅ O_{P^N}`: `O(0) ⊗ O(0) ≅ O(0)` and `− ⊗ O(0)` is an autoequivalence. -/
theorem projectiveSpaceTwist_zero_iso_unit' {k : Type u} [Field k] (N : ℕ) :
    Nonempty (projectiveSpaceTwist k N 0 ≅ 𝟙_ (ProjectiveSpace N k).Modules) := by
  let A : (ProjectiveSpace N k).Modules := projectiveSpaceTwist k N 0
  let FA := CategoryTheory.MonoidalCategory.tensorRight A
  have : FA.IsEquivalence :=
    AlgebraicGeometry.Scheme.Modules.isEquivalence_tensorRight_of_isLineBundle A
  have eAA₀ : A ⊗ A ≅ A := by
    let e : AlgebraicGeometry.Scheme.Modules.tensor
        (projectiveSpaceTwist k N 0) (projectiveSpaceTwist k N 0) ≅
        projectiveSpaceTwist k N (0 + 0) := Classical.choice (projectiveSpaceTwist_tensor N 0 0)
    simpa [A] using
      (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj A A).symm ≪≫ e
  let eF : FA.obj A ≅ FA.obj (𝟙_ (ProjectiveSpace N k).Modules) :=
    eAA₀ ≪≫ (CategoryTheory.MonoidalCategory.leftUnitor A).symm
  exact ⟨(FA.asEquivalence.fullyFaithfulFunctor).preimageIso eF⟩

/-- `O(1)^{⊗n} ≅ O(n)` on `P^N_k` (`tensorPow` is the right-multiplication recursion). -/
theorem projectiveSpaceTwist_tensorPow_one {k : Type u} [Field k] (N : ℕ) :
    ∀ n : ℕ, Nonempty (AlgebraicGeometry.Scheme.Modules.tensorPow (projectiveSpaceTwist k N 1) n ≅
      projectiveSpaceTwist k N n)
  | 0 => by
    obtain ⟨e⟩ := projectiveSpaceTwist_zero_iso_unit' (k := k) N
    exact ⟨(eqToIso (AlgebraicGeometry.Scheme.Modules.unit_eq_tensorUnit (ProjectiveSpace N k))) ≪≫
      e.symm ≪≫ eqToIso (by simp)⟩
  | n + 1 => by
    obtain ⟨e⟩ := projectiveSpaceTwist_tensorPow_one (k := k) N n
    obtain ⟨f⟩ := projectiveSpaceTwist_tensor (k := k) N n 1
    exact ⟨AlgebraicGeometry.Scheme.Modules.tensorCongrLeftIso e _ ≪≫ f ≪≫
      eqToIso (by push_cast; rfl)⟩

end
