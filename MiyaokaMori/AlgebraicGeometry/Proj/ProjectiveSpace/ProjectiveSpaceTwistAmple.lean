import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Ample.AmpleLineBundle
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpaceStructureMorphism
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpaceCoordinate
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.SerreTwistIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorUnitIso
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.NonvanishingLocusIsoInvariant
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.Stacks01mw
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedProjCoordinateCover

/-! # `O(1)` on projective space is ample

Statement: for a field `k` and any `N`, the Serre twisting sheaf `O(1)` on the projective space
`P^N_k` is an ample line bundle.

Proof:
1. `P^N_k → Spec k` is proper and `Spec k` is quasi-compact, so `P^N_k` is quasi-compact.
2. The nonvanishing locus of the homogeneous coordinate section `x_i ∈ Γ(P^N_k, O(1))` is the
   standard open `D₊(x_i)`; at every point at least one coordinate does not vanish, so these opens
   cover projective space.
3. Mathlib's `Proj.isAffineOpen_basicOpen` says that every `D₊(x_i)` is an affine open.
4. Take `m = 1` and the coordinate sections in the definition of `AlgebraicGeometry.IsAmple`.

Source: Stacks 01PR (`O(1)` is ample on projective space).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem projectiveSpaceTwist_one_isAmple (k : Type u) [Field k] (N : ℕ) :
    AlgebraicGeometry.IsAmple (projectiveSpaceTwist k N 1) := by
  letI := MvPolynomial.gradedAlgebra (σ := Fin (N + 1)) (R := k)
  unfold AlgebraicGeometry.IsAmple
  constructor
  · letI : AlgebraicGeometry.IsProper
      (ProjectiveSpace N k ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ProjectiveSpace.isProper_toSpecBase N k
    exact AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace
      (ProjectiveSpace N k ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
  · intro x
    obtain ⟨i, hi⟩ := MiyaokaMori.WeightedJets.exists_mem_weightedCoordinateOpen k
      (fun _ : Fin (N + 1) ↦ (1 : ℕ+)) x
    let U : (ProjectiveSpace N k).Opens :=
      MiyaokaMori.WeightedJets.weightedCoordinateOpen k
        (fun _ : Fin (N + 1) ↦ (1 : ℕ+)) i
    have hxi : MvPolynomial.X i ∈ AlgebraicGeometry.Proj.projectiveGrading k N 1 :=
      (MvPolynomial.mem_homogeneousSubmodule 1 _).mpr (MvPolynomial.isHomogeneous_X k i)
    let L : (ProjectiveSpace N k).Modules := projectiveSpaceTwist k N 1
    let e1 : AlgebraicGeometry.Scheme.Modules.tensorPow L 1 ≅ L := by
      change AlgebraicGeometry.Scheme.Modules.tensor
        (SheafOfModules.unit (ProjectiveSpace N k).ringCatSheaf) L ≅ L
      exact AlgebraicGeometry.Scheme.Modules.unitTensorIso L
    let s : Γ(L, ⊤) := projectiveSpaceCoordinate k N i
    let s1 : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L 1, ⊤) :=
      e1.inv.app ⊤ s
    have he1 : e1.hom.app ⊤ s1 = s := by
      dsimp [s1]
      have hh := e1.inv_hom_id
      have hh' := congrArg (fun q => q.val.app (Opposite.op ⊤)) hh
      exact congrArg (fun q => q.hom s) hh'
    have hcoord : x ∈ L.nonvanishingLocus s ↔ x ∈ U := by
      rw [AlgebraicGeometry.Scheme.Modules.mem_nonvanishingLocus]
      change ¬ IsZeroAt (projectiveSpaceCoordinate k N i) x ↔ x ∈ U
      exact (AlgebraicGeometry.Proj.not_isZeroAt_twistSection_iff_of_iSup_eq_top
        (AlgebraicGeometry.Proj.projectiveGrading k N) MvPolynomial.X
        (fun j => (MvPolynomial.mem_homogeneousSubmodule 1 _).mpr (MvPolynomial.isHomogeneous_X k j))
        (projectiveSpace_iSup_basicOpen_X k N) (MvPolynomial.X i) hxi x)
    have hmem : x ∈ (AlgebraicGeometry.Scheme.Modules.tensorPow L 1).nonvanishingLocus s1 := by
      rw [← AlgebraicGeometry.Scheme.Modules.mem_nonvanishingLocus_iso e1 s1 x]
      rw [he1]
      exact hcoord.mpr hi
    refine ⟨1, Nat.one_pos, s1, hmem, ?_⟩
    have hopen := AlgebraicGeometry.Scheme.Modules.nonvanishingLocus_iso e1 s1
    rw [← hopen]
    have hloc : L.nonvanishingLocus s = U := by
      ext y
      change y ∈ L.nonvanishingLocus s ↔ y ∈ U
      rw [AlgebraicGeometry.Scheme.Modules.mem_nonvanishingLocus]
      change ¬ IsZeroAt (projectiveSpaceCoordinate k N i) y ↔ y ∈ U
      exact (AlgebraicGeometry.Proj.not_isZeroAt_twistSection_iff_of_iSup_eq_top
        (AlgebraicGeometry.Proj.projectiveGrading k N) MvPolynomial.X
        (fun j => (MvPolynomial.mem_homogeneousSubmodule 1 _).mpr (MvPolynomial.isHomogeneous_X k j))
        (projectiveSpace_iSup_basicOpen_X k N) (MvPolynomial.X i) hxi y)
    rw [he1, hloc]
    exact AlgebraicGeometry.Proj.isAffineOpen_basicOpen
      (AlgebraicGeometry.Proj.projectiveGrading k N) (MvPolynomial.X i) hxi (by decide)

end
