import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpaceOver
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpaceTwistTensor
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpaceTwistAmple

/-! # Serre twists on projective space over a commutative ring

The Serre twisting sheaves `O(m)` on `P^N_R` over a commutative ring `R`, the (definitional)
comparison with the version `projectiveSpaceTwist` over a field, and three basic properties:
`O(m)` is a line bundle, `O(a) ⊗ O(b) ≅ O(a+b)`, and `O(1)` is ample.

Source: Stacks 01MM (definition of `O(d)`), 01MS/01MT (the multiplication isomorphisms; `O(d)` is
invertible when the ring is generated in degree one), 01MW + 01PS (`O(1)` is ample).

None of the proofs uses that the base is a field: the first two are theorems about `Proj` of a
general graded ring instantiated at `P^N`; the ampleness proof uses
`ProjectiveSpaceOver.isProper_toSpecBase`, `ProjectiveSpaceOver.iSup_chart` and `Proj.twistSection`,
together with `Proj.not_isZeroAt_twistSection_iff_of_iSup_eq_top` (Stacks 01MW).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
open scoped CategoryTheory.MonoidalCategory

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The Serre twisting sheaf `O(m)` (`m : ℤ`) on `P^N_R`: `Proj.twist` (definitionally
`ProjTwisting.sheaf`) applied to `R[T₀..T_N]` with its standard grading. The argument order is the
same as for `projectiveSpaceTwist k N m` over a field. -/
noncomputable def projectiveSpaceOverTwist (R : Type u) [CommRing R] (N : ℕ) (m : ℤ) :
    (ProjectiveSpaceOver N R).Modules :=
  AlgebraicGeometry.Proj.twist (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) m

/-- Over a field this is definitionally `projectiveSpaceTwist` (the types agree by
`ProjectiveSpace_eq_projectiveSpaceOver`, which is `rfl`). -/
theorem projectiveSpaceTwist_eq_over (k : Type u) [Field k] (N : ℕ) (m : ℤ) :
    projectiveSpaceTwist k N m = projectiveSpaceOverTwist k N m := rfl

/-- `O(m)` is a line bundle (Stacks 01MT: `R[T]` is generated in degree one). The signature of
`IsAmple` requires `[L.IsLineBundle]`, so this is an instance; it is keyed on the head symbol
`projectiveSpaceOverTwist`, and `IsLineBundle` is a `Prop`, so there is no diamond. -/
instance projectiveSpaceOverTwist_isLineBundle (R : Type u) [CommRing R] (N : ℕ) (m : ℤ) :
    (projectiveSpaceOverTwist R N m).IsLineBundle :=
  AlgebraicGeometry.Proj.twist_isLineBundle (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
    (fun i : Fin (N + 1) ↦ MvPolynomial.X i)
    (fun i ↦ MvPolynomial.isHomogeneous_X R i)
    (ProjectiveSpaceOver.iSup_chart N R) m

/-- `O(a) ⊗ O(b) ≅ O(a+b)` (Stacks 01MS + 01MT). -/
theorem projectiveSpaceOverTwist_tensor (R : Type u) [CommRing R] (N : ℕ) (a b : ℤ) :
    Nonempty (AlgebraicGeometry.Scheme.Modules.tensor (projectiveSpaceOverTwist R N a)
      (projectiveSpaceOverTwist R N b) ≅ projectiveSpaceOverTwist R N (a + b)) := by
  let φ := AlgebraicGeometry.Proj.twistMul (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) a b
  have hφ : CategoryTheory.IsIso φ := by
    apply AlgebraicGeometry.Scheme.Modules.moduleHom_isIso_of_locally_isIso φ
    intro x
    have hmem : x ∈ ⨆ i : Fin (N + 1), ProjectiveSpaceOver.chart N R i := by
      rw [ProjectiveSpaceOver.iSup_chart N R]
      trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hmem
    let U := AlgebraicGeometry.Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
      (MvPolynomial.X i)
    have hlocal : CategoryTheory.IsIso
        ((AlgebraicGeometry.Scheme.Modules.restrictFunctor U.ι).map φ) := by
      have hh := (AlgebraicGeometry.Proj.twist_mul_isIso_on_basicOpen
        (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.X i)
        (MvPolynomial.mem_homogeneousSubmodule 1 _ |>.mpr (MvPolynomial.isHomogeneous_X R i))
        (by decide : 0 < 1) a b).2
      have ha : a * (↑(1 : ℕ) : ℤ) = a := by norm_num
      rw [ha] at hh
      simpa [U, φ] using hh
    exact ⟨U, hi, hlocal⟩
  exact ⟨@CategoryTheory.asIso _ _ _ _ φ hφ⟩

/-- `P^N_R` is quasi-compact: it is proper over `Spec R`, which is quasi-compact (alternatively, it is
covered by the `N+1` affine opens `D₊(T_i)`). -/
theorem ProjectiveSpaceOver.compactSpace (N : ℕ) (R : Type u) [CommRing R] :
    CompactSpace (ProjectiveSpaceOver N R) := by
  have := ProjectiveSpaceOver.isProper_toSpecBase N R
  exact AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace
    (ProjectiveSpaceOver N R ↘ AlgebraicGeometry.Spec (CommRingCat.of R))

/-- The homogeneous coordinate `T_i ∈ Γ(P^N_R, O(1))`. -/
noncomputable def projectiveSpaceOverCoordinate (R : Type u) [CommRing R] (N : ℕ) (i : Fin (N + 1)) :
    ((projectiveSpaceOverTwist R N 1).val.obj (Opposite.op ⊤) : Type u) :=
  AlgebraicGeometry.Proj.twistSection (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
    (d := 1) (MvPolynomial.X i)
    ((MvPolynomial.mem_homogeneousSubmodule 1 _).mpr (MvPolynomial.isHomogeneous_X R i))

/-- `O(1)` is ample on `P^N_R` (the definition of Stacks 01PS together with 01MW: the nonvanishing
loci `X_{T_i} = D₊(T_i)` are affine and cover `P^N_R`). Uses
`Proj.not_isZeroAt_twistSection_iff_of_iSup_eq_top`, with the cover given by
`ProjectiveSpaceOver.iSup_chart`. -/
theorem projectiveSpaceOverTwist_one_isAmple (R : Type u) [CommRing R] (N : ℕ) :
    AlgebraicGeometry.IsAmple (projectiveSpaceOverTwist R N 1) := by
  unfold AlgebraicGeometry.IsAmple
  refine ⟨ProjectiveSpaceOver.compactSpace N R, ?_⟩
  intro x
  have hmem : x ∈ ⨆ i : Fin (N + 1), ProjectiveSpaceOver.chart N R i := by
    rw [ProjectiveSpaceOver.iSup_chart N R]
    trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hmem
  let U : (ProjectiveSpaceOver N R).Opens := ProjectiveSpaceOver.chart N R i
  have hxi : MvPolynomial.X i ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R 1 :=
    (MvPolynomial.mem_homogeneousSubmodule 1 _).mpr (MvPolynomial.isHomogeneous_X R i)
  let L : (ProjectiveSpaceOver N R).Modules := projectiveSpaceOverTwist R N 1
  let e1 : AlgebraicGeometry.Scheme.Modules.tensorPow L 1 ≅ L := by
    change AlgebraicGeometry.Scheme.Modules.tensor
      (SheafOfModules.unit (ProjectiveSpaceOver N R).ringCatSheaf) L ≅ L
    exact AlgebraicGeometry.Scheme.Modules.unitTensorIso L
  let s : Γ(L, ⊤) := projectiveSpaceOverCoordinate R N i
  let s1 : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L 1, ⊤) := e1.inv.app ⊤ s
  have he1 : e1.hom.app ⊤ s1 = s := by
    dsimp [s1]
    have hh := e1.inv_hom_id
    have hh' := congrArg (fun q => q.val.app (Opposite.op ⊤)) hh
    exact congrArg (fun q => q.hom s) hh'
  have hloc : L.nonvanishingLocus s = U := by
    ext y
    change y ∈ L.nonvanishingLocus s ↔ y ∈ U
    rw [AlgebraicGeometry.Scheme.Modules.mem_nonvanishingLocus]
    change ¬ IsZeroAt (projectiveSpaceOverCoordinate R N i) y ↔ y ∈ U
    exact (AlgebraicGeometry.Proj.not_isZeroAt_twistSection_iff_of_iSup_eq_top
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) MvPolynomial.X
      (fun j => (MvPolynomial.mem_homogeneousSubmodule 1 _).mpr (MvPolynomial.isHomogeneous_X R j))
      (ProjectiveSpaceOver.iSup_chart N R) (MvPolynomial.X i) hxi y)
  have hmem1 : x ∈ (AlgebraicGeometry.Scheme.Modules.tensorPow L 1).nonvanishingLocus s1 := by
    rw [← AlgebraicGeometry.Scheme.Modules.mem_nonvanishingLocus_iso e1 s1 x, he1, hloc]
    exact hi
  refine ⟨1, Nat.one_pos, s1, hmem1, ?_⟩
  have hopen := AlgebraicGeometry.Scheme.Modules.nonvanishingLocus_iso e1 s1
  rw [← hopen, he1, hloc]
  exact ProjectiveSpaceOver.isAffineOpen_chart N R i

end
