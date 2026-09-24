import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpaceOverTwist
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorPowCanonicalIso
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorPowMapIso
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorUnitIso
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.TensorRightInvertibleEquivalence
import MiyaokaMori.AlgebraicGeometry.Cohomology.Vanishing.GrothendieckVanishing
import MiyaokaMori.AlgebraicGeometry.Cohomology.Coherent.Stacks01xt
import MiyaokaMori.AlgebraicGeometry.Modules.Stacks0892_TensorPowIsos

/-! # Auxiliary facts on projective space over a ring for Serre vanishing

Small facts about `P^N_R = ProjectiveSpaceOver N R` over an arbitrary commutative ring `R`, used by the ring
version of Serre vanishing (Stacks 0B5T(4) over a Noetherian ring). Each of them is the field statement of
`Stacks0b5tProjectiveSpaceAux.lean` / `Stacks0b5tTwistTransport.lean` / `Stacks01xt.lean` with `k` replaced
by `R`; none of the proofs uses that the base is a field.

1. **Čech bound** `sheafCohomology_projectiveSpaceOver_subsingleton_of_lt`: `M` quasi-coherent on `P^N_R`,
   `p > N` ⇒ `H^p(P^N_R, M) = 0`. `P^N_R → Spec R` is proper hence separated, `Spec R → pt` is affine
   hence separated, so `P^N_R` is semi-separated and the Mayer–Vietoris induction of
   `GrothendieckVanishing.lean` (`sheafCohomology'_vanishing_of_affine_cover`) applies to the cover by the
   `N + 1` affine charts `D_+(T_i)` (Stacks 01XS).
2. **Twists**: `O(0) ≅ O`, `O(1)^{⊗n} ≅ O(n)` (from `O(a) ⊗ O(b) ≅ O(a + b)`, `projectiveSpaceOverTwist_tensor`,
   and the fact that `− ⊗ L` is an autoequivalence for a line bundle). (`O(a)^∨ ≅ O(-a)` and the quotient
   `⨁ O(d_j) ↠ G` over `R` are in `exists_epi_biproduct_twists_projectiveSpaceOver`.)
3. **Twist transport**: given `i : X ⟶ P^N_R` and `e : i^*O(1) ≅ L^{⊗d}`,
   `F ⊗ L^{⊗(q + d m)} ≅ (F ⊗ L^{⊗q}) ⊗ i^*O(m)` (Stacks 0B5T proof of (4): "treat the residue classes
   `q` modulo `d` separately").
4. **Noetherian**: `R` Noetherian ⇒ `P^N_R` locally Noetherian (finite type over `Spec R`, Stacks 01T6).
5. **Stacks 01XT, vanishing part, over `R`**: `H^{q+1}(P^N_R, O(d)) = 0` unless `q + 1 = N` and
   `d ≤ -N - 1`; Leray for the standard cover (`Stacks01xtAux.exists_leray`, over `R`) and the
   Laurent–Čech computation `ProjectiveSpaceOver.subsingleton_cechComplexAlt_homology_succ` (over `R`;
   `ProjectiveSpaceCechLaurent.lean` / `LaurentCechCohomology.lean`, shared with the field case).

Source: Stacks 0B5T (proof of (4)), 01XS, 01XT, 01MS/01MT.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry CategoryTheory.MonoidalCategory

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

/-- `P^N_R` is semi-separated: the diagonal of `P^N_R → pt` is affine (`P^N_R → Spec R` is proper, hence
separated, and `Spec R → pt` is affine). -/
theorem ProjectiveSpaceOver.isAffineHom_diagonal_terminal (R : Type u) [CommRing R] (N : ℕ) :
    AlgebraicGeometry.IsAffineHom (pullback.diagonal (terminal.from (ProjectiveSpaceOver N R))) := by
  haveI := ProjectiveSpaceOver.isProper_toSpecBase N R
  haveI : AlgebraicGeometry.IsSeparated (terminal.from (ProjectiveSpaceOver N R)) := by
    rw [← terminal.comp_from (ProjectiveSpaceOver N R ↘ AlgebraicGeometry.Spec (CommRingCat.of R))]
    infer_instance
  infer_instance

/-- **Čech bound on `P^N_R`**: quasi-coherent cohomology vanishes above `N` (Stacks 01XS, via the affine
cover by the `N + 1` standard charts). -/
theorem AlgebraicGeometry.sheafCohomology_projectiveSpaceOver_subsingleton_of_lt {R : Type u} [CommRing R]
    (N : ℕ) (M : (ProjectiveSpaceOver N R).Modules) [M.IsQuasicoherent] (p : ℕ) (hp : N < p) :
    Subsingleton (CategoryTheory.Sheaf.H M.toAddCommGrpSheaf p) := by
  haveI := ProjectiveSpaceOver.isAffineHom_diagonal_terminal R N
  have h := sheafCohomology'_vanishing_of_affine_cover M (N + 1) (ProjectiveSpaceOver.chart N R)
    (ProjectiveSpaceOver.isAffineOpen_chart N R) p hp
  rw [ProjectiveSpaceOver.iSup_chart N R] at h
  exact Equiv.subsingleton
    (CategoryTheory.Sheaf.H'TopAddEquiv _ isTerminalTop M.toAddCommGrpSheaf p).symm.toEquiv

/-- `R` Noetherian ⇒ `P^N_R` locally Noetherian (finite type over `Spec R`). The same lemma as
`ProjectiveSpaceOver.isLocallyNoetherian` (`ClosedSubschemeProjectiveSpaceCohomologyFinite.lean`) with the
arguments in the order `(R) (N)`. -/
theorem ProjectiveSpaceOver.isLocallyNoetherian' (R : Type u) [CommRing R] [IsNoetherianRing R] (N : ℕ) :
    AlgebraicGeometry.IsLocallyNoetherian (ProjectiveSpaceOver N R) := by
  haveI := ProjectiveSpaceOver.isProper_toSpecBase N R
  exact AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian
    (ProjectiveSpaceOver N R ↘ AlgebraicGeometry.Spec (CommRingCat.of R))

/-- `O(0) ≅ O_{P^N_R}`: `O(0) ⊗ O(0) ≅ O(0)` and `− ⊗ O(0)` is an autoequivalence. -/
theorem projectiveSpaceOverTwist_zero_iso_unit (R : Type u) [CommRing R] (N : ℕ) :
    Nonempty (projectiveSpaceOverTwist R N 0 ≅ 𝟙_ (ProjectiveSpaceOver N R).Modules) := by
  let A : (ProjectiveSpaceOver N R).Modules := projectiveSpaceOverTwist R N 0
  let FA := CategoryTheory.MonoidalCategory.tensorRight A
  have : FA.IsEquivalence :=
    AlgebraicGeometry.Scheme.Modules.isEquivalence_tensorRight_of_isLineBundle A
  have eAA₀ : A ⊗ A ≅ A := by
    let e : AlgebraicGeometry.Scheme.Modules.tensor
        (projectiveSpaceOverTwist R N 0) (projectiveSpaceOverTwist R N 0) ≅
        projectiveSpaceOverTwist R N (0 + 0) := Classical.choice (projectiveSpaceOverTwist_tensor R N 0 0)
    simpa [A] using
      (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj A A).symm ≪≫ e
  let eF : FA.obj A ≅ FA.obj (𝟙_ (ProjectiveSpaceOver N R).Modules) :=
    eAA₀ ≪≫ (CategoryTheory.MonoidalCategory.leftUnitor A).symm
  exact ⟨(FA.asEquivalence.fullyFaithfulFunctor).preimageIso eF⟩

/-- `O(1)^{⊗n} ≅ O(n)` on `P^N_R` (`tensorPow` is the right-multiplication recursion). -/
theorem projectiveSpaceOverTwist_tensorPow_one (R : Type u) [CommRing R] (N : ℕ) :
    ∀ n : ℕ, Nonempty (AlgebraicGeometry.Scheme.Modules.tensorPow (projectiveSpaceOverTwist R N 1) n ≅
      projectiveSpaceOverTwist R N n)
  | 0 => by
    obtain ⟨e⟩ := projectiveSpaceOverTwist_zero_iso_unit R N
    exact ⟨(eqToIso (AlgebraicGeometry.Scheme.Modules.unit_eq_tensorUnit (ProjectiveSpaceOver N R))) ≪≫
      e.symm ≪≫ eqToIso (by simp)⟩
  | n + 1 => by
    obtain ⟨e⟩ := projectiveSpaceOverTwist_tensorPow_one R N n
    obtain ⟨f⟩ := projectiveSpaceOverTwist_tensor R N n 1
    exact ⟨AlgebraicGeometry.Scheme.Modules.tensorCongrLeftIso e _ ≪≫ f ≪≫
      eqToIso (by push_cast; rfl)⟩

/-- Twist transport: `L^{⊗(q + d m)} ≅ L^{⊗q} ⊗ i^* O(m)` given `i^* O(1) ≅ L^{⊗d}` (`i : X ⟶ P^N_R`). -/
theorem AlgebraicGeometry.Scheme.Modules.tensorPow_add_mul_iso_tensor_pullback_twist_over {R : Type u}
    [CommRing R] {X : AlgebraicGeometry.Scheme.{u}} {N : ℕ} (i : X ⟶ ProjectiveSpaceOver N R)
    (L : X.Modules) {d : ℕ}
    (e : (AlgebraicGeometry.Scheme.Modules.pullback i).obj (projectiveSpaceOverTwist R N 1) ≅
      AlgebraicGeometry.Scheme.Modules.tensorPow L d) (q m : ℕ) :
    Nonempty (AlgebraicGeometry.Scheme.Modules.tensorPow L (q + d * m) ≅
      AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.Modules.tensorPow L q)
        ((AlgebraicGeometry.Scheme.Modules.pullback i).obj (projectiveSpaceOverTwist R N m))) := by
  obtain ⟨t⟩ := projectiveSpaceOverTwist_tensorPow_one R N m
  refine ⟨AlgebraicGeometry.Scheme.Modules.tensorPowAddIso L q (d * m) ≪≫
    CategoryTheory.MonoidalCategory.whiskerLeftIso (AlgebraicGeometry.Scheme.Modules.tensorPow L q)
      ((AlgebraicGeometry.Scheme.Modules.tensorPowMulIso L d m).symm ≪≫
        AlgebraicGeometry.Scheme.Modules.tensorPowMapIso e.symm m ≪≫
        (AlgebraicGeometry.Scheme.Modules.pullbackTensorPowIso i (projectiveSpaceOverTwist R N 1) m).symm ≪≫
        (AlgebraicGeometry.Scheme.Modules.pullback i).mapIso t) ≪≫
    (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _).symm⟩

/-- Twist transport: `F ⊗ L^{⊗(q + d m)} ≅ (F ⊗ L^{⊗q}) ⊗ i^* O(m)` given `i^* O(1) ≅ L^{⊗d}`. -/
theorem AlgebraicGeometry.Scheme.Modules.tensor_tensorPow_add_mul_iso_tensor_pullback_twist_over {R : Type u}
    [CommRing R] {X : AlgebraicGeometry.Scheme.{u}} {N : ℕ} (i : X ⟶ ProjectiveSpaceOver N R)
    (L : X.Modules) {d : ℕ}
    (e : (AlgebraicGeometry.Scheme.Modules.pullback i).obj (projectiveSpaceOverTwist R N 1) ≅
      AlgebraicGeometry.Scheme.Modules.tensorPow L d) (F : X.Modules) (q m : ℕ) :
    Nonempty (AlgebraicGeometry.Scheme.Modules.tensor F
        (AlgebraicGeometry.Scheme.Modules.tensorPow L (q + d * m)) ≅
      AlgebraicGeometry.Scheme.Modules.tensor
        (AlgebraicGeometry.Scheme.Modules.tensor F (AlgebraicGeometry.Scheme.Modules.tensorPow L q))
        ((AlgebraicGeometry.Scheme.Modules.pullback i).obj (projectiveSpaceOverTwist R N m))) := by
  obtain ⟨s⟩ := AlgebraicGeometry.Scheme.Modules.tensorPow_add_mul_iso_tensor_pullback_twist_over i L e q m
  exact ⟨AlgebraicGeometry.Scheme.Modules.tensorCongrRightIso F s ≪≫
    (AlgebraicGeometry.Scheme.Modules.tensorAssocIso F _ _).symm⟩

/-- **Stacks 01XT, vanishing part, over a ring**: `H^{q+1}(P^N_R, O(d)) = 0` unless `q + 1 = N` and
`d ≤ -N-1` (Leray for the standard affine cover + the Laurent–Čech computation, both over `R`). -/
theorem subsingleton_sheafCohomology_projectiveSpaceOverTwist_succ (R : Type u) [CommRing R] (N : ℕ)
    (d : ℤ) (q : ℕ) (hN : ¬ (q + 1 = N ∧ d ≤ -((N : ℤ) + 1))) :
    Subsingleton (AlgebraicGeometry.sheafCohomology (ProjectiveSpaceOver N R)
      (projectiveSpaceOverTwist R N d) (q + 1)) := by
  obtain ⟨r⟩ := Stacks01xtAux.exists_leray N R d (q + 1)
  have := ProjectiveSpaceOver.subsingleton_cechComplexAlt_homology_succ R N d q hN
  exact r.toEquiv.subsingleton

/-- `H^p(P^N_R, O(d)) = 0` for `p > 0` and `d ≥ -N` (the form used for Serre vanishing). -/
theorem subsingleton_H_projectiveSpaceOverTwist_of_pos (R : Type u) [CommRing R] (N : ℕ) (d : ℤ) (p : ℕ)
    (hp : 0 < p) (hd : -(N : ℤ) ≤ d) :
    Subsingleton (CategoryTheory.Sheaf.H (projectiveSpaceOverTwist R N d).toAddCommGrpSheaf p) := by
  obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  exact subsingleton_sheafCohomology_projectiveSpaceOverTwist_succ R N d q (fun h => by omega)

end
