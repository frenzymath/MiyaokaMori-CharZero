import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjDegreeZeroIsoBase
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveLine
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpace
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpaceStructureMorphism
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveLineRationalPointCoords
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveLineLinearAction
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveLineBasicOpenExt
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-! # Linear automorphisms of the projective line

An invertible `2 × 2` matrix `M` induces a `k`-automorphism of `P¹_k`, acting on points with
homogeneous coordinates by `[v] ↦ [Mv]`. This is used to reparametrize a rational curve so that
`0` is sent to a prescribed point (Lemma 5.1 of the paper).

The casts are spelled over `ProjectiveLine k` and `ProjectiveSpace.toSpecBase 1 k`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry BigOperators
open AlgebraicGeometry AlgebraicGeometry.Proj
open AlgebraicGeometry.Proj.ProjectiveLineLinearAction
attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

private theorem eval_comp_substitution {k : Type u} [Field k]
    (v : Fin 2 → k) (a b c d : k) :
    (MvPolynomial.eval v).comp (substitution a b c d).toRingHom =
      MvPolynomial.eval (![a * v 0 + b * v 1, c * v 0 + d * v 1] : Fin 2 → k) := by
  apply MvPolynomial.ringHom_ext
  · intro r
    simp [MvPolynomial.algebraMap_eq]
  · intro i
    fin_cases i <;> simp [substitution, linearForms, MvPolynomial.eval]

private theorem eval_comp_substitution_mulVec {k : Type u} [Field k]
    (M : Matrix (Fin 2) (Fin 2) k) (v : Fin 2 → k) :
    (MvPolynomial.eval v).comp
        (substitution (M 0 0) (M 0 1) (M 1 0) (M 1 1)).toRingHom =
      MvPolynomial.eval (M.mulVec v) := by
  rw [eval_comp_substitution]
  congr 1
  funext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

private theorem mulVec_nonzero_of_det {k : Type u} [Field k]
    (M : Matrix (Fin 2) (Fin 2) k) (hdet : M.det ≠ 0)
    (v : Fin 2 → k) (hv : v ≠ 0) : M.mulVec v ≠ 0 := by
  intro hz
  apply hv
  apply Matrix.mulVec_injective_of_det_ne_zero hdet
  simpa using hz

private theorem eval_smul_homogeneous {k : Type u} [Field k]
    (r : k) (v : Fin 2 → k) {n : ℕ} {f : MvPolynomial (Fin 2) k}
    (hf : f.IsHomogeneous n) :
    MvPolynomial.eval (r • v) f = r ^ n * MvPolynomial.eval v f := by
  induction hf using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => simp
  | add p q hp hq ihp ihq =>
      simp only [map_add, ihp, ihq]
      ring
  | monomial d z hd =>
      rw [MvPolynomial.eval_monomial, MvPolynomial.eval_monomial]
      rw [Finsupp.prod_pow, Finsupp.prod_pow]
      simp_rw [Pi.smul_apply, smul_eq_mul, mul_pow]
      rw [Finset.prod_mul_distrib]
      have hdeg : d.sum (fun _ e => e) = n := by
        simpa [Finsupp.degree_eq_weight_one, Finsupp.weight_apply] using hd
      rw [Fin.prod_univ_two]
      have hsum : d 0 + d 1 = n := by
        simpa [Finsupp.sum_fintype, Fin.sum_univ_two] using hdeg
      rw [← pow_add, hsum]
      ring

private theorem span_scale_eq {k : Type u} [Field k] (r : k) (hr : r ≠ 0)
    (v : Fin 2 → k) :
    Ideal.span ({(r • v) 1 • MvPolynomial.X (0 : Fin 2) -
      (r • v) 0 • MvPolynomial.X (1 : Fin 2)} : Set (MvPolynomial (Fin 2) k)) =
    Ideal.span ({v 1 • MvPolynomial.X (0 : Fin 2) -
      v 0 • MvPolynomial.X (1 : Fin 2)} : Set (MvPolynomial (Fin 2) k)) := by
  let L : MvPolynomial (Fin 2) k :=
    v 1 • MvPolynomial.X (0 : Fin 2) - v 0 • MvPolynomial.X (1 : Fin 2)
  have hgen : (r • v) 1 • MvPolynomial.X (0 : Fin 2) -
      (r • v) 0 • MvPolynomial.X (1 : Fin 2) = MvPolynomial.C r * L := by
    simp [L, Pi.smul_apply, Algebra.smul_def, mul_sub]
    ring
  rw [hgen]
  have hunit : IsUnit (MvPolynomial.C r : MvPolynomial (Fin 2) k) :=
    (isUnit_iff_ne_zero.mpr hr).map MvPolynomial.C
  rw [Ideal.span_singleton_mul_left_unit hunit L]

private theorem ofCoords_scale_eq {k : Type u} [Field k]
    (r : k) (hr : r ≠ 0) (v : Fin 2 → k) (hv : v ≠ 0)
    (hrv : r • v ≠ 0) :
    ProjectiveLine.ofCoords (r • v) hrv = ProjectiveLine.ofCoords v hv := by
  apply ProjectiveSpectrum.ext
  apply HomogeneousIdeal.ext'
  intro n p hp
  change p ∈ Ideal.span ({(r • v) 1 • MvPolynomial.X (0 : Fin 2) -
      (r • v) 0 • MvPolynomial.X (1 : Fin 2)} : Set (MvPolynomial (Fin 2) k)) ↔ _
  change _ ↔ p ∈ Ideal.span ({v 1 • MvPolynomial.X (0 : Fin 2) -
      v 0 • MvPolynomial.X (1 : Fin 2)} : Set (MvPolynomial (Fin 2) k))
  rw [span_scale_eq r hr v]

private theorem ofCoords_mem_basicOpen_iff_eval_general {k : Type u} [Field k]
    (v : Fin 2 → k) (hv : v ≠ 0)
    {n : ℕ} (hn : 0 < n) {f : MvPolynomial (Fin 2) k}
    (hf : f.IsHomogeneous n) :
    (ProjectiveLine.ofCoords v hv : ProjectiveLine k) ∈
        Proj.basicOpen (AlgebraicGeometry.Proj.projectiveGrading k 1) f ↔
      MvPolynomial.eval v f ≠ 0 := by
  have hcoord : v 0 ≠ 0 ∨ v 1 ≠ 0 := by
    by_contra h
    push_neg at h
    apply hv
    funext i
    fin_cases i <;> simp [h.1, h.2]
  rcases hcoord with h0 | h1
  · let r : k := (v 0)⁻¹
    let w : Fin 2 → k := r • v
    have hr : r ≠ 0 := inv_ne_zero h0
    have hw : w ≠ 0 := by
      intro hw
      apply hv
      funext i
      have hi := congrFun hw i
      have hi' : r * v i = 0 := by simpa [w, Pi.smul_apply, Algebra.smul_def] using hi
      exact (mul_eq_zero.mp hi').resolve_left hr
    have hwi : w 0 = 1 := by
      simp [w, r, Pi.smul_apply, Algebra.smul_def, h0]
    have hpoint := ofCoords_scale_eq r hr v hv hw
    have heval := eval_smul_homogeneous r v hf
    rw [← hpoint, ProjectiveLine.ofCoords_mem_basicOpen_iff_eval w hw 0 hwi hn hf,
      heval]
    simp [hr]
  · let r : k := (v 1)⁻¹
    let w : Fin 2 → k := r • v
    have hr : r ≠ 0 := inv_ne_zero h1
    have hw : w ≠ 0 := by
      intro hw
      apply hv
      funext i
      have hi := congrFun hw i
      have hi' : r * v i = 0 := by simpa [w, Pi.smul_apply, Algebra.smul_def] using hi
      exact (mul_eq_zero.mp hi').resolve_left hr
    have hwi : w 1 = 1 := by
      simp [w, r, Pi.smul_apply, Algebra.smul_def, h1]
    have hpoint := ofCoords_scale_eq r hr v hv hw
    have heval := eval_smul_homogeneous r v hf
    rw [← hpoint, ProjectiveLine.ofCoords_mem_basicOpen_iff_eval w hw 1 hwi hn hf,
      heval]
    simp [hr]

private theorem schemeIso_point_ofCoords {k : Type u} [Field k]
    (M : Matrix (Fin 2) (Fin 2) k) (hM : IsUnit M.det)
    (v : Fin 2 → k) (hv : v ≠ 0) :
    (schemeIso (M 0 0) (M 0 1) (M 1 0) (M 1 1) (by
      simpa [Matrix.det_fin_two] using (isUnit_iff_ne_zero.mp hM))).hom.base
        (ProjectiveLine.ofCoords v hv) =
      ProjectiveLine.ofCoords (M.mulVec v)
        (mulVec_nonzero_of_det M (isUnit_iff_ne_zero.mp hM) v hv) := by
  apply AlgebraicGeometry.Proj.ProjectiveLineBasicOpenExt.point_eq_of_pos_homogeneous_basicOpen
  intro n hn f hf
  change (ProjectiveLine.ofCoords v hv : ProjectiveLine k) ∈
      (schemeIso (M 0 0) (M 0 1) (M 1 0) (M 1 1) (by
        simpa [Matrix.det_fin_two] using (isUnit_iff_ne_zero.mp hM))).hom ⁻¹ᵁ
        Proj.basicOpen (projectiveGrading k 1) f ↔ _
  rw [schemeIso_preimage_basicOpen]
  have hfsub :
      (substitution (M 0 0) (M 0 1) (M 1 0) (M 1 1) f).IsHomogeneous n := by
    change (gradedSubstitution (M 0 0) (M 0 1) (M 1 0) (M 1 1)) f ∈
      projectiveGrading k 1 n
    exact (gradedSubstitution (M 0 0) (M 0 1) (M 1 0) (M 1 1)).map_mem hf
  have hleft := ofCoords_mem_basicOpen_iff_eval_general v hv hn hfsub
  have hright := ofCoords_mem_basicOpen_iff_eval_general (M.mulVec v)
      (mulVec_nonzero_of_det M (isUnit_iff_ne_zero.mp hM) v hv) hn hf
  change ((ProjectiveLine.ofCoords v hv : ProjectiveLine k) ∈
      Proj.basicOpen (projectiveGrading k 1)
        (substitution (M 0 0) (M 0 1) (M 1 0) (M 1 1) f)) ↔ _
  rw [hleft]
  change _ ↔ ((ProjectiveLine.ofCoords (M.mulVec v)
      (mulVec_nonzero_of_det M (isUnit_iff_ne_zero.mp hM) v hv) :
      ProjectiveLine k) ∈
      Proj.basicOpen (projectiveGrading k 1) f)
  rw [hright]
  have he := RingHom.congr_fun (eval_comp_substitution_mulVec M v) f
  change (MvPolynomial.eval v)
      (substitution (M 0 0) (M 0 1) (M 1 0) (M 1 1) f) ≠ 0 ↔ _
  have he' : (MvPolynomial.eval v)
      (substitution (M 0 0) (M 0 1) (M 1 0) (M 1 1) f) =
        (MvPolynomial.eval (M.mulVec v)) f := by
    exact he
  rw [he']

private theorem schemeIso_ofCoords {k : Type u} [Field k]
    (M : Matrix (Fin 2) (Fin 2) k) (hM : IsUnit M.det) :
    ∃ g : ProjectiveLine k ≅ ProjectiveLine k,
      g.hom ≫ ProjectiveSpace.toSpecBase 1 k = ProjectiveSpace.toSpecBase 1 k ∧
      ∀ (v : Fin 2 → k) (hv : v ≠ 0), ∃ hMv : M.mulVec v ≠ 0,
        g.hom.base (ProjectiveLine.ofCoords v hv) =
          ProjectiveLine.ofCoords (M.mulVec v) hMv := by
  have hdet : M.det ≠ 0 := isUnit_iff_ne_zero.mp hM
  let g : ProjectiveLine k ≅ ProjectiveLine k :=
    schemeIso (M 0 0) (M 0 1) (M 1 0) (M 1 1)
      (by simpa [Matrix.det_fin_two] using hdet)
  refine ⟨g, ?_, ?_⟩
  · change (schemeIso (M 0 0) (M 0 1) (M 1 0) (M 1 1)
      (by simpa [Matrix.det_fin_two] using hdet)).hom ≫
        ProjectiveSpace.toSpecBase 1 k = ProjectiveSpace.toSpecBase 1 k
    exact schemeIso_hom_over_base _ _ _ _ _
  · intro v hv
    let hMv : M.mulVec v ≠ 0 := mulVec_nonzero_of_det M hdet v hv
    refine ⟨hMv, ?_⟩
    dsimp [g]
    exact schemeIso_point_ofCoords M hM v hv

theorem ProjectiveLine.exists_aut_of_matrix {k : Type u} [Field k]
    (M : Matrix (Fin 2) (Fin 2) k) (hM : IsUnit M.det) :
    ∃ g : ProjectiveLine k ≅ ProjectiveLine k,
      g.hom ≫ ProjectiveSpace.toSpecBase 1 k = ProjectiveSpace.toSpecBase 1 k ∧
      ∀ (v : Fin 2 → k) (hv : v ≠ 0), ∃ hMv : M.mulVec v ≠ 0,
        g.hom.base (ProjectiveLine.ofCoords v hv) =
          ProjectiveLine.ofCoords (M.mulVec v) hMv := by
  exact schemeIso_ofCoords M hM

end
