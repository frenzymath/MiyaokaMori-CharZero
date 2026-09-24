import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Base change for exterior powers

The exterior power commutes with extension of scalars along any commutative-ring
algebra `R → S`. The construction uses the alternating universal property and the
degree projection of the exterior algebra, with no freeness, flatness or characteristic
hypotheses. Degree zero is included.

This is the module-level (stalk) algebra behind the comparison of exterior powers with
pullback of sheaves of modules; the sheaf isomorphism itself is constructed elsewhere.
-/

noncomputable section

open scoped TensorProduct

namespace MiyaokaMori.Algebra

universe u v w

variable (R : Type u) (S : Type v) (M : Type w)
variable [CommRing R] [CommRing S] [Algebra R S]
variable [AddCommGroup M] [Module R M]

private def exteriorPowerBaseChangeGenerator (n : ℕ) :
    M [⋀^Fin n]→ₗ[R] ⋀[S]^n (S ⊗[R] M) where
  toFun m := exteriorPower.ιMulti S n ((TensorProduct.mk R S M 1) ∘ m)
  map_update_add' m i x y := by
    simp only [Function.comp_update, map_add, AlternatingMap.map_update_add]
  map_update_smul' m i r x := by
    simp only [Function.comp_update, map_smul]
    exact (exteriorPower.ιMulti S n).toMultilinearMap.toLinearMap
      ((TensorProduct.mk R S M 1) ∘ m) i |>.map_smul_of_tower r ((1 : S) ⊗ₜ[R] x)
  map_eq_zero_of_eq' m i j hij hne :=
    (exteriorPower.ιMulti S n).map_eq_zero_of_eq _
      (congrArg (fun x ↦ (1 : S) ⊗ₜ[R] x) hij) hne

/-- The canonical comparison map, obtained by wedging the scalar-extension unit. -/
def exteriorPowerBaseChangeMap (n : ℕ) :
    S ⊗[R] (⋀[R]^n M) →ₗ[S] ⋀[S]^n (S ⊗[R] M) :=
  (exteriorPower.alternatingMapLinearEquiv
    (exteriorPowerBaseChangeGenerator R S M n)).liftBaseChange S

@[simp]
theorem exteriorPowerBaseChangeMap_tmul_ιMulti (n : ℕ) (s : S) (m : Fin n → M) :
    exteriorPowerBaseChangeMap R S M n (s ⊗ₜ[R] exteriorPower.ιMulti R n m) =
      s • exteriorPower.ιMulti S n (fun i ↦ 1 ⊗ₜ[R] m i) := by
  simp only [exteriorPowerBaseChangeMap, LinearMap.liftBaseChange_tmul,
    exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rfl

private def exteriorBaseChangeVectors :
    S ⊗[R] M →ₗ[S] S ⊗[R] ExteriorAlgebra R M :=
  (ExteriorAlgebra.ι R).baseChange S

private theorem exteriorBaseChangeVectors_anticommute (x y : S ⊗[R] M) :
    exteriorBaseChangeVectors R S M x * exteriorBaseChangeVectors R S M y +
      exteriorBaseChangeVectors R S M y * exteriorBaseChangeVectors R S M x = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s m =>
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul t p =>
          simp only [exteriorBaseChangeVectors, LinearMap.baseChange_tmul,
            Algebra.TensorProduct.tmul_mul_tmul]
          rw [mul_comm t s, ← TensorProduct.tmul_add, ExteriorAlgebra.ι_add_mul_swap,
            TensorProduct.tmul_zero]
      | add x y hx hy =>
          simpa only [map_add, mul_add, add_mul, add_add_add_comm, add_zero] using
            congrArg₂ (· + ·) hx hy
  | add x y hx hy =>
      simpa only [map_add, mul_add, add_mul, add_add_add_comm, add_zero] using
        congrArg₂ (· + ·) hx hy

private theorem exteriorBaseChangeVectors_sq_zero (x : S ⊗[R] M) :
    exteriorBaseChangeVectors R S M x * exteriorBaseChangeVectors R S M x = 0 := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul s m =>
      simp only [exteriorBaseChangeVectors, LinearMap.baseChange_tmul,
        Algebra.TensorProduct.tmul_mul_tmul, ExteriorAlgebra.ι_sq_zero, TensorProduct.tmul_zero]
  | add x y hx hy =>
      rw [map_add, add_mul, mul_add, mul_add, hx, hy, zero_add, add_zero]
      exact exteriorBaseChangeVectors_anticommute R S M x y

private def exteriorAlgebraBaseChangeReverse :
    ExteriorAlgebra S (S ⊗[R] M) →ₐ[S] S ⊗[R] ExteriorAlgebra R M :=
  ExteriorAlgebra.lift S
    ⟨exteriorBaseChangeVectors R S M, exteriorBaseChangeVectors_sq_zero R S M⟩

private theorem exteriorAlgebraBaseChangeReverse_ι (s : S) (m : M) :
    exteriorAlgebraBaseChangeReverse R S M (ExteriorAlgebra.ι S (s ⊗ₜ[R] m)) =
      s ⊗ₜ[R] ExteriorAlgebra.ι R m := by
  exact ExteriorAlgebra.lift_ι_apply _ _ _ _

private theorem exteriorAlgebraBaseChangeReverse_ιMulti (n : ℕ) (m : Fin n → M) :
    exteriorAlgebraBaseChangeReverse R S M
        (ExteriorAlgebra.ιMulti S n (fun i ↦ 1 ⊗ₜ[R] m i)) =
      1 ⊗ₜ[R] ExteriorAlgebra.ιMulti R n m := by
  change exteriorAlgebraBaseChangeReverse R S M
      (ExteriorAlgebra.ιMulti S n (fun i ↦ 1 ⊗ₜ[R] m i)) =
    (Algebra.TensorProduct.includeRight :
      ExteriorAlgebra R M →ₐ[R] S ⊗[R] ExteriorAlgebra R M)
        (ExteriorAlgebra.ιMulti R n m)
  simp only [ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn, Function.comp_def,
    exteriorAlgebraBaseChangeReverse_ι, Algebra.TensorProduct.includeRight_apply]

private def exteriorPowerProjection (n : ℕ) : ExteriorAlgebra R M →ₗ[R] ⋀[R]^n M :=
  ExteriorAlgebra.liftAlternating (Function.update 0 n (exteriorPower.ιMulti R n))

private theorem exteriorPowerProjection_ιMulti (n : ℕ) (m : Fin n → M) :
    exteriorPowerProjection R M n (ExteriorAlgebra.ιMulti R n m) =
      exteriorPower.ιMulti R n m := by
  simp only [exteriorPowerProjection, ExteriorAlgebra.liftAlternating_apply_ιMulti,
    Function.update_self]

/-- The inverse comparison, restricted from the exterior algebra and projected to degree `n`. -/
def exteriorPowerBaseChangeInv (n : ℕ) :
    ⋀[S]^n (S ⊗[R] M) →ₗ[S] S ⊗[R] (⋀[R]^n M) :=
  ((exteriorPowerProjection R M n).baseChange S).comp
    ((exteriorAlgebraBaseChangeReverse R S M).toLinearMap.comp
      (⋀[S]^n (S ⊗[R] M)).subtype)

@[simp]
theorem exteriorPowerBaseChangeInv_ιMulti (n : ℕ) (m : Fin n → M) :
    exteriorPowerBaseChangeInv R S M n
        (exteriorPower.ιMulti S n (fun i ↦ 1 ⊗ₜ[R] m i)) =
      1 ⊗ₜ[R] exteriorPower.ιMulti R n m := by
  simp only [exteriorPowerBaseChangeInv, LinearMap.comp_apply, Submodule.subtype_apply,
    exteriorPower.ιMulti_apply_coe, AlgHom.toLinearMap_apply,
    exteriorAlgebraBaseChangeReverse_ιMulti, LinearMap.baseChange_tmul]
  congr 1
  exact exteriorPowerProjection_ιMulti R M n m

/-- The reverse comparison is a left inverse on all tensors of exterior powers. -/
theorem exteriorPowerBaseChangeInv_comp_map (n : ℕ) :
    (exteriorPowerBaseChangeInv R S M n).comp (exteriorPowerBaseChangeMap R S M n) =
      LinearMap.id := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro s x
  have h :
      (((exteriorPowerBaseChangeInv R S M n).comp
        (exteriorPowerBaseChangeMap R S M n)).restrictScalars R).comp
          (TensorProduct.mk R S (⋀[R]^n M) s) =
        TensorProduct.mk R S (⋀[R]^n M) s := by
    apply exteriorPower.linearMap_ext
    apply AlternatingMap.ext
    intro m
    simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
      LinearMap.coe_restrictScalars, TensorProduct.mk_apply,
      exteriorPowerBaseChangeMap_tmul_ιMulti, map_smul,
      exteriorPowerBaseChangeInv_ιMulti, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  exact DFunLike.congr_fun h x

private theorem baseChangeUnit_span :
    Submodule.span S (Set.range (fun m : M ↦ (1 : S) ⊗ₜ[R] m)) = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro x
  induction x using TensorProduct.induction_on with
  | zero => exact Submodule.zero_mem _
  | tmul s m =>
      have h := Submodule.smul_mem
        (Submodule.span S (Set.range (fun m : M ↦ (1 : S) ⊗ₜ[R] m))) s
        (Submodule.subset_span (Set.mem_range_self m))
      simpa only [TensorProduct.smul_tmul', smul_eq_mul, mul_one] using h
  | add x y hx hy => exact Submodule.add_mem _ hx hy

/-- The two comparisons agree with the identity on wedges of a spanning family. -/
theorem exteriorPowerBaseChangeMap_comp_inv (n : ℕ) :
    (exteriorPowerBaseChangeMap R S M n).comp (exteriorPowerBaseChangeInv R S M n) =
      LinearMap.id := by
  classical
  apply (Submodule.linearMap_eq_iff_of_span_eq_top _ _
    (exteriorPower.ιMulti_span_of_span S n (S ⊗[R] M)
      (baseChangeUnit_span R S M))).2
  rintro ⟨_, ⟨v, hv, rfl⟩⟩
  have h : ∀ i, ∃ m : M, (1 : S) ⊗ₜ[R] m = v i :=
    fun i ↦ hv (Set.mem_range_self i)
  choose m hm using h
  have heq : v = fun i ↦ (1 : S) ⊗ₜ[R] m i := funext fun i ↦ (hm i).symm
  subst v
  simp only [LinearMap.comp_apply, exteriorPowerBaseChangeInv_ιMulti,
    exteriorPowerBaseChangeMap_tmul_ιMulti, one_smul, LinearMap.id_apply]

/-- Exterior powers commute with arbitrary extension of scalars. -/
def exteriorPowerBaseChange (n : ℕ) :
    S ⊗[R] (⋀[R]^n M) ≃ₗ[S] ⋀[S]^n (S ⊗[R] M) :=
  LinearEquiv.ofLinearMap (exteriorPowerBaseChangeMap R S M n)
    (exteriorPowerBaseChangeInv R S M n)
    (exteriorPowerBaseChangeMap_comp_inv R S M n)
    (exteriorPowerBaseChangeInv_comp_map R S M n)

/-- The canonical comparison sends a scalar times a wedge to the pulled-back wedge. -/
@[simp]
theorem exteriorPowerBaseChange_tmul_ιMulti (n : ℕ) (s : S) (m : Fin n → M) :
    exteriorPowerBaseChange R S M n (s ⊗ₜ[R] exteriorPower.ιMulti R n m) =
      s • exteriorPower.ιMulti S n (fun i ↦ 1 ⊗ₜ[R] m i) :=
  exteriorPowerBaseChangeMap_tmul_ιMulti R S M n s m

/-- The wedge formula also specifies the image of the empty wedge when `n = 0`. -/
@[simp]
theorem exteriorPowerBaseChange_one_tmul_ιMulti (n : ℕ) (m : Fin n → M) :
    exteriorPowerBaseChange R S M n (1 ⊗ₜ[R] exteriorPower.ιMulti R n m) =
      exteriorPower.ιMulti S n (fun i ↦ 1 ⊗ₜ[R] m i) := by
  rw [exteriorPowerBaseChange_tmul_ιMulti, one_smul]

end MiyaokaMori.Algebra
