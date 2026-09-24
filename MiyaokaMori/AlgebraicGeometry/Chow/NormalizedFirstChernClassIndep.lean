import MiyaokaMori.Prelude
import MiyaokaMori.Algebra.ChowRatExtend
import MiyaokaMori.AlgebraicGeometry.Chow.CapTrivialBundleZero
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.TwistInvertibleSufficientlyDivisible
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.TwistPowerIso
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.FirstChernClassTensor
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.FirstChernClassNoIf
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.Stacks01ct

/-! # Independence of the normalized first Chern class of the twist

For a graded quasi-coherent algebra `S` over any base scheme `X` and two sufficiently divisible `a`, `b`:
`c_1(O(a))/a = c_1(O(b))/b` (with ℚ-coefficients, as ℚ-linear maps `CH_e(Proj S)_ℚ → CH_{e-1}(Proj S)_ℚ`).
This is the general form of the well-definedness of the rational tautological class `H_k = c_1(B_k)/m` of
Proposition 2.4 of the paper ("replacing it by a multiple leaves the rational tautological
class unchanged"), independent of the origin of `S` (jet algebras and split weighted algebras are special
cases).

Route:
1. `twistPowIso`: `O(a)^{⊗b} ≅ O(ba) = O(ab) ≅ O(b)^{⊗a}`.
2. `firstChernClass_congr` (`c_1` depends only on the isomorphism class) + `firstChernClass_tensorPow`
   (`c_1(L^{⊗n}) = n·c_1(L)`, by induction on `n` from `firstChernClass_tensor` and `firstChernClass_one`):
   `b·c_1(O(a)) = a·c_1(O(b))`.
3. `.ratExtend` is ℚ-linear; divide both sides by `ab`.
In dimension `e = 0`, `firstChernClass _ 0 = 0` (the condition `0 < d` of the definition fails) and both
sides are `0`.

`firstChernClass_tensor` needs "`X` locally of finite type over some field"; this hypothesis is not
assumed here: if it fails, `firstChernClass_eq_zero_of_not` shows that all three terms are `0` and the
identity holds trivially (`firstChernClass_tensor_any`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- `c_1` is additive under tensor products **without** the hypothesis "`X` locally of finite type over a
field": when the condition fails, `firstChernClass` is the zero map (`firstChernClass_eq_zero_of_not`) and
all three terms are `0`; when it holds, extract the field `K` and the structure morphism and apply
`firstChernClass_tensor`. -/
theorem AlgebraicGeometry.firstChernClass_tensor_any {X : AlgebraicGeometry.Scheme.{u}}
    (L M : X.Modules) [L.IsLineBundle] [M.IsLineBundle]
    [(AlgebraicGeometry.Scheme.Modules.tensor L M).IsLineBundle] (e : ℕ) :
    AlgebraicGeometry.firstChernClass (AlgebraicGeometry.Scheme.Modules.tensor L M) e =
      AlgebraicGeometry.firstChernClass L e + AlgebraicGeometry.firstChernClass M e := by
  by_cases h : ∃ (_ : AlgebraicGeometry.IsLocallyNoetherian X),
      X.IsLocallyOfFiniteTypeOverField
  · obtain ⟨_, ⟨K, hK, π, hπ⟩⟩ := h
    let _ : Field K := hK
    let _ : X.Over (AlgebraicGeometry.Spec (CommRingCat.of K)) := ⟨π⟩
    let _ : AlgebraicGeometry.LocallyOfFiniteType
        (X ↘ AlgebraicGeometry.Spec (CommRingCat.of K)) := hπ
    exact AlgebraicGeometry.firstChernClass_tensor (k := K) L M e
  · rw [AlgebraicGeometry.firstChernClass_eq_zero_of_not _ e h,
      AlgebraicGeometry.firstChernClass_eq_zero_of_not L e h,
      AlgebraicGeometry.firstChernClass_eq_zero_of_not M e h, add_zero]

/-- `c_1(L^{⊗n}) = n · c_1(L)` (in dimension `e + 1 ≥ 1`): by induction on `n`; `tensorPow L 0 = O_X` uses
`firstChernClass_one`, and the step `tensorPow L (n+1) = tensorPow L n ⊗ L` uses
`firstChernClass_tensor_any`. -/
theorem AlgebraicGeometry.firstChernClass_tensorPow {X : AlgebraicGeometry.Scheme.{u}}
    (L : X.Modules) [L.IsLineBundle] (n e : ℕ) :
    AlgebraicGeometry.firstChernClass (AlgebraicGeometry.Scheme.Modules.tensorPow L n) (e + 1) =
      n • AlgebraicGeometry.firstChernClass L (e + 1) := by
  induction n with
  | zero =>
      change AlgebraicGeometry.firstChernClass (SheafOfModules.unit X.ringCatSheaf) (e + 1) = _
      rw [AlgebraicGeometry.firstChernClass_one]
      simp
  | succ n ih =>
      change AlgebraicGeometry.firstChernClass
          (AlgebraicGeometry.Scheme.Modules.tensor
            (AlgebraicGeometry.Scheme.Modules.tensorPow L n) L) (e + 1) = _
      rw [AlgebraicGeometry.firstChernClass_tensor_any, ih]
      simp [succ_nsmul]

/-- `ratExtend` commutes with ℕ-multiples: `(n • f).ratExtend = (n : ℚ) • f.ratExtend`. -/
theorem AddMonoidHom.ratExtend_nsmul {A B : Type u} [AddCommGroup A] [AddCommGroup B]
    (f : A →+ B) (n : ℕ) :
    (n • f).ratExtend = (n : ℚ) • f.ratExtend := by
  ext x
  simpa [AddMonoidHom.ratExtend] using
    (Nat.cast_smul_eq_nsmul ℚ n ((1 : ℚ) ⊗ₜ[ℤ] f x)).symm

/-- The `ratExtend` of the zero homomorphism is zero. -/
theorem AddMonoidHom.ratExtend_zero {A B : Type u} [AddCommGroup A] [AddCommGroup B] :
    (0 : A →+ B).ratExtend = 0 := by
  unfold AddMonoidHom.ratExtend
  rw [show (0 : A →+ B).toIntLinearMap = 0 by rfl, LinearMap.baseChange_zero]

/-- The normalized first Chern class is independent of the sufficiently divisible `a`: for two sufficiently
divisible `a`, `b` for `S`, `(1/a)·c_1(O(a)) = (1/b)·c_1(O(b))` (ℚ-coefficients). See the module docstring
for the proof. -/
theorem AlgebraicGeometry.Scheme.relativeProj.normalizedFirstChernClass_indep
    {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) (a b : ℕ) (ha : S.SufficientlyDivisible a)
    (hb : S.SufficientlyDivisible b) (e : ℕ) :
    haveI := AlgebraicGeometry.Scheme.relativeProj.isLineBundle_twist S a ha
    haveI := AlgebraicGeometry.Scheme.relativeProj.isLineBundle_twist S b hb
    (a : ℚ)⁻¹ • (AlgebraicGeometry.firstChernClass
        (AlgebraicGeometry.Scheme.relativeProj.twist S (a : ℤ)) e).ratExtend =
      (b : ℚ)⁻¹ • (AlgebraicGeometry.firstChernClass
        (AlgebraicGeometry.Scheme.relativeProj.twist S (b : ℤ)) e).ratExtend := by
  cases e with
  | zero => simp [AlgebraicGeometry.firstChernClass, AddMonoidHom.ratExtend_zero]
  | succ e =>
      let L := AlgebraicGeometry.Scheme.relativeProj.twist S (a : ℤ)
      let L' := AlgebraicGeometry.Scheme.relativeProj.twist S (b : ℤ)
      have : L.IsLineBundle :=
        AlgebraicGeometry.Scheme.relativeProj.isLineBundle_twist S a ha
      have : L'.IsLineBundle :=
        AlgebraicGeometry.Scheme.relativeProj.isLineBundle_twist S b hb
      have ha0 : (a : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt ha.1
      have hb0 : (b : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hb.1
      have iso : AlgebraicGeometry.Scheme.Modules.tensorPow L b ≅
          AlgebraicGeometry.Scheme.Modules.tensorPow L' a :=
        AlgebraicGeometry.Scheme.relativeProj.twistPowIso S a b ha ≪≫
          CategoryTheory.eqToIso (by simp [Nat.mul_comm]) ≪≫
          (AlgebraicGeometry.Scheme.relativeProj.twistPowIso S b a hb).symm
      have hcross :
          b • AlgebraicGeometry.firstChernClass L (e + 1) =
            a • AlgebraicGeometry.firstChernClass L' (e + 1) := by
        calc
          b • AlgebraicGeometry.firstChernClass L (e + 1) =
              AlgebraicGeometry.firstChernClass
                (AlgebraicGeometry.Scheme.Modules.tensorPow L b) (e + 1) :=
            (AlgebraicGeometry.firstChernClass_tensorPow L b e).symm
          _ = AlgebraicGeometry.firstChernClass
                (AlgebraicGeometry.Scheme.Modules.tensorPow L' a) (e + 1) :=
            AlgebraicGeometry.firstChernClass_congr _ _ iso e
          _ = a • AlgebraicGeometry.firstChernClass L' (e + 1) :=
            AlgebraicGeometry.firstChernClass_tensorPow L' a e
      have hcrossRat :
          (b : ℚ) • (AlgebraicGeometry.firstChernClass L (e + 1)).ratExtend =
            (a : ℚ) • (AlgebraicGeometry.firstChernClass L' (e + 1)).ratExtend := by
        rw [← AddMonoidHom.ratExtend_nsmul, ← AddMonoidHom.ratExtend_nsmul, hcross]
      change (a : ℚ)⁻¹ • (AlgebraicGeometry.firstChernClass L (e + 1)).ratExtend =
        (b : ℚ)⁻¹ • (AlgebraicGeometry.firstChernClass L' (e + 1)).ratExtend
      rw [inv_smul_eq_iff₀ ha0, smul_smul]
      rw [show (a : ℚ) * (b : ℚ)⁻¹ = (b : ℚ)⁻¹ * a by ring, ← smul_smul]
      exact (eq_inv_smul_iff₀ hb0).2 hcrossRat

end
