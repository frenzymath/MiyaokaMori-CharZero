import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.DivisorOperator.RatDivisorOpOfCycleClass
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorPowCanonicalIso
import MiyaokaMori.AlgebraicGeometry.Chow.CapTrivialBundleZero
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Chow.DivisorOperator.RatDivisorOperator
import MiyaokaMori.Paper.S2WeightedJets.Intersection.SplitTautologicalClass
import MiyaokaMori.Paper.S2WeightedJets.Intersection.SplitWeightedAlgebraSufficientlyDivisible
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.TwistInvertibleSufficientlyDivisible
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.FirstChernClassTensor
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.FirstChernClassNoIf
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.Stacks01ct

/-! # The class of a coordinate divisor

The first Chern class (as a `ℚ`-divisor operator) of the line bundle `L_{i,q} = O_{Y^sp}(m) ⊗ π_sp^*Q_i^{⊗ m/q}`
carrying the coordinate power section equals `m · H^sp + (m/q) · π_sp^*c_1(Q_i)`; dividing by `m` gives
`H^sp + (1/q) π_sp^*c_1(Q_i)` (proof of Proposition 2.4 of the paper).

Proof: `c_1` is additive on tensor products (`firstChernClass_tensor`; when the structural condition fails,
`firstChernClass_eq_zero_of_not` makes both sides `0`); `π^*(Q_i^{⊗e}) ≅ (π^*Q_i)^{⊗e}` (`pullbackTensorPowIso`),
invariance of `c_1` under isomorphism (`firstChernClass_congr`) and `c_1(O) = 0` (`firstChernClass_one`) give
`e · c_1(π^*Q_i)` by induction; `m • H^sp = c_1(O(m))` is `splitTautologicalClass_eq_of_dvd`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem coordinate_divisor_class {K : Type u} [Field K] {C : SmoothProjectiveCurve K}
    {n kk : ℕ} {E : AlgebraicGeometry.VectorBundle C.toVariety} (F : SubbundleFiltration E (n + 1))
    (i : Fin (n + 1)) (q m : ℕ) (hq : q ∈ Finset.Icc 1 kk) (hqm : q ∣ m) (hm : 0 < m)
    (hdiv : ∀ q' ∈ Finset.Icc 1 kk, q' ∣ m)
    [((AlgebraicGeometry.Scheme.relativeProj.twist (splitWeightedAlgebraOf F kk) (m : ℤ)).tensor
        ((AlgebraicGeometry.Scheme.Modules.pullback (splitWeightedProjectivization F kk).hom).obj
          (AlgebraicGeometry.Scheme.Modules.tensorPow (F.lineQuotient i).toModules (m / q)))).IsLineBundle] :
    AlgebraicGeometry.ratDivisorOpOfLineBundle
        ((AlgebraicGeometry.Scheme.relativeProj.twist (splitWeightedAlgebraOf F kk) (m : ℤ)).tensor
          ((AlgebraicGeometry.Scheme.Modules.pullback (splitWeightedProjectivization F kk).hom).obj
            (AlgebraicGeometry.Scheme.Modules.tensorPow (F.lineQuotient i).toModules (m / q))))
      = (m : ℚ) • ratDivisorOpOfCycleClass (splitTautologicalClass F kk m hm)
        + ((m / q : ℕ) : ℚ) • AlgebraicGeometry.ratDivisorOpOfLineBundle
            ((AlgebraicGeometry.Scheme.Modules.pullback
              (splitWeightedProjectivization F kk).hom).obj (F.lineQuotient i).toModules) := by
  classical
  -- `c_1` is additive on tensor products (both sides are `0` when the structural condition fails)
  have firstChernClass_tensor_any {X : AlgebraicGeometry.Scheme.{u}}
      (L M : X.Modules) [L.IsLineBundle] [M.IsLineBundle]
      [(AlgebraicGeometry.Scheme.Modules.tensor L M).IsLineBundle] (e : ℕ) :
      AlgebraicGeometry.firstChernClass (AlgebraicGeometry.Scheme.Modules.tensor L M) e =
        AlgebraicGeometry.firstChernClass L e + AlgebraicGeometry.firstChernClass M e := by
    by_cases h : ∃ (_ : AlgebraicGeometry.IsLocallyNoetherian X),
        X.IsLocallyOfFiniteTypeOverField
    · obtain ⟨_, ⟨K', hK', π, hπ⟩⟩ := h
      let _ : Field K' := hK'
      let _ : X.Over (AlgebraicGeometry.Spec (CommRingCat.of K')) := ⟨π⟩
      let _ : AlgebraicGeometry.LocallyOfFiniteType
          (X ↘ AlgebraicGeometry.Spec (CommRingCat.of K')) := hπ
      exact AlgebraicGeometry.firstChernClass_tensor (k := K') L M e
    · rw [AlgebraicGeometry.firstChernClass_eq_zero_of_not _ e h,
        AlgebraicGeometry.firstChernClass_eq_zero_of_not L e h,
        AlgebraicGeometry.firstChernClass_eq_zero_of_not M e h, add_zero]
  -- `c_1(L^{⊗n}) = n · c_1(L)`, by induction on `n`
  have firstChernClass_tensorPow {X : AlgebraicGeometry.Scheme.{u}}
      (L : X.Modules) [L.IsLineBundle] (n e : ℕ) :
      AlgebraicGeometry.firstChernClass
          (AlgebraicGeometry.Scheme.Modules.tensorPow L n) (e + 1) =
        n • AlgebraicGeometry.firstChernClass L (e + 1) := by
    induction n with
    | zero =>
        change AlgebraicGeometry.firstChernClass
          (SheafOfModules.unit X.ringCatSheaf) (e + 1) = _
        rw [AlgebraicGeometry.firstChernClass_one]
        simp
    | succ n ih =>
        change AlgebraicGeometry.firstChernClass
            (AlgebraicGeometry.Scheme.Modules.tensor
              (AlgebraicGeometry.Scheme.Modules.tensorPow L n) L) (e + 1) = _
        rw [firstChernClass_tensor_any, ih]
        simp [succ_nsmul]
  -- `ratExtend` commutes with `ℕ`-scalar multiplication and addition
  have ratExtend_nsmul {A B : Type u} [AddCommGroup A] [AddCommGroup B]
      (f : A →+ B) (n : ℕ) :
      (n • f).ratExtend = (n : ℚ) • f.ratExtend := by
    ext x
    simpa [AddMonoidHom.ratExtend] using
      (Nat.cast_smul_eq_nsmul ℚ n ((1 : ℚ) ⊗ₜ[ℤ] f x)).symm
  have ratExtend_add {A B : Type u} [AddCommGroup A] [AddCommGroup B]
      (f g : A →+ B) :
      (f + g).ratExtend = f.ratExtend + g.ratExtend := by
    unfold AddMonoidHom.ratExtend
    rw [show (f + g).toIntLinearMap = f.toIntLinearMap + g.toIntLinearMap from rfl,
      LinearMap.baseChange_add]
  -- notation
  set S := splitWeightedAlgebraOf F kk with hS
  set π := (splitWeightedProjectivization F kk).hom with hπ
  set Q := (F.lineQuotient i).toModules with hQ
  set e := m / q with he
  have hmS : S.SufficientlyDivisible m :=
    splitWeightedAlgebra_sufficientlyDivisible_of_dvd F kk m hm hdiv
  have hOm : (AlgebraicGeometry.Scheme.relativeProj.twist S (m : ℤ)).IsLineBundle :=
    AlgebraicGeometry.Scheme.relativeProj.isLineBundle_twist S m hmS
  have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  funext d
  -- left side: `c_1(O(m) ⊗ π^*(Q^{⊗e})) = c_1(O(m)) + c_1(π^*(Q^{⊗e}))`, and the latter is `e · c_1(π^*Q)`
  have hpull :
      AlgebraicGeometry.firstChernClass
          ((AlgebraicGeometry.Scheme.Modules.pullback π).obj
            (AlgebraicGeometry.Scheme.Modules.tensorPow Q e)) (d + 1) =
        e • AlgebraicGeometry.firstChernClass
          ((AlgebraicGeometry.Scheme.Modules.pullback π).obj Q) (d + 1) := by
    rw [AlgebraicGeometry.firstChernClass_congr _ _
      (AlgebraicGeometry.Scheme.Modules.pullbackTensorPowIso π Q e) d]
    exact firstChernClass_tensorPow _ e d
  have hL :
      AlgebraicGeometry.ratDivisorOpOfLineBundle
        ((AlgebraicGeometry.Scheme.relativeProj.twist S (m : ℤ)).tensor
          ((AlgebraicGeometry.Scheme.Modules.pullback π).obj
            (AlgebraicGeometry.Scheme.Modules.tensorPow Q e))) d =
        AlgebraicGeometry.ratDivisorOpOfLineBundle
          (AlgebraicGeometry.Scheme.relativeProj.twist S (m : ℤ)) d +
        (e : ℚ) • AlgebraicGeometry.ratDivisorOpOfLineBundle
          ((AlgebraicGeometry.Scheme.Modules.pullback π).obj Q) d := by
    change (AlgebraicGeometry.firstChernClass _ (d + 1)).ratExtend =
      (AlgebraicGeometry.firstChernClass
        (AlgebraicGeometry.Scheme.relativeProj.twist S (m : ℤ)) (d + 1)).ratExtend +
      (e : ℚ) • (AlgebraicGeometry.firstChernClass
        ((AlgebraicGeometry.Scheme.Modules.pullback π).obj Q) (d + 1)).ratExtend
    rw [firstChernClass_tensor_any, hpull, ratExtend_add, ratExtend_nsmul]
  -- right side: `m • H^sp = c_1(O(m))` (the comparison lemma of the split tautological class, typed in `ChowGroupRat`)
  have h1 : ratDivisorOpOfCycleClass (splitTautologicalClass F kk m hm) d =
      (m : ℚ)⁻¹ • AlgebraicGeometry.ratDivisorOpOfLineBundle
        (AlgebraicGeometry.Scheme.relativeProj.twist S (m : ℤ)) d :=
    splitTautologicalClass_eq_of_dvd F kk m hm hdiv (d + 1)
  rw [hL, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, h1, smul_smul, mul_inv_cancel₀ hm0, one_smul]

end
