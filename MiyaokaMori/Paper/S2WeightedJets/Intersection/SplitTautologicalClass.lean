import MiyaokaMori.Prelude
import MiyaokaMori.Algebra.ChowRatExtend
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.ClosedSubvariety
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundle
import MiyaokaMori.AlgebraicGeometry.Chow.CapTrivialBundleZero
import MiyaokaMori.AlgebraicGeometry.Chow.RationalEquivalence.ChowGroupRational
import MiyaokaMori.AlgebraicGeometry.Chow.FirstChernClass
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.RelativeProjTwistQC
import MiyaokaMori.Paper.S2WeightedJets.Intersection.SplitWeightedAlgebra
import MiyaokaMori.Paper.S2WeightedJets.Intersection.SplitWeightedAlgebraSufficientlyDivisible
import MiyaokaMori.Paper.S2WeightedJets.Intersection.SplitWeightedProjectivization
import MiyaokaMori.AlgebraicGeometry.Modules.SubbundleFiltration
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.TwistPowerIso
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.WeightedSymAlgebra
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.FirstChernClassTensor
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.Stacks01ms

/-! # The split tautological class

`H^sp = c_1(O_{Y^sp}(m))/m` (Lemma 2.3 of the paper).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

noncomputable def splitTautologicalClass {k : Type u} [Field k]
    {C : SmoothProjectiveCurve k} {r : ℕ} {E : AlgebraicGeometry.VectorBundle C.toVariety}
    (F : SubbundleFiltration E r) (jetOrder m : ℕ) (hm : 0 < m) (d : ℕ) :
    AlgebraicGeometry.ChowGroupRat (splitWeightedProjectivization F jetOrder).left d →ₗ[ℚ]
      AlgebraicGeometry.ChowGroupRat (splitWeightedProjectivization F jetOrder).left (d - 1) :=
  -- take `M := m · jetOrder!`: every weight `1..jetOrder` divides `M`, so `O(M)` is always a line bundle (locally
  -- it is `O(M)` on `U × P(w)`, generated on `D_+(x_{i,q})` by `x_{i,q}^{M/q}`), and the `else` branch below is
  -- never taken; when `O(m)` is invertible (downstream `hdiv : ∀ q ∈ Icc 1 jetOrder, q ∣ m`) we have
  -- `O(M) ≅ O(m)^{⊗ jetOrder!}`, hence `c_1(O(M))/M = c_1(O(m))/m`, in agreement with the paper's
  -- `H^sp = c_1(O(m))/m`
  let M : ℕ := m * jetOrder.factorial
  open Classical in
  if h : (AlgebraicGeometry.Scheme.relativeProj.twist (splitWeightedAlgebraOf F jetOrder) (M : ℤ)).IsLineBundle then
    haveI := h
    (M : ℚ)⁻¹ • (AlgebraicGeometry.firstChernClass
      (AlgebraicGeometry.Scheme.relativeProj.twist (splitWeightedAlgebraOf F jetOrder) (M : ℤ)) d).ratExtend
  else 0

/-- Agreement with the paper's `H^sp = c_1(O(m))/m` (§2: `O(m)` is used only for sufficiently divisible `m`):
when `m` is divisible by all weights `1..jetOrder` and `O(m)` is a line bundle, the `c_1(O(M))/M` of the definition
(`M = m · jetOrder!`) equals `c_1(O(m))/m`. Argument: `O(M) ≅ O(m)^{⊗ jetOrder!}` (`twistPowIso`), `c_1` is
additive on tensor powers, divide both sides by `M`. -/

theorem splitTautologicalClass_eq_of_dvd {k : Type u} [Field k]
    {C : SmoothProjectiveCurve k} {r : ℕ} {E : AlgebraicGeometry.VectorBundle C.toVariety}
    (F : SubbundleFiltration E r) (jetOrder m : ℕ) (hm : 0 < m)
    (hdiv : ∀ q ∈ Finset.Icc 1 jetOrder, q ∣ m)
    [(AlgebraicGeometry.Scheme.relativeProj.twist (splitWeightedAlgebraOf F jetOrder) (m : ℤ)).IsLineBundle] (d : ℕ) :
    splitTautologicalClass F jetOrder m hm d =
      (m : ℚ)⁻¹ • (AlgebraicGeometry.firstChernClass
        (AlgebraicGeometry.Scheme.relativeProj.twist (splitWeightedAlgebraOf F jetOrder) (m : ℤ)) d).ratExtend := by
  classical
  have firstChernClass_tensor_any {X : AlgebraicGeometry.Scheme.{u}}
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
  have ratExtend_nsmul {A B : Type u} [AddCommGroup A] [AddCommGroup B]
      (f : A →+ B) (n : ℕ) :
      (n • f).ratExtend = (n : ℚ) • f.ratExtend := by
    ext x
    simpa [AddMonoidHom.ratExtend] using
      (Nat.cast_smul_eq_nsmul ℚ n ((1 : ℚ) ⊗ₜ[ℤ] f x)).symm
  have ratExtend_zero {A B : Type u} [AddCommGroup A] [AddCommGroup B] :
      (0 : A →+ B).ratExtend = 0 := by
    unfold AddMonoidHom.ratExtend
    rw [show (0 : A →+ B).toIntLinearMap = 0 by rfl, LinearMap.baseChange_zero]
  have normalizedFirstChernClass_indep {X : AlgebraicGeometry.Scheme.{u}}
      (S : X.GradedQCAlgebra) (a b : ℕ) (ha : S.SufficientlyDivisible a)
      (hb : S.SufficientlyDivisible b) (e : ℕ) :
      haveI := AlgebraicGeometry.Scheme.relativeProj.isLineBundle_twist S a ha
      haveI := AlgebraicGeometry.Scheme.relativeProj.isLineBundle_twist S b hb
      (a : ℚ)⁻¹ • (AlgebraicGeometry.firstChernClass
          (AlgebraicGeometry.Scheme.relativeProj.twist S (a : ℤ)) e).ratExtend =
        (b : ℚ)⁻¹ • (AlgebraicGeometry.firstChernClass
          (AlgebraicGeometry.Scheme.relativeProj.twist S (b : ℤ)) e).ratExtend := by
    cases e with
    | zero => simp [AlgebraicGeometry.firstChernClass, ratExtend_zero]
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
              (firstChernClass_tensorPow L b e).symm
            _ = AlgebraicGeometry.firstChernClass
                  (AlgebraicGeometry.Scheme.Modules.tensorPow L' a) (e + 1) :=
              AlgebraicGeometry.firstChernClass_congr _ _ iso e
            _ = a • AlgebraicGeometry.firstChernClass L' (e + 1) :=
              firstChernClass_tensorPow L' a e
        have hcrossRat :
            (b : ℚ) • (AlgebraicGeometry.firstChernClass L (e + 1)).ratExtend =
              (a : ℚ) • (AlgebraicGeometry.firstChernClass L' (e + 1)).ratExtend := by
          rw [← ratExtend_nsmul, ← ratExtend_nsmul, hcross]
        change (a : ℚ)⁻¹ • (AlgebraicGeometry.firstChernClass L (e + 1)).ratExtend =
          (b : ℚ)⁻¹ • (AlgebraicGeometry.firstChernClass L' (e + 1)).ratExtend
        rw [inv_smul_eq_iff₀ ha0, smul_smul]
        rw [show (a : ℚ) * (b : ℚ)⁻¹ = (b : ℚ)⁻¹ * a by ring, ← smul_smul]
        exact (eq_inv_smul_iff₀ hb0).2 hcrossRat
  let S := splitWeightedAlgebraOf F jetOrder
  let M := m * jetOrder.factorial
  have hMpos : 0 < M := Nat.mul_pos hm (Nat.factorial_pos _)
  have hMdiv : ∀ q ∈ Finset.Icc 1 jetOrder, q ∣ M := by
    intro q hq
    exact dvd_mul_of_dvd_left (hdiv q hq) _
  have hmS : S.SufficientlyDivisible m :=
    splitWeightedAlgebra_sufficientlyDivisible_of_dvd F jetOrder m hm hdiv
  have hMS : S.SufficientlyDivisible M :=
    splitWeightedAlgebra_sufficientlyDivisible_of_dvd F jetOrder M hMpos hMdiv
  have hML : (AlgebraicGeometry.Scheme.relativeProj.twist S (M : ℤ)).IsLineBundle :=
    AlgebraicGeometry.Scheme.relativeProj.isLineBundle_twist S M hMS
  unfold splitTautologicalClass
  dsimp only
  change (if h : (AlgebraicGeometry.Scheme.relativeProj.twist S (M : ℤ)).IsLineBundle then
      haveI := h
      (M : ℚ)⁻¹ • (AlgebraicGeometry.firstChernClass
        (AlgebraicGeometry.Scheme.relativeProj.twist S (M : ℤ)) d).ratExtend
    else 0) = _
  rw [dif_pos hML]
  exact normalizedFirstChernClass_indep S M m hMS hmS d

/-- `H^sp` is independent of `m` (the well-definedness implicit in "define `H_k` by dividing its first Chern class
by `m`", §2 of the paper): for any positive `m`, `m'`, both `M = m · jetOrder!` and `M' = m' · jetOrder!` are
sufficiently divisible and `c_1(O(M))/M = c_1(O(M'))/M'`. -/

theorem splitTautologicalClass_indep {k : Type u} [Field k]
    {C : SmoothProjectiveCurve k} {r : ℕ} {E : AlgebraicGeometry.VectorBundle C.toVariety}
    (F : SubbundleFiltration E r) (jetOrder m m' : ℕ) (hm : 0 < m) (hm' : 0 < m') (d : ℕ) :
    splitTautologicalClass F jetOrder m hm d = splitTautologicalClass F jetOrder m' hm' d := by
  classical
  have firstChernClass_tensor_any {X : AlgebraicGeometry.Scheme.{u}}
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
  have ratExtend_nsmul {A B : Type u} [AddCommGroup A] [AddCommGroup B]
      (f : A →+ B) (n : ℕ) :
      (n • f).ratExtend = (n : ℚ) • f.ratExtend := by
    ext x
    simpa [AddMonoidHom.ratExtend] using
      (Nat.cast_smul_eq_nsmul ℚ n ((1 : ℚ) ⊗ₜ[ℤ] f x)).symm
  have ratExtend_zero {A B : Type u} [AddCommGroup A] [AddCommGroup B] :
      (0 : A →+ B).ratExtend = 0 := by
    unfold AddMonoidHom.ratExtend
    rw [show (0 : A →+ B).toIntLinearMap = 0 by rfl, LinearMap.baseChange_zero]
  have normalizedFirstChernClass_indep {X : AlgebraicGeometry.Scheme.{u}}
      (S : X.GradedQCAlgebra) (a b : ℕ) (ha : S.SufficientlyDivisible a)
      (hb : S.SufficientlyDivisible b) (e : ℕ) :
      haveI := AlgebraicGeometry.Scheme.relativeProj.isLineBundle_twist S a ha
      haveI := AlgebraicGeometry.Scheme.relativeProj.isLineBundle_twist S b hb
      (a : ℚ)⁻¹ • (AlgebraicGeometry.firstChernClass
          (AlgebraicGeometry.Scheme.relativeProj.twist S (a : ℤ)) e).ratExtend =
        (b : ℚ)⁻¹ • (AlgebraicGeometry.firstChernClass
          (AlgebraicGeometry.Scheme.relativeProj.twist S (b : ℤ)) e).ratExtend := by
    cases e with
    | zero => simp [AlgebraicGeometry.firstChernClass, ratExtend_zero]
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
              (firstChernClass_tensorPow L b e).symm
            _ = AlgebraicGeometry.firstChernClass
                  (AlgebraicGeometry.Scheme.Modules.tensorPow L' a) (e + 1) :=
              AlgebraicGeometry.firstChernClass_congr _ _ iso e
            _ = a • AlgebraicGeometry.firstChernClass L' (e + 1) :=
              firstChernClass_tensorPow L' a e
        have hcrossRat :
            (b : ℚ) • (AlgebraicGeometry.firstChernClass L (e + 1)).ratExtend =
              (a : ℚ) • (AlgebraicGeometry.firstChernClass L' (e + 1)).ratExtend := by
          rw [← ratExtend_nsmul, ← ratExtend_nsmul, hcross]
        change (a : ℚ)⁻¹ • (AlgebraicGeometry.firstChernClass L (e + 1)).ratExtend =
          (b : ℚ)⁻¹ • (AlgebraicGeometry.firstChernClass L' (e + 1)).ratExtend
        rw [inv_smul_eq_iff₀ ha0, smul_smul]
        rw [show (a : ℚ) * (b : ℚ)⁻¹ = (b : ℚ)⁻¹ * a by ring, ← smul_smul]
        exact (eq_inv_smul_iff₀ hb0).2 hcrossRat
  let S := splitWeightedAlgebraOf F jetOrder
  let M := m * jetOrder.factorial
  let M' := m' * jetOrder.factorial
  have hMpos : 0 < M := Nat.mul_pos hm (Nat.factorial_pos _)
  have hMpos' : 0 < M' := Nat.mul_pos hm' (Nat.factorial_pos _)
  have hMdiv : ∀ q ∈ Finset.Icc 1 jetOrder, q ∣ M := by
    intro q hq
    exact dvd_mul_of_dvd_right (Nat.dvd_factorial (Finset.mem_Icc.mp hq).1
      (Finset.mem_Icc.mp hq).2) _
  have hMdiv' : ∀ q ∈ Finset.Icc 1 jetOrder, q ∣ M' := by
    intro q hq
    exact dvd_mul_of_dvd_right (Nat.dvd_factorial (Finset.mem_Icc.mp hq).1
      (Finset.mem_Icc.mp hq).2) _
  have hMS : S.SufficientlyDivisible M :=
    splitWeightedAlgebra_sufficientlyDivisible_of_dvd F jetOrder M hMpos hMdiv
  have hMS' : S.SufficientlyDivisible M' :=
    splitWeightedAlgebra_sufficientlyDivisible_of_dvd F jetOrder M' hMpos' hMdiv'
  have hML : (AlgebraicGeometry.Scheme.relativeProj.twist S (M : ℤ)).IsLineBundle :=
    AlgebraicGeometry.Scheme.relativeProj.isLineBundle_twist S M hMS
  have hML' : (AlgebraicGeometry.Scheme.relativeProj.twist S (M' : ℤ)).IsLineBundle :=
    AlgebraicGeometry.Scheme.relativeProj.isLineBundle_twist S M' hMS'
  unfold splitTautologicalClass
  dsimp only
  change (if h : (AlgebraicGeometry.Scheme.relativeProj.twist S (M : ℤ)).IsLineBundle then
      haveI := h
      (M : ℚ)⁻¹ • (AlgebraicGeometry.firstChernClass
        (AlgebraicGeometry.Scheme.relativeProj.twist S (M : ℤ)) d).ratExtend
    else 0) =
    (if h : (AlgebraicGeometry.Scheme.relativeProj.twist S (M' : ℤ)).IsLineBundle then
      haveI := h
      (M' : ℚ)⁻¹ • (AlgebraicGeometry.firstChernClass
        (AlgebraicGeometry.Scheme.relativeProj.twist S (M' : ℤ)) d).ratExtend
    else 0)
  rw [dif_pos hML, dif_pos hML']
  exact normalizedFirstChernClass_indep S M M' hMS hMS' d

end
