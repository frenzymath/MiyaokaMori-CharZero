import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.DivisorOperator.ChowGroupRatCongr
import MiyaokaMori.AlgebraicGeometry.Chow.DivisorOperator.RatDivisorOpOfCycleClass
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedQcAlgebraPullback
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierDivisorPullback
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.ClosedSubvariety
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.Paper.S1Intro.TangentBundlePullback
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundle
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundlePullback
import MiyaokaMori.AlgebraicGeometry.Chow.CartierRestriction
import MiyaokaMori.AlgebraicGeometry.Chow.RationalEquivalence.ChowGroupRational
import MiyaokaMori.Paper.S2WeightedJets.Intersection.CoordinateDivisorClass
import MiyaokaMori.Paper.S2WeightedJets.Intersection.CoordinateDivisorsEmptyIntersection
import MiyaokaMori.Paper.S2WeightedJets.Intersection.CoordinatePowerSection
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.FundamentalClassRat
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.IdealSheafToModules
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Chow.DivisorOperator.RatDivisorOpToEnd
import MiyaokaMori.AlgebraicGeometry.Chow.DivisorOperator.RatDivisorOperator
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.SchemeDimension
import MiyaokaMori.Paper.S2WeightedJets.Intersection.SplitTautologicalClass
import MiyaokaMori.Paper.S2WeightedJets.Intersection.SplitWeightedProjectivization
import MiyaokaMori.AlgebraicGeometry.Modules.SubbundleFiltration
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.VarietyDimension
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedPolynomialAlgebraPullback
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundlePullback
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.NefPullback

/-! # The weighted relation

Eq. (2.10) of the paper: `∏_{i=1}^{n+1} ∏_{q=1}^{k} (H^sp + (1/q) · π_sp^*c_1(Q_i)) ∩ [Y^sp] = 0` in
`A_0(Y^sp)_ℚ`. The proof uses only the classes of the coordinate divisors, the emptiness of the intersection of all
their zero schemes, and the support refinement of Gysin maps; no regularity or multiplicities are needed.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

private lemma weighted_relation_of_congr
    {X : AlgebraicGeometry.Scheme.{u}} {p q : ℕ}
    (h : p = q) (α : AlgebraicGeometry.ChowGroupRat X p) :
    DirectSum.of _ p α = DirectSum.of _ q
      (AlgebraicGeometry.ChowGroupRat.congr X h α) := by
  cases h
  rfl

private lemma weighted_relation_capList_toEnd
    {X : AlgebraicGeometry.Scheme.{u}}
    (l : List (AlgebraicGeometry.RatDivisorOp X)) (d : ℕ)
    (α : AlgebraicGeometry.ChowGroupRat X (d + l.length)) :
    DirectSum.of _ d (AlgebraicGeometry.RatDivisorOp.capList l d α) =
      ((l.reverse.map (AlgebraicGeometry.RatDivisorOp.toEnd)).prod)
        (DirectSum.of _ (d + l.length) α) := by
  induction l with
  | nil =>
      simp [AlgebraicGeometry.RatDivisorOp.capList]
  | cons A l ih =>
      simp only [AlgebraicGeometry.RatDivisorOp.capList, LinearMap.comp_apply,
        List.length_cons]
      have ih' := ih (A (d + l.length) α)
      rw [ih']
      rw [← AlgebraicGeometry.RatDivisorOp.toEnd_of A (d + l.length) α]
      simp only [List.reverse_cons, List.map_append, List.map_singleton,
        List.prod_append, List.prod_singleton, Module.End.mul_apply, mul_one]
      rfl

private lemma weighted_relation_list_prod_smul
    {N : Type u} [AddCommMonoid N] [Module ℚ N]
    (l : List (Module.End ℚ N)) (c : ℚ) :
    (l.map (fun A => c • A)).prod = c ^ l.length • l.prod := by
  induction l with
  | nil => simp
  | cons A l ih =>
      simp only [List.map_cons, List.prod_cons, List.length_cons]
      rw [ih, pow_succ]
      change (c • A) ∘ₗ (c ^ l.length • l.prod) =
        (c ^ l.length * c) • (A ∘ₗ l.prod)
      calc
        (c • A) ∘ₗ (c ^ l.length • l.prod) =
            c • (A ∘ₗ (c ^ l.length • l.prod)) := by
              exact LinearMap.smul_comp _ _ _
        _ = c • (c ^ l.length • (A * l.prod)) := by
          congr 1
          exact LinearMap.comp_smul _ _ _
        _ = (c * c ^ l.length) • (A ∘ₗ l.prod) := by
          rw [smul_smul]
          rfl
        _ = (c ^ l.length * c) • (A ∘ₗ l.prod) := by rw [mul_comm]

private lemma weighted_relation_toEnd_smul
    {X : AlgebraicGeometry.Scheme.{u}}
    (c : ℚ) (D : AlgebraicGeometry.RatDivisorOp X) :
    AlgebraicGeometry.RatDivisorOp.toEnd (c • D) =
      c • AlgebraicGeometry.RatDivisorOp.toEnd D := by
  exact AlgebraicGeometry.RatDivisorOp.toEnd.map_smul c D

private theorem weighted_relation_capProd_smul
    {X : AlgebraicGeometry.Scheme.{u}}
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (D : ι → AlgebraicGeometry.RatDivisorOp X) (c : ℚ) (d : ℕ) :
    AlgebraicGeometry.RatDivisorOp.capProd (fun i => c • D i) d =
      c ^ Fintype.card ι • AlgebraicGeometry.RatDivisorOp.capProd D d := by
  apply LinearMap.ext
  intro α
  let b : List ι := (Finset.univ : Finset ι).toList
  let l : List (AlgebraicGeometry.RatDivisorOp X) := b.map D
  let l' : List (AlgebraicGeometry.RatDivisorOp X) := b.map (fun i => c • D i)
  have hb : b.length = Fintype.card ι := by simp [b]
  have hl : l.length = Fintype.card ι := by simp [l, b]
  have hl' : l'.length = Fintype.card ι := by simp [l', b]
  have hscaled : l'.reverse.map AlgebraicGeometry.RatDivisorOp.toEnd =
      (l.reverse.map AlgebraicGeometry.RatDivisorOp.toEnd).map (fun A => c • A) := by
    simp [l', l, b, List.map_reverse, List.map_map, Function.comp_def,
      weighted_relation_toEnd_smul]
  have hleft := weighted_relation_capList_toEnd l' d
      (AlgebraicGeometry.ChowGroupRat.congr X (by simp [hl']) α)
  have hright := weighted_relation_capList_toEnd l d
      (AlgebraicGeometry.ChowGroupRat.congr X (by simp [hl]) α)
  have hinleft : DirectSum.of _ (d + l'.length)
      (AlgebraicGeometry.ChowGroupRat.congr X (by simp [hl']) α) =
      DirectSum.of _ (d + Fintype.card ι) α := by
    symm
    exact weighted_relation_of_congr (by simp [hl']) α
  have hinright : DirectSum.of _ (d + l.length)
      (AlgebraicGeometry.ChowGroupRat.congr X (by simp [hl]) α) =
      DirectSum.of _ (d + Fintype.card ι) α := by
    symm
    exact weighted_relation_of_congr (by simp [hl]) α
  have hprod := weighted_relation_list_prod_smul
      (l.reverse.map AlgebraicGeometry.RatDivisorOp.toEnd) c
  have hright' :
      DirectSum.of _ d (AlgebraicGeometry.RatDivisorOp.capProd D d α) =
        (l.reverse.map AlgebraicGeometry.RatDivisorOp.toEnd).prod
          (DirectSum.of _ (d + Fintype.card ι) α) := by
    unfold AlgebraicGeometry.RatDivisorOp.capProd
    change DirectSum.of _ d (AlgebraicGeometry.RatDivisorOp.capList l d
      (AlgebraicGeometry.ChowGroupRat.congr X (by simp [hl]) α)) = _
    rw [hright]
    rw [hinright]
  have hout : DirectSum.of _ d
      (AlgebraicGeometry.RatDivisorOp.capProd (fun i => c • D i) d α) =
      c ^ Fintype.card ι • DirectSum.of _ d
        (AlgebraicGeometry.RatDivisorOp.capProd D d α) := by
    change DirectSum.of _ d (AlgebraicGeometry.RatDivisorOp.capList l' d
      (AlgebraicGeometry.ChowGroupRat.congr X (by simp [hl']) α)) =
      c ^ Fintype.card ι • DirectSum.of _ d
        (AlgebraicGeometry.RatDivisorOp.capProd D d α)
    rw [hleft, hscaled, hprod]
    rw [hinleft]
    have hlenrev : (l.reverse.map AlgebraicGeometry.RatDivisorOp.toEnd).length =
        Fintype.card ι := by simp [l, b]
    rw [hlenrev]
    simp only [LinearMap.smul_apply]
    rw [hright']
  apply DirectSum.of_injective _
  change _ = DirectSum.of _ d (c ^ Fintype.card ι •
    AlgebraicGeometry.RatDivisorOp.capProd D d α)
  rw [← DirectSum.lof_eq_of ℚ ℕ
    (fun j => AlgebraicGeometry.ChowGroupRat X j) d]
  rw [← DirectSum.lof_eq_of ℚ ℕ
    (fun j => AlgebraicGeometry.ChowGroupRat X j) d]
  rw [map_smul]
  exact hout

theorem weighted_relation {K : Type u} [Field K] {C : SmoothProjectiveCurve K}
    {n kk : ℕ} (hkk : 1 ≤ kk) {E : AlgebraicGeometry.VectorBundle C.toVariety}
    (F : SubbundleFiltration E (n + 1)) (m : ℕ) (hm : 0 < m)
    (hdiv : ∀ q ∈ Finset.Icc 1 kk, q ∣ m)
    [AlgebraicGeometry.IsIntegral (splitWeightedProjectivization F kk).left]
    (hdim : (splitWeightedProjectivization F kk).left.dimension = (n + 1) * kk) :
    AlgebraicGeometry.RatDivisorOp.capProd
        (fun p : Fin (n + 1) × Fin kk =>
          ratDivisorOpOfCycleClass (splitTautologicalClass F kk m hm)
            + (((p.2 : ℕ) + 1 : ℚ))⁻¹ • AlgebraicGeometry.ratDivisorOpOfLineBundle
                ((AlgebraicGeometry.Scheme.Modules.pullback
                  (splitWeightedProjectivization F kk).hom).obj
                    (F.lineQuotient p.1).toModules))
        0 (AlgebraicGeometry.ChowGroupRat.congr (splitWeightedProjectivization F kk).left
            (by simp : (n + 1) * kk = 0 + Fintype.card (Fin (n + 1) × Fin kk))
          (AlgebraicGeometry.fundamentalClassRat
            (splitWeightedProjectivization F kk).left ((n + 1) * kk) hdim))
      = 0 := by
  let X := (splitWeightedProjectivization F kk).left
  let ι := Fin (n + 1) × Fin kk
  let L : ι → X.Modules := fun p =>
    (AlgebraicGeometry.Scheme.relativeProj.twist
      (splitWeightedAlgebraOf F kk) (m : ℤ)).tensor
        ((AlgebraicGeometry.Scheme.Modules.pullback
          (splitWeightedProjectivization F kk).hom).obj
            (AlgebraicGeometry.Scheme.Modules.tensorPow
              (F.lineQuotient p.1).toModules (m / ((p.2 : ℕ) + 1))))
  letI : ∀ p, (L p).IsLineBundle := fun p =>
    coordPowSection_isLineBundle F m hm hdiv p
  have hfactor : ∀ p : ι,
      ratDivisorOpOfCycleClass (splitTautologicalClass F kk m hm)
          + (((p.2 : ℕ) + 1 : ℚ))⁻¹ • AlgebraicGeometry.ratDivisorOpOfLineBundle
              ((AlgebraicGeometry.Scheme.Modules.pullback
                (splitWeightedProjectivization F kk).hom).obj
                  (F.lineQuotient p.1).toModules) =
        (m : ℚ)⁻¹ • AlgebraicGeometry.ratDivisorOpOfLineBundle (L p) := by
    intro p
    have hq : (p.2 : ℕ) + 1 ∈ Finset.Icc 1 kk := by
      simp only [Finset.mem_Icc]
      omega
    have hqm : (p.2 : ℕ) + 1 ∣ m := hdiv _ hq
    have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
    have hqQ : (((p.2 : ℕ) + 1 : ℚ)) ≠ 0 := by positivity
    have hquot : (((m / ((p.2 : ℕ) + 1) : ℕ) : ℚ)) =
        (m : ℚ) / (((p.2 : ℕ) + 1 : ℚ)) := by
      simpa only [Nat.cast_add, Nat.cast_one] using Nat.cast_div hqm (by simpa using hqQ)
    rw [coordinate_divisor_class F p.1 ((p.2 : ℕ) + 1) m hq hqm hm hdiv]
    change _ = (m : ℚ)⁻¹ • (_ + _)
    simp only [smul_add, smul_smul]
    rw [inv_mul_cancel₀ hmQ, one_smul, hquot]
    field_simp
  have hfun :
      (fun p : ι =>
        ratDivisorOpOfCycleClass (splitTautologicalClass F kk m hm)
          + (((p.2 : ℕ) + 1 : ℚ))⁻¹ • AlgebraicGeometry.ratDivisorOpOfLineBundle
              ((AlgebraicGeometry.Scheme.Modules.pullback
                (splitWeightedProjectivization F kk).hom).obj
                  (F.lineQuotient p.1).toModules)) =
      fun p => (m : ℚ)⁻¹ • AlgebraicGeometry.ratDivisorOpOfLineBundle (L p) :=
    funext hfactor
  rw [hfun]
  rw [weighted_relation_capProd_smul]
  letI : Nonempty ι := ⟨(⟨0, by omega⟩, ⟨0, by omega⟩)⟩
  have hzero : AlgebraicGeometry.RatDivisorOp.capProd
      (fun p : ι => AlgebraicGeometry.ratDivisorOpOfLineBundle (L p)) 0 = 0 := by
    apply AlgebraicGeometry.RatDivisorOp.capProd_eq_zero_of_iInter_support_empty
      L (fun p => coordPowSection F m hdiv p)
    exact splitWeightedCoord_iInter_support_empty hkk F m hm hdiv
  rw [hzero]
  simp

end
