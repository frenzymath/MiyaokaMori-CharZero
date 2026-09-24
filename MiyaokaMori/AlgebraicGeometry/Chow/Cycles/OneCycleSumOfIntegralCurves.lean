import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.ClosedSubvariety
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.CycleGroup
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.FundamentalClass
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.OneCycle
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.FundamentalClassLemmas
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.SmoothProjectiveVariety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.AlgebraicGeometry.Varieties.Points.ClosedSubvarietyOfPoint
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.IntegralCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietyQcqs
import Mathlib.Data.Fintype.EquivFin
import MiyaokaMori.AlgebraicGeometry.Morphisms.IsProjectiveOverIsProper

/-! # A one-cycle on a proper scheme is a sum of integral curves

A one-cycle on a proper scheme is a finite integer combination of fundamental classes of integral
curves: `Z = Σ_i Z(η_i)·[Γ_i]`, where `η_i` runs over the support of `Z` and `Γ_i` is the closure of
`η_i` (Lazarsfeld, Positivity in Algebraic Geometry I, p. 16, "by linearity one can replace `V` by an
arbitrary `k`-cycle"; used in §4 of the paper).

Proof: `X` is proper over `k`, so the support of `Z` is finite (`properCycle_finiteSupport`). At a
support point `x`, `Z(x) ≠ 0` and `Z ∈ Z_1(X)` give `height x = 1`, i.e. the reduced closure
`ClosedSubvariety.ofPoint x` of `x` is one-dimensional; since `X` is proper it is an integral curve
`Γ_x := IntegralCurve.ofClosedSubvariety`, whose generic point maps back to `x`
(`ClosedSubvariety.genericPt_ofPoint`), so `x ↦ Γ_x` is injective. `[Γ_x]` is the single-point cycle
with coefficient `1` at `x` (`ClosedSubvariety.fundamentalClass_eq_single`), and
`Z = Σ_{x ∈ supp Z} Z(x)·1_x` (`sum_apply_smul_single_eq_self_on_univ`); compare termwise. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

private theorem coe_cast_cycleGroup {k : Type u} [Field k] {X : Variety k}
    {i j : ℕ} (h : i = j) (c : CycleGroup X i) :
    ((cast (congrArg (fun n : ℕ => ↥(CycleGroup X n)) h) c : CycleGroup X j) :
      AlgebraicGeometry.AlgebraicCycle X.toScheme ℤ) = c.1 := by
  cases h
  rfl

open Classical in
private theorem integralCurve_fundamentalClass_eq_single
    {k : Type u} [Field k] {X : SmoothProjectiveVariety k}
    (Γ : IntegralCurve k X.toScheme) :
    (Γ.fundamentalClass : AlgebraicGeometry.AlgebraicCycle X.toScheme ℤ) =
      Function.locallyFinsuppWithin.single
        (Γ.ι.base (genericPoint Γ.carrier)) (1 : ℤ) := by
  unfold IntegralCurve.fundamentalClass
  rw [coe_cast_cycleGroup Γ.dimension_eq_one]
  exact ClosedSubvariety.fundamentalClass_eq_single Γ.toClosedSubvariety

theorem OneCycle.eq_sum_fundamentalClass {k : Type u} [Field k] {X : SmoothProjectiveVariety k}
    (Z : OneCycle X.toVariety) :
    ∃ (s : Finset (IntegralCurve k X.toScheme)),
      Z = ∑ Γ ∈ s, (Z : AlgebraicGeometry.AlgebraicCycle X.toScheme ℤ) (Γ.ι.base (genericPoint Γ.carrier)) •
        Γ.fundamentalClass := by
  classical
  have : AlgebraicGeometry.IsProper X.structureMorphism := IsProjectiveOver.isProper X.projective
  have hX : IsProperOver k X.toScheme := inferInstance
  have hfinite : (Function.support (Z : AlgebraicGeometry.AlgebraicCycle X.toScheme ℤ)).Finite :=
    AlgebraicGeometry.Intersection.properCycle_finiteSupport X.structureMorphism Z.1
  -- the reduced closure of a support point is one-dimensional
  have hdim : ∀ x : Function.support (Z : AlgebraicGeometry.AlgebraicCycle X.toScheme ℤ),
      SchemeIsOneDimensional (ClosedSubvariety.ofPoint (X := X.toVariety) x.1).carrier := by
    intro x
    have hht : Order.height x.1 = (1 : ℕ∞) := Z.2 x.1 x.2
    change topologicalKrullDim (AlgebraicGeometry.Intersection.ReducedPointClosure.scheme X.toScheme x.1) = 1
    rw [AlgebraicGeometry.Intersection.ReducedPointClosure.dimension_eq,
      AlgebraicGeometry.Intersection.pointClosureDimension_eq_height, hht]
    rfl
  let Γ : Function.support (Z : AlgebraicGeometry.AlgebraicCycle X.toScheme ℤ) →
      IntegralCurve k X.toScheme :=
    fun x => IntegralCurve.ofClosedSubvariety hX (ClosedSubvariety.ofPoint x.1) (hdim x)
  have hgen : ∀ x, (Γ x).ι.base (genericPoint (Γ x).carrier) = x.1 :=
    fun x => ClosedSubvariety.genericPt_ofPoint x.1
  have hΓinj : Function.Injective Γ := by
    intro i j hij
    apply Subtype.ext
    rw [← hgen i, ← hgen j, hij]
  letI : Fintype (Function.support (Z : AlgebraicGeometry.AlgebraicCycle X.toScheme ℤ)) :=
    hfinite.fintype
  refine ⟨Finset.univ.image Γ, ?_⟩
  rw [Finset.sum_image (fun i _ j _ hij => hΓinj hij)]
  apply Subtype.ext
  let coeHom : OneCycle X.toVariety →+ AlgebraicGeometry.AlgebraicCycle X.toScheme ℤ :=
    { toFun := fun c => c.1
      map_zero' := rfl
      map_add' := by intro a b; rfl }
  change coeHom Z = coeHom (∑ x : Function.support (Z : AlgebraicGeometry.AlgebraicCycle X.toScheme ℤ),
    (Z : AlgebraicGeometry.AlgebraicCycle X.toScheme ℤ) ((Γ x).ι.base (genericPoint (Γ x).carrier)) •
      (Γ x).fundamentalClass)
  rw [map_sum]
  calc
    coeHom Z = ∑ x ∈ hfinite.toFinset,
        Function.locallyFinsuppWithin.single x ((Z : AlgebraicGeometry.AlgebraicCycle X.toScheme ℤ) x) :=
      (Function.locallyFinsuppWithin.sum_apply_smul_single_eq_self_on_univ hfinite).symm
    _ = ∑ x : Function.support (Z : AlgebraicGeometry.AlgebraicCycle X.toScheme ℤ),
        Function.locallyFinsuppWithin.single x.1 ((Z : AlgebraicGeometry.AlgebraicCycle X.toScheme ℤ) x.1) :=
      Finset.sum_subtype hfinite.toFinset (fun x => hfinite.mem_toFinset)
        (fun x => Function.locallyFinsuppWithin.single x
          ((Z : AlgebraicGeometry.AlgebraicCycle X.toScheme ℤ) x))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      rw [hgen x]
      change Function.locallyFinsuppWithin.single x.1
          ((Z : AlgebraicGeometry.AlgebraicCycle X.toScheme ℤ) x.1) =
        (Z : AlgebraicGeometry.AlgebraicCycle X.toScheme ℤ) x.1 •
          ((Γ x).fundamentalClass : AlgebraicGeometry.AlgebraicCycle X.toScheme ℤ)
      rw [integralCurve_fundamentalClass_eq_single, hgen x]
      apply DFunLike.ext
      intro y
      by_cases hy : y = x.1
      · subst hy
        simp [Function.locallyFinsuppWithin.single_apply]
      · simp [Function.locallyFinsuppWithin.single_apply, hy]

end
