import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.CurveStalkDVR
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModuleSheafStalk
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierDivisor
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierDivisorLocalData
import MiyaokaMori.AlgebraicGeometry.Divisors.Weil.CartierWeilIso
import MiyaokaMori.AlgebraicGeometry.Varieties.Points.ClosedPoint
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.ClosedSubvariety
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.CurveDivisorDegree
import MiyaokaMori.AlgebraicGeometry.Divisors.Weil.Divisor
import MiyaokaMori.AlgebraicGeometry.Divisors.Weil.PrimeDivisor
import MiyaokaMori.AlgebraicGeometry.Divisors.OrderOfVanishing.PrincipalDivisorFiniteness
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Divisors.Weil.CartierToWeil
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.FundamentalClass
import MiyaokaMori.AlgebraicGeometry.Varieties.FunctionField.AffineResidueFieldBase
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ZeroCycleDegreePushforward
import MiyaokaMori.AlgebraicGeometry.Morphisms.IsProjectiveOverIsProper
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.CurveAsSmoothProjectiveVariety

/-! # The point divisor on a smooth projective curve

The Cartier divisor `[y]` of a closed point `y` of a smooth projective curve, used for the fibre
`π_S^*(y)` in the proof of Lemma 5.1 of the paper.

`Divisor.ofPoint y` is defined canonically: the inverse of the Cartier–Weil isomorphism
`cartierWeilEquiv` (Hartshorne II.6.11) applied to the Weil divisor `1·[y]`; no local data are
chosen. Its Weil cycle is `1_{x = y}` (`ofPoint_weilCycle`), and its degree over an algebraically
closed field is `1` (`ofPoint_degree`). At a non-closed point (the generic point) the divisor is `0`,
so that `Divisor.ofPoint y` can be used without a closedness proof.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
open AlgebraicGeometry
open Classical

noncomputable section

/-- A closed point of a smooth projective curve is a prime divisor (coheight `1`):
`SmoothProjectiveCurve.coheight_eq_one_of_isClosed`. -/
theorem SmoothProjectiveCurve.isPrimeDivisor_of_isClosed {k : Type u} [Field k]
    (C : SmoothProjectiveCurve k) (y : C.toScheme) (hy : IsClosed ({y} : Set C.toScheme)) :
    C.toScheme.IsPrimeDivisor y :=
  C.coheight_eq_one_of_isClosed y hy

open Classical in

/-- The Cartier divisor `[y]` of a closed point `y`: the inverse of the Cartier–Weil isomorphism
`cartierWeilEquiv` (`CDiv ≅ Div` on a smooth variety, Hartshorne II.6.11) applied to the Weil divisor
`1·[y]` (`FreeAbelianGroup.of ⟨y, _⟩`; `y` is a prime divisor since a closed point has coheight `1`).
When `y` is not closed (i.e. is the generic point of `C`) the divisor is `0`, so that `Divisor.ofPoint y`
can be written without a closedness proof. -/
noncomputable def Divisor.ofPoint {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (y : C.toScheme) : CartierDivisor C.toVariety :=
  if hy : IsClosed ({y} : Set C.toScheme) then
    (cartierWeilEquiv C.toSmoothProjectiveVariety).symm
      (FreeAbelianGroup.of ⟨y, C.isPrimeDivisor_of_isClosed y hy⟩)
  else 0

/-- The point divisor of a non-closed point is `0`. -/
theorem Divisor.ofPoint_of_not_isClosed {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (y : C.toScheme) (hy : ¬ IsClosed ({y} : Set C.toScheme)) : Divisor.ofPoint y = 0 := by
  simp [Divisor.ofPoint, hy]

open Classical in

/-- The Weil cycle of `[y]` is `1` at `y` and `0` elsewhere (together with the injectivity of
Cartier → Weil this determines `ofPoint y`).
Proof: if `x` is a prime divisor, `cartierWeilEquiv_apply` turns the cycle coefficient into the
coefficient at `⟨x, _⟩` of the Weil divisor `cartierWeilEquiv (ofPoint y) = of ⟨y, _⟩`
(`AddEquiv.apply_symm_apply`), i.e. a value of `Finsupp.single`; if `x` is not a prime divisor
(coheight `≠ 1`) the Weil cycle is `0` by definition and `x ≠ y`. -/
theorem Divisor.ofPoint_weilCycle {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (y : C.toScheme) (hy : IsClosed ({y} : Set C.toScheme)) (x : C.toScheme) :
    (CartierDivisor.weilCycle C.toVariety (Divisor.ofPoint y) :
        AlgebraicGeometry.AlgebraicCycle C.toVariety.toScheme ℤ) x
      = if x = y then 1 else 0 := by
  have hyp : C.toScheme.IsPrimeDivisor y := C.isPrimeDivisor_of_isClosed y hy
  -- the Weil divisor of [y] is the generator 1·[y]
  have hdef : Divisor.ofPoint y =
      (cartierWeilEquiv C.toSmoothProjectiveVariety).symm
        (FreeAbelianGroup.of (⟨y, hyp⟩ : {Z : C.toSmoothProjectiveVariety.toScheme //
          C.toSmoothProjectiveVariety.toScheme.IsPrimeDivisor Z})) :=
    dif_pos hy
  have hW : cartierWeilEquiv C.toSmoothProjectiveVariety (Divisor.ofPoint y) =
      FreeAbelianGroup.of (⟨y, hyp⟩ : {Z : C.toSmoothProjectiveVariety.toScheme //
          C.toSmoothProjectiveVariety.toScheme.IsPrimeDivisor Z}) :=
    (congrArg (cartierWeilEquiv C.toSmoothProjectiveVariety) hdef).trans
      (AddEquiv.apply_symm_apply _ _)
  by_cases hx : C.toScheme.IsPrimeDivisor x
  · -- x is a prime divisor: the cycle coefficient is the coefficient of the Weil divisor at ⟨x, _⟩
    have h2 : (CartierDivisor.weilCycle C.toVariety (Divisor.ofPoint y) :
        AlgebraicGeometry.AlgebraicCycle C.toVariety.toScheme ℤ) x =
        FreeAbelianGroup.coeff (⟨x, hx⟩ : {Z : C.toSmoothProjectiveVariety.toScheme //
          C.toSmoothProjectiveVariety.toScheme.IsPrimeDivisor Z}) (FreeAbelianGroup.of (⟨y, hyp⟩ : {Z : C.toSmoothProjectiveVariety.toScheme //
          C.toSmoothProjectiveVariety.toScheme.IsPrimeDivisor Z})) :=
      (cartierWeilEquiv_apply C.toSmoothProjectiveVariety (Divisor.ofPoint y) x hx).symm.trans
        (congrArg (FreeAbelianGroup.coeff (⟨x, hx⟩ : {Z : C.toSmoothProjectiveVariety.toScheme //
          C.toSmoothProjectiveVariety.toScheme.IsPrimeDivisor Z})) hW)
    have h3 : FreeAbelianGroup.coeff (⟨x, hx⟩ : {Z : C.toSmoothProjectiveVariety.toScheme //
          C.toSmoothProjectiveVariety.toScheme.IsPrimeDivisor Z}) (FreeAbelianGroup.of ⟨y, hyp⟩)
        = (Finsupp.single (⟨y, hyp⟩ : {Z : C.toSmoothProjectiveVariety.toScheme //
            C.toSmoothProjectiveVariety.toScheme.IsPrimeDivisor Z}) (1 : ℤ)) ⟨x, hx⟩ :=
      congrArg (fun f : {Z : C.toSmoothProjectiveVariety.toScheme //
          C.toSmoothProjectiveVariety.toScheme.IsPrimeDivisor Z} →₀ ℤ => f ⟨x, hx⟩)
        (FreeAbelianGroup.toFinsupp_of _)
    rw [h2, h3]
    by_cases hxy : x = y
    · subst hxy
      rw [if_pos rfl]
      exact Finsupp.single_eq_same
    · have hne' : (⟨y, hyp⟩ : {Z : C.toSmoothProjectiveVariety.toScheme //
          C.toSmoothProjectiveVariety.toScheme.IsPrimeDivisor Z}) ≠ ⟨x, hx⟩ :=
        fun h => hxy (congrArg Subtype.val h).symm
      rw [if_neg hxy]
      first
        | exact Finsupp.single_eq_of_ne hne'
        | exact Finsupp.single_eq_of_ne (Ne.symm hne')
  · -- x is not a prime divisor (coheight ≠ 1): the Weil cycle is 0 by definition, and x ≠ y
    have hne : x ≠ y := fun h => hx (h ▸ hyp)
    have hx' : ¬ Order.coheight x = 1 := hx
    rw [if_neg hne]
    change CartierDivisor.weilCoefficient (Divisor.ofPoint y) x = 0
    rw [CartierDivisor.weilCoefficient, if_neg hx']

/-- The degree of the point divisor `[y]` is the residue degree of the closed point `y` over `k`. -/
theorem Divisor.ofPoint_degree_eq_residueDegree {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (y : C.toScheme) (hy : IsClosed ({y} : Set C.toScheme)) :
    CartierDivisor.degree C (Divisor.ofPoint y)
      = (AlgebraicGeometry.Scheme.Hom.residueDegree (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) y : ℤ) := by
  unfold CartierDivisor.degree
  let f := C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)
  letI : AlgebraicGeometry.IsProper f := by
    exact IsProjectiveOver.isProper C.projective
  let α := AlgebraicGeometry.Intersection.closedPointZeroCycle y hy 1
  let β : AlgebraicGeometry.Intersection.DimensionCycle C.toScheme 0 :=
    ⟨(CartierDivisor.weilCycle C.toVariety (Divisor.ofPoint y) :
      AlgebraicGeometry.AlgebraicCycle C.toVariety.toScheme ℤ), by
        have hdim_eq : C.toScheme.dimension = 1 := by
          unfold AlgebraicGeometry.Scheme.dimension
          rw [C.dim_one]
          simp
        have hdim : C.toScheme.dimension - 1 = 0 := by omega
        have hmem := (CartierDivisor.weilCycle C.toVariety (Divisor.ofPoint y)).2
        generalize ((CartierDivisor.weilCycle C.toVariety (Divisor.ofPoint y) :
          AlgebraicGeometry.AlgebraicCycle C.toVariety.toScheme ℤ)) = z at hmem ⊢
        rw [hdim] at hmem
        first
          | exact hmem
          | exact (AlgebraicGeometry.mem_cycleSubgroup_iff_isDimensionCycle z).mp hmem⟩
  have hcycle : β = α := by
    apply Subtype.ext
    apply Function.locallyFinsuppWithin.ext
    intro x
    change (CartierDivisor.weilCycle C.toVariety (Divisor.ofPoint y) :
      AlgebraicGeometry.AlgebraicCycle C.toVariety.toScheme ℤ) x = _
    rw [Divisor.ofPoint_weilCycle y hy x]
    simp [α, AlgebraicGeometry.Intersection.closedPointZeroCycle,
      Function.locallyFinsuppWithin.single_apply]
  change AlgebraicGeometry.Intersection.rawZeroCycleDegree f β = _
  rw [hcycle]
  rw [AlgebraicGeometry.Intersection.rawZeroCycleDegree_closedPointZeroCycle f y hy 1]
  rw [AlgebraicGeometry.Scheme.Hom.residueFieldDegree_eq_residueDegree]
  simp [f]

/-- Over an algebraically closed field the point divisor of a closed point has degree `1`. -/
theorem Divisor.ofPoint_degree {k : Type u} [Field k] [IsAlgClosed k] {C : SmoothProjectiveCurve k}
    (y : C.toScheme) (hy : IsClosed ({y} : Set C.toScheme)) :
    CartierDivisor.degree C (Divisor.ofPoint y) = 1 := by
  rw [Divisor.ofPoint_degree_eq_residueDegree y hy]
  have h := AlgebraicGeometry.Intersection.residueFieldDegree_eq_one
    (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) y hy
  rw [← AlgebraicGeometry.Scheme.Hom.residueFieldDegree_eq_residueDegree]
  exact_mod_cast h

end
