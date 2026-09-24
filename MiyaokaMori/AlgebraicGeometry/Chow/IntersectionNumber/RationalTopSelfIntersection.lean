import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.FundamentalClassRat
import MiyaokaMori.AlgebraicGeometry.Chow.DivisorOperator.RatDivisorOpCapPowTmul

/-! # Top self-intersection of a ℚ-divisor operator

The top self-intersection `H^s := deg(H^s ∩ [Y]) ∈ ℚ` of a ℚ-divisor operator (`Y` integral, proper
over `K`, `dim Y = s`). `LineBundle.topSelfIntersection` handles only line bundles; the ℚ-class
version is needed because `H^sp + (1/q)π^*c_1(Q_i)` is not the `c_1` of any line bundle
(the rational tautological class `H_k` of Proposition 2.4 of the paper). -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The top self-intersection `H^s := deg(H^s ∩ [Y]) ∈ ℚ` of a ℚ-divisor operator on an integral scheme `Y`
proper over `K` of dimension `s`. -/
noncomputable def AlgebraicGeometry.RatDivisorOp.topSelfIntersection {K : Type u} [Field K]
    (Y : AlgebraicGeometry.Scheme.{u}) [Y.Over (AlgebraicGeometry.Spec (CommRingCat.of K))]
    [AlgebraicGeometry.IsIntegral Y] (hY : IsProperOver K Y)
    (H : AlgebraicGeometry.RatDivisorOp Y) (s : ℕ) (hs : Y.dimension = s) : ℚ :=
  AlgebraicGeometry.ChowGroupRat.degree Y hY
    (AlgebraicGeometry.RatDivisorOp.capPow H s 0
      ((zero_add s).symm ▸ AlgebraicGeometry.fundamentalClassRat Y s hs))

theorem AlgebraicGeometry.RatDivisorOp.topSelfIntersection_lineBundle {K : Type u} [Field K]
    (Y : AlgebraicGeometry.Scheme.{u}) [Y.Over (AlgebraicGeometry.Spec (CommRingCat.of K))]
    [AlgebraicGeometry.IsIntegral Y] (hY : IsProperOver K Y) (L : Y.Modules) [L.IsLineBundle]
    (s : ℕ) (hs : Y.dimension = s) :
    AlgebraicGeometry.RatDivisorOp.topSelfIntersection Y hY
        (AlgebraicGeometry.ratDivisorOpOfLineBundle L) s hs
      = (AlgebraicGeometry.topSelfIntersection Y hY L : ℚ) := by
  subst s
  have : AlgebraicGeometry.IsProper
      (Y ↘ AlgebraicGeometry.Spec (CommRingCat.of K)) := hY
  have : AlgebraicGeometry.IsOfFiniteType
      (Y ↘ AlgebraicGeometry.Spec (CommRingCat.of K)) := {}
  have : AlgebraicGeometry.IsLocallyNoetherian Y :=
    AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian
      (Y ↘ AlgebraicGeometry.Spec (CommRingCat.of K))
  let W : Variety K := { carrier := Y }
  have hheight : Order.height (genericPoint Y) = (Y.dimension : ℕ∞) := by
    have h := Variety.height_add_coheight W (genericPoint W.toScheme)
    have hzero : Order.coheight (genericPoint W.toScheme) = 0 :=
      Order.coheight_eq_zero.mpr (isMax_top (α := W.toScheme))
    simpa [W, hzero] using h
  have hfund := AlgebraicGeometry.Scheme.fundamentalCycle_of_isIntegral_of_isOfFiniteType
    (k := K) Y
  have hfundRat :
      AlgebraicGeometry.fundamentalClassRat Y Y.dimension rfl =
        ((1 : ℚ) ⊗ₜ[ℤ] Y.fundamentalChowClass Y.dimension :
          AlgebraicGeometry.ChowGroupRat Y Y.dimension) := by
    unfold AlgebraicGeometry.fundamentalClassRat
    rw [dif_pos hheight]
    change ((1 : ℚ) ⊗ₜ[ℤ] AlgebraicGeometry.ChowGroup.mk _ :
        AlgebraicGeometry.ChowGroupRat Y Y.dimension) = _
    apply congrArg (fun z : AlgebraicGeometry.ChowGroup Y Y.dimension =>
      ((1 : ℚ) ⊗ₜ[ℤ] z : AlgebraicGeometry.ChowGroupRat Y Y.dimension))
    apply congrArg AlgebraicGeometry.ChowGroup.mk
    apply Subtype.ext
    apply DFunLike.ext
    intro x
    have hx := congrFun hfund x
    simpa [Function.locallyFinsuppWithin.single_apply] using hx.symm
  unfold AlgebraicGeometry.RatDivisorOp.topSelfIntersection
  rw [hfundRat]
  unfold AlgebraicGeometry.topSelfIntersection
  exact AlgebraicGeometry.ratDivisorOp_capPow_degree_eq_degreeOver Y hY L Y.dimension
    (Y.fundamentalChowClass Y.dimension)

end
