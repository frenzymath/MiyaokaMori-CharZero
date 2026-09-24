import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.DivisorOperator.ChowGroupRatCongr
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ChowDegreeRat
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.FiberDegree
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.FundamentalClassRat
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProperOverField
import MiyaokaMori.AlgebraicGeometry.Chow.DivisorOperator.RatDivisorOperator
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.SchemeDimension
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.RationalTopSelfIntersection
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.TopSelfIntersectionIsoInvariant

/-! # The top self-intersection on a fiber equals the relative polarization fiber degree

The top self-intersection on a fiber (`Y_c` viewed as a `K`-scheme) equals
`relativePolarizationFiberDegree` (`Y_c` viewed as a `κ(c)`-scheme). One of the inputs for the pushforward
of the tautological power (`pushforward_taut_pow_eq_fiberDegree`) in the proof of Proposition 2.4 of the paper; the route is in the docstring of the main theorem. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- `ChowGroupRat.congr X h` is the transport `h ▸ ·` along `h` (`rfl` after `subst`). -/
theorem AlgebraicGeometry.ChowGroupRat.congr_eq_eqRec (X : AlgebraicGeometry.Scheme.{u})
    {p q : ℕ} (h : p = q) (z : AlgebraicGeometry.ChowGroupRat X p) :
    AlgebraicGeometry.ChowGroupRat.congr X h z = h ▸ z := by
  subst h
  rfl

/-- Transporting the fundamental class by `ChowGroupRat.congr`, capping `s` times and taking the degree is
`RatDivisorOp.topSelfIntersection` (whose definition transports with `▸`; the two transports agree). -/
theorem AlgebraicGeometry.ChowGroupRat.degree_capPow_congr_fundamentalClassRat
    {K : Type u} [Field K] (Y : AlgebraicGeometry.Scheme.{u})
    [Y.Over (AlgebraicGeometry.Spec (CommRingCat.of K))] [AlgebraicGeometry.IsIntegral Y]
    (hY : IsProperOver K Y) (H : AlgebraicGeometry.RatDivisorOp Y) (s : ℕ) (hs : Y.dimension = s) :
    AlgebraicGeometry.ChowGroupRat.degree Y hY
        (AlgebraicGeometry.RatDivisorOp.capPow H s 0
          (AlgebraicGeometry.ChowGroupRat.congr Y (zero_add s).symm
            (AlgebraicGeometry.fundamentalClassRat Y s hs)))
      = AlgebraicGeometry.RatDivisorOp.topSelfIntersection Y hY H s hs := by
  unfold AlgebraicGeometry.RatDivisorOp.topSelfIntersection
  rw [AlgebraicGeometry.ChowGroupRat.congr_eq_eqRec]

/-- For `K` algebraically closed, `f : X ⟶ Spec K` locally of finite type and `x` a closed point,
`Spec κ(x) ⟶ Spec K` is an isomorphism (Mathlib's `residueFieldIsoBase`: `κ(x) ≅ K`). -/
theorem AlgebraicGeometry.isIso_fromSpecResidueField_comp_of_isClosed
    {K : Type u} [Field K] [IsAlgClosed K] {X : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of K)) [AlgebraicGeometry.LocallyOfFiniteType f]
    (x : X) (hx : IsClosed ({x} : Set X)) :
    IsIso (X.fromSpecResidueField x ≫ f) := by
  rw [← AlgebraicGeometry.SpecMap_residueFieldIsoBase_inv f x hx]
  exact AlgebraicGeometry.isIso_SpecMap_iff.mpr (ConcreteCategory.bijective_of_isIso _)

/-- **The top self-intersection on a fiber equals the fiber degree of the relative polarization**: the
number `deg(c_1(ι^*L)^d ∩ [Y_c]_ℚ)` computed with `Y_c` viewed as a `K`-scheme (through
`Y_c → Y → C → Spec K`) equals `relativePolarizationFiberDegree π L c h₁ = topSelfIntersection (Y_c / κ(c)) (ι^*L)`
computed with `Y_c` viewed as a `κ(c)`-scheme (`K` algebraically closed, `c` a closed point). This is the
identification of the fiber degree with the top self-intersection of `O(m)|_{Y_c}` in Proposition 2.4 of the paper.

**Proof.**
1. The left side is by definition
   `RatDivisorOp.topSelfIntersection (Y_c / K) hfibK (ratDivisorOpOfLineBundle ι^*L) d hfib`
   (`ChowGroupRat.congr` and `▸` are the same transport, `ChowGroupRat.congr_eq_eqRec`), which equals
   `topSelfIntersection (Y_c / K) hfibK ι^*L` by `RatDivisorOp.topSelfIntersection_lineBundle` (`Y_c` integral).
2. The right side is `topSelfIntersection (Y_c / κ(c)) h₁ ι^*L` (definition of
   `relativePolarizationFiberDegree`).
3. Both `topSelfIntersection`s are `degreeOver _ Y_c (c_1(ι^*L)^{dim Y_c} ∩ [Y_c])`, the same zero-cycle
   class over different base fields. The two structure morphisms are compatible by
   `Scheme.Hom.fiber_fac`: `fiberι c ≫ π ≫ (C ↘ Spec K) = fiberToSpecResidueField c ≫ τ`, where
   `τ = C.fromSpecResidueField c ≫ (C ↘ Spec K) : Spec κ(c) ⟶ Spec K` is an isomorphism (`K` algebraically
   closed, `c` closed, `C` of finite type: Mathlib's `residueFieldIsoBase`). Changing the base field along
   an isomorphism preserves the degree: `ChowGroup.degreeOver_eq_of_eq_comp`
   (`TopSelfIntersectionIsoInvariant.lean`; pointwise `residueDegree_comp_isIso`).
4. Hence the left side equals the right side (cast `ℤ → ℚ`). -/
theorem AlgebraicGeometry.degree_capPow_pullback_fiberι_eq_relativePolarizationFiberDegree
    {K : Type u} [Field K] [IsAlgClosed K] {C : SmoothProjectiveCurve K}
    {Y : AlgebraicGeometry.Scheme.{u}} (π : Y ⟶ C.carrier) [AlgebraicGeometry.IsProper π]
    (c : C.carrier) (hc : IsClosed ({c} : Set C.carrier))
    (L : Y.Modules) [L.IsLineBundle] [AlgebraicGeometry.IsIntegral (π.fiber c)]
    (d : ℕ) (hfib : (π.fiber c).dimension = d)
    (h₁ : letI := π.fiberOverSpecResidueField c;
      IsProperOver (C.carrier.residueField c) (π.fiber c))
    (hfibK : letI : (π.fiber c).Over (AlgebraicGeometry.Spec (CommRingCat.of K)) :=
        ⟨π.fiberι c ≫ π ≫ (C.carrier ↘ AlgebraicGeometry.Spec (CommRingCat.of K))⟩;
      IsProperOver K (π.fiber c)) :
    letI : (π.fiber c).Over (AlgebraicGeometry.Spec (CommRingCat.of K)) :=
      ⟨π.fiberι c ≫ π ≫ (C.carrier ↘ AlgebraicGeometry.Spec (CommRingCat.of K))⟩
    AlgebraicGeometry.ChowGroupRat.degree (π.fiber c) hfibK
        (AlgebraicGeometry.RatDivisorOp.capPow
          (AlgebraicGeometry.ratDivisorOpOfLineBundle
            ((AlgebraicGeometry.Scheme.Modules.pullback (π.fiberι c)).obj L)) d 0
          (AlgebraicGeometry.ChowGroupRat.congr (π.fiber c) (zero_add d).symm
            (AlgebraicGeometry.fundamentalClassRat (π.fiber c) d hfib)))
      = (AlgebraicGeometry.relativePolarizationFiberDegree π L c h₁ : ℚ) := by
  let instK : (π.fiber c).Over (AlgebraicGeometry.Spec (CommRingCat.of K)) :=
    ⟨π.fiberι c ≫ π ≫ (C.carrier ↘ AlgebraicGeometry.Spec (CommRingCat.of K))⟩
  let instκ := π.fiberOverSpecResidueField c
  rw [AlgebraicGeometry.ChowGroupRat.degree_capPow_congr_fundamentalClassRat,
    AlgebraicGeometry.RatDivisorOp.topSelfIntersection_lineBundle]
  unfold AlgebraicGeometry.relativePolarizationFiberDegree
  congr 1
  -- change the base field from `K` to `κ(c)`: `τ : Spec κ(c) ⟶ Spec K` is an isomorphism
  have hC : AlgebraicGeometry.IsProper
      (C.carrier ↘ AlgebraicGeometry.Spec (CommRingCat.of K)) := C.isProper
  let τ : AlgebraicGeometry.Spec (C.carrier.residueField c) ⟶
      AlgebraicGeometry.Spec (CommRingCat.of K) :=
    C.carrier.fromSpecResidueField c ≫ (C.carrier ↘ AlgebraicGeometry.Spec (CommRingCat.of K))
  have hτ : IsIso τ :=
    AlgebraicGeometry.isIso_fromSpecResidueField_comp_of_isClosed
      (C.carrier ↘ AlgebraicGeometry.Spec (CommRingCat.of K)) c hc
  have hcomp : ((π.fiber c) ↘ AlgebraicGeometry.Spec (CommRingCat.of K)) =
      ((π.fiber c) ↘ AlgebraicGeometry.Spec (CommRingCat.of (C.carrier.residueField c))) ≫ τ := by
    change π.fiberι c ≫ π ≫ (C.carrier ↘ AlgebraicGeometry.Spec (CommRingCat.of K)) =
      π.fiberToSpecResidueField c ≫ (C.carrier.fromSpecResidueField c ≫
        (C.carrier ↘ AlgebraicGeometry.Spec (CommRingCat.of K)))
    rw [← Category.assoc, AlgebraicGeometry.Scheme.Hom.fiber_fac, Category.assoc]
  unfold AlgebraicGeometry.topSelfIntersection
  exact AlgebraicGeometry.ChowGroup.degreeOver_eq_of_eq_comp
    (k := C.carrier.residueField c) (k' := K) h₁ hfibK τ hcomp _

end
