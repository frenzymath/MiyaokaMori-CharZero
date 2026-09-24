import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.VarietyLineBundle
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.SmoothProjectiveVariety
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ChowGroupDegree
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.CapDivisorEqFirstChernClass
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.ProjectionFormula
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.SchemeFundamentalCycle
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.TopSelfIntersection
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ZeroCycleDegreeScheme
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.IntegralCurveDegree
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.IntegralCurve
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.LineBundleCurveIntersection
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.NefLineBundle
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.TopSelfIntersectionCurve
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ChowDegreeRatPushforward
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.Stacks02suPointClosure
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.Stacks0az2
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.IdealSheafCycleEqPushforward

/-! # The intersection number with an integral curve is the degree of the restriction

The intersection number of a line bundle `L` on a smooth projective variety `X` with an integral curve
`Γ ⊂ X` equals the degree of `L` restricted to `Γ`: `L ⬝ [Γ] = deg(ι^*L) = Γ.degree L.toModules`.

This is the bridge between `IsNef` (defined through the intersection numbers `L ⬝ [Γ]`) and `Γ.degree`
(the form used in Kleiman's criterion and in the positivity of the degree of an ample restriction).

Proof (Fulton Prop. 2.3(c) projection formula + Prop. 1.4 degree preserved by pushforward + the
one-dimensional case `deg(c₁(L) ∩ [C]) = deg L`):
1. `[Γ] ∈ Z_1(X)` is by definition the proper pushforward of the fundamental cycle `[Γ]_1` of `Γ` along the
   closed immersion `ι`; in the quotient `[Γ] = ι_*[Γ]_1` (`chowPushforward_mk`).
2. Projection formula for the closed immersion `ι` (`chowPushforward_firstChernClass_pullback`):
   `c₁(L) ∩ ι_*[Γ]_1 = ι_*(c₁(ι^*L) ∩ [Γ]_1)`.
3. The degree `ChowGroup.degree X` on the variety is by definition the scheme-level `degreeOver`, which is
   invariant under proper pushforward (`degreeOver_chowPushforward`). Hence
   `L ⬝ [Γ] = deg_Γ(c₁(ι^*L) ∩ [Γ]_1) = topSelfIntersection Γ (ι^*L)`.
4. The one-dimensional top self-intersection satisfies the curve-degree relation `HasCurveModuleDegree`,
   and the uniqueness of `Γ.degree` (`degree_eq_of_hasCurveModuleDegree`) gives
   `topSelfIntersection Γ (ι^*L) = Γ.degree L`.

Source: the conversion between `L·Γ` and `deg(L|_Γ)` in §4 of the paper; Fulton Prop. 2.3(c), Prop. 1.4,
Ex. 2.5.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Casting a cycle along an equality of dimensions does not change the underlying cycle. -/
private theorem coe_cast_cycleGroup {k : Type u} [Field k] {X : Variety k}
    {i j : ℕ} (h : i = j) (c : CycleGroup X i) :
    ((cast (congrArg (fun n : ℕ => ↥(CycleGroup X n)) h) c : CycleGroup X j) :
      AlgebraicGeometry.AlgebraicCycle X.toScheme ℤ) = c.1 := by
  cases h
  rfl

/-- The underlying cycle of `[Γ] ∈ Z_1(X)` (the fundamental class, transported to `Z_1` by
`IntegralCurve.fundamentalClass`) is the Mathlib-style proper pushforward along `Γ.ι` of the
fundamental cycle `[Γ.carrier]_1` of the curve itself. Any `IsLocallyNoetherian Γ.carrier`
instance may be supplied (it is a `Prop`). -/
theorem IntegralCurve.fundamentalClass_coe_eq_properPushforward {k : Type u} [Field k]
    {X : Variety k} (Γ : IntegralCurve k X.toScheme)
    [AlgebraicGeometry.IsLocallyNoetherian Γ.carrier] :
    (Γ.fundamentalClass : AlgebraicGeometry.AlgebraicCycle X.toScheme ℤ) =
      AlgebraicGeometry.AlgebraicCycle.properPushforward Γ.ι (Γ.carrier.fundamentalCycle 1) := by
  have : AlgebraicGeometry.IsNoetherian Γ.carrier :=
    AlgebraicGeometry.Intersection.properFieldScheme_isNoetherian
      (Γ.ι ≫ (X.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))
  unfold IntegralCurve.fundamentalClass
  rw [coe_cast_cycleGroup Γ.dimension_eq_one]
  change AlgebraicGeometry.AlgebraicCycle.properPushforward Γ.ι
      (AlgebraicGeometry.Intersection.dimensionFundamentalCycle Γ.carrier
        Γ.toClosedSubvariety.dimension).1 = _
  congr 1
  ext x
  rw [AlgebraicGeometry.Intersection.dimensionFundamentalCycle_apply, Γ.dimension_eq_one]
  rfl

/-- **Bridge**: the intersection number `L ⬝ [Γ]` of a line bundle on a smooth projective variety
with an integral curve `Γ ⊂ X` equals the degree `deg(ι^*L)` of the restriction to `Γ`.
Proof: projection formula for the closed immersion `ι : Γ → X`, invariance of the degree of a
zero-cycle under proper pushforward, and `deg(c₁(ι^*L) ∩ [Γ]) = deg(ι^*L)`
(`hasCurveModuleDegree_topSelfIntersection`); see the module docstring. -/
theorem LineBundle.inter_fundamentalClass_eq_degree {k : Type u} [Field k] [IsAlgClosed k]
    {X : SmoothProjectiveVariety k} (L : LineBundle X.toVariety)
    (Γ : IntegralCurve k X.toScheme) :
    L ⬝ Γ.fundamentalClass = Γ.degree L.toModules := by
  -- Set-up: Γ.carrier is a proper (hence locally Noetherian) k-scheme of dimension 1.
  have hC : IsProperOver k Γ.carrier := Γ.isProperOver
  have hX : IsProperOver k X.toScheme := SmoothProjectiveVariety.isProper_structureMorphism X
  have hdim : Γ.carrier.dimension = 1 := Γ.carrier_dimension
  have : AlgebraicGeometry.IsProper
      (Γ.carrier ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := hC
  have : AlgebraicGeometry.IsLocallyNoetherian Γ.carrier :=
    AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian
      (Γ.carrier ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
  have : Γ.ι.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) := ⟨rfl⟩
  let ιL : Γ.carrier.Modules := (AlgebraicGeometry.Scheme.Modules.pullback Γ.ι).obj L.toModules
  -- Step 1: [Γ] (in the scheme Chow group of X) is ι_*[Γ.carrier]_1.
  have hdesc : AlgebraicGeometry.PushforwardDescends Γ.ι 1 := fun β γ hβγ =>
    AlgebraicGeometry.AlgebraicCycle.properPushforward_rationallyEquivalent (k := k) Γ.ι 1 β γ hβγ
  have hfund : AlgebraicGeometry.ChowGroup.mk Γ.fundamentalClass =
      AlgebraicGeometry.chowPushforward Γ.ι 1 (Γ.carrier.fundamentalChowClass 1) := by
    unfold AlgebraicGeometry.Scheme.fundamentalChowClass
    rw [AlgebraicGeometry.chowPushforward_mk Γ.ι 1 hdesc]
    change AlgebraicGeometry.ChowGroup.mk Γ.fundamentalClass = _
    congr 1
    apply Subtype.ext
    exact Γ.fundamentalClass_coe_eq_properPushforward
  -- Step 2: projection formula for the closed immersion ι.
  have hproj : AlgebraicGeometry.firstChernClass L.toModules 1
        (AlgebraicGeometry.chowPushforward Γ.ι 1 (Γ.carrier.fundamentalChowClass 1)) =
      AlgebraicGeometry.chowPushforward Γ.ι 0
        (AlgebraicGeometry.firstChernClass ιL 1 (Γ.carrier.fundamentalChowClass 1)) :=
    (AlgebraicGeometry.chowPushforward_firstChernClass_pullback (k := k) Γ.ι L.toModules 0
      (Γ.carrier.fundamentalChowClass 1)).symm
  -- Step 3: degrees.  L ⬝ [Γ] = deg_X(c₁(L) ∩ [Γ]) = deg_Γ(c₁(ι^*L) ∩ [Γ]_1) = (ι^*L)^1.
  have hLHS : L ⬝ Γ.fundamentalClass =
      AlgebraicGeometry.ChowGroup.degreeOver k X.toScheme hX
        (AlgebraicGeometry.firstChernClass L.toModules 1
          (AlgebraicGeometry.ChowGroup.mk Γ.fundamentalClass)) := rfl
  have hTSI : AlgebraicGeometry.topSelfIntersection Γ.carrier hC ιL =
      AlgebraicGeometry.ChowGroup.degreeOver k Γ.carrier hC
        (AlgebraicGeometry.firstChernClass ιL 1 (Γ.carrier.fundamentalChowClass 1)) := by
    rw [MiyaokaMori.TopSelfIntersectionCurve.topSelfIntersection_eq_of_dimension hC ιL hdim]
    rfl
  -- Step 4: (ι^*L)^1 = deg(ι^*L) via the curve-degree relation.
  have hdegΓ : Γ.degree L.toModules = AlgebraicGeometry.topSelfIntersection Γ.carrier hC ιL :=
    Γ.degree_eq_of_hasCurveModuleDegree L.toModules
      (MiyaokaMori.TopSelfIntersectionCurve.hasCurveModuleDegree_topSelfIntersection hC hdim ιL)
  rw [hLHS, hfund, hproj,
    MiyaokaMori.ChowDegreeRatPushforward.degreeOver_chowPushforward hC hX Γ.ι, hdegΓ, hTSI]

/-- `IsNef L` in the `Γ.degree` form used by Kleiman's criterion: `∀ Γ, 0 ≤ deg(L|_Γ)`. -/
theorem IsNef.degree_nonneg {k : Type u} [Field k] [IsAlgClosed k]
    {X : SmoothProjectiveVariety k} {L : LineBundle X.toVariety} (hL : IsNef L)
    (Γ : IntegralCurve k X.toScheme) : 0 ≤ Γ.degree L.toModules := by
  rw [← LineBundle.inter_fundamentalClass_eq_degree L Γ]
  exact hL Γ

end
