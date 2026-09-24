import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.TopSelfIntersection
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ZeroCycleDegreeScheme
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.FirstChernClassMk
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.FirstChernCapPointGeneric
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.RationalSectionDegree

/-! # The top self-intersection on a curve and the curve-degree relation

Let `X` be an integral scheme proper over a field `k` with `X.dimension = 1`, and `L` a line bundle on `X`.
Then the top self-intersection `topSelfIntersection X hX L = deg(c₁(L) ∩ [X])` of the Chow route satisfies
the curve-degree relation `HasCurveModuleDegree ⟨X, X ↘ Spec k⟩ L (topSelfIntersection X hX L)` (`X` may be
singular).

Proof:
1. Replace `X.dimension` in the definition by `1` (`topSelfIntersection_eq_of_dimension`: `rfl` after
   `subst`); `capPow L 1 0` is `firstChernClass L 1`, and the `cast` along `0 + 1 = 1` is the identity.
2. `[X]_1` is the cycle with coefficient `1` at the generic point; `firstChernClass_mk` (via Stacks 02TI)
   computes `c₁(L) ∩ [X]` as the class of the cycle-level `firstChernCapCycleAux L 1 [X]_1`, which is the
   single-point contribution `firstChernCapPoint L η` of the generic point
   (`firstChernCapCycleAux_fundamentalCycle`).
3. `firstChernCapPoint L η = div_L(s′)` with `s′ ≠ 0` (`FirstChernCapPointGeneric.lean`); `degreeOver` on
   the class `mk Z` is by definition `AlgebraicCycle.degree Z`.
4. `HasCurveModuleDegree X L (deg div_L(s′))` (the rational-section-divisor form of the relation).

Source: the divisor form of Stacks 0BEY; Fulton, Intersection Theory, Ex. 2.5.1 (`deg(c₁(L) ∩ [C]) = deg L`).

This module is **the** place where the relation `HasCurveModuleDegree` meets the primary curve degree
`topSelfIntersection`:
* `hasCurveModuleDegree_topSelfIntersection` — the spec theorem (the relation holds at `d = topSelfIntersection X hX L`);
* `hasCurveModuleDegree_iff_eq_topSelfIntersection` — the relation is *equivalent* to `d = topSelfIntersection X hX L`
  (uniqueness = degree of a principal divisor is zero, `curveModuleDegree_value_unique`);
* `topSelfIntersection_eq_degree_rationalSectionDivisor` — `topSelfIntersection X hX L = deg div_L(s)` for **every** nonzero
  rational section `s` (Stacks 0BEY / Fulton Ex. 2.5.1); this is the theorem-level form that replaces every downstream
  use of `hasCurveModuleDegree_degree_rationalSectionDivisor` + uniqueness;
* `AlgebraicGeometry.topSelfIntersection_congr` (any dimension) — the value depends only on the isomorphism
  class of the line bundle.
Downstream modules state curve degrees as `topSelfIntersection` / `LineBundle.degree` / `IntegralCurve.degree`
and never take `HasCurveModuleDegree … d` as a hypothesis; the relation is a theorem about the primary
definition, not an interface.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

/-- The iterated cap with `c_1` depends only on the isomorphism class of the line bundle (any dimension). -/
theorem AlgebraicGeometry.firstChernClass.capPow_congr {X : AlgebraicGeometry.Scheme.{u}}
    (L L' : X.Modules) [L.IsLineBundle] [L'.IsLineBundle] (e : L ≅ L') :
    ∀ (n d : ℕ), AlgebraicGeometry.firstChernClass.capPow L n d =
      AlgebraicGeometry.firstChernClass.capPow L' n d
  | 0, _ => rfl
  | n + 1, d => by
    show (AlgebraicGeometry.firstChernClass.capPow L n d).comp
        (AlgebraicGeometry.firstChernClass L (d + n + 1)) =
      (AlgebraicGeometry.firstChernClass.capPow L' n d).comp
        (AlgebraicGeometry.firstChernClass L' (d + n + 1))
    rw [AlgebraicGeometry.firstChernClass.capPow_congr L L' e n d,
      AlgebraicGeometry.firstChernClass_congr L L' e (d + n)]

/-- The top self-intersection depends only on the isomorphism class of the line bundle (any dimension). -/
theorem AlgebraicGeometry.topSelfIntersection_congr {K : Type u} [Field K]
    (X : AlgebraicGeometry.Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (CommRingCat.of K))]
    (hX : IsProperOver K X) (L L' : X.Modules) [L.IsLineBundle] [L'.IsLineBundle] (e : L ≅ L') :
    AlgebraicGeometry.topSelfIntersection X hX L = AlgebraicGeometry.topSelfIntersection X hX L' := by
  unfold AlgebraicGeometry.topSelfIntersection
  rw [AlgebraicGeometry.firstChernClass.capPow_congr L L' e]

/-- The top self-intersection depends on the `Over` instance only through the structure morphism
`X ↘ Spec k`: two `Over` instances with equal structure morphisms give the same value (used to compare
`IntegralCurve.degree` on the same carrier with different but equal `k`-structures). -/
theorem AlgebraicGeometry.topSelfIntersection_congr_over {k : Type u} [Field k]
    {X : AlgebraicGeometry.Scheme.{u}} (i₁ i₂ : X.Over (AlgebraicGeometry.Spec (CommRingCat.of k)))
    (h : @CategoryTheory.over _ _ X (AlgebraicGeometry.Spec (CommRingCat.of k)) i₁ =
      @CategoryTheory.over _ _ X (AlgebraicGeometry.Spec (CommRingCat.of k)) i₂)
    (h₁ : @IsProperOver k _ X i₁) (h₂ : @IsProperOver k _ X i₂)
    (L : X.Modules) [L.IsLineBundle] :
    @AlgebraicGeometry.topSelfIntersection k _ X i₁ h₁ L _ =
      @AlgebraicGeometry.topSelfIntersection k _ X i₂ h₂ L _ := by
  cases i₁
  cases i₂
  cases h
  rfl

namespace MiyaokaMori.TopSelfIntersectionCurve

variable {k : Type u} [Field k]

/-- `SchemeIsOneDimensional X` (topological Krull dimension `1`) ⇒ `X.dimension = 1`. -/
theorem dimension_eq_one_of_schemeIsOneDimensional {X : Scheme.{u}} (h : SchemeIsOneDimensional X) :
    X.dimension = 1 := by
  unfold Scheme.dimension
  rw [show topologicalKrullDim X = 1 from h]
  simp

/-- `X.dimension = d > 0` forces the topological Krull dimension to be finite. -/
theorem topologicalKrullDim_ne_top_of_dimension {X : Scheme.{u}} {d : ℕ} (hd : 0 < d)
    (hX : X.dimension = d) : topologicalKrullDim X ≠ ⊤ := by
  intro h
  unfold Scheme.dimension at hX
  rw [h] at hX
  have : (WithBot.unbotD 0 (⊤ : WithBot ℕ∞)).toNat = 0 := by
    show (⊤ : ℕ∞).toNat = 0
    exact ENat.toNat_top
  omega

theorem topologicalKrullDim_ne_bot {X : Scheme.{u}} [IsIntegral X] : topologicalKrullDim X ≠ ⊥ := by
  unfold topologicalKrullDim
  have : Nonempty (TopologicalSpace.IrreducibleCloseds X) :=
    ⟨⟨Set.univ, (IrreducibleSpace.isIrreducible_univ X), isClosed_univ⟩⟩
  exact Order.krullDim_ne_bot_iff.mpr inferInstance

/-- On an integral scheme, `X.dimension = 1` ⇒ `SchemeIsOneDimensional X` (the converse of
`dimension_eq_one_of_schemeIsOneDimensional`). -/
theorem schemeIsOneDimensional_of_dimension_eq_one {X : Scheme.{u}} [IsIntegral X]
    (hdim : X.dimension = 1) : SchemeIsOneDimensional X := by
  show topologicalKrullDim X = 1
  rw [X.dimension_spec topologicalKrullDim_ne_bot
    (topologicalKrullDim_ne_top_of_dimension Nat.one_pos hdim), hdim]
  rfl

theorem height_genericPoint_of_dimension {X : Scheme.{u}} [IsIntegral X] {d : ℕ} (hd : 0 < d)
    (hX : X.dimension = d) : Order.height (genericPoint X) = (d : ℕ∞) := by
  have hk : Order.krullDim X = topologicalKrullDim X :=
    (Order.krullDim_eq_of_orderIso
      (@irreducibleSetEquivPoints X _ _ _ :
        TopologicalSpace.IrreducibleCloseds X ≃o X)).symm
  have h1 : ((Order.height (⊤ : X) : ℕ∞) : WithBot ℕ∞) = Order.krullDim X :=
    Order.height_top_eq_krullDim
  rw [hk, X.dimension_spec topologicalKrullDim_ne_bot (topologicalKrullDim_ne_top_of_dimension hd hX),
    hX] at h1
  exact WithBot.coe_injective h1

/-- `c_1(L) ∩ [X]` (at the level of cycles) is the single-point contribution of the generic point; the
general form of the `n + 2` version in `Stacks02th.lean`. -/
theorem firstChernCapCycleAux_fundamentalCycle {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] (L : X.Modules) [L.IsLineBundle] {d : ℕ} (hd : 0 < d)
    (hX : X.dimension = d) :
    firstChernCapCycleAux L d (X.fundamentalCycle d) = firstChernCapPoint L (genericPoint X) := by
  classical
  have hfund : ∀ x : X, X.fundamentalCycle d x = if x = genericPoint X then 1 else 0 := by
    intro x
    have h := congrFun (X.fundamentalCycle_of_isIntegral
      (topologicalKrullDim_ne_top_of_dimension hd hX)) x
    rw [hX] at h
    rw [h]
  ext z
  show (∑ᶠ w : X, firstChernCapTerm L d (X.fundamentalCycle d) z w) = _
  rw [finsum_eq_single _ (genericPoint X)]
  · unfold firstChernCapTerm
    rw [if_pos (height_genericPoint_of_dimension hd hX), hfund, if_pos rfl, one_mul]
  · intro w hw
    unfold firstChernCapTerm
    rw [hfund, if_neg hw, zero_mul, ite_self]

/-- Replace `X.dimension` in the definition by a given `n`. -/
theorem topSelfIntersection_eq_of_dimension {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]
    (hX : IsProperOver k X) [IsLocallyNoetherian X] (L : X.Modules) [L.IsLineBundle] {n : ℕ}
    (hn : X.dimension = n) :
    topSelfIntersection X hX L = ChowGroup.degreeOver k X hX
      (firstChernClass.capPow L n 0
        (cast (congrArg (ChowGroup X) (zero_add n).symm) (X.fundamentalChowClass n))) := by
  subst hn
  rfl

/-- **The one-dimensional top self-intersection satisfies the curve-degree relation.** -/
theorem hasCurveModuleDegree_topSelfIntersection {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k))] [IsIntegral X] (hX : IsProperOver k X)
    (hdim : X.dimension = 1) (L : X.Modules) [L.IsLineBundle] :
    AlgebraicGeometry.Intersection.HasCurveModuleDegree
      (⟨X, X ↘ Spec (CommRingCat.of k)⟩ : AlgebraicGeometry.Proj.SchemeOver k) L
      (topSelfIntersection X hX L) := by
  haveI : IsProper (X ↘ Spec (CommRingCat.of k)) := hX
  haveI : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (CommRingCat.of k))
  have hXk := Scheme.isLocallyOfFiniteTypeOverField_of_over (k := k) X
  obtain ⟨s, hs, hcap⟩ := MiyaokaMori.FirstChernCapPointGeneric.firstChernCapPoint_genericPoint L
  have hfund := firstChernCapCycleAux_fundamentalCycle L Nat.one_pos hdim
  -- the class of `c₁(L) ∩ [X]`
  have hc1 : firstChernClass L 1 (X.fundamentalChowClass 1) =
      ChowGroup.mk ⟨firstChernCapCycleAux L 1 (X.fundamentalCycle 1),
        firstChernCapCycleAux_mem hXk L 1 _⟩ :=
    firstChernClass_mk (k := k) L Nat.one_pos _ _
  have hT : topSelfIntersection X hX L =
      AlgebraicCycle.degree (k := k) (L.rationalSectionDivisor s) := by
    rw [topSelfIntersection_eq_of_dimension hX L hdim]
    change ChowGroup.degreeOver k X hX (firstChernClass L 1 (X.fundamentalChowClass 1)) = _
    rw [hc1]
    change AlgebraicCycle.degree (k := k) (firstChernCapCycleAux L 1 (X.fundamentalCycle 1)) = _
    rw [hfund, hcap]
  have hkd : topologicalKrullDim X ≤ 1 := by
    rw [X.dimension_spec topologicalKrullDim_ne_bot
      (topologicalKrullDim_ne_top_of_dimension Nat.one_pos hdim), hdim]
    rfl
  rw [hT]
  exact MiyaokaMori.RationalSectionDegree.hasCurveModuleDegree_degree_rationalSectionDivisor
    hX hkd L s hs

/-- **Characterization of the curve-degree relation**: for a line bundle `L` on a one-dimensional proper
integral `k`-scheme, `HasCurveModuleDegree ⟨X, X ↘ Spec k⟩ L d ↔ d = topSelfIntersection X hX L`.
→: uniqueness of the value (`curveModuleDegree_value_unique`, principal divisors on a proper integral curve
have degree zero) + the previous theorem; ←: the previous theorem. This is the precise form of the
statement that `HasCurveModuleDegree` is a theorem about the primary definition. -/
theorem hasCurveModuleDegree_iff_eq_topSelfIntersection {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k))] [IsIntegral X] (hX : IsProperOver k X)
    (hdim : X.dimension = 1) (L : X.Modules) [L.IsLineBundle] (d : ℤ) :
    AlgebraicGeometry.Intersection.HasCurveModuleDegree
      (⟨X, X ↘ Spec (CommRingCat.of k)⟩ : AlgebraicGeometry.Proj.SchemeOver k) L d ↔
      d = topSelfIntersection X hX L := by
  constructor
  · intro hd
    exact AlgebraicGeometry.Intersection.curveModuleDegree_value_unique
      (⟨X, X ↘ Spec (CommRingCat.of k)⟩ : AlgebraicGeometry.Proj.SchemeOver k) L hd
      (hasCurveModuleDegree_topSelfIntersection hX hdim L)
  · rintro rfl
    exact hasCurveModuleDegree_topSelfIntersection hX hdim L

/-- **The top self-intersection is the degree of the divisor of any nonzero rational section** (Stacks 0BEY;
Fulton Ex. 2.5.1): for a line bundle `L` on a one-dimensional proper integral `k`-scheme `X` and any
`s ≠ 0` in the generic stalk, `topSelfIntersection X hX L = deg_k div_L(s)`, where `deg` is
`AlgebraicCycle.degree` (`Σ n_x [κ(x):k]`). Proof: both sides satisfy the curve-degree relation
(`hasCurveModuleDegree_topSelfIntersection`, `hasCurveModuleDegree_degree_rationalSectionDivisor`), whose
value is unique. This is the theorem-level interface for computing degrees on curves (additivity under
tensor products, degree zero of bundles isomorphic to `O_X`, the degree of `O(D)`, finite pullbacks, …). -/
theorem topSelfIntersection_eq_degree_rationalSectionDivisor {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k))] [IsIntegral X] [IsLocallyNoetherian X] (hX : IsProperOver k X)
    (hdim : X.dimension = 1) (L : X.Modules) [L.IsLineBundle]
    (s : L.stalk (genericPoint X)) (hs : s ≠ 0) :
    topSelfIntersection X hX L = AlgebraicCycle.degree (k := k) (L.rationalSectionDivisor s) := by
  have : IsProper (X ↘ Spec (CommRingCat.of k)) := hX
  have hkd : topologicalKrullDim X ≤ 1 := le_of_eq (schemeIsOneDimensional_of_dimension_eq_one hdim)
  exact AlgebraicGeometry.Intersection.curveModuleDegree_value_unique
    (⟨X, X ↘ Spec (CommRingCat.of k)⟩ : AlgebraicGeometry.Proj.SchemeOver k) L
    (hasCurveModuleDegree_topSelfIntersection hX hdim L)
    (MiyaokaMori.RationalSectionDegree.hasCurveModuleDegree_degree_rationalSectionDivisor
      hX hkd L s hs)

end MiyaokaMori.TopSelfIntersectionCurve

end
