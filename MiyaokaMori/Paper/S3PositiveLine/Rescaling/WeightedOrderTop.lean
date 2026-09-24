import Mathlib.AlgebraicGeometry.OrderOfVanishing
import MiyaokaMori.AlgebraicGeometry.Divisors.OrderOfVanishing.CurveStalkValuation
import MiyaokaMori.RingTheory.WeightedJetValuation

/-! # The weighted order with values in `WithTop ℚ`

The main definition `weightedOrderQ` (with values in `ℚ`) is obtained from `weightedOrderTop` here by `untop`.

`weightedOrderTop a z` is an `abbrev` of
`MiyaokaMori.WeightedJets.weightedOrder jetCoordinateWeight (X.ordTop · z) (fun p ↦ a p.1 p.2)` (same index type
`JetCoordinate n κ = Fin (n+1) × Fin κ`, same weights `jetCoordinateWeight` (`q ↦ q+1`), same `Finset.univ.inf`).
`weightedOrder` / `normalizedOrder` accept an arbitrary order function `v : K → WithTop ℤ` (they only use `v a`):
a valuation exists only at points of coheight `1` with DVR stalk, whereas downstream (`DivisorDL`,
`normalizeCoefficients`, finiteness of the support) evaluates at all points including the generic point, so we
substitute the everywhere-defined `Scheme.ordTop` (`⊤` on zero, `Scheme.ord` on nonzero functions). At a
coheight-`1` DVR point, `ordTop_fun_eq_valuation` replaces `X.ordTop · z` by the stalk valuation
`CurveStalkValuation.valuation`, so the lemmas about `AddValuation` (`weightedOrder_le_coordinate`,
`weightedPolynomial_order_lowerBound`, …) apply directly.

Source: §3 of the paper (equation (3.3)).
-/

set_option autoImplicit false

universe u

open AlgebraicGeometry Order MiyaokaMori.WeightedJets

noncomputable section

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]

open Classical in
/-- The everywhere-defined order of vanishing: `⊤` on the zero function, Mathlib's `Scheme.ord` on a nonzero function. -/
def ordTop (f : X.functionField) (x : X) : WithTop ℤ :=
  if f = 0 then ⊤ else ((X.ord f x : ℤ) : WithTop ℤ)

@[simp] theorem ordTop_zero (x : X) : X.ordTop 0 x = ⊤ := by simp [ordTop]

theorem ordTop_of_ne_zero {f : X.functionField} (hf : f ≠ 0) (x : X) :
    X.ordTop f x = ((X.ord f x : ℤ) : WithTop ℤ) := by simp [ordTop, hf]

theorem ordTop_eq_top_iff {f : X.functionField} {x : X} : X.ordTop f x = ⊤ ↔ f = 0 := by
  by_cases hf : f = 0 <;> simp [ordTop, hf]

/-- At a point of coheight `1`, `ordTop` is the stalk valuation (as a function). -/
theorem ordTop_eq_valuation (x : X) (hx : coheight x = 1)
    [IsDiscreteValuationRing (X.presheaf.stalk x)] (f : X.functionField) :
    X.ordTop f x = AlgebraicGeometry.Divisors.CurveStalkValuation.valuation X x hx f := by
  by_cases hf : f = 0
  · simp [hf]
  · rw [ordTop_of_ne_zero X hf, AlgebraicGeometry.Divisors.CurveStalkValuation.valuation_of_ne_zero X x hx hf]

/-- Function form of `ordTop_eq_valuation`: at a coheight-`1` DVR point the order function `X.ordTop · x` is the
underlying function of the stalk valuation. Used to replace `ordTop` inside `weightedOrderTop` by an `AddValuation`
so that the lemmas requiring the valuation axioms apply. -/
theorem ordTop_fun_eq_valuation (x : X) (hx : coheight x = 1)
    [IsDiscreteValuationRing (X.presheaf.stalk x)] :
    (fun f : X.functionField ↦ X.ordTop f x) = ⇑(AlgebraicGeometry.Divisors.CurveStalkValuation.valuation X x hx) :=
  funext (ordTop_eq_valuation X x hx)

end AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X] {n κ : ℕ}

/-- The normalized order `ord_z(a_p) / (q+1) ∈ WithTop ℚ` of the `p`-th coordinate: `normalizedOrder` specialized to the order function `X.ordTop · z`. -/
abbrev normalizedOrdTop (a : Fin (n + 1) → Fin κ → X.functionField) (z : X)
    (p : JetCoordinate n κ) : WithTop ℚ :=
  normalizedOrder (fun f ↦ X.ordTop f z) (jetCoordinateWeight p) (a p.1 p.2)

/-- The weighted order `β_z = min_{i,q} ord_z(a_{i,q}) / (q+1) ∈ WithTop ℚ` (zero coordinates contribute `⊤`):
`weightedOrder` specialized to the jet weights `jetCoordinateWeight` and the order function `X.ordTop · z`. -/
abbrev weightedOrderTop (a : Fin (n + 1) → Fin κ → X.functionField) (z : X) : WithTop ℚ :=
  weightedOrder jetCoordinateWeight (fun f ↦ X.ordTop f z) (fun p : JetCoordinate n κ ↦ a p.1 p.2)

theorem weightedOrderTop_def (a : Fin (n + 1) → Fin κ → X.functionField) (z : X) :
    weightedOrderTop a z = Finset.univ.inf (normalizedOrdTop a z) := rfl

theorem normalizedOrdTop_of_ne_zero (a : Fin (n + 1) → Fin κ → X.functionField) (z : X)
    (p : JetCoordinate n κ) (hp : a p.1 p.2 ≠ 0) :
    normalizedOrdTop a z p = (((X.ord (a p.1 p.2) z : ℤ) : ℚ) / ((p.2 : ℕ) + 1) : ℚ) := by
  simp [normalizedOrdTop, normalizedOrder, X.ordTop_of_ne_zero hp, jetCoordinateWeight]

theorem normalizedOrdTop_eq_top_iff (a : Fin (n + 1) → Fin κ → X.functionField) (z : X)
    (p : JetCoordinate n κ) : normalizedOrdTop a z p = ⊤ ↔ a p.1 p.2 = 0 := by
  rw [normalizedOrdTop, normalizedOrder, WithTop.map_eq_top_iff, Scheme.ordTop_eq_top_iff]

theorem weightedOrderTop_le (a : Fin (n + 1) → Fin κ → X.functionField) (z : X)
    (p : JetCoordinate n κ) : weightedOrderTop a z ≤ normalizedOrdTop a z p :=
  weightedOrder_le_coordinate jetCoordinateWeight (fun f ↦ X.ordTop f z) (fun p ↦ a p.1 p.2) p

/-- The weighted order of a nonzero tuple is finite and attained at some nonzero coordinate. -/
theorem weightedOrderTop_attained (a : Fin (n + 1) → Fin κ → X.functionField)
    (hne : ∃ i q, a i q ≠ 0) (z : X) :
    ∃ p : JetCoordinate n κ, a p.1 p.2 ≠ 0 ∧
      weightedOrderTop a z = (((X.ord (a p.1 p.2) z : ℤ) : ℚ) / ((p.2 : ℕ) + 1) : ℚ) := by
  obtain ⟨i, q, hiq⟩ := hne
  obtain ⟨p, -, hp⟩ := Finset.exists_mem_eq_inf Finset.univ ⟨(i, q), Finset.mem_univ _⟩
    (normalizedOrdTop a z)
  have hp0 : a p.1 p.2 ≠ 0 := by
    intro h0
    have hle := weightedOrderTop_le a z (i, q)
    rw [weightedOrderTop_def, hp, (normalizedOrdTop_eq_top_iff a z p).mpr h0, top_le_iff,
      normalizedOrdTop_eq_top_iff] at hle
    exact hiq hle
  exact ⟨p, hp0, by rw [weightedOrderTop_def, hp, normalizedOrdTop_of_ne_zero a z p hp0]⟩

theorem weightedOrderTop_ne_top (a : Fin (n + 1) → Fin κ → X.functionField)
    (hne : ∃ i q, a i q ≠ 0) (z : X) : weightedOrderTop a z ≠ ⊤ := by
  obtain ⟨p, -, hp⟩ := weightedOrderTop_attained a hne z
  rw [hp]; exact WithTop.coe_ne_top

end
