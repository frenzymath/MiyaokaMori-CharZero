import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.PNat.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.RingTheory.Valuation.Basic
import MiyaokaMori.Paper.S2WeightedJets.Ygg.JetWeightLcm

/-!
# Weighted orders of rational jet coordinates

These are the local algebra objects used in the proof of Proposition 3.2 of the paper
and in (3.3). Orders are
genuine additive valuations with integer values and value `⊤` at zero. The weighted order
is the finite minimum of the rational numbers `ord(aᵢ) / weight(i)`, with infinity retained
for zero coefficients. Polynomial changes are actual mutually inverse substitutions, and
their weighted homogeneity is Mathlib's monomial-by-monomial notion.

This file does not construct a global jet atlas or identify a valuation with a curve stalk.

`normalizedOrder` and `weightedOrder` take an arbitrary order function `v : K → WithTop ℤ` (they
only ever use the values `v a`); the lemmas that need the valuation axioms keep
`v : AddValuation K (WithTop ℤ)` and pass `⇑v`. This makes them the single definition of the
weighted order: `weightedOrderTop` is an `abbrev` of `weightedOrder jetCoordinateWeight (X.ordTop · z)`.
The weight of one coordinate is `jetCoordinateWeight`; the least common multiple of the weights is
the top-level `jetWeight k = lcm(1..k)` (module `JetWeightLcm`).
-/

noncomputable section

open scoped Classical BigOperators

namespace MiyaokaMori.WeightedJets

variable {K : Type*} [Field K]
variable {ι : Type*} [Fintype ι]

/-- Division of an actual integer order by a positive weight, retaining infinity. The order
function `v` is arbitrary (an `AddValuation` is passed as `⇑v`). -/
def normalizedOrder (v : K → WithTop ℤ) (q : ℕ+) (a : K) : WithTop ℚ :=
  WithTop.map (fun m : ℤ ↦ (m : ℚ) / (q : ℕ)) (v a)

/-- The minimum weighted order. An empty coordinate family has minimum infinity. The order
function `v` is arbitrary (an `AddValuation` is passed as `⇑v`). -/
def weightedOrder (w : ι → ℕ+) (v : K → WithTop ℤ)
    (a : ι → K) : WithTop ℚ :=
  Finset.univ.inf fun i ↦ normalizedOrder v (w i) (a i)

/-- The weighted minimum is bounded above by each normalized coordinate order. -/
theorem weightedOrder_le_coordinate (w : ι → ℕ+) (v : K → WithTop ℤ)
    (a : ι → K) (i : ι) :
    weightedOrder w v a ≤ normalizedOrder v (w i) (a i) := by
  exact Finset.inf_le (Finset.mem_univ i)

/-- Zero coefficients contribute infinity, never the integer zero. -/
@[simp] theorem normalizedOrder_zero (v : AddValuation K (WithTop ℤ)) (q : ℕ+) :
    normalizedOrder v q 0 = ⊤ := by
  simp [normalizedOrder]

/-- At a finite integer order the normalization is exactly ordinary rational division. -/
theorem normalizedOrder_of_eq (v : K → WithTop ℤ) (q : ℕ+) (a : K)
    (m : ℤ) (hm : v a = (m : WithTop ℤ)) :
    normalizedOrder v q a = ((m : ℚ) / (q : ℕ) : ℚ) := by
  simp [normalizedOrder, hm]

/-- If each coordinate is zero or has order zero, and at least one coordinate is
nonzero, then the weighted minimum is zero. Zero coordinates retain order `⊤`. -/
theorem weightedOrder_eq_zero_of_zero_or_order_zero (w : ι → ℕ+)
    (v : AddValuation K (WithTop ℤ)) (a : ι → K)
    (hzero : ∀ i, a i = 0 ∨ v (a i) = 0) (ha : ∃ i, a i ≠ 0) :
    weightedOrder w v a = 0 := by
  obtain ⟨i, hi⟩ := ha
  have hvi : v (a i) = 0 := (hzero i).resolve_left hi
  apply le_antisymm
  · simpa [normalizedOrder, hvi] using weightedOrder_le_coordinate w v a i
  · apply Finset.le_inf
    intro j _
    rcases hzero j with hz | hv
    · simp [hz]
    · simp [normalizedOrder, hv]

/-- A regular coefficient times a monomial has order at least the sum of the
exponent-weighted lower bounds of its coordinates. Infinite values are retained. -/
theorem monomial_order_lowerBound (v : AddValuation K (WithTop ℤ))
    (d : ι →₀ ℕ) (c : K) (a : ι → K) (lower : ι → WithTop ℤ)
    (hc : 0 ≤ v c) (ha : ∀ i, lower i ≤ v (a i)) :
    d.sum (fun i n ↦ n • lower i) ≤ v (MvPolynomial.eval a (MvPolynomial.monomial d c)) := by
  have hprod : ∀ s : Finset ι,
      (∑ i ∈ s, d i • lower i) ≤ v (∏ i ∈ s, a i ^ d i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      simp only [Finset.sum_insert hi, Finset.prod_insert hi, AddValuation.map_mul,
        AddValuation.map_pow]
      exact add_le_add (nsmul_le_nsmul_right (ha i) (d i)) ih
  rw [MvPolynomial.eval_monomial, AddValuation.map_mul]
  simpa only [Finsupp.sum, Finsupp.prod] using
    (hprod d.support).trans (le_add_of_nonneg_left hc)

/-- Exact weighted homogeneity converts the monomial estimate into a target-weight
bound. The common bound may be negative; no positivity of it is assumed. -/
theorem weightedMonomial_order_lowerBound (w : ι → ℕ+)
    (v : AddValuation K (WithTop ℤ)) (d : ι →₀ ℕ) (c : K) (q : ℕ)
    (hd : Finsupp.weight (fun i ↦ (w i : ℕ)) d = q) (a : ι → K)
    (b : WithTop ℤ) (hc : 0 ≤ v c) (ha : ∀ i, (w i : ℕ) • b ≤ v (a i)) :
    q • b ≤ v (MvPolynomial.eval a (MvPolynomial.monomial d c)) := by
  have hd' : (∑ i ∈ d.support, d i * (w i : ℕ)) = q := by
    simpa only [Finsupp.weight_apply, Finsupp.sum, smul_eq_mul] using hd
  have hsum : d.sum (fun i n ↦ n • ((w i : ℕ) • b)) = q • b := by
    rw [← hd']
    simp only [Finsupp.sum, smul_smul]
    exact Finset.sum_nsmul_assoc d.support (fun i ↦ d i * (w i : ℕ)) b
  rw [← hsum]
  exact monomial_order_lowerBound v d c a (fun i ↦ (w i : ℕ) • b) hc ha

/-- Evaluating an exactly weighted homogeneous polynomial with regular coefficients
preserves a lower bound in the integer valuation group, including negative bounds. -/
theorem weightedPolynomial_order_lowerBound_integral (w : ι → ℕ+)
    (v : AddValuation K (WithTop ℤ)) (p : MvPolynomial ι K) (q : ℕ)
    (hp : p.IsWeightedHomogeneous (fun i ↦ (w i : ℕ)) q)
    (hregular : ∀ d, 0 ≤ v (p.coeff d)) (a : ι → K) (b : WithTop ℤ)
    (hbound : ∀ i, (w i : ℕ) • b ≤ v (a i)) :
    q • b ≤ v (MvPolynomial.eval a p) := by
  rw [MvPolynomial.eval_eq]
  apply v.map_le_sum
  intro d hd
  simpa only [MvPolynomial.eval_monomial, Finsupp.prod, AddValuation.map_mul] using
    weightedMonomial_order_lowerBound w v d (p.coeff d) q
      (hp (MvPolynomial.mem_support_iff.mp hd)) a b (hregular d) hbound

/-- The paper has `n + 1` coordinates of each positive weight through `T`. -/
abbrev JetCoordinate (n T : ℕ) := Fin (n + 1) × Fin T

/-- The weight of one jet coordinate: the second index `0,...,T-1` records the actual weights
`1,...,T`. (The least common multiple of these weights is the top-level `jetWeight T`.) -/
def jetCoordinateWeight {n T : ℕ} (i : JetCoordinate n T) : ℕ+ :=
  ⟨i.2.val + 1, Nat.zero_lt_succ _⟩

section PolynomialTransition

/-- Actual weighted homogeneous polynomial changes of coordinates in both directions.
The inverse equations are polynomial identities, before evaluation at any tuple. -/
structure WeightedPolynomialEquiv {K : Type*} [CommSemiring K] (w : ι → ℕ+) where
  forward : ι → MvPolynomial ι K
  inverse : ι → MvPolynomial ι K
  forward_homogeneous : ∀ i,
    (forward i).IsWeightedHomogeneous (fun j ↦ (w j : ℕ)) (w i : ℕ)
  inverse_homogeneous : ∀ i,
    (inverse i).IsWeightedHomogeneous (fun j ↦ (w j : ℕ)) (w i : ℕ)
  forward_inverse : ∀ i,
    MvPolynomial.eval₂Hom MvPolynomial.C forward (inverse i) = MvPolynomial.X i
  inverse_forward : ∀ i,
    MvPolynomial.eval₂Hom MvPolynomial.C inverse (forward i) = MvPolynomial.X i

namespace WeightedPolynomialEquiv

variable {w : ι → ℕ+}

/-- Evaluate the actual forward polynomial substitution on a rational tuple. -/
def evalForward {K : Type*} [CommSemiring K]
    (G : WeightedPolynomialEquiv (K := K) w) (a : ι → K) : ι → K :=
  fun i ↦ MvPolynomial.eval a (G.forward i)

/-- Evaluate the actual inverse polynomial substitution on a rational tuple. -/
def evalInverse {K : Type*} [CommSemiring K]
    (G : WeightedPolynomialEquiv (K := K) w) (a : ι → K) : ι → K :=
  fun i ↦ MvPolynomial.eval a (G.inverse i)

end WeightedPolynomialEquiv
end PolynomialTransition

namespace WeightedPolynomialEquiv

variable {w : ι → ℕ+}

/-- Both transitions have coefficients in the valuation ring at the point in question.
This constrains each actual coefficient; it does not assume preservation of weighted order. -/
def RegularAt (G : WeightedPolynomialEquiv (K := K) w)
    (v : AddValuation K (WithTop ℤ)) : Prop :=
  (∀ i d, 0 ≤ v ((G.forward i).coeff d)) ∧
    (∀ i d, 0 ≤ v ((G.inverse i).coeff d))

end WeightedPolynomialEquiv

/-- The finite-character property of a family of genuine valuations: every nonzero
rational function has only finitely many zeros or poles. No assertion about weighted
tuples is assumed in this property. -/
def ValuationFiniteCharacter {Z : Type*} (v : Z → AddValuation K (WithTop ℤ)) : Prop :=
  ∀ a : K, a ≠ 0 → {z : Z | v z a ≠ 0}.Finite

/-- The points where at least one member of a finite family has nonzero weighted order. -/
def weightedSupport {Z μ : Type*} [Fintype μ]
    (w : ι → ℕ+) (v : Z → AddValuation K (WithTop ℤ)) (a : μ → ι → K) : Set Z :=
  {z | ∃ c, weightedOrder w (v z) (a c) ≠ 0}

/-- The union of valuation supports of the nonzero coordinates in a finite family.
Identically zero coordinates are excluded because their order is `⊤` everywhere. -/
def valuationSupport {Z μ : Type*} [Fintype μ]
    (v : Z → AddValuation K (WithTop ℤ)) (a : μ → ι → K) : Set Z :=
  {z | ∃ c i, a c i ≠ 0 ∧ v z (a c i) ≠ 0}

/-- Weighted support is contained in the union of the genuine coordinate supports. -/
theorem weightedSupport_subset_valuationSupport {Z μ : Type*} [Fintype μ]
    (w : ι → ℕ+) (v : Z → AddValuation K (WithTop ℤ)) (a : μ → ι → K)
    (ha : ∀ c, ∃ i, a c i ≠ 0) :
    weightedSupport w v a ⊆ valuationSupport v a := by
  classical
  intro z hz
  rcases hz with ⟨c, hc⟩
  by_contra h
  apply hc (weightedOrder_eq_zero_of_zero_or_order_zero w (v z) (a c) ?_ (ha c))
  intro i
  by_cases hi : a c i = 0
  · exact Or.inl hi
  · right
    by_contra hv
    exact h ⟨c, i, hi, hv⟩

/-- A finite-support boundary for a family of weighted tuples. -/
def HasFiniteWeightedSupport {Z μ : Type*} [Fintype μ]
    (w : ι → ℕ+) (v : Z → AddValuation K (WithTop ℤ)) (a : μ → ι → K) : Prop :=
  (weightedSupport w v a).Finite

/-- The finite rational boundary supplied by the jet weights, with a nonzero coordinate
attaining the minimum and the actual integer valuation at that coordinate. -/
def HasJetDenominatorBoundary {n T : ℕ}
    (v : AddValuation K (WithTop ℤ)) (a : JetCoordinate n T → K) : Prop :=
  ∃ b : ℚ, weightedOrder jetCoordinateWeight v a = (b : WithTop ℚ) ∧
    b.den ∣ jetWeight T ∧
    ∃ i : JetCoordinate n T, ∃ m : ℤ,
      a i ≠ 0 ∧ v (a i) = (m : WithTop ℤ) ∧ b = (m : ℚ) / (jetCoordinateWeight i : ℕ)

/-! The following milestone statements are intentionally registered individually. -/

private theorem cast_le_of_normalizedOrder
    (v : AddValuation K (WithTop ℤ)) (q : ℕ+) (a : K) (b : ℚ)
    (h : (b : WithTop ℚ) ≤ normalizedOrder v q a) :
    ((q : ℕ) : ℚ) * b ≤
      AddMonoidHom.withTopMap (Int.castAddHom ℚ) (v a) := by
  cases hval : v a with
  | top => simp [hval]
  | coe m =>
    rw [normalizedOrder, hval] at h
    have hb : b ≤ (m : ℚ) / (q : ℕ) := by
      simpa using h
    have hq : (0 : ℚ) < (q : ℕ) := by exact_mod_cast q.pos
    have hb' := (le_div_iff₀ hq).mp hb
    change ((↑((q : ℕ) : ℚ) : WithTop ℚ) * (↑b : WithTop ℚ)) ≤ ↑(m : ℚ)
    rw [← WithTop.coe_mul]
    exact_mod_cast
      (show ((q : ℕ) : ℚ) * b ≤ (m : ℚ) by simpa [mul_comm] using hb')

private theorem monomial_order_lowerBound_rat
    (v : AddValuation K (WithTop ℚ))
    (d : ι →₀ ℕ) (c : K) (a : ι → K) (lower : ι → WithTop ℚ)
    (hc : 0 ≤ v c) (ha : ∀ i, lower i ≤ v (a i)) :
    d.sum (fun i n ↦ n • lower i) ≤
      v (MvPolynomial.eval a (MvPolynomial.monomial d c)) := by
  have hprod : ∀ s : Finset ι,
      (∑ i ∈ s, d i • lower i) ≤ v (∏ i ∈ s, a i ^ d i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s hi ih =>
      simp only [Finset.sum_insert hi, Finset.prod_insert hi, AddValuation.map_mul,
        AddValuation.map_pow]
      exact add_le_add (nsmul_le_nsmul_right (ha i) (d i)) ih
  rw [MvPolynomial.eval_monomial, AddValuation.map_mul]
  simpa only [Finsupp.sum, Finsupp.prod] using
    (hprod d.support).trans (le_add_of_nonneg_left hc)

private theorem weightedMonomial_order_lowerBound_rat
    (w : ι → ℕ+) (v : AddValuation K (WithTop ℚ))
    (d : ι →₀ ℕ) (c : K) (q : ℕ)
    (hd : Finsupp.weight (fun i ↦ (w i : ℕ)) d = q)
    (a : ι → K) (b : ℚ) (hc : 0 ≤ v c)
    (ha : ∀ i, ((w i : ℕ) : ℕ) • (b : WithTop ℚ) ≤ v (a i)) :
    (q : ℕ) • (b : WithTop ℚ) ≤
      v (MvPolynomial.eval a (MvPolynomial.monomial d c)) := by
  have hd' : (∑ i ∈ d.support, d i * (w i : ℕ)) = q := by
    simpa only [Finsupp.weight_apply, Finsupp.sum, smul_eq_mul] using hd
  have hsum : d.sum (fun i n ↦ n • ((w i : ℕ) • (b : WithTop ℚ))) =
      q • (b : WithTop ℚ) := by
    rw [← hd']
    simp only [Finsupp.sum, smul_smul]
    exact Finset.sum_nsmul_assoc d.support (fun i ↦ d i * (w i : ℕ))
      (b : WithTop ℚ)
  rw [← hsum]
  exact monomial_order_lowerBound_rat v d c a
    (fun i ↦ (w i : ℕ) • (b : WithTop ℚ)) hc ha

/-- An exactly weight-`q` polynomial with regular coefficients preserves a common
weighted lower bound after evaluation. -/
theorem weightedPolynomial_order_lowerBound (w : ι → ℕ+)
    (v : AddValuation K (WithTop ℤ)) (p : MvPolynomial ι K) (q : ℕ+)
    (hp : p.IsWeightedHomogeneous (fun i ↦ (w i : ℕ)) (q : ℕ))
    (hregular : ∀ d, 0 ≤ v (p.coeff d)) (a : ι → K) (b : ℚ)
    (hbound : ∀ i, (b : WithTop ℚ) ≤ normalizedOrder v (w i) (a i)) :
    (b : WithTop ℚ) ≤ normalizedOrder v q (MvPolynomial.eval a p) := by
  let f : WithTop ℤ →+ WithTop ℚ :=
    AddMonoidHom.withTopMap (Int.castAddHom ℚ)
  have htop : f ⊤ = ⊤ := by simp [f]
  have hmono : Monotone f := by
    intro x y hxy
    cases x with
    | top => simp_all [f]
    | coe x =>
      cases y with
      | top => exact le_top
      | coe y =>
        change ((x : ℚ) : WithTop ℚ) ≤ ((y : ℚ) : WithTop ℚ)
        rw [WithTop.coe_le_coe]
        exact_mod_cast hxy
  let vr : AddValuation K (WithTop ℚ) := AddValuation.map f htop hmono v
  have hbound' : ∀ i, ((w i : ℕ) : ℕ) • (b : WithTop ℚ) ≤ vr (a i) := by
    intro i
    have hi := cast_le_of_normalizedOrder v (w i) (a i) b (hbound i)
    change ((w i : ℕ) : ℚ) * b ≤ f (v (a i)) at hi
    change ((w i : ℕ) : ℚ) * b ≤ vr (a i)
    rw [AddValuation.map_apply f htop hmono v]
    exact hi
  have hreg : ∀ d, 0 ≤ vr (p.coeff d) := by
    intro d
    rw [AddValuation.map_apply f htop hmono v]
    exact hmono (hregular d)
  have hpoly : (q : ℕ) • (b : WithTop ℚ) ≤ vr (MvPolynomial.eval a p) := by
    rw [MvPolynomial.eval_eq]
    apply vr.map_le_sum
    intro d hd
    simpa only [MvPolynomial.eval_monomial, Finsupp.prod, AddValuation.map_mul] using
      weightedMonomial_order_lowerBound_rat (w := w) vr d (p.coeff d) (q : ℕ)
        (hp (MvPolynomial.mem_support_iff.mp hd)) a b (hreg d) hbound'
  cases hval : v (MvPolynomial.eval a p) with
  | top => simp [normalizedOrder, hval]
  | coe m =>
    have hq : (0 : ℚ) < (q : ℕ) := by exact_mod_cast q.pos
    have hm : (q : ℚ) * b ≤ (m : ℚ) := by
      have h := hpoly
      rw [AddValuation.map_apply f htop hmono v, hval] at h
      change ((↑((q : ℕ) : ℚ) : WithTop ℚ) * (↑b : WithTop ℚ)) ≤ ↑(m : ℚ) at h
      rw [← WithTop.coe_mul] at h
      exact_mod_cast h
    have hm' : b ≤ (m : ℚ) / (q : ℕ) :=
      (le_div_iff₀ hq).mpr (by simpa [mul_comm] using hm)
    simpa [normalizedOrder, hval] using hm'

private theorem weightedOrder_le_eval_weightedPolynomial
    (w : ι → ℕ+) (v : AddValuation K (WithTop ℤ))
    (p : ι → MvPolynomial ι K)
    (hp : ∀ i, (p i).IsWeightedHomogeneous (fun j ↦ (w j : ℕ)) (w i : ℕ))
    (hregular : ∀ i d, 0 ≤ v ((p i).coeff d)) (a : ι → K) :
    weightedOrder w v a ≤ weightedOrder w v (fun i ↦ MvPolynomial.eval a (p i)) := by
  apply WithTop.forall_coe_le_iff_le.mp
  intro β hβ
  apply Finset.le_inf
  intro i hi
  have hbound : ∀ j, (β : WithTop ℚ) ≤ normalizedOrder v (w j) (a j) := by
    intro j
    exact hβ.trans (weightedOrder_le_coordinate w v a j)
  have hpoly :=
    weightedPolynomial_order_lowerBound w v (p i) (w i) (hp i)
      (hregular i) a β hbound
  simpa [normalizedOrder] using hpoly

private theorem eval_forward_after_inverse
    (w : ι → ℕ+) (G : WeightedPolynomialEquiv (K := K) (w := w))
    (a : ι → K) (i : ι) :
    MvPolynomial.eval (fun j ↦ MvPolynomial.eval a (G.inverse j)) (G.forward i) = a i := by
  have h := congrArg (MvPolynomial.eval a) (G.inverse_forward i)
  change MvPolynomial.eval (MvPolynomial.eval a ∘ G.inverse) (G.forward i) = a i
  rw [MvPolynomial.eval_assoc]
  change MvPolynomial.eval a
      ((MvPolynomial.eval₂Hom MvPolynomial.C G.inverse) (G.forward i)) = a i
  simpa using h

private theorem eval_inverse_after_forward
    (w : ι → ℕ+) (G : WeightedPolynomialEquiv (K := K) (w := w))
    (a : ι → K) (i : ι) :
    MvPolynomial.eval (fun j ↦ MvPolynomial.eval a (G.forward j)) (G.inverse i) = a i := by
  have h := congrArg (MvPolynomial.eval a) (G.forward_inverse i)
  change MvPolynomial.eval (MvPolynomial.eval a ∘ G.forward) (G.inverse i) = a i
  rw [MvPolynomial.eval_assoc]
  change MvPolynomial.eval a
      ((MvPolynomial.eval₂Hom MvPolynomial.C G.forward) (G.inverse i)) = a i
  simpa using h

/-- A regular weighted polynomial equivalence leaves the weighted order invariant. -/
theorem weightedOrder_invariant (w : ι → ℕ+) (v : AddValuation K (WithTop ℤ))
    (G : WeightedPolynomialEquiv (K := K) w) (hG : G.RegularAt v) (a : ι → K) :
    weightedOrder w v (G.evalForward a) = weightedOrder w v a := by
  have hforward : ∀ i d, 0 ≤ v ((G.forward i).coeff d) := hG.1
  have hinverse : ∀ i d, 0 ≤ v ((G.inverse i).coeff d) := hG.2
  have hforward_order : weightedOrder w v a ≤ weightedOrder w v (G.evalForward a) := by
    exact weightedOrder_le_eval_weightedPolynomial w v G.forward
      G.forward_homogeneous hforward a
  have hinverse_order : weightedOrder w v (G.evalForward a) ≤ weightedOrder w v a := by
    have htuple : a = fun i ↦ MvPolynomial.eval (G.evalForward a) (G.inverse i) := by
      funext i
      exact (eval_inverse_after_forward w G a i).symm
    calc
      weightedOrder w v (G.evalForward a) ≤
          weightedOrder w v (fun i ↦ MvPolynomial.eval (G.evalForward a) (G.inverse i)) :=
        weightedOrder_le_eval_weightedPolynomial w v G.inverse
          G.inverse_homogeneous hinverse (G.evalForward a)
      _ = weightedOrder w v a := congrArg (weightedOrder w v) htuple.symm
  exact le_antisymm hinverse_order hforward_order

/-- Finite character of individual nonzero coordinates gives finite weighted support. -/
theorem weightedSupport_finite_of_finiteCharacter {Z μ : Type*} [Fintype μ]
    (w : ι → ℕ+) (v : Z → AddValuation K (WithTop ℤ))
    (hv : ValuationFiniteCharacter v) (a : μ → ι → K)
    (ha : ∀ c, ∃ i, a c i ≠ 0) :
    HasFiniteWeightedSupport w v a := by
  let J := {ci : μ × ι // a ci.1 ci.2 ≠ 0}
  have hfinite : (⋃ j : J, {z : Z | v z (a j.1.1 j.1.2) ≠ 0}).Finite :=
    Set.finite_iUnion fun j ↦ hv _ j.2
  apply hfinite.subset
  intro z hz
  obtain ⟨c, i, hi, hvi⟩ := weightedSupport_subset_valuationSupport w v a ha hz
  exact Set.mem_iUnion.mpr ⟨⟨(c, i), hi⟩, hvi⟩

/-- Every nonzero jet tuple has a rational weighted order whose reduced denominator
divides the least common multiple of the jet weights. -/
theorem weightedOrder_has_jetDenominatorBoundary {n T : ℕ}
    (v : AddValuation K (WithTop ℤ)) (a : JetCoordinate n T → K)
    (ha : ∃ i, a i ≠ 0) :
    HasJetDenominatorBoundary v a := by
  classical
  obtain ⟨j, hj⟩ := ha
  have huniv : (Finset.univ : Finset (JetCoordinate n T)).Nonempty :=
    ⟨j, Finset.mem_univ j⟩
  obtain ⟨i, hi_mem, hi_inf⟩ :=
    Finset.exists_mem_eq_inf (Finset.univ : Finset (JetCoordinate n T)) huniv
      (fun k ↦ normalizedOrder v (jetCoordinateWeight k) (a k))
  have hweighted : weightedOrder jetCoordinateWeight v a =
      normalizedOrder v (jetCoordinateWeight i) (a i) := by
    simpa [weightedOrder] using hi_inf
  have hnorm_j : normalizedOrder v (jetCoordinateWeight j) (a j) ≠ ⊤ := by
    intro htop
    have hvtop : v (a j) = ⊤ := by
      exact WithTop.map_eq_top_iff.mp htop
    exact (AddValuation.ne_top_iff v).2 hj hvtop
  have hai : a i ≠ 0 := by
    intro hzero
    have htop_i : normalizedOrder v (jetCoordinateWeight i) (a i) = ⊤ := by
      rw [hzero, normalizedOrder_zero]
    have hle := weightedOrder_le_coordinate jetCoordinateWeight v a j
    rw [hweighted, htop_i] at hle
    exact hnorm_j ((top_le_iff.mp hle))
  have hvi_top : v (a i) ≠ ⊤ := (AddValuation.ne_top_iff v).2 hai
  obtain ⟨m, hm⟩ := (WithTop.ne_top_iff_exists.mp hvi_top)
  let b : ℚ := Rat.divInt m (jetCoordinateWeight i : ℤ)
  have hb_eq : b = (m : ℚ) / (jetCoordinateWeight i : ℕ) := by
    simp [b, Rat.divInt_eq_div]
  have hden_weight : b.den ∣ (jetCoordinateWeight i : ℕ) := by
    have hd : (b.den : ℤ) ∣ (jetCoordinateWeight i : ℤ) := by
      simpa [b] using Rat.den_dvd m (jetCoordinateWeight i : ℤ)
    exact Int.natCast_dvd_natCast.mp hd
  have hweight_lcm : (jetCoordinateWeight i : ℕ) ∣ jetWeight T := by
    unfold jetWeight
    exact Finset.dvd_lcm (f := id) (Finset.mem_Icc.mpr ⟨Nat.succ_pos _, i.2.isLt⟩)
  refine ⟨b, ?_, hden_weight.trans hweight_lcm, ⟨i, m, hai, hm.symm, hb_eq⟩⟩
  calc
    weightedOrder jetCoordinateWeight v a = normalizedOrder v (jetCoordinateWeight i) (a i) := hweighted
    _ = ((m : ℚ) / (jetCoordinateWeight i : ℕ) : ℚ) :=
      normalizedOrder_of_eq v (jetCoordinateWeight i) (a i) m hm.symm
    _ = (b : WithTop ℚ) := by rw [hb_eq]

end MiyaokaMori.WeightedJets
