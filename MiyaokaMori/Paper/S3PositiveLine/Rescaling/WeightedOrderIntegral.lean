import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.OrdDvdOfIsPow
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.WeightedOrder

/-! # Integrality of the weighted order

If every nonzero entry `a i q` (of weight `q+1`) of the tuple `a` has a `(q+1)`-st root in the function field,
then the weighted order `w_y = min_{i,q} ord_y(a_{i,q})/(q+1)` is an integer.

Source: Lemma 3.1 of the paper (a finite extension is taken so that every nonzero
coefficient has a `q`-th root; then `ord_y(b_{α,i,q})/q ∈ ℤ` and `w_y = min_{i,q} ord_y(b_{α,i,q})/q ∈ ℤ`).

Proof: the minimum defining `weightedOrderQ` is attained at some nonzero coordinate `(i,q)`
(`weightedOrder_attained`), so `w_y = ord_y(a_{i,q})/(q+1)`. The hypothesis gives `c` with `c^{q+1} = a_{i,q}`;
since `a_{i,q} ≠ 0` also `c ≠ 0`, hence `ord_y(a_{i,q}) = (q+1)·ord_y(c)` (`ord_eq_mul_of_eq_pow`), and the quotient
is the integer `ord_y(c)`.

Note that the minimum is taken over the **nonzero** coordinates only (the normalized order of a zero coordinate
is `+∞` by convention), so the hypothesis is only needed for nonzero coordinates — exactly the paper's
"every nonzero coefficient".
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

variable {k : Type u} [Field k] {Ct : SmoothProjectiveCurve k} {n κ : ℕ}

/-- If every nonzero coordinate has a root of its weight, the denominator of the weighted order is `1`
(i.e. `w_y ∈ ℤ`). Lemma 3.1 of the paper. -/
theorem weightedOrder_den_eq_one (a : Fin (n + 1) → Fin κ → Ct.toScheme.functionField)
    (hne : ∃ i q, a i q ≠ 0)
    (hroot : ∀ (i : Fin (n + 1)) (q : Fin κ), a i q ≠ 0 →
      ∃ c : Ct.toScheme.functionField, c ^ ((q : ℕ) + 1) = a i q)
    (z : Ct.toScheme) :
    (weightedOrderQ a hne z).den = 1 := by
  obtain ⟨p, hp0, hp⟩ := weightedOrder_attained a hne z
  obtain ⟨c, hc⟩ := hroot p.1 p.2 hp0
  have hc0 : c ≠ 0 := by
    intro h
    exact hp0 (by rw [← hc, h, zero_pow (Nat.succ_ne_zero _)])
  have hord : Ct.toScheme.ord (a p.1 p.2) z = (((p.2 : ℕ) + 1 : ℕ) : ℤ) * Ct.toScheme.ord c z :=
    ord_eq_mul_of_eq_pow hc0 hc.symm z
  have hq : (((p.2 : ℕ) : ℚ) + 1) ≠ 0 := by positivity
  have hval : weightedOrderQ a hne z = (Ct.toScheme.ord c z : ℚ) := by
    rw [hp, hord]
    field_simp
    push_cast
    ring
  rw [hval, Rat.den_intCast]

/-- The same fact in the form "there exists an integer", so that downstream users can extract `w_y : ℤ` directly. -/
theorem exists_int_weightedOrder (a : Fin (n + 1) → Fin κ → Ct.toScheme.functionField)
    (hne : ∃ i q, a i q ≠ 0)
    (hroot : ∀ (i : Fin (n + 1)) (q : Fin κ), a i q ≠ 0 →
      ∃ c : Ct.toScheme.functionField, c ^ ((q : ℕ) + 1) = a i q)
    (z : Ct.toScheme) :
    ∃ m : ℤ, weightedOrderQ a hne z = (m : ℚ) :=
  ⟨(weightedOrderQ a hne z).num, by
    conv_lhs => rw [← Rat.num_div_den (weightedOrderQ a hne z)]
    rw [weightedOrder_den_eq_one a hne hroot z]
    norm_num⟩

end
