import MiyaokaMori.Prelude
import MiyaokaMori.RingTheory.KeyLemma.TameSymbol

/-! # The summand `ord_{A/q}(∂_{A_q}(f, g))` of Stacks 0EAX

The summand of 0EAX: `A` a two-dimensional Noetherian local domain, `q` a height-one prime, `f, g ∈ K^*`;
`Ring.tameOrd A hA hfin q f g = ord_{A/q}(∂_{A_q}(f, g))` (with values in `ℤᵐ⁰`, multiplicative notation).
It is multiplicative in `f` and in `g` (0EAS + additivity of `ord`). Also the two dimension lemmas
`dim A_q ≤ 1`, `dim A/q ≤ 1`.

References: the summand in the statement of Stacks 0EAX; 0EAS (bimultiplicativity); 02MD (additivity of
`ord`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

noncomputable section

/-- The localization at a height-one prime has dimension `≤ 1` (`dim A_q = ht q`). -/

theorem Ring.krullDimLE_one_localization_of_height_eq_one {A : Type u} [CommRing A]
    (q : PrimeSpectrum A) (hq : q.asIdeal.height = 1) :
    Ring.KrullDimLE 1 (Localization.AtPrime q.asIdeal) := by
  rw [Ring.krullDimLE_iff, IsLocalization.AtPrime.ringKrullDim_eq_height q.asIdeal, hq]
  rfl

/-- A two-dimensional Noetherian local ring modulo a height-one prime has dimension `≤ 1`
(`ht q + dim A/q ≤ dim A`). -/

theorem Ring.krullDimLE_one_quotient_of_height_eq_one {A : Type u} [CommRing A] [IsLocalRing A]
    [IsNoetherianRing A] (hA : ringKrullDim A = 2) (q : PrimeSpectrum A) (hq : q.asIdeal.height = 1) :
    Ring.KrullDimLE 1 (A ⧸ q.asIdeal) := by
  rw [Ring.krullDimLE_iff]
  by_contra hcon
  rw [not_le] at hcon
  have h2 : ((2 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (A ⧸ q.asIdeal) := by
    revert hcon
    generalize ringKrullDim (A ⧸ q.asIdeal) = d
    induction d using WithBot.recBotCoe with
    | bot => intro h; exact absurd h (by simp)
    | coe n =>
      intro h
      have h' : (1 : ℕ∞) < n := by exact_mod_cast h
      have h'' : (1 : ℕ∞) + 1 ≤ n := Order.add_one_le_of_lt h'
      have e : ((2 : ℕ) : WithBot ℕ∞) = (((1 : ℕ∞) + 1 : ℕ∞) : WithBot ℕ∞) := by norm_num
      rw [e]
      exact WithBot.coe_le_coe.mpr h''
  obtain ⟨l, hl⟩ := Order.le_krullDim_iff.mp h2
  -- pull back to `Spec A`: strictly increasing, and all `≥ q`
  let c : PrimeSpectrum (A ⧸ q.asIdeal) → PrimeSpectrum A :=
    PrimeSpectrum.comap (Ideal.Quotient.mk q.asIdeal)
  have hc : StrictMono c := by
    intro a b hab
    refine lt_of_le_of_ne (Ideal.comap_mono hab.le) fun h => hab.ne ?_
    exact PrimeSpectrum.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective h
  have i0 : (0 : ℕ) < l.length + 1 := by omega
  have i1 : (1 : ℕ) < l.length + 1 := by omega
  have i2 : (2 : ℕ) < l.length + 1 := by omega
  have s01 : c (l ⟨0, i0⟩) < c (l ⟨1, i1⟩) := hc (l.strictMono (by simp [Fin.lt_def]))
  have s12 : c (l ⟨1, i1⟩) < c (l ⟨2, i2⟩) := hc (l.strictMono (by simp [Fin.lt_def]))
  have hq0 : q ≤ c (l ⟨0, i0⟩) := by
    intro x hx
    change Ideal.Quotient.mk q.asIdeal x ∈ (l ⟨0, i0⟩).asIdeal
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]; exact Ideal.zero_mem _
  have hh0 : (1 : ℕ∞) ≤ Order.height (c (l ⟨0, i0⟩)) := by
    rw [← hq, PrimeSpectrum.height_eq_orderHeight]; exact Order.height_mono hq0
  have hh1 : (1 : ℕ∞) + 1 ≤ Order.height (c (l ⟨1, i1⟩)) :=
    le_trans (by gcongr) (Order.height_add_one_le s01)
  have h3 : (1 : ℕ∞) + 1 + 1 ≤ Order.height (c (l ⟨2, i2⟩)) :=
    le_trans (by gcongr) (Order.height_add_one_le s12)
  have hlast : (Order.height (c (l ⟨2, i2⟩)) : WithBot ℕ∞) ≤ ringKrullDim A :=
    Order.height_le_krullDim _
  rw [hA] at hlast
  have : (((1 : ℕ∞) + 1 + 1 : ℕ∞) : WithBot ℕ∞) ≤ 2 := le_trans (WithBot.coe_le_coe.mpr h3) hlast
  have this' : (((1 : ℕ∞) + 1 + 1 : ℕ∞) : WithBot ℕ∞) ≤ ((2 : ℕ∞) : WithBot ℕ∞) := this
  have h32 : ((1 : ℕ∞) + 1 + 1) ≤ 2 := WithBot.coe_le_coe.mp this'
  exact absurd h32 (by decide)

/-- `ord_{A/q}(∂_{A_q}(f, g))`, the summand of Stacks 0EAX. -/
def Ring.tameOrd (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsNoetherianRing A] (hA : ringKrullDim A = 2)
    (hfin : ∀ q : PrimeSpectrum A, q.asIdeal.height = 1 →
      Module.Finite (Localization.AtPrime q.asIdeal)
        (integralClosure (Localization.AtPrime q.asIdeal) (FractionRing A)))
    (q : {q : PrimeSpectrum A // q.asIdeal.height = 1}) (f g : (FractionRing A)ˣ) :
    WithZero (Multiplicative ℤ) :=
  letI : Ring.KrullDimLE 1 (Localization.AtPrime q.1.asIdeal) :=
    Ring.krullDimLE_one_localization_of_height_eq_one q.1 q.2
  letI : Ring.KrullDimLE 1 (A ⧸ q.1.asIdeal) :=
    Ring.krullDimLE_one_quotient_of_height_eq_one hA q.1 q.2
  Ring.ordFrac (A ⧸ q.1.asIdeal) (K := q.1.asIdeal.ResidueField)
    (Ring.tameSymbol (Localization.AtPrime q.1.asIdeal) (hfin q.1 q.2) f g)

theorem Ring.tameOrd_mul_left (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsNoetherianRing A] (hA : ringKrullDim A = 2)
    (hfin : ∀ q : PrimeSpectrum A, q.asIdeal.height = 1 →
      Module.Finite (Localization.AtPrime q.asIdeal)
        (integralClosure (Localization.AtPrime q.asIdeal) (FractionRing A)))
    (q : {q : PrimeSpectrum A // q.asIdeal.height = 1}) (f f' g : (FractionRing A)ˣ) :
    Ring.tameOrd A hA hfin q (f * f') g = Ring.tameOrd A hA hfin q f g * Ring.tameOrd A hA hfin q f' g := by
  unfold Ring.tameOrd
  letI : Ring.KrullDimLE 1 (Localization.AtPrime q.1.asIdeal) :=
    Ring.krullDimLE_one_localization_of_height_eq_one q.1 q.2
  rw [Ring.tameSymbol_mul_left, map_mul]

theorem Ring.tameOrd_mul_right (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsNoetherianRing A] (hA : ringKrullDim A = 2)
    (hfin : ∀ q : PrimeSpectrum A, q.asIdeal.height = 1 →
      Module.Finite (Localization.AtPrime q.asIdeal)
        (integralClosure (Localization.AtPrime q.asIdeal) (FractionRing A)))
    (q : {q : PrimeSpectrum A // q.asIdeal.height = 1}) (f g g' : (FractionRing A)ˣ) :
    Ring.tameOrd A hA hfin q f (g * g') = Ring.tameOrd A hA hfin q f g * Ring.tameOrd A hA hfin q f g' := by
  unfold Ring.tameOrd
  letI : Ring.KrullDimLE 1 (Localization.AtPrime q.1.asIdeal) :=
    Ring.krullDimLE_one_localization_of_height_eq_one q.1 q.2
  rw [Ring.tameSymbol_mul_right, map_mul]

end
