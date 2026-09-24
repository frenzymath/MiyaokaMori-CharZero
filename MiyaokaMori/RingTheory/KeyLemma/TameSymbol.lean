import MiyaokaMori.Prelude
import MiyaokaMori.RingTheory.Length.LengthSumInertia
import MiyaokaMori.RingTheory.OrderOfVanishing.Stacks02mj
import MiyaokaMori.RingTheory.KeyLemma.TameSymbolValuationOrd
import MiyaokaMori.RingTheory.KeyLemma.TameSymbolResidueDegree

/-! # The tame symbol of a one-dimensional Noetherian local domain

The tame symbol `∂_A : K^* × K^* → κ^*` of a one-dimensional Noetherian local domain `A` (fraction field `K`,
residue field `κ`): taking the normalization `Ã` (a semi-local Dedekind domain),
`∂_A(f,g) = ∏_v Norm_{κ(v)/κ}((−1)^{ord_v f·ord_v g} f^{ord_v g}/g^{ord_v f} mod 𝔪_v)` (Stacks 0EAQ with
`B = Ã`); together with: the value is nonzero, multiplicativity in the second variable, antisymmetry (0EAS),
and the normalization `∂(u,g) = ū^{ord_A g}` (0EAN).

References: Stacks 0EAQ (chow-equation-tame-symbol, the recipe), 0EAR (chow-lemma-well-defined-tame-symbol,
well-definedness), 0EAS (chow-lemma-tame-symbol, properties 0EAL/0EAM/0EAN); for the normalization, Stacks 09IG
(a variant of Krull–Akizuki).

`Ring.tameSymbolAt`, `Ring.tameSymbol` and the four properties of 0EAS carry the hypothesis
`hfin : Module.Finite A (integralClosure A K)` (finite normalization). Without it the definition would need
"the integral closure of a one-dimensional Noetherian domain is Dedekind" (Krull–Akizuki, Stacks 09IG), which
is not in Mathlib; with `hfin`, `Ã` is Noetherian, integrally closed and satisfies `Ring.DimensionLEOne`
(preserved by integral extensions), hence Dedekind. The hypothesis also matches the recipe of Stacks: when `Ã`
is finite, `Ã` is an admissible `B` of 0EAG and this definition agrees with the `∂` of Stacks; when `Ã` is not
finite (`A` analytically ramified) the two differ anyway (0EAN fails for this definition). The user 0EAX
requires `hfin` at each `A_q`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/- The tame symbol `∂_A : K^* × K^* → κ^*` (the `∂_A` of Stacks, section 0EAH; recipe 0EAQ, well-definedness
   0EAR, properties 0EAS). `A` is a one-dimensional (`Ring.KrullDimLE 1`) Noetherian local domain and `K` its
   fraction field. The recipe of Stacks first chooses a finite extension `B` by 0EAG (existence); here the
   definition takes `B = Ã`, the normalization (the integral closure of `A` in `K`; Dedekind by `hfin`, with
   finitely many maximal ideals and residue fields finite over `κ`), whose local rings `Ã_v` are DVRs, so with
   a uniformizer `π_v` the `m_v = length(Ã_v/π_v)` of 0EAQ is `1` and the formula becomes
     ∂_A(f, g) = ∏_v Norm_{κ(v)/κ}( (−1)^{ord_v f · ord_v g} · f^{ord_v g} / g^{ord_v f} mod 𝔪_v ).
   `ord_v` is Mathlib's `HeightOneSpectrum.valuation` (`v(x) = exp(−ord_v x)`); "mod `𝔪_v`" is taken in the
   residue field of the valuation subring `(v.valuation K).valuationSubring` (`= Ã_v`); `κ(v)` becomes a
   `κ`-algebra via the local homomorphism `A → Ã_v`, and the norm is `Algebra.norm`.
   Relation to the recipe of Stacks: when `Ã` is finite over `A`, `Ã` itself is an admissible `B` of 0EAG, and
   by 0EAR (independence of the choice of `B`) the two agree; when `Ã` is not finite (`A` analytically
   ramified) they differ in general (the normalization property 0EAN fails for this definition), which is why
   the normalization property carries the finiteness assumption. -/

/-- If the normalization `Ã` is finite over `A`, then `Ã` is a Dedekind domain.

The hypothesis `hfin : Module.Finite A (integralClosure A K)` replaces Krull–Akizuki (the integral closure of
a one-dimensional Noetherian domain is Dedekind), which is not in Mathlib: with `hfin`, `Ã` is Noetherian as
a finite `A`-module, integrally closed as an integral closure, and integral extensions preserve
`Ring.DimensionLEOne`; together this is Dedekind. All users (0EAX, 0EAN, 0AYC) are in the setting of
Nagata rings / finite normalization and can supply `hfin`. -/

theorem Ring.TameSymbol.isDedekindDomain_integralClosure (A : Type u) [CommRing A] [IsDomain A]
    [IsNoetherianRing A] [Ring.KrullDimLE 1 A] (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K]
    (hfin : Module.Finite A (integralClosure A K)) :
    IsDedekindDomain (integralClosure A K) := by
  haveI := hfin
  haveI : Ring.DimensionLEOne A := ⟨fun hp0 hp => hp.isMaximal_of_ne_bot hp0⟩
  haveI hdim : Ring.DimensionLEOne (integralClosure A K) := inferInstance
  haveI hN : IsNoetherianRing (integralClosure A K) :=
    IsNoetherianRing.of_finite A (integralClosure A K)
  haveI hIC : IsIntegrallyClosed (integralClosure A K) :=
    integralClosure.isIntegrallyClosedOfFiniteExtension (R := A) K (L := K)
  exact { }

/-- The fraction field of the integral closure is still `K` (`K` is algebraic over `A`; Mathlib
`integralClosure.isFractionRing_of_algebraic`). -/

theorem Ring.TameSymbol.isFractionRing_integralClosure (A : Type u) [CommRing A] [IsDomain A]
    (K : Type u) [Field K] [Algebra A K] [IsFractionRing A K] :
    IsFractionRing (integralClosure A K) K := by
  have : Algebra.IsAlgebraic A K := IsLocalization.isAlgebraic K (nonZeroDivisors A)
  exact integralClosure.isFractionRing_of_algebraic (A := A) (L := K)
    (fun x hx => (IsFractionRing.injective A K) (by rw [hx, map_zero]))

/-- Elements of `A` lie in the valuation ring of `v` (`Ã_v ⊇ Ã ⊇ A`). -/
theorem Ring.TameSymbol.algebraMap_mem_valuationSubring (A : Type u) [CommRing A] [IsDomain A]
    {K : Type u} [Field K] [Algebra A K] [IsDedekindDomain (integralClosure A K)]
    [IsFractionRing (integralClosure A K) K]
    (v : IsDedekindDomain.HeightOneSpectrum (integralClosure A K)) (r : A) :
    algebraMap A K r ∈ (IsDedekindDomain.HeightOneSpectrum.valuation K v).valuationSubring := by
  have h : algebraMap A K r = algebraMap (integralClosure A K) K (algebraMap A (integralClosure A K) r) :=
    IsScalarTower.algebraMap_apply A (integralClosure A K) K r
  rw [h]
  exact IsDedekindDomain.HeightOneSpectrum.valuation_le_one v _

/-- The map `A → Ã_v` (the valuation ring of `v`). -/
noncomputable def Ring.TameSymbol.toValuationSubring (A : Type u) [CommRing A] [IsDomain A]
    {K : Type u} [Field K] [Algebra A K] [IsDedekindDomain (integralClosure A K)]
    [IsFractionRing (integralClosure A K) K]
    (v : IsDedekindDomain.HeightOneSpectrum (integralClosure A K)) :
    A →+* (IsDedekindDomain.HeightOneSpectrum.valuation K v).valuationSubring where
  toFun := fun r => ⟨algebraMap A K r, Ring.TameSymbol.algebraMap_mem_valuationSubring A v r⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' := fun r s => Subtype.ext (map_mul _ r s)
  map_zero' := Subtype.ext (map_zero _)
  map_add' := fun r s => Subtype.ext (map_add _ r s)

/-- `A → Ã_v` is a local homomorphism: `v ∩ A` is a nonzero prime of `A` (`Ã` is integral over `A`), and `A` is
a one-dimensional local domain, so `v ∩ A = 𝔪_A`. -/
theorem Ring.TameSymbol.isLocalHom_toValuationSubring (A : Type u) [CommRing A] [IsDomain A]
    [IsLocalRing A] [Ring.KrullDimLE 1 A]
    {K : Type u} [Field K] [Algebra A K] [IsDedekindDomain (integralClosure A K)]
    [IsFractionRing (integralClosure A K) K]
    (v : IsDedekindDomain.HeightOneSpectrum (integralClosure A K)) :
    IsLocalHom (Ring.TameSymbol.toValuationSubring A v) := by
  refine ⟨fun r hr => ?_⟩
  by_contra hru
  have hrm : r ∈ IsLocalRing.maximalIdeal A := (IsLocalRing.mem_maximalIdeal r).mpr hru
  -- v ∩ A = 𝔪_A
  obtain ⟨x, hxv, hx0⟩ : ∃ x ∈ v.asIdeal, x ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact v.ne_bot (eq_bot_iff.mpr fun x hx => (Submodule.mem_bot _).mpr (hcon x hx))
  have hne : v.asIdeal.comap (algebraMap A (integralClosure A K)) ≠ ⊥ :=
    Ideal.comap_ne_bot_of_integral_mem hx0 hxv (Algebra.IsIntegral.isIntegral x)
  have hprime : (v.asIdeal.comap (algebraMap A (integralClosure A K))).IsPrime :=
    Ideal.comap_isPrime _ _
  have hmax := hprime.isMaximal_of_ne_bot hne
  have hrv : algebraMap A (integralClosure A K) r ∈ v.asIdeal := by
    have : r ∈ v.asIdeal.comap (algebraMap A (integralClosure A K)) := by
      rw [IsLocalRing.eq_maximalIdeal hmax]; exact hrm
    exact this
  have hlt : IsDedekindDomain.HeightOneSpectrum.valuation K v (algebraMap A K r) < 1 := by
    rw [IsScalarTower.algebraMap_apply A (integralClosure A K) K r]
    exact (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem v _).mpr hrv
  obtain ⟨b, hb⟩ := hr.exists_right_inv
  have hb' : IsDedekindDomain.HeightOneSpectrum.valuation K v (algebraMap A K r) *
      IsDedekindDomain.HeightOneSpectrum.valuation K v (b : K) = 1 := by
    rw [← map_mul]
    have := congrArg Subtype.val hb
    change algebraMap A K r * (b : K) = 1 at this
    rw [this, map_one]
  have hb1 : IsDedekindDomain.HeightOneSpectrum.valuation K v (b : K) ≤ 1 := b.2
  have : IsDedekindDomain.HeightOneSpectrum.valuation K v (algebraMap A K r) *
      IsDedekindDomain.HeightOneSpectrum.valuation K v (b : K) < 1 :=
    lt_of_le_of_lt (mul_le_of_le_one_right' hb1) hlt
  exact absurd hb' this.ne

/-- For any `ℤᵐ⁰`-valued valuation `val` and `f, g ∈ K^*`, with `a = ord f`, `b = ord g` (`ord x = −log val x`),
the element `u = (−1)^{ab} f^b / g^a` has valuation `1`; in particular `u` lies in the valuation ring. -/
theorem Ring.TameSymbol.symbol_mem_valuationSubring {K : Type u} [Field K]
    (val : Valuation K (WithZero (Multiplicative ℤ))) (f g : Kˣ) :
    (-1 : K) ^ ((- Multiplicative.toAdd (WithZero.unzero ((Valuation.ne_zero_iff val).mpr f.ne_zero))) *
        (- Multiplicative.toAdd (WithZero.unzero ((Valuation.ne_zero_iff val).mpr g.ne_zero)))) *
      (f : K) ^ (- Multiplicative.toAdd (WithZero.unzero ((Valuation.ne_zero_iff val).mpr g.ne_zero))) /
      (g : K) ^ (- Multiplicative.toAdd (WithZero.unzero ((Valuation.ne_zero_iff val).mpr f.ne_zero)))
      ∈ val.valuationSubring := by
  set x := WithZero.unzero ((Valuation.ne_zero_iff val).mpr f.ne_zero) with hx
  set y := WithZero.unzero ((Valuation.ne_zero_iff val).mpr g.ne_zero) with hy
  have hfx : val (f : K) = (x : WithZero (Multiplicative ℤ)) := (WithZero.coe_unzero _).symm
  have hgy : val (g : K) = (y : WithZero (Multiplicative ℤ)) := (WithZero.coe_unzero _).symm
  have hneg : val ((-1 : K) ^ ((- Multiplicative.toAdd x) * (- Multiplicative.toAdd y))) = 1 := by
    rw [map_zpow₀, Valuation.map_neg, map_one, one_zpow]
  have hxy : x ^ (- Multiplicative.toAdd y) = y ^ (- Multiplicative.toAdd x) := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_zpow, toAdd_zpow]
    simp only [smul_eq_mul]
    ring
  change val _ ≤ 1
  rw [map_div₀, map_mul, hneg, one_mul, map_zpow₀, map_zpow₀, hfx, hgy, ← WithZero.coe_zpow,
    ← WithZero.coe_zpow, hxy, div_self (WithZero.coe_ne_zero)]

namespace Ring.TameSymbol

section Valuation

variable {K : Type u} [Field K] (val : Valuation K (WithZero (Multiplicative ℤ)))

/-- `ord x = −log val x` (`x ∈ K^*`). -/
def ordv (x : Kˣ) : ℤ :=
  - Multiplicative.toAdd (WithZero.unzero ((Valuation.ne_zero_iff val).mpr x.ne_zero))

theorem ordv_mul (x y : Kˣ) : ordv val (x * y) = ordv val x + ordv val y := by
  unfold ordv
  have h : WithZero.unzero ((Valuation.ne_zero_iff val).mpr (x * y).ne_zero) =
      WithZero.unzero ((Valuation.ne_zero_iff val).mpr x.ne_zero) *
        WithZero.unzero ((Valuation.ne_zero_iff val).mpr y.ne_zero) := by
    apply WithZero.coe_injective
    rw [WithZero.coe_mul, WithZero.coe_unzero, WithZero.coe_unzero, WithZero.coe_unzero,
      Units.val_mul, map_mul]
  rw [h, toAdd_mul, neg_add]

theorem ordv_eq_zero (x : Kˣ) (h : val (x : K) = 1) : ordv val x = 0 := by
  unfold ordv
  have h1 : WithZero.unzero ((Valuation.ne_zero_iff val).mpr x.ne_zero) = 1 := by
    apply WithZero.coe_injective
    rw [WithZero.coe_unzero, h, WithZero.coe_one]
  rw [h1, toAdd_one, neg_zero]

/-- `u(f, g) = (−1)^{ab} f^b / g^a ∈ O_val`, with `a = ord f`, `b = ord g`. -/
def symbolElt (f g : Kˣ) : val.valuationSubring :=
  ⟨(-1 : K) ^ (ordv val f * ordv val g) * (f : K) ^ (ordv val g) / (g : K) ^ (ordv val f),
    Ring.TameSymbol.symbol_mem_valuationSubring val f g⟩

theorem symbolElt_mul_right (f g h : Kˣ) :
    symbolElt val f (g * h) = symbolElt val f g * symbolElt val f h := by
  apply Subtype.ext
  change (-1 : K) ^ (ordv val f * ordv val (g * h)) * (f : K) ^ (ordv val (g * h)) /
      ((g * h : Kˣ) : K) ^ (ordv val f) =
    ((-1 : K) ^ (ordv val f * ordv val g) * (f : K) ^ (ordv val g) / (g : K) ^ (ordv val f)) *
      ((-1 : K) ^ (ordv val f * ordv val h) * (f : K) ^ (ordv val h) / (h : K) ^ (ordv val f))
  have hm1 : (-1 : K) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  rw [ordv_mul, mul_add, zpow_add₀ hm1, zpow_add₀ f.ne_zero, Units.val_mul, mul_zpow]
  field_simp

theorem symbolElt_mul_swap (f g : Kˣ) : symbolElt val f g * symbolElt val g f = 1 := by
  apply Subtype.ext
  change ((-1 : K) ^ (ordv val f * ordv val g) * (f : K) ^ (ordv val g) / (g : K) ^ (ordv val f)) *
      ((-1 : K) ^ (ordv val g * ordv val f) * (g : K) ^ (ordv val f) / (f : K) ^ (ordv val g)) = 1
  have h1 : (-1 : K) ^ (ordv val f * ordv val g) * (-1 : K) ^ (ordv val g * ordv val f) = 1 := by
    rw [mul_comm (ordv val g), ← mul_zpow]
    norm_num
  have hf : (f : K) ^ (ordv val g) ≠ 0 := zpow_ne_zero _ f.ne_zero
  have hg : (g : K) ^ (ordv val f) ≠ 0 := zpow_ne_zero _ g.ne_zero
  field_simp
  linear_combination h1

theorem symbolElt_eq_one (f g : Kˣ) (hf : val (f : K) = 1) (hg : val (g : K) = 1) :
    symbolElt val f g = 1 := by
  apply Subtype.ext
  change (-1 : K) ^ (ordv val f * ordv val g) * (f : K) ^ (ordv val g) / (g : K) ^ (ordv val f) = 1
  rw [ordv_eq_zero val f hf, ordv_eq_zero val g hg]
  simp

end Valuation

section LocalFactor

variable (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A] [Ring.KrullDimLE 1 A]
  {K : Type u} [Field K] [Algebra A K] [IsDedekindDomain (integralClosure A K)]
  [IsFractionRing (integralClosure A K) K]

/-- The local factor `Norm_{κ(v)/κ}(u(f, g) mod 𝔪_v)` at `v`. -/
noncomputable def localFactor (v : IsDedekindDomain.HeightOneSpectrum (integralClosure A K))
    (f g : Kˣ) : IsLocalRing.ResidueField A :=
  let val := IsDedekindDomain.HeightOneSpectrum.valuation K v
  let O := val.valuationSubring
  let φ : A →+* O := Ring.TameSymbol.toValuationSubring A v
  haveI : IsLocalHom φ := Ring.TameSymbol.isLocalHom_toValuationSubring A v
  letI : Algebra (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField O) :=
    (IsLocalRing.ResidueField.map φ).toAlgebra
  Algebra.norm (IsLocalRing.ResidueField A) (IsLocalRing.residue O (symbolElt val f g))

theorem localFactor_mul_right (v : IsDedekindDomain.HeightOneSpectrum (integralClosure A K))
    (f g h : Kˣ) : localFactor A v f (g * h) = localFactor A v f g * localFactor A v f h := by
  simp only [localFactor]
  simp only [symbolElt_mul_right, map_mul]

theorem localFactor_mul_swap (v : IsDedekindDomain.HeightOneSpectrum (integralClosure A K))
    (f g : Kˣ) : localFactor A v f g * localFactor A v g f = 1 := by
  simp only [localFactor]
  simp only [← map_mul, symbolElt_mul_swap, map_one]

theorem localFactor_eq_one (v : IsDedekindDomain.HeightOneSpectrum (integralClosure A K))
    (f g : Kˣ) (hf : IsDedekindDomain.HeightOneSpectrum.valuation K v (f : K) = 1)
    (hg : IsDedekindDomain.HeightOneSpectrum.valuation K v (g : K) = 1) :
    localFactor A v f g = 1 := by
  simp only [localFactor]
  simp only [symbolElt_eq_one _ f g hf hg, map_one]

/-- Only finitely many `v` have `v(f) ≠ 1`. -/
theorem finite_valuation_ne_one (f : Kˣ) :
    {v : IsDedekindDomain.HeightOneSpectrum (integralClosure A K) |
      IsDedekindDomain.HeightOneSpectrum.valuation K v (f : K) ≠ 1}.Finite := by
  refine ((IsDedekindDomain.HeightOneSpectrum.Support.finite (integralClosure A K) (f : K)).union
    (IsDedekindDomain.HeightOneSpectrum.Support.finite (integralClosure A K) ((f⁻¹ : Kˣ) : K))).subset ?_
  intro v hv
  rcases lt_or_gt_of_ne hv with h | h
  · right
    change 1 < IsDedekindDomain.HeightOneSpectrum.valuation K v ((f⁻¹ : Kˣ) : K)
    rw [Units.val_inv_eq_inv_val, map_inv₀]
    exact (one_lt_inv₀ (lt_of_le_of_ne zero_le (Ne.symm
      ((Valuation.ne_zero_iff _).mpr f.ne_zero)))).mpr h
  · left; exact h

theorem finite_mulSupport_localFactor (f g : Kˣ) :
    (Function.mulSupport fun v : IsDedekindDomain.HeightOneSpectrum (integralClosure A K) =>
      localFactor A v f g).Finite := by
  refine ((finite_valuation_ne_one A f).union (finite_valuation_ne_one A g)).subset ?_
  intro v hv
  by_contra hcon
  rw [Set.mem_union, not_or] at hcon
  exact hv (localFactor_eq_one A v f g (not_not.mp hcon.1) (not_not.mp hcon.2))

end LocalFactor

end Ring.TameSymbol

namespace Ring.TameSymbol

section UnitLeft

variable (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A] [Ring.KrullDimLE 1 A]
  {K : Type u} [Field K] [Algebra A K] [IsDedekindDomain (integralClosure A K)]
  [IsFractionRing (integralClosure A K) K]

/-- Units of `A` have valuation `1` at every `v` (both `u` and `u⁻¹` lie in the valuation ring). -/
theorem valuation_unit_eq_one (v : IsDedekindDomain.HeightOneSpectrum (integralClosure A K))
    (u : Aˣ) :
    IsDedekindDomain.HeightOneSpectrum.valuation K v (algebraMap A K (u : A)) = 1 := by
  set val := IsDedekindDomain.HeightOneSpectrum.valuation K v with hval
  have h1 : val (algebraMap A K (u : A)) ≤ 1 :=
    Ring.TameSymbol.algebraMap_mem_valuationSubring A v (u : A)
  have h2 : val (algebraMap A K ((u⁻¹ : Aˣ) : A)) ≤ 1 :=
    Ring.TameSymbol.algebraMap_mem_valuationSubring A v ((u⁻¹ : Aˣ) : A)
  have hmul : val (algebraMap A K (u : A)) * val (algebraMap A K ((u⁻¹ : Aˣ) : A)) = 1 := by
    rw [← map_mul, ← map_mul, u.mul_inv, map_one, map_one]
  refine le_antisymm h1 ?_
  calc (1 : WithZero (Multiplicative ℤ))
      = val (algebraMap A K (u : A)) * val (algebraMap A K ((u⁻¹ : Aˣ) : A)) := hmul.symm
    _ ≤ val (algebraMap A K (u : A)) := mul_le_of_le_one_right' h2

/-- Units of `A` have `ord` equal to `0` at every `v`. -/
theorem ordv_unit (v : IsDedekindDomain.HeightOneSpectrum (integralClosure A K)) (u : Aˣ) :
    ordv (IsDedekindDomain.HeightOneSpectrum.valuation K v)
      (Units.map (algebraMap A K).toMonoidHom u) = 0 :=
  ordv_eq_zero _ _ (Ring.TameSymbol.valuation_unit_eq_one A v u)

/-- For `u ∈ A^*`, `symbolElt` degenerates to `u^{ord_v g}`: `a = ord_v u = 0`, so `(−1)^{ab} = 1` and `g^a = 1`.
The right-hand side is written as `u^{ord_v g}` in the unit group of `A`, pushed along `A → Ã_v`, so that
`ResidueField.map` can be used when taking residue classes in the next step. -/
theorem symbolElt_unit_left (v : IsDedekindDomain.HeightOneSpectrum (integralClosure A K))
    (u : Aˣ) (g : Kˣ) :
    symbolElt (IsDedekindDomain.HeightOneSpectrum.valuation K v)
        (Units.map (algebraMap A K).toMonoidHom u) g
      = Ring.TameSymbol.toValuationSubring A v
          ((u ^ (ordv (IsDedekindDomain.HeightOneSpectrum.valuation K v) g) : Aˣ) : A) := by
  set val := IsDedekindDomain.HeightOneSpectrum.valuation K v with hval
  set φ := (algebraMap A K).toMonoidHom with hφ
  set U := Units.map φ u with hU
  set n := ordv val g with hn
  apply Subtype.ext
  show (-1 : K) ^ (ordv val U * n) * (U : K) ^ n / (g : K) ^ (ordv val U)
      = algebraMap A K ((u ^ n : Aˣ) : A)
  rw [Ring.TameSymbol.ordv_unit A v u, zero_mul, zpow_zero, one_mul, zpow_zero, div_one]
  calc (U : K) ^ n = ((U ^ n : Kˣ) : K) := (Units.val_zpow_eq_zpow_val U n).symm
    _ = ((Units.map φ (u ^ n) : Kˣ) : K) := by rw [hU, map_zpow]
    _ = algebraMap A K ((u ^ n : Aˣ) : A) := rfl


/-- The local factor for `u ∈ A^*`: `∂_v(u, g) = ū^{[κ(v):κ]·ord_v g}`.
Three steps: `symbolElt_unit_left` (`symbolElt = φ(u^{ord_v g})`), `ResidueField.map_residue` (residue classes
commute with `φ`), `Algebra.norm_algebraMap` (the norm of an element of the base field is its `[κ(v):κ]`-th
power). -/
theorem localFactor_unit_left (v : IsDedekindDomain.HeightOneSpectrum (integralClosure A K))
    (u : Aˣ) (g : Kˣ) :
    letI : IsLocalHom (Ring.TameSymbol.toValuationSubring A v) :=
      Ring.TameSymbol.isLocalHom_toValuationSubring A v
    letI : Algebra (IsLocalRing.ResidueField A)
        (IsLocalRing.ResidueField
          (IsDedekindDomain.HeightOneSpectrum.valuation K v).valuationSubring) :=
      (IsLocalRing.ResidueField.map (Ring.TameSymbol.toValuationSubring A v)).toAlgebra
    localFactor A v (Units.map (algebraMap A K).toMonoidHom u) g
      = IsLocalRing.residue A (u : A) ^
          ((Module.finrank (IsLocalRing.ResidueField A)
              (IsLocalRing.ResidueField
                (IsDedekindDomain.HeightOneSpectrum.valuation K v).valuationSubring) : ℤ) *
            ordv (IsDedekindDomain.HeightOneSpectrum.valuation K v) g) := by
  letI hloc : IsLocalHom (Ring.TameSymbol.toValuationSubring A v) :=
    Ring.TameSymbol.isLocalHom_toValuationSubring A v
  letI halg : Algebra (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField
        (IsDedekindDomain.HeightOneSpectrum.valuation K v).valuationSubring) :=
    (IsLocalRing.ResidueField.map (Ring.TameSymbol.toValuationSubring A v)).toAlgebra
  have hmap : (algebraMap (IsLocalRing.ResidueField A)
      (IsLocalRing.ResidueField
        (IsDedekindDomain.HeightOneSpectrum.valuation K v).valuationSubring)) =
      IsLocalRing.ResidueField.map (Ring.TameSymbol.toValuationSubring A v) :=
    RingHom.algebraMap_toAlgebra _
  -- the residue class of `ū^n`
  have hu : ∀ n : ℤ, IsLocalRing.residue A ((u ^ n : Aˣ) : A)
      = IsLocalRing.residue A (u : A) ^ n := by
    intro n
    calc IsLocalRing.residue A ((u ^ n : Aˣ) : A)
        = ((Units.map (IsLocalRing.residue A).toMonoidHom (u ^ n) :
            (IsLocalRing.ResidueField A)ˣ) : IsLocalRing.ResidueField A) := rfl
      _ = (((Units.map (IsLocalRing.residue A).toMonoidHom u) ^ n :
            (IsLocalRing.ResidueField A)ˣ) : IsLocalRing.ResidueField A) := by rw [map_zpow]
      _ = IsLocalRing.residue A (u : A) ^ n := Units.val_zpow_eq_zpow_val _ _
  simp only [localFactor]
  rw [Ring.TameSymbol.symbolElt_unit_left A v u g,
    ← IsLocalRing.ResidueField.map_residue (Ring.TameSymbol.toValuationSubring A v), hu,
    ← hmap, Algebra.norm_algebraMap,
    ← zpow_natCast (IsLocalRing.residue A (u : A) ^
      ordv (IsDedekindDomain.HeightOneSpectrum.valuation K v) g) _,
    ← zpow_mul, mul_comm]


/-- A finite product of powers `a^{f i}` (`a ≠ 0`, integer exponents). -/
private theorem prod_zpow_eq_zpow_sum {ι M : Type*} [DecidableEq ι] [Field M] (s : Finset ι)
    (f : ι → ℤ) {a : M} (ha : a ≠ 0) : ∏ i ∈ s, a ^ f i = a ^ (∑ i ∈ s, f i) := by
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, ih, zpow_add₀ ha]

/-- Only finitely many `v` have `ord_v g ≠ 0`. -/
theorem finite_support_ordv (g : Kˣ) :
    {v : IsDedekindDomain.HeightOneSpectrum (integralClosure A K) |
      ordv (IsDedekindDomain.HeightOneSpectrum.valuation K v) g ≠ 0}.Finite := by
  refine (Ring.TameSymbol.finite_valuation_ne_one A g).subset fun v hv => ?_
  by_contra hcon
  exact hv (ordv_eq_zero _ g (not_not.mp hcon))

/-- **The arithmetic core of 0EAN** (Stacks 02MJ with `B = Ã`, `L = K`):
`Σ_{v ∈ MaxSpec Ã} [κ(v):κ] · ord_v(g) = ord_A(g)` (`g ∈ K^*`).

Proof (assembled from `TameSymbolValuationOrd`, `TameSymbolResidueDegree` and 02MJ):
1. Let `B := integralClosure A K`, `haveI := hfin`. `IsFractionRing.div_surjective (A := B) (g : K)` writes
   `g = b/b'` (`b, b' ∈ B ∖ 0`). Stacks 02MJ (`Ring.ordFrac_norm_eq_sum_inertiaDeg_mul_ord_of_eq_div` with
   `L = K`; `Algebra.norm K` on `K` is the identity) gives
   `ordFrac A g = exp (Σ_{m ∈ MaxSpec B} inertiaDeg' 𝔪_A m · (ord_{B_m} b − ord_{B_m} b'))`.
   `FaithfulSMul A B` follows from injectivity of `A → K` (`IsFractionRing.injective`) via
   `faithfulSMul_iff_algebraMap_injective`.
2. **Index correspondence**: when `B` is not a field, Mathlib's
   `IsDedekindDomain.HeightOneSpectrum.equivMaximalSpectrum` is `HeightOneSpectrum B ≃ MaximalSpectrum B`
   with `(equivMaximalSpectrum h v).asIdeal = v.asIdeal` by `rfl`; re-index with `finsum_comp_equiv`.
   Degenerate case `B` a field: then `HeightOneSpectrum B` is empty (`finsum_of_isEmpty`), and termwise on
   the right-hand side of 02MJ `Ring.ord_of_isUnit` applies (`B` a field ⇒ `b, b'` units ⇒ `Ring.ord = 0` in
   the localization), so both sides are `0`.
3. **Termwise**: `Ring.TameSymbol.finrank_residueField_valuationSubring_eq_inertiaDeg'`
   (`φ := toValuationSubring A v`, `hφ` is `IsScalarTower.algebraMap_apply A B K`) replaces `finrank` by
   `inertiaDeg'`; `Ring.TameSymbol.valuation_eq_exp_neg_ord_localization` gives `v(b) = exp(−ord_{B_v} b)`,
   hence `v(g) = exp(ord b' − ord b)` and `ordv (v.valuation K) g = ord b − ord b'` (unfold `ordv`,
   `WithZero.unzero_coe`/`WithZero.exp`).
References: Stacks 0EAN (the normalization clause of `chow-lemma-tame-symbol`), 02MJ. -/
theorem finsum_finrank_mul_ordv_eq_ordFrac [IsNoetherianRing A]
    [IsFractionRing A K] (hfin : Module.Finite A (integralClosure A K)) (g : Kˣ) :
    letI : ∀ v : IsDedekindDomain.HeightOneSpectrum (integralClosure A K),
        IsLocalHom (Ring.TameSymbol.toValuationSubring A v) := fun v =>
      Ring.TameSymbol.isLocalHom_toValuationSubring A v
    letI : ∀ v : IsDedekindDomain.HeightOneSpectrum (integralClosure A K),
        Algebra (IsLocalRing.ResidueField A)
          (IsLocalRing.ResidueField
            (IsDedekindDomain.HeightOneSpectrum.valuation K v).valuationSubring) := fun v =>
      (IsLocalRing.ResidueField.map (Ring.TameSymbol.toValuationSubring A v)).toAlgebra
    ∑ᶠ v : IsDedekindDomain.HeightOneSpectrum (integralClosure A K),
        (Module.finrank (IsLocalRing.ResidueField A)
            (IsLocalRing.ResidueField
              (IsDedekindDomain.HeightOneSpectrum.valuation K v).valuationSubring) : ℤ) *
          ordv (IsDedekindDomain.HeightOneSpectrum.valuation K v) g
      = Multiplicative.toAdd
          (WithZero.unzero ((map_ne_zero (Ring.ordFrac A (K := K))).mpr g.ne_zero)) := by
  classical
  letI hloc : ∀ v : IsDedekindDomain.HeightOneSpectrum (integralClosure A K),
      IsLocalHom (Ring.TameSymbol.toValuationSubring A v) := fun v =>
    Ring.TameSymbol.isLocalHom_toValuationSubring A v
  letI halg : ∀ v : IsDedekindDomain.HeightOneSpectrum (integralClosure A K),
      Algebra (IsLocalRing.ResidueField A)
        (IsLocalRing.ResidueField
          (IsDedekindDomain.HeightOneSpectrum.valuation K v).valuationSubring) := fun v =>
    (IsLocalRing.ResidueField.map (Ring.TameSymbol.toValuationSubring A v)).toAlgebra
  haveI : Module.Finite A (integralClosure A K) := hfin
  haveI : FaithfulSMul A (integralClosure A K) :=
    (faithfulSMul_iff_algebraMap_injective A (integralClosure A K)).mpr (by
      intro x y hxy
      apply IsFractionRing.injective A K
      have := congrArg (algebraMap (integralClosure A K) K) hxy
      rwa [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply] at this)
  -- step 1: `g = b / b'` with `b, b' ∈ Ã ∖ 0`; apply 02MJ (`L = K`)
  obtain ⟨b, b', hb'mem, hg⟩ := IsFractionRing.div_surjective (A := integralClosure A K) (g : K)
  have hb' : b' ≠ 0 := nonZeroDivisors.ne_zero hb'mem
  have hb : b ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div] at hg
    exact g.ne_zero hg.symm
  have h02 := Ring.ordFrac_norm_eq_sum_inertiaDeg_mul_ord_of_eq_div (A := A)
    (B := integralClosure A K) (K := K) (L := K) (g : K) b b' hb hb' hg.symm
  rw [Algebra.norm_self, MonoidHom.id_apply] at h02
  -- right-hand side: `ordFrac A g = exp S ⇒ toAdd (unzero (ordFrac A g)) = S`
  have hR : Multiplicative.toAdd
      (WithZero.unzero ((map_ne_zero (Ring.ordFrac A (K := K))).mpr g.ne_zero))
      = ∑ᶠ m : MaximalSpectrum (integralClosure A K),
        (Ideal.inertiaDeg' (IsLocalRing.maximalIdeal A) m.asIdeal : ℤ) *
          (((Ring.ord (Localization.AtPrime m.asIdeal)
              (algebraMap (integralClosure A K) _ b)).toNat : ℤ) -
            ((Ring.ord (Localization.AtPrime m.asIdeal)
              (algebraMap (integralClosure A K) _ b')).toNat : ℤ)) := by
    have h1 := (WithZero.coe_unzero ((map_ne_zero (Ring.ordFrac A (K := K))).mpr g.ne_zero)).trans h02
    rw [WithZero.coe_injective h1, toAdd_ofAdd]
  rw [hR]
  -- termwise: `ordv g = ord_{Ã_v} b − ord_{Ã_v} b'`
  have hord : ∀ v : IsDedekindDomain.HeightOneSpectrum (integralClosure A K),
      ordv (IsDedekindDomain.HeightOneSpectrum.valuation K v) g =
        ((Ring.ord (Localization.AtPrime v.asIdeal)
            (algebraMap (integralClosure A K) _ b)).toNat : ℤ) -
          ((Ring.ord (Localization.AtPrime v.asIdeal)
            (algebraMap (integralClosure A K) _ b')).toNat : ℤ) := by
    intro v
    have hvb := Ring.TameSymbol.valuation_eq_exp_neg_ord_localization (K := K) v b hb
    have hvb' := Ring.TameSymbol.valuation_eq_exp_neg_ord_localization (K := K) v b' hb'
    have hvg : IsDedekindDomain.HeightOneSpectrum.valuation K v (g : K) =
        WithZero.exp (-((Ring.ord (Localization.AtPrime v.asIdeal)
            (algebraMap (integralClosure A K) _ b)).toNat : ℤ) -
          -((Ring.ord (Localization.AtPrime v.asIdeal)
            (algebraMap (integralClosure A K) _ b')).toNat : ℤ)) := by
      rw [← hg, map_div₀, hvb, hvb', WithZero.exp_sub]
    unfold ordv
    have h1 := (WithZero.coe_unzero
      ((Valuation.ne_zero_iff (IsDedekindDomain.HeightOneSpectrum.valuation K v)).mpr
        g.ne_zero)).trans hvg
    rw [WithZero.coe_injective h1, toAdd_ofAdd]
    ring
  -- step 2: index correspondence `HeightOneSpectrum Ã ≃ MaximalSpectrum Ã` (`Ã` not a field); if `Ã` is a
  -- field both sides are `0`
  by_cases hB : IsField (integralClosure A K)
  · haveI : IsEmpty (IsDedekindDomain.HeightOneSpectrum (integralClosure A K)) :=
      ⟨fun v => Ring.not_isField_iff_exists_prime.mpr ⟨v.asIdeal, v.ne_bot, v.isPrime⟩ hB⟩
    rw [finsum_of_isEmpty]
    symm
    refine finsum_eq_zero_of_forall_eq_zero fun m => ?_
    have hu : ∀ x : integralClosure A K, x ≠ 0 →
        Ring.ord (Localization.AtPrime m.asIdeal) (algebraMap (integralClosure A K) _ x) = 0 := by
      intro x hx
      obtain ⟨c, hc⟩ := hB.mul_inv_cancel hx
      exact Ring.ord_of_isUnit ((IsUnit.of_mul_eq_one c hc).map _)
    rw [hu b hb, hu b' hb']
    simp
  · refine Eq.trans ?_
      (finsum_comp_equiv (IsDedekindDomain.HeightOneSpectrum.equivMaximalSpectrum hB))
    refine finsum_congr fun v => ?_
    have hfr := Ring.TameSymbol.finrank_residueField_valuationSubring_eq_inertiaDeg'
      (A := A) (B := integralClosure A K) (K := K) v (Ring.TameSymbol.toValuationSubring A v)
      (fun r => IsScalarTower.algebraMap_apply A (integralClosure A K) K r)
    change (Module.finrank (IsLocalRing.ResidueField A)
        (IsLocalRing.ResidueField
          (IsDedekindDomain.HeightOneSpectrum.valuation K v).valuationSubring) : ℤ) *
        ordv (IsDedekindDomain.HeightOneSpectrum.valuation K v) g
      = (Ideal.inertiaDeg' (IsLocalRing.maximalIdeal A) v.asIdeal : ℤ) *
          (((Ring.ord (Localization.AtPrime v.asIdeal)
              (algebraMap (integralClosure A K) _ b)).toNat : ℤ) -
            ((Ring.ord (Localization.AtPrime v.asIdeal)
              (algebraMap (integralClosure A K) _ b')).toNat : ℤ))
    rw [hfr, hord v]

end UnitLeft

end Ring.TameSymbol

/-- The local factor `Norm_{κ(v)/κ}((−1)^{ab} f^b / g^a mod 𝔪_v)` at a nonzero prime `v` of `Ã`, with
`a = ord_v f`, `b = ord_v g` (the data are `Ring.TameSymbol.localFactor`; here the Dedekind instance on
`Ã` is substituted). -/

noncomputable def Ring.tameSymbolAt (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsNoetherianRing A] [Ring.KrullDimLE 1 A] {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
    (hfin : Module.Finite A (integralClosure A K))
    (v : IsDedekindDomain.HeightOneSpectrum (integralClosure A K))
    (f g : Kˣ) : IsLocalRing.ResidueField A :=
  letI : IsDedekindDomain (integralClosure A K) :=
    Ring.TameSymbol.isDedekindDomain_integralClosure A K hfin
  letI : IsFractionRing (integralClosure A K) K := Ring.TameSymbol.isFractionRing_integralClosure A K
  Ring.TameSymbol.localFactor A v f g

/-- The tame symbol `∂_A(f, g) := ∏_v tameSymbolAt A v f g` (a finite product: only finitely many `v` have
`f` or `g` not a unit of `Ã_v`, the other factors are `1`; `finprod` is `1` on infinite support, and the
support is finite since `Ã` is Dedekind). -/

noncomputable def Ring.tameSymbol (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsNoetherianRing A] [Ring.KrullDimLE 1 A] {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
    (hfin : Module.Finite A (integralClosure A K))
    (f g : Kˣ) : IsLocalRing.ResidueField A :=
  ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (integralClosure A K), Ring.tameSymbolAt A hfin v f g

/-- 0EAS(1): multiplicativity in the second variable, `∂(f, gh) = ∂(f, g) ∂(f, h)`. -/

theorem Ring.tameSymbol_mul_right (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsNoetherianRing A] [Ring.KrullDimLE 1 A] {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
    (hfin : Module.Finite A (integralClosure A K))
    (f g h : Kˣ) : Ring.tameSymbol A hfin f (g * h)
      = Ring.tameSymbol A hfin f g * Ring.tameSymbol A hfin f h := by
  letI : IsDedekindDomain (integralClosure A K) :=
    Ring.TameSymbol.isDedekindDomain_integralClosure A K hfin
  letI : IsFractionRing (integralClosure A K) K := Ring.TameSymbol.isFractionRing_integralClosure A K
  unfold Ring.tameSymbol Ring.tameSymbolAt
  rw [← finprod_mul_distrib (Ring.TameSymbol.finite_mulSupport_localFactor A f g)
    (Ring.TameSymbol.finite_mulSupport_localFactor A f h)]
  exact finprod_congr fun v => Ring.TameSymbol.localFactor_mul_right A v f g h

/-- 0EAS(2): antisymmetry `∂(f, g) ∂(g, f) = 1` (together with (1) this gives multiplicativity in the first
variable). -/

theorem Ring.tameSymbol_mul_swap (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsNoetherianRing A] [Ring.KrullDimLE 1 A] {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
    (hfin : Module.Finite A (integralClosure A K))
    (f g : Kˣ) : Ring.tameSymbol A hfin f g * Ring.tameSymbol A hfin g f = 1 := by
  letI : IsDedekindDomain (integralClosure A K) :=
    Ring.TameSymbol.isDedekindDomain_integralClosure A K hfin
  letI : IsFractionRing (integralClosure A K) K := Ring.TameSymbol.isFractionRing_integralClosure A K
  unfold Ring.tameSymbol Ring.tameSymbolAt
  rw [← finprod_mul_distrib (Ring.TameSymbol.finite_mulSupport_localFactor A f g)
    (Ring.TameSymbol.finite_mulSupport_localFactor A g f)]
  rw [finprod_congr fun v => Ring.TameSymbol.localFactor_mul_swap A v f g, finprod_one]

/-- The value lies in `κ^*`. -/

theorem Ring.tameSymbol_ne_zero (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsNoetherianRing A] [Ring.KrullDimLE 1 A] {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
    (hfin : Module.Finite A (integralClosure A K))
    (f g : Kˣ) : Ring.tameSymbol A hfin f g ≠ 0 :=
  left_ne_zero_of_mul_eq_one (Ring.tameSymbol_mul_swap A hfin f g)

/-- 0EAS: multiplicativity in the first variable, `∂(fh, g) = ∂(f, g) ∂(h, g)` (from (1) and (2)). -/

theorem Ring.tameSymbol_mul_left (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsNoetherianRing A] [Ring.KrullDimLE 1 A] {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
    (hfin : Module.Finite A (integralClosure A K))
    (f h g : Kˣ) : Ring.tameSymbol A hfin (f * h) g
      = Ring.tameSymbol A hfin f g * Ring.tameSymbol A hfin h g := by
  have h1 := Ring.tameSymbol_mul_swap A hfin (f * h) g
  have h2 := Ring.tameSymbol_mul_swap A hfin f g
  have h3 := Ring.tameSymbol_mul_swap A hfin h g
  have h4 := Ring.tameSymbol_mul_right A hfin g f h
  have hne := Ring.tameSymbol_ne_zero A hfin g (f * h)
  apply mul_right_cancel₀ hne
  rw [h1, h4]
  calc (1 : IsLocalRing.ResidueField A) = (Ring.tameSymbol A hfin f g * Ring.tameSymbol A hfin g f) *
        (Ring.tameSymbol A hfin h g * Ring.tameSymbol A hfin g h) := by rw [h2, h3, one_mul]
    _ = _ := by ring

/-- Normalization 0EAS/0EAN: if `Ã` is finite over `A`, then for `u ∈ A^*`, `g ∈ K^*`,
`∂(u, g) = ū^{ord_A g}`, where `ord_A` is Mathlib's `Ring.ordFrac` (a length, 02MD).
The finiteness assumption cannot be dropped: if `Ã` is not finite, this definition gives
`ū^{length_A(Ã/gÃ)}`, which may differ from `ū^{length_A(A/gA)}`. -/

theorem Ring.tameSymbol_unit_left (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsNoetherianRing A] [Ring.KrullDimLE 1 A] {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
    (hfin : Module.Finite A (integralClosure A K)) (u : Aˣ) (g : Kˣ) :
    Ring.tameSymbol A hfin (Units.map (algebraMap A K).toMonoidHom u) g =
      (IsLocalRing.residue A (u : A)) ^
        Multiplicative.toAdd (WithZero.unzero ((map_ne_zero (Ring.ordFrac A (K := K))).mpr g.ne_zero)) := by
  classical
  letI : IsDedekindDomain (integralClosure A K) :=
    Ring.TameSymbol.isDedekindDomain_integralClosure A K hfin
  letI : IsFractionRing (integralClosure A K) K := Ring.TameSymbol.isFractionRing_integralClosure A K
  letI hloc : ∀ v : IsDedekindDomain.HeightOneSpectrum (integralClosure A K),
      IsLocalHom (Ring.TameSymbol.toValuationSubring A v) := fun v =>
    Ring.TameSymbol.isLocalHom_toValuationSubring A v
  letI halg : ∀ v : IsDedekindDomain.HeightOneSpectrum (integralClosure A K),
      Algebra (IsLocalRing.ResidueField A)
        (IsLocalRing.ResidueField
          (IsDedekindDomain.HeightOneSpectrum.valuation K v).valuationSubring) := fun v =>
    (IsLocalRing.ResidueField.map (Ring.TameSymbol.toValuationSubring A v)).toAlgebra
  set ū := IsLocalRing.residue A (u : A) with hūdef
  have hū : ū ≠ 0 := by
    rw [hūdef, Ne, IsLocalRing.residue_eq_zero_iff]
    exact fun h => ((IsLocalRing.mem_maximalIdeal _).mp h) u.isUnit
  set e : IsDedekindDomain.HeightOneSpectrum (integralClosure A K) → ℤ := fun v =>
    (Module.finrank (IsLocalRing.ResidueField A)
        (IsLocalRing.ResidueField
          (IsDedekindDomain.HeightOneSpectrum.valuation K v).valuationSubring) : ℤ) *
      Ring.TameSymbol.ordv (IsDedekindDomain.HeightOneSpectrum.valuation K v) g with hedef
  have hsupp : (Function.support e).Finite := by
    refine (Ring.TameSymbol.finite_support_ordv A g).subset fun v hv => ?_
    intro hzero
    exact hv (by simp [hedef, hzero])
  -- left-hand side: `localFactor_unit_left` at each `v`
  have hL : Ring.tameSymbol A hfin (Units.map (algebraMap A K).toMonoidHom u) g
      = ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum (integralClosure A K), ū ^ e v := by
    unfold Ring.tameSymbol Ring.tameSymbolAt
    exact finprod_congr fun v => Ring.TameSymbol.localFactor_unit_left A v u g
  -- turn the finite product into a `Finset` product and combine into a single power of `ū`
  have hsub : Function.mulSupport (fun v => ū ^ e v) ⊆ hsupp.toFinset := by
    intro v hv
    simp only [Set.Finite.coe_toFinset, Function.mem_mulSupport] at hv ⊢
    intro hzero
    exact hv (by rw [hzero, zpow_zero])
  rw [hL, finprod_eq_prod_of_mulSupport_subset _ hsub,
    Ring.TameSymbol.prod_zpow_eq_zpow_sum _ e hū,
    ← finsum_eq_sum_of_support_subset e (by simpa using Set.Subset.refl (Function.support e))]
  exact congrArg (fun n : ℤ => ū ^ n)
    (Ring.TameSymbol.finsum_finrank_mul_ordv_eq_ordFrac A hfin g)

end
