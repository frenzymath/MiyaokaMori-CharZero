import MiyaokaMori.Prelude
import MiyaokaMori.RingTheory.KeyLemma.Defs
import MiyaokaMori.RingTheory.KeyLemma.RankOneLength

/-! # Herbrand quotient of `(xM, 0, y)` on a quotient by a symbolic power

Stacks 02QF in the present situation: `M = B/𝔭^(n)`, `x ∈ 𝔭^(e) ∖ 𝔭^(e+1)` (`e ≤ n`), `y ∉ 𝔭`; then
`e_A(xM, 0, y) = (n − e)·λ_𝔭(y)`, and the cohomology has finite length.

References: Stacks 02QF (chow-lemma-length-multiplication); third paragraph of 0EAW
("`(π^e M_i)_{𝔮_i} ≅ A_{𝔮_i}/π^{f}`").
-/

set_option autoImplicit false

universe u

open PeriodicComplex

noncomputable section

namespace KeyLemma

section SymbPowFacts

variable {B : Type u} [CommRing B] [IsDomain B] (𝔭 : Ideal B) [𝔭.IsPrime]

omit [IsDomain B] in
/-- The same statement as `HerbrandUniformizerPowers.symbPow_zero`; `private` to avoid a name clash. -/
private theorem symbPow_zero : symbPow 𝔭 0 = ⊤ := by
  unfold symbPow; rw [pow_zero, Ideal.one_eq_top, Ideal.comap_top]

omit [IsDomain B] in
theorem symbPow_anti {m n : ℕ} (h : m ≤ n) : symbPow 𝔭 n ≤ symbPow 𝔭 m :=
  Ideal.comap_mono (Ideal.pow_le_pow_right h)

omit [IsDomain B] in
/-- `y ∉ 𝔭` is invertible in `B_𝔭`, so `y·b ∈ 𝔭^(m) ⇒ b ∈ 𝔭^(m)`. -/
theorem mem_symbPow_of_notMem_mul_mem {y b : B} {m : ℕ} (hy : y ∉ 𝔭) (h : y * b ∈ symbPow 𝔭 m) :
    b ∈ symbPow 𝔭 m := by
  unfold symbPow at h ⊢
  rw [Ideal.mem_comap, map_mul] at h
  rw [Ideal.mem_comap]
  exact (Ideal.unit_mul_mem_iff_mem _
    ((IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime 𝔭) 𝔭 y).mpr hy)).mp h

variable [IsDiscreteValuationRing (Localization.AtPrime 𝔭)]

/-- For `x ∈ 𝔭^(e) ∖ 𝔭^(e+1)` (`ord x = e`): `x·b ∈ 𝔭^(n) ⟺ b ∈ 𝔭^(n−e)` (`e ≤ n`). -/
theorem mul_mem_symbPow_iff {x b : B} {e n : ℕ} (hen : e ≤ n)
    (hx : x ∈ symbPow 𝔭 e) (hx' : x ∉ symbPow 𝔭 (e + 1)) :
    x * b ∈ symbPow 𝔭 n ↔ b ∈ symbPow 𝔭 (n - e) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime 𝔭)
  have hmax : IsLocalRing.maximalIdeal (Localization.AtPrime 𝔭) = Ideal.span {ϖ} :=
    hϖ.maximalIdeal_eq
  have hprime : Prime ϖ := hϖ.prime
  unfold symbPow at hx hx' ⊢
  simp only [Ideal.mem_comap, hmax, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    map_mul] at hx hx' ⊢
  obtain ⟨x', hfx⟩ := hx
  rw [hfx] at hx' ⊢
  have hx'' : ¬ ϖ ∣ x' := fun h => hx' (by rw [pow_succ]; exact mul_dvd_mul_left _ h)
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hen
  rw [Nat.add_sub_cancel_left, pow_add, mul_assoc,
    mul_dvd_mul_iff_left (pow_ne_zero _ hϖ.ne_zero)]
  constructor
  · intro h
    exact hprime.pow_dvd_of_dvd_mul_left m hx'' h
  · intro h
    exact dvd_mul_of_dvd_right h _

end SymbPowFacts

variable {A B : Type u} [CommRing A] [IsNoetherianRing A] [CommRing B] [IsDomain B] [Algebra A B]
  [Module.Finite A B] (𝔭 : Ideal B) [𝔭.IsPrime] [IsDiscreteValuationRing (Localization.AtPrime 𝔭)]

omit [IsNoetherianRing A] [IsDomain B] [Module.Finite A B] in
/-- The preimage of `Im(mult. by z)` under the quotient map `B → B/I` is `zB + I`. -/
theorem comap_mk_range_mulQ (I : Ideal B) (z : B) :
    (LinearMap.range (mulQ A I z)).comap (Ideal.Quotient.mkₐ A I).toLinearMap
      = (Ideal.span {z} ⊔ I).restrictScalars A := by
  ext b
  simp only [Submodule.mem_comap, LinearMap.mem_range, AlgHom.toLinearMap_apply,
    Ideal.Quotient.mkₐ_eq_mk, mulQ_apply, Submodule.restrictScalars_mem]
  constructor
  · rintro ⟨m, hm⟩
    obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective m
    rw [← map_mul, Ideal.Quotient.mk_eq_mk_iff_sub_mem] at hm
    have : b = c * z + -(z * c - b) := by ring
    rw [this]
    exact Submodule.add_mem _ (Submodule.mem_sup_left (Ideal.mem_span_singleton'.mpr ⟨c, rfl⟩))
      (Submodule.mem_sup_right (I.neg_mem hm))
  · intro hb
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hb
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hu
    refine ⟨Ideal.Quotient.mk I c, ?_⟩
    rw [← map_mul, Ideal.Quotient.mk_eq_mk_iff_sub_mem]
    have : z * c - (c * z + v) = -v := by ring
    rw [this]; exact I.neg_mem hv

/-- `l(B/(yB + 𝔭^(m))) = m·λ(y)`: along `𝔭^(m) ⊂ 𝔭^(m−1) ⊂ … ⊂ 𝔭^(0) = B` use `relLength_add` and
`relLength_symbPow_succ`; at each step `(yB + 𝔭^(j+1)) ∩ 𝔭^(j) = y𝔭^(j) + 𝔭^(j+1)` (`y` is invertible
in `B_𝔭`). -/
theorem relLength_span_sup_symbPow_top
    (hfl : ∀ y ∉ 𝔭, Module.length A (B ⧸ (𝔭 ⊔ Ideal.span {y})) ≠ ⊤) {y : B} (hy : y ∉ 𝔭) (m : ℕ) :
    relLength ((Ideal.span {y} ⊔ symbPow 𝔭 m).restrictScalars A) (⊤ : Submodule A B)
      = ((m * lam A 𝔭 y : ℕ) : ℕ∞) := by
  induction m with
  | zero =>
    rw [symbPow_zero, sup_top_eq, Submodule.restrictScalars_top, relLength_self, Nat.zero_mul,
      Nat.cast_zero]
  | succ m ih =>
    have hle : symbPow 𝔭 (m + 1) ≤ symbPow 𝔭 m := symbPow_anti 𝔭 (Nat.le_succ m)
    have h1 : (Ideal.span {y} ⊔ symbPow 𝔭 (m + 1)).restrictScalars A
        ≤ (Ideal.span {y} ⊔ symbPow 𝔭 m).restrictScalars A :=
      (Submodule.restrictScalars_le A).mpr (sup_le_sup_left hle _)
    rw [relLength_add h1 le_top, ih]
    have h2 : (Ideal.span {y} ⊔ symbPow 𝔭 m).restrictScalars A
        = (Ideal.span {y} ⊔ symbPow 𝔭 (m + 1)).restrictScalars A
          ⊔ (symbPow 𝔭 m).restrictScalars A := by
      rw [← Submodule.restrictScalars_sup, sup_assoc, sup_eq_right.mpr hle]
    rw [h2, relLength_sup_left, ← relLength_congr_inf]
    have h3 : (Ideal.span {y} ⊔ symbPow 𝔭 (m + 1)).restrictScalars A ⊓ (symbPow 𝔭 m).restrictScalars A
        = (symbPow 𝔭 (m + 1) ⊔ Ideal.span {y} * symbPow 𝔭 m).restrictScalars A := by
      rw [← Submodule.restrictScalars_inf]
      congr 1
      ext b
      rw [Submodule.mem_inf, Submodule.mem_sup, Submodule.mem_sup]
      constructor
      · rintro ⟨⟨u, hu, v, hv, rfl⟩, hb⟩
        obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hu
        have hc : y * c ∈ symbPow 𝔭 m := by
          have : y * c = c * y + v - v := by ring
          rw [this]; exact Submodule.sub_mem _ hb (hle hv)
        exact ⟨v, hv, c * y, Ideal.mem_span_singleton_mul.mpr
          ⟨c, mem_symbPow_of_notMem_mul_mem 𝔭 hy hc, mul_comm y c⟩, add_comm _ _⟩
      · rintro ⟨u, hu, v, hv, rfl⟩
        obtain ⟨c, hc, rfl⟩ := Ideal.mem_span_singleton_mul.mp hv
        exact ⟨⟨y * c, Ideal.mem_span_singleton'.mpr ⟨c, mul_comm c y⟩, u, hu, add_comm _ _⟩,
          Submodule.add_mem _ (hle hu) (Ideal.mul_mem_left _ y hc)⟩
    rw [h3, relLength_symbPow_succ 𝔭 hfl m hy, ← ENat.natCast_toNat (hfl y hy)]
    change ((lam A 𝔭 y : ℕ) : ℕ∞) + _ = _
    push_cast
    ring

omit [IsNoetherianRing A] [Module.Finite A B] in
/-- `l((xB + 𝔭^(n))/(xyB + 𝔭^(n))) = l(B/(yB + 𝔭^(n−e)))`: the modular law + `xB ∩ 𝔭^(n) = x·𝔭^(n−e)` +
injectivity of multiplication by `x`. -/
theorem relLength_span_mul_sup {x y : B} {e n : ℕ} (hen : e ≤ n)
    (hx : x ∈ symbPow 𝔭 e) (hx' : x ∉ symbPow 𝔭 (e + 1)) :
    relLength ((Ideal.span {x * y} ⊔ symbPow 𝔭 n).restrictScalars A)
        ((Ideal.span {x} ⊔ symbPow 𝔭 n).restrictScalars A)
      = relLength ((Ideal.span {y} ⊔ symbPow 𝔭 (n - e)).restrictScalars A) (⊤ : Submodule A B) := by
  have hx0 : x ≠ 0 := by rintro rfl; exact hx' (Ideal.zero_mem _)
  set μ : B →ₗ[A] B := LinearMap.mulLeft A x with hμdef
  have hμ : Function.Injective μ := fun a b h => mul_left_cancel₀ hx0 h
  have h1 : (Ideal.span {x} ⊔ symbPow 𝔭 n).restrictScalars A
      = (Ideal.span {x * y} ⊔ symbPow 𝔭 n).restrictScalars A
        ⊔ (Ideal.span {x}).restrictScalars A := by
    rw [← Submodule.restrictScalars_sup]
    congr 1
    have : Ideal.span {x * y} ≤ Ideal.span {x} :=
      Ideal.span_singleton_le_span_singleton.mpr (dvd_mul_right x y)
    rw [sup_comm (Ideal.span {x * y}), sup_assoc, sup_eq_right.mpr this, sup_comm]
  rw [h1, relLength_sup_left, ← relLength_congr_inf]
  have h2 : (Ideal.span {x * y} ⊔ symbPow 𝔭 n).restrictScalars A ⊓ (Ideal.span {x}).restrictScalars A
      = ((Ideal.span {y} ⊔ symbPow 𝔭 (n - e)).restrictScalars A).map μ := by
    ext b
    rw [Submodule.mem_inf, Submodule.mem_map]
    simp only [Submodule.restrictScalars_mem, hμdef, LinearMap.mulLeft_apply]
    constructor
    · rintro ⟨hb1, hb2⟩
      obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hb1
      obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.mp hu
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hb2
      have hv' : x * (c - d * y) = v := by linear_combination hc
      exact ⟨c, Submodule.mem_sup.mpr ⟨d * y, Ideal.mem_span_singleton'.mpr ⟨d, rfl⟩, c - d * y,
        (mul_mem_symbPow_iff 𝔭 hen hx hx').mp (by rw [hv']; exact hv), by ring⟩,
        by rw [mul_comm]; exact hc⟩
    · rintro ⟨c, hc, rfl⟩
      obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.mp hc
      obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.mp hu
      refine ⟨Submodule.mem_sup.mpr ⟨x * (d * y), Ideal.mem_span_singleton'.mpr ⟨d, by ring⟩,
        x * w, (mul_mem_symbPow_iff 𝔭 hen hx hx').mpr hw, by ring⟩,
        Ideal.mem_span_singleton'.mpr ⟨d * y + w, mul_comm _ _⟩⟩
  have h3 : (Ideal.span {x}).restrictScalars A = (⊤ : Submodule A B).map μ := by
    ext b
    simp only [Submodule.restrictScalars_mem, Submodule.mem_map, Submodule.mem_top, true_and,
      hμdef, LinearMap.mulLeft_apply, Ideal.mem_span_singleton']
    exact ⟨fun ⟨a, ha⟩ => ⟨a, by rw [mul_comm]; exact ha⟩, fun ⟨a, ha⟩ => ⟨a, by rw [mul_comm]; exact ha⟩⟩
  rw [h2, h3, relLength_map_of_injective μ hμ le_top]

/-- Proof. Write `I_j = 𝔭^(j)`, `M = B/I_n`, `xM = (xB + I_n)/I_n`, and `χ` for the restriction of
multiplication by `y` to `xM`.
(1) `y` is injective on `M` (`y·b ∈ I_n ⇒ b ∈ I_n`: `y` is invertible in `B_𝔭`,
    `mem_symbPow_of_notMem_mul_mem`), so `Ker χ = 0` has length `0`.
(2) 0EA6 (`herbrand_zero_left`, `finiteCohomology_zero_left_iff`): only `l(xM/χ(xM))` is needed.
(3) Pull back along the quotient map `B → M` (`relLength_comap_of_surjective`, `comap_mk_range_mulQ`):
    `l(xM/y·xM) = l((xB + I_n)/(xyB + I_n))`.
(4) `relLength_span_mul_sup`: the modular law `(xyB + I_n) ∩ xB = xyB + (xB ∩ I_n)`, and
    `xB ∩ I_n = x·I_{n−e}` (`ord x = e`, `mul_mem_symbPow_iff`); multiplication by `x` is injective (`B` a
    domain), so this equals `l(B/(yB + I_{n−e}))`.
(5) `relLength_span_sup_symbPow_top`: along `I_{m} ⊂ I_{m−1} ⊂ … ⊂ I_0 = B` use `relLength_add`; at each
    step `(yB + I_{j+1}) ∩ I_j = y·I_j + I_{j+1}` (`y` injective) and `relLength_symbPow_succ` gives
    `λ(y)`, in total `(n−e)·λ(y)`.
Edge case `e = n`: `xM/y·xM` has length `0` and both sides are `0`. -/
theorem herbrand_restrictRange_mulQ
    (hfl : ∀ y ∉ 𝔭, Module.length A (B ⧸ (𝔭 ⊔ Ideal.span {y})) ≠ ⊤) {x y : B} {e n : ℕ} (hen : e ≤ n)
    (hx : x ∈ symbPow 𝔭 e) (hx' : x ∉ symbPow 𝔭 (e + 1)) (hy : y ∉ 𝔭) :
    FiniteCohomology
        (0 : ↥(LinearMap.range (mulQ A (symbPow 𝔭 n) x)) →ₗ[A] ↥(LinearMap.range (mulQ A (symbPow 𝔭 n) x)))
        (restrictRange (mulQ A (symbPow 𝔭 n) x) (mulQ A (symbPow 𝔭 n) y) (range_mulQ_le_comap _ x y)) ∧
      herbrand
        (0 : ↥(LinearMap.range (mulQ A (symbPow 𝔭 n) x)) →ₗ[A] ↥(LinearMap.range (mulQ A (symbPow 𝔭 n) x)))
        (restrictRange (mulQ A (symbPow 𝔭 n) x) (mulQ A (symbPow 𝔭 n) y) (range_mulQ_le_comap _ x y))
        = ((n - e : ℕ) : ℤ) * (lam A 𝔭 y : ℤ) := by
  classical
  set I := symbPow 𝔭 n with hI
  set R := LinearMap.range (mulQ A I x) with hR
  set χ := restrictRange (mulQ A I x) (mulQ A I y) (range_mulQ_le_comap I x y) with hχ
  -- (1) `y` is injective on `M`, so `Ker χ = 0`
  have hker : LinearMap.ker χ = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    rintro ⟨r, hr⟩ h
    have h' : mulQ A I y r = 0 := congrArg Subtype.val h
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective r
    rw [mulQ_apply, ← map_mul, Ideal.Quotient.eq_zero_iff_mem] at h'
    exact Subtype.ext (Ideal.Quotient.eq_zero_iff_mem.mpr (mem_symbPow_of_notMem_mul_mem 𝔭 hy h'))
  have hk0 : Module.length A (LinearMap.ker χ) = 0 :=
    Module.length_eq_zero_iff.mpr (Submodule.subsingleton_iff_eq_bot.mpr hker)
  -- (2) the cokernel `xM/yxM ≅ (xB + I)/(xyB + I)`
  have hcok : Module.length A (↥R ⧸ LinearMap.range χ) = ((n - e) * lam A 𝔭 y : ℕ) := by
    have e1 : Module.length A (↥R ⧸ LinearMap.range χ)
        = relLength ((LinearMap.range χ).map R.subtype) R := by
      unfold relLength
      rw [show ((LinearMap.range χ).map R.subtype).submoduleOf R = LinearMap.range χ from
        Submodule.comap_map_eq_of_injective (Submodule.subtype_injective R) _]
    have e2 : (LinearMap.range χ).map R.subtype = LinearMap.range (mulQ A I (x * y)) := by
      ext z
      simp only [Submodule.mem_map, LinearMap.mem_range]
      constructor
      · rintro ⟨_, ⟨⟨_, ⟨m, rfl⟩⟩, rfl⟩, rfl⟩
        refine ⟨m, ?_⟩
        change mulQ A I (x * y) m = mulQ A I y (mulQ A I x m)
        simp only [mulQ_apply, map_mul, mul_left_comm, mul_assoc]
      · rintro ⟨m, rfl⟩
        refine ⟨χ ⟨mulQ A I x m, ⟨m, rfl⟩⟩, ⟨⟨mulQ A I x m, ⟨m, rfl⟩⟩, rfl⟩, ?_⟩
        change mulQ A I y (mulQ A I x m) = mulQ A I (x * y) m
        simp only [mulQ_apply, map_mul, mul_left_comm, mul_assoc]
    have hle : LinearMap.range (mulQ A I (x * y)) ≤ R := by
      rw [mulQ_mul]; exact LinearMap.range_comp_le_range _ _
    rw [e1, e2, ← relLength_comap_of_surjective (Ideal.Quotient.mkₐ A I).toLinearMap
      (Ideal.Quotient.mkₐ_surjective A I) hle, hR, comap_mk_range_mulQ, comap_mk_range_mulQ,
      relLength_span_mul_sup 𝔭 hen hx hx', relLength_span_sup_symbPow_top 𝔭 hfl hy]
  refine ⟨(finiteCohomology_zero_left_iff χ).mpr
    ⟨by rw [hcok]; exact ENat.natCast_ne_top _, by rw [hk0]; exact ENat.zero_ne_top⟩, ?_⟩
  rw [herbrand_zero_left, hcok, hk0, ENat.toNat_natCast, ENat.toNat_zero]
  push_cast
  ring

end KeyLemma

end
