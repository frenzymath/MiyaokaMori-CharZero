import MiyaokaMori.Prelude
import MiyaokaMori.RingTheory.KeyLemma.Defs
import MiyaokaMori.RingTheory.KeyLemma.Uniformizer
import MiyaokaMori.RingTheory.KeyLemma.Factorization
import MiyaokaMori.RingTheory.KeyLemma.SymbPowMul
import MiyaokaMori.RingTheory.KeyLemma.LamMul
import MiyaokaMori.RingTheory.KeyLemma.HerbrandRange
import MiyaokaMori.RingTheory.KeyLemma.HerbrandUniformizerPowers

/-! # Herbrand quotient of `(B/𝔭^(e+f), a, b)` in terms of `λ`

The conclusion of the third and fourth paragraphs of Stacks 0EAW, in purely commutative-algebraic form:
`A` Noetherian, `B` a domain finite over `A`, `𝔭` a prime with `B_𝔭` a DVR, and
`length_A(B/(𝔭+yB)) < ∞` for `y ∉ 𝔭`. Let `a ∈ 𝔭^(e) ∖ 𝔭^(e+1)`, `b ∈ 𝔭^(f) ∖ 𝔭^(f+1)`, and
`y₁, y₂ ∈ B ∖ 𝔭` with `y₁b^e = (−1)^{ef}y₂a^f` (i.e. `(−1)^{ef}a^f/b^e = y₁/y₂`). Then
`e_A(B/𝔭^(e+f), a, b) = λ(y₂) − λ(y₁)`.

Reference: third and fourth paragraphs of the proof of Stacks 0EAW (0EAC twice + 0EAB + 02QF).
-/

set_option autoImplicit false

universe u

open PeriodicComplex

noncomputable section

namespace KeyLemma

variable {A B : Type u} [CommRing A] [IsNoetherianRing A] [CommRing B] [IsDomain B] [Algebra A B]
  [Module.Finite A B] (𝔭 : Ideal B) [𝔭.IsPrime] [IsDiscreteValuationRing (Localization.AtPrime 𝔭)]

/-- Proof. Write `n = e + f`, `M = B/𝔭^(n)`, `E(x, y) := herbrand (mulQ x) (mulQ y)`.
1. `exists_uniformizer` gives `π`; `exists_mul_eq_mul_pow` twice, with a common denominator:
   `c, u, v ∉ 𝔭`, `c·a = u·π^e`, `c·b = v·π^f`.
2. (Third paragraph.) `herbrand_mulQ_pow_uniformizer`: `E(π^e, π^f) = 0` and finite. `mulQ_mul` writes
   `mulQ (u·π^e)` as `mulQ u ∘ mulQ π^e`; 0EAC `PeriodicComplex.herbrand_comp_left/right` (hypotheses
   `range_mulQ_le_comap`, `mulQ_comp_eq_zero` (`π^e·π^f ∈ 𝔭^(n)`), `herbrand_restrictRange_mulQ`, where
   `π^e ∈ 𝔭^(e) ∖ 𝔭^(e+1)` by induction via `mul_mem_symbPow`) give
   `E(uπ^e, vπ^f) = 0 − (n−e)λ(u) + (n−f)λ(v) = −fλ(u) + eλ(v)`, with finite-length cohomology.
3. (Fourth paragraph.) `mulQ (c·a) = mulQ c ∘ mulQ a`. First `PeriodicComplex.length_H_comp_left/right`
   (unconditional `ℕ∞` equalities) deduce finite length for `(a, b)` from finite length for `(ca, cb)`;
   then 0EAC: `E(ca, cb) = E(a, b) − fλ(c) + eλ(c)` (`herbrand_restrictRange_mulQ` with `x = a`, `x = b`).
4. Arithmetic: substitute `c^f a^f = u^f π^{ef}`, `c^e b^e = v^e π^{ef}` into `hy` and cancel `π^{ef}`
   (domain, `π ≠ 0`) to get `y₁ v^e c^f = ± y₂ u^f c^e`; `lam_mul`, `lam_pow`, `lam_neg`
   (`(−1)^{ef} = ±1`: `neg_one_pow_eq_or`) give `λ(y₁) + eλ(v) + fλ(c) = λ(y₂) + fλ(u) + eλ(c)`. Combine
   with 2 and 3 (`omega`/`linarith`).
Edge cases: `e = f = 0 ⇒ M = 0`, `y₁ = ±y₂`; `a = b ⇒ y₁ = ±y₂` and `E(a,a) = 0` (antisymmetry
`herbrand_symm`); `𝔭` maximal ⇒ `λ ≡ 0`, `M` of finite length.
Sanity check: `A = B = k[[x,y]]`, `𝔭 = (x)`, `a = x`, `b = y`: `M = k[[y]]`, `E = 1`; `y₁ = 1`, `y₂ = y`,
`λ(y₂) − λ(y₁) = 1`. -/
theorem herbrand_symbPow_eq
    (hfl : ∀ y ∉ 𝔭, Module.length A (B ⧸ (𝔭 ⊔ Ideal.span {y})) ≠ ⊤) {a b : B} {e f : ℕ}
    (ha : a ∈ symbPow 𝔭 e) (ha' : a ∉ symbPow 𝔭 (e + 1))
    (hb : b ∈ symbPow 𝔭 f) (hb' : b ∉ symbPow 𝔭 (f + 1))
    {y₁ y₂ : B} (hy₁ : y₁ ∉ 𝔭) (hy₂ : y₂ ∉ 𝔭) (hy : y₁ * b ^ e = (-1) ^ (e * f) * y₂ * a ^ f) :
    FiniteCohomology (mulQ A (symbPow 𝔭 (e + f)) a) (mulQ A (symbPow 𝔭 (e + f)) b) ∧
      herbrand (mulQ A (symbPow 𝔭 (e + f)) a) (mulQ A (symbPow 𝔭 (e + f)) b)
        = (lam A 𝔭 y₂ : ℤ) - (lam A 𝔭 y₁ : ℤ) := by
  classical
  obtain ⟨π, hπ1, hπ2⟩ := exists_uniformizer 𝔭
  obtain ⟨c₁, u₁, hc₁, hu₁, h₁⟩ := exists_mul_eq_mul_pow 𝔭 hπ1 hπ2 ha ha'
  obtain ⟨c₂, v₂, hc₂, hv₂, h₂⟩ := exists_mul_eq_mul_pow 𝔭 hπ1 hπ2 hb hb'
  have hnm : ∀ {x y : B}, x ∉ 𝔭 → y ∉ 𝔭 → x * y ∉ 𝔭 := fun hx hy h =>
    (Ideal.IsPrime.mem_or_mem inferInstance h).elim hx hy
  have hnp : ∀ {x : B} (k : ℕ), x ∉ 𝔭 → x ^ k ∉ 𝔭 := fun k hx h =>
    hx (Ideal.IsPrime.mem_of_pow_mem inferInstance k h)
  obtain ⟨c, hcdef⟩ : ∃ c, c = c₁ * c₂ := ⟨_, rfl⟩
  obtain ⟨u, hudef⟩ : ∃ u, u = c₂ * u₁ := ⟨_, rfl⟩
  obtain ⟨v, hvdef⟩ : ∃ v, v = c₁ * v₂ := ⟨_, rfl⟩
  have hc : c ∉ 𝔭 := hcdef ▸ hnm hc₁ hc₂
  have hu : u ∉ 𝔭 := hudef ▸ hnm hc₂ hu₁
  have hv : v ∉ 𝔭 := hvdef ▸ hnm hc₁ hv₂
  have hca : c * a = u * π ^ e := by rw [hcdef, hudef]; linear_combination c₂ * h₁
  have hcb : c * b = v * π ^ f := by rw [hcdef, hvdef]; linear_combination c₁ * h₂
  -- powers of `π`
  have h1top : (1 : B) ∈ symbPow 𝔭 0 := by
    unfold symbPow; rw [pow_zero, Ideal.one_eq_top, Ideal.comap_top]; trivial
  have h1not : (1 : B) ∉ symbPow 𝔭 (0 + 1) := by
    unfold symbPow
    rw [zero_add, pow_one, Ideal.mem_comap, map_one]
    exact fun h => (IsLocalRing.maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).mpr h)
  have hπpow : ∀ k : ℕ, π ^ k ∈ symbPow 𝔭 k ∧ π ^ k ∉ symbPow 𝔭 (k + 1) := by
    intro k
    induction k with
    | zero => rw [pow_zero]; exact ⟨h1top, h1not⟩
    | succ k ih => rw [pow_succ]; exact mul_mem_symbPow 𝔭 ih.1 ih.2 hπ1 hπ2
  have hπ0 : π ≠ 0 := by
    rintro rfl
    exact hπ2 (Ideal.zero_mem _)
  have hprod : π ^ e * π ^ f ∈ symbPow 𝔭 (e + f) := by rw [← pow_add]; exact (hπpow (e + f)).1
  have hab : a * b ∈ symbPow 𝔭 (e + f) := (mul_mem_symbPow 𝔭 ha ha' hb hb').1
  -- third paragraph: `E(uπ^e, vπ^f)`
  have h0 := herbrand_mulQ_pow_uniformizer (A := A) 𝔭 hfl hπ1 hπ2 e f
  have hφψ := mulQ_comp_eq_zero (A := A) (symbPow 𝔭 (e + f)) hprod
  have hψφ := mulQ_comp_eq_zero (A := A) (x := π ^ f) (y := π ^ e) (symbPow 𝔭 (e + f))
    (by rw [mul_comm]; exact hprod)
  have hRu := herbrand_restrictRange_mulQ (A := A) 𝔭 hfl (Nat.le_add_right e f)
    (hπpow e).1 (hπpow e).2 hu
  have hRv := herbrand_restrictRange_mulQ (A := A) 𝔭 hfl (Nat.le_add_left f e)
    (hπpow f).1 (hπpow f).2 hv
  obtain ⟨hFC1, hE1⟩ := herbrand_comp_left (mulQ A (symbPow 𝔭 (e + f)) (π ^ e))
    (mulQ A (symbPow 𝔭 (e + f)) (π ^ f)) (mulQ A (symbPow 𝔭 (e + f)) u) hφψ hψφ
    (range_mulQ_le_comap _ (π ^ e) u) h0.1 hRu.1
  obtain ⟨hFC2, hE2⟩ := herbrand_comp_right (mulQ A (symbPow 𝔭 (e + f)) u ∘ₗ
      mulQ A (symbPow 𝔭 (e + f)) (π ^ e)) (mulQ A (symbPow 𝔭 (e + f)) (π ^ f))
    (mulQ A (symbPow 𝔭 (e + f)) v) (comp_left_isComplex _ _ _ hφψ)
    (comp_left_isComplex' _ _ _ hψφ (range_mulQ_le_comap _ (π ^ e) u))
    (range_mulQ_le_comap _ (π ^ f) v) hFC1 hRv.1
  have e1 : mulQ A (symbPow 𝔭 (e + f)) u ∘ₗ mulQ A (symbPow 𝔭 (e + f)) (π ^ e) =
      mulQ A (symbPow 𝔭 (e + f)) c ∘ₗ mulQ A (symbPow 𝔭 (e + f)) a := by
    rw [← mulQ_mul, ← mulQ_mul, hca]
  have e2 : mulQ A (symbPow 𝔭 (e + f)) v ∘ₗ mulQ A (symbPow 𝔭 (e + f)) (π ^ f) =
      mulQ A (symbPow 𝔭 (e + f)) c ∘ₗ mulQ A (symbPow 𝔭 (e + f)) b := by
    rw [← mulQ_mul, ← mulQ_mul, hcb]
  rw [e1, e2] at hFC2 hE2
  rw [e1] at hE1
  -- fourth paragraph: from `(ca, cb)` back to `(a, b)`
  have hφψab := mulQ_comp_eq_zero (A := A) (symbPow 𝔭 (e + f)) hab
  have hψφab := mulQ_comp_eq_zero (A := A) (x := b) (y := a) (symbPow 𝔭 (e + f))
    (by rw [mul_comm]; exact hab)
  have hχa := range_mulQ_le_comap (A := A) (symbPow 𝔭 (e + f)) a c
  have hχb := range_mulQ_le_comap (A := A) (symbPow 𝔭 (e + f)) b c
  have L1 := length_H_comp_left (mulQ A (symbPow 𝔭 (e + f)) a) (mulQ A (symbPow 𝔭 (e + f)) b)
    (mulQ A (symbPow 𝔭 (e + f)) c) hφψab hχa
  have L2 := length_H_comp_right (mulQ A (symbPow 𝔭 (e + f)) a) (mulQ A (symbPow 𝔭 (e + f)) b)
    (mulQ A (symbPow 𝔭 (e + f)) c) hψφab hχa
  have hcab : (mulQ A (symbPow 𝔭 (e + f)) c ∘ₗ mulQ A (symbPow 𝔭 (e + f)) a) ∘ₗ
      mulQ A (symbPow 𝔭 (e + f)) b = 0 := comp_left_isComplex _ _ _ hφψab
  have hbca : mulQ A (symbPow 𝔭 (e + f)) b ∘ₗ
      (mulQ A (symbPow 𝔭 (e + f)) c ∘ₗ mulQ A (symbPow 𝔭 (e + f)) a) = 0 :=
    comp_left_isComplex' _ _ _ hψφab hχa
  have L3 := length_H_comp_left (mulQ A (symbPow 𝔭 (e + f)) b)
    (mulQ A (symbPow 𝔭 (e + f)) c ∘ₗ mulQ A (symbPow 𝔭 (e + f)) a)
    (mulQ A (symbPow 𝔭 (e + f)) c) hbca hχb
  have L4 := length_H_comp_right (mulQ A (symbPow 𝔭 (e + f)) b)
    (mulQ A (symbPow 𝔭 (e + f)) c ∘ₗ mulQ A (symbPow 𝔭 (e + f)) a)
    (mulQ A (symbPow 𝔭 (e + f)) c) hcab hχb
  have hcab_fin : Module.length A (H (mulQ A (symbPow 𝔭 (e + f)) c ∘ₗ
      mulQ A (symbPow 𝔭 (e + f)) a) (mulQ A (symbPow 𝔭 (e + f)) b)) ≠ ⊤ :=
    ne_top_of_le_ne_top hFC2.1 (by rw [L4]; exact le_self_add)
  have hbca_fin : Module.length A (H (mulQ A (symbPow 𝔭 (e + f)) b)
      (mulQ A (symbPow 𝔭 (e + f)) c ∘ₗ mulQ A (symbPow 𝔭 (e + f)) a)) ≠ ⊤ :=
    ne_top_of_le_ne_top hFC2.2 (by rw [L3]; exact le_self_add)
  have FCab : FiniteCohomology (mulQ A (symbPow 𝔭 (e + f)) a) (mulQ A (symbPow 𝔭 (e + f)) b) :=
    ⟨ne_top_of_le_ne_top hcab_fin (by rw [L1]; exact le_self_add),
      ne_top_of_le_ne_top hbca_fin (by rw [L2]; exact le_self_add)⟩
  have hRa := herbrand_restrictRange_mulQ (A := A) 𝔭 hfl (Nat.le_add_right e f) ha ha' hc
  have hRb := herbrand_restrictRange_mulQ (A := A) 𝔭 hfl (Nat.le_add_left f e) hb hb' hc
  obtain ⟨hFC3, hE3⟩ := herbrand_comp_left (mulQ A (symbPow 𝔭 (e + f)) a)
    (mulQ A (symbPow 𝔭 (e + f)) b) (mulQ A (symbPow 𝔭 (e + f)) c) hφψab hψφab hχa FCab hRa.1
  obtain ⟨-, hE4⟩ := herbrand_comp_right (mulQ A (symbPow 𝔭 (e + f)) c ∘ₗ
      mulQ A (symbPow 𝔭 (e + f)) a) (mulQ A (symbPow 𝔭 (e + f)) b)
    (mulQ A (symbPow 𝔭 (e + f)) c) hcab hbca hχb hFC3 hRb.1
  -- arithmetic
  have Hf : c ^ f * a ^ f = u ^ f * π ^ (e * f) := by rw [← mul_pow, hca, mul_pow, ← pow_mul]
  have He : c ^ e * b ^ e = v ^ e * π ^ (e * f) := by
    rw [← mul_pow, hcb, mul_pow, ← pow_mul, mul_comm f e]
  have key : y₁ * v ^ e * c ^ f = (-1) ^ (e * f) * y₂ * u ^ f * c ^ e := by
    refine mul_left_cancel₀ (pow_ne_zero (e * f) hπ0) ?_
    linear_combination (-y₁ * c ^ f) * He + ((-1) ^ (e * f) * y₂ * c ^ e) * Hf + (c ^ e * c ^ f) * hy
  have hl : lam A 𝔭 y₁ + e * lam A 𝔭 v + f * lam A 𝔭 c
      = lam A 𝔭 y₂ + f * lam A 𝔭 u + e * lam A 𝔭 c := by
    have hL : lam A 𝔭 (y₁ * v ^ e * c ^ f) = lam A 𝔭 y₁ + e * lam A 𝔭 v + f * lam A 𝔭 c := by
      rw [lam_mul 𝔭 hfl (hnm hy₁ (hnp e hv)) (hnp f hc), lam_mul 𝔭 hfl hy₁ (hnp e hv),
        lam_pow 𝔭 hfl hv, lam_pow 𝔭 hfl hc]
    have hR : lam A 𝔭 (y₂ * u ^ f * c ^ e) = lam A 𝔭 y₂ + f * lam A 𝔭 u + e * lam A 𝔭 c := by
      rw [lam_mul 𝔭 hfl (hnm hy₂ (hnp f hu)) (hnp e hc), lam_mul 𝔭 hfl hy₂ (hnp f hu),
        lam_pow 𝔭 hfl hu, lam_pow 𝔭 hfl hc]
    rw [← hL, ← hR, key]
    rcases neg_one_pow_eq_or B (e * f) with hs | hs
    · rw [hs, one_mul]
    · rw [hs, neg_one_mul, neg_mul, neg_mul, lam_neg]
  refine ⟨FCab, ?_⟩
  rw [hE3] at hE4
  rw [hE4, hE1, h0.2, hRu.2, hRv.2, hRa.2, hRb.2, Nat.add_sub_cancel_left, Nat.add_sub_cancel] at hE2
  have hl' : (lam A 𝔭 y₁ : ℤ) + e * lam A 𝔭 v + f * lam A 𝔭 c
      = lam A 𝔭 y₂ + f * lam A 𝔭 u + e * lam A 𝔭 c := by exact_mod_cast hl
  linarith


end KeyLemma

end
