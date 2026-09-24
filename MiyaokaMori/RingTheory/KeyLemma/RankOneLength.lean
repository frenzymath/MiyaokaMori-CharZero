import MiyaokaMori.Prelude
import MiyaokaMori.RingTheory.KeyLemma.Defs
import MiyaokaMori.RingTheory.KeyLemma.Uniformizer
import MiyaokaMori.RingTheory.Length.FiniteLengthCriterion

/-! # Length of a rank-one lattice modulo an element

For `B_𝔭` a DVR and `y ∉ 𝔭`: `L_j := 𝔭^(j)/𝔭^(j+1)` is a torsion-free finite module of rank `1` over
`D = B/𝔭`, and `length_A(L_j/yL_j) = length_A(D/yD)`. In terms of relative lengths of `A`-submodules
of `B`: `l(𝔭^(j) / (𝔭^(j+1) + y𝔭^(j))) = length_A(B/(𝔭+yB))`.

Reference: last paragraph of the proof of Stacks 02QF (for a lattice `M` over `R/𝔮`,
`length(M/xM) = rank·ord(x)`) in the rank-one case; the comparison `M ⊃ xD` uses 0EA9.

The proof actually used (equivalent to the Herbrand-quotient argument of 0EA9, but using only lattice
computations with relative lengths): write `I = 𝔭^(j)`, `N = 𝔭^(j+1)`, `x = π^j` (`π ∈ 𝔭^(1) ∖ 𝔭^(2)`),
`X = xB + N`, `Y = N + yI`, `Z = xyB + N`. The chains `Z ≤ X ≤ I` and `Z ≤ Y ≤ I` give
`l(I/Z) = l(X/Z) + l(I/X) = l(Y/Z) + l(I/Y)`. Second isomorphism theorem + injectivity of multiplication
by `x`: `X/Z ≅ xB/(xB ∩ Z) ≅ B/(𝔭 + yB)` (`xb ∈ Z ⇔ b ∈ 𝔭 + yB`, using `ord x = j`); injectivity of
multiplication by `y`: `Y/Z ≅ yI/(yI ∩ Z) ≅ I/X` (`ym ∈ Z ⇔ m ∈ X`, using `y ∉ 𝔭` and saturation of
`N = 𝔭^(j+1)`). `l(I/X) < ∞` (`length_ne_top_of_smul_eq_zero`); cancelling gives
`l(I/Y) = l(B/(𝔭 + yB))`.

Note: this module is imported by `HerbrandRange`, which has a `private theorem symbPow_zero` clashing with
the public `KeyLemma.symbPow_zero` of `HerbrandUniformizerPowers` ("a non-private declaration has already
been declared"), so this module cannot import `HerbrandUniformizerPowers`; the private auxiliary lemmas
below are copies of the lemmas of the same name in `HerbrandUniformizerPowers` / `HerbrandRange`.
-/

set_option autoImplicit false

universe u

open PeriodicComplex

noncomputable section

namespace KeyLemma

section SymbPowFacts

/-- Copy of `HerbrandUniformizerPowers.mem_submoduleOf_iff`. -/
private theorem mem_submoduleOf_iff' {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    {p q : Submodule R M} {x : q} : x ∈ p.submoduleOf q ↔ (x : M) ∈ p := Iff.rfl

/-- Copy of `HerbrandUniformizerPowers.exists_smul_mem_of_fg`: if `K` is finitely generated and every element
of `K` is multiplied into `J` by some element of `S`, then a single element of `S` multiplies all of `K`
into `J`. -/
private theorem exists_smul_mem_of_fg' {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
    (S : Submonoid R) {K J : Submodule R M} (hK : K.FG)
    (h : ∀ k ∈ K, ∃ s ∈ S, s • k ∈ J) : ∃ s ∈ S, ∀ k ∈ K, s • k ∈ J := by
  refine Submodule.fg_induction
    (motive := fun K' _ => K' ≤ K → ∃ s ∈ S, ∀ k ∈ K', s • k ∈ J) ?_ ?_ K hK le_rfl
  · intro x hx
    obtain ⟨s, hs, hsx⟩ := h x (hx (Submodule.mem_span_singleton_self x))
    refine ⟨s, hs, fun k hk => ?_⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hk
    rw [smul_comm]
    exact J.smul_mem c hsx
  · intro K₁ K₂ _ _ h₁ h₂ hle
    obtain ⟨s₁, hs₁, h₁⟩ := h₁ (le_sup_left.trans hle)
    obtain ⟨s₂, hs₂, h₂⟩ := h₂ (le_sup_right.trans hle)
    refine ⟨s₁ * s₂, S.mul_mem hs₁ hs₂, fun k hk => ?_⟩
    obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := Submodule.mem_sup.mp hk
    have e1 : (s₁ * s₂) • k₁ = s₂ • (s₁ • k₁) := by rw [mul_comm, mul_smul]
    have e2 : (s₁ * s₂) • k₂ = s₁ • (s₂ • k₂) := mul_smul _ _ _
    rw [smul_add, e1, e2]
    exact J.add_mem (J.smul_mem _ (h₁ k₁ hk₁)) (J.smul_mem _ (h₂ k₂ hk₂))

variable {B : Type u} [CommRing B] [IsDomain B] (𝔭 : Ideal B) [𝔭.IsPrime]

omit [IsDomain B] in
/-- `𝔭^(n+1) ⊆ 𝔭^(n)`. (Analogous to `HerbrandRange.symbPow_anti`; `HerbrandRange` imports this module, so it
cannot be reused here.) -/
private theorem symbPow_succ_le (n : ℕ) : symbPow 𝔭 (n + 1) ≤ symbPow 𝔭 n :=
  Ideal.comap_mono (Ideal.pow_le_pow_right (Nat.le_succ n))

omit [IsDomain B] in
/-- `y ∉ 𝔭` is invertible in `B_𝔭`, so `y·b ∈ 𝔭^(m) ⇒ b ∈ 𝔭^(m)`. (Same statement as
`HerbrandRange.mem_symbPow_of_notMem_mul_mem`; `HerbrandRange` imports this module, so it cannot be
reused here.) -/
private theorem mem_symbPow_of_notMem_mul_mem' {y b : B} {m : ℕ} (hy : y ∉ 𝔭)
    (h : y * b ∈ symbPow 𝔭 m) : b ∈ symbPow 𝔭 m := by
  unfold symbPow at h ⊢
  rw [Ideal.mem_comap, map_mul] at h
  rw [Ideal.mem_comap]
  exact (Ideal.unit_mul_mem_iff_mem _
    ((IsLocalization.AtPrime.isUnit_to_map_iff (Localization.AtPrime 𝔭) 𝔭 y).mpr hy)).mp h

omit [IsDomain B] in
/-- `z ∈ 𝔭`, `b ∈ 𝔭^(n) ⇒ z·b ∈ 𝔭^(n+1)` (`z/1 ∈ 𝔪`, `b/1 ∈ 𝔪^n`). -/
private theorem mul_mem_symbPow_succ {z b : B} {n : ℕ} (hz : z ∈ 𝔭) (hb : b ∈ symbPow 𝔭 n) :
    z * b ∈ symbPow 𝔭 (n + 1) := by
  unfold symbPow at hb ⊢
  rw [Ideal.mem_comap] at hb ⊢
  rw [map_mul, pow_succ']
  exact Ideal.mul_mem_mul
    ((IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime 𝔭) 𝔭 z).mpr hz) hb

omit [IsDomain B] in
/-- For `ord x = j` (`x ∈ 𝔭^(j) ∖ 𝔭^(j+1)`): `x·b ∈ 𝔭^(j+1) ⇒ b ∈ 𝔭`. -/
private theorem mem_of_mul_mem_symbPow_succ {x b : B} {j : ℕ}
    (hx' : x ∉ symbPow 𝔭 (j + 1)) (h : x * b ∈ symbPow 𝔭 (j + 1)) : b ∈ 𝔭 := by
  by_contra hb
  exact hx' (mem_symbPow_of_notMem_mul_mem' 𝔭 hb (by rw [mul_comm]; exact h))

variable [IsDiscreteValuationRing (Localization.AtPrime 𝔭)]

/-- Copy of `HerbrandUniformizerPowers.maximalIdeal_eq_span_of_uniformizer`: `π ∈ 𝔭^(1) ∖ 𝔭^(2) ⇒ 𝔪_{B_𝔭} = (π/1)`. -/
private theorem maximalIdeal_eq_span_of_uniformizer' {π : B} (hπ1 : π ∈ symbPow 𝔭 1)
    (hπ2 : π ∉ symbPow 𝔭 2) :
    IsLocalRing.maximalIdeal (Localization.AtPrime 𝔭) =
      Ideal.span {algebraMap B (Localization.AtPrime 𝔭) π} := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime 𝔭)
  have hm : IsLocalRing.maximalIdeal (Localization.AtPrime 𝔭) = Ideal.span {ϖ} :=
    hϖ.maximalIdeal_eq
  simp only [symbPow, Ideal.mem_comap, hm, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    pow_one] at hπ1 hπ2
  obtain ⟨a, ha⟩ := hπ1
  rw [ha] at hπ2 ⊢
  rw [hm, Ideal.span_singleton_eq_span_singleton]
  have hu : IsUnit a := by
    rw [← IsLocalRing.notMem_maximalIdeal, hm, Ideal.mem_span_singleton]
    rintro ⟨b, rfl⟩
    exact hπ2 ⟨b, by ring⟩
  exact ⟨hu.unit, by rw [IsUnit.unit_spec]⟩

variable {𝔭}

/-- Copy of `HerbrandUniformizerPowers.mem_symbPow_iff_pow_dvd`. -/
private theorem mem_symbPow_iff_pow_dvd' {π : B} (hπ1 : π ∈ symbPow 𝔭 1) (hπ2 : π ∉ symbPow 𝔭 2)
    (x : B) (n : ℕ) :
    x ∈ symbPow 𝔭 n ↔
      algebraMap B (Localization.AtPrime 𝔭) π ^ n ∣ algebraMap B (Localization.AtPrime 𝔭) x := by
  simp only [symbPow, Ideal.mem_comap, maximalIdeal_eq_span_of_uniformizer' 𝔭 hπ1 hπ2,
    Ideal.span_singleton_pow, Ideal.mem_span_singleton]

/-- Copy of `HerbrandUniformizerPowers.exists_mul_eq_pow_mul_of_mem_symbPow`: `b ∈ 𝔭^(m) ⇒` there are `s ∉ 𝔭`
and `c` with `sb = π^m c`. -/
private theorem exists_mul_eq_pow_mul_of_mem_symbPow' {π : B} (hπ1 : π ∈ symbPow 𝔭 1)
    (hπ2 : π ∉ symbPow 𝔭 2) {b : B} {m : ℕ} (hb : b ∈ symbPow 𝔭 m) :
    ∃ s ∉ 𝔭, ∃ c : B, s * b = π ^ m * c := by
  rw [mem_symbPow_iff_pow_dvd' hπ1 hπ2] at hb
  obtain ⟨u, hu⟩ := hb
  obtain ⟨⟨c, s⟩, hcs⟩ := IsLocalization.surj 𝔭.primeCompl u
  simp only at hcs
  refine ⟨s, s.2, c, IsLocalization.injective (Localization.AtPrime 𝔭)
    (Ideal.primeCompl_le_nonZeroDivisors 𝔭) ?_⟩
  rw [map_mul, map_mul, map_pow, hu, mul_comm, mul_assoc, hcs]

/-- `π ∈ 𝔭^(1) ∖ 𝔭^(2) ⇒ π^j ∈ 𝔭^(j) ∖ 𝔭^(j+1)`. -/
private theorem pow_mem_symbPow_and_not_mem {π : B} (hπ1 : π ∈ symbPow 𝔭 1) (hπ2 : π ∉ symbPow 𝔭 2)
    (j : ℕ) : π ^ j ∈ symbPow 𝔭 j ∧ π ^ j ∉ symbPow 𝔭 (j + 1) := by
  have hmem : algebraMap B (Localization.AtPrime 𝔭) π ∈
      IsLocalRing.maximalIdeal (Localization.AtPrime 𝔭) := by
    rw [maximalIdeal_eq_span_of_uniformizer' 𝔭 hπ1 hπ2]
    exact Ideal.mem_span_singleton_self _
  have hne : algebraMap B (Localization.AtPrime 𝔭) π ≠ 0 := by
    intro h
    apply hπ2
    rw [mem_symbPow_iff_pow_dvd' hπ1 hπ2, h]
    exact dvd_zero _
  have hnu : ¬ IsUnit (algebraMap B (Localization.AtPrime 𝔭) π) := fun hu =>
    IsLocalRing.notMem_maximalIdeal.mpr hu hmem
  rw [mem_symbPow_iff_pow_dvd' hπ1 hπ2, mem_symbPow_iff_pow_dvd' hπ1 hπ2, map_pow,
    pow_dvd_pow_iff hne hnu, pow_dvd_pow_iff hne hnu]
  omega

end SymbPowFacts

variable {A B : Type u} [CommRing A] [IsNoetherianRing A] [CommRing B] [IsDomain B] [Algebra A B]
  [Module.Finite A B] (𝔭 : Ideal B) [𝔭.IsPrime] [IsDiscreteValuationRing (Localization.AtPrime 𝔭)]

/-- The `A`-length of `T = 𝔭^(j)/(xB + 𝔭^(j+1))` (`x = π^j`) is finite: `T` is a finite `B`-module,
annihilated by `𝔭` (`𝔭·𝔭^(j) ⊆ 𝔭^(j+1)`) and by some `s ∉ 𝔭` (`𝔭^(j)` is finitely generated and every
generator `m` satisfies `sm = π^j c`); apply `length_ne_top_of_smul_eq_zero` (with `n = 1`). -/
theorem relLength_span_pow_sup_symbPow_ne_top
    (hfl : ∀ y ∉ 𝔭, Module.length A (B ⧸ (𝔭 ⊔ Ideal.span {y})) ≠ ⊤) {π : B}
    (hπ1 : π ∈ symbPow 𝔭 1) (hπ2 : π ∉ symbPow 𝔭 2) (j : ℕ) :
    relLength ((Ideal.span {π ^ j} ⊔ symbPow 𝔭 (j + 1)).restrictScalars A)
      ((symbPow 𝔭 j).restrictScalars A) ≠ ⊤ := by
  have : IsNoetherianRing B := IsNoetherianRing.of_finite A B
  set I := symbPow 𝔭 j with hI
  set X : Ideal B := Ideal.span {π ^ j} ⊔ symbPow 𝔭 (j + 1) with hX
  -- `T := I/X`, a `B`-module
  let T : Type u := ↥I ⧸ X.submoduleOf I
  let g : ↥(I.restrictScalars A) →ₗ[A] T :=
    { toFun := fun m => Submodule.Quotient.mk (⟨m.1, m.2⟩ : I)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hg : Function.Surjective g := by
    intro t
    obtain ⟨⟨m, hm⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ t
    exact ⟨⟨m, hm⟩, rfl⟩
  have hker : LinearMap.ker g = (X.restrictScalars A).submoduleOf (I.restrictScalars A) := by
    ext m
    rw [LinearMap.mem_ker, mem_submoduleOf_iff']
    show Submodule.Quotient.mk (⟨m.1, m.2⟩ : I) = 0 ↔ _
    rw [Submodule.Quotient.mk_eq_zero, mem_submoduleOf_iff']
    exact Iff.rfl
  rw [← length_eq_relLength g hg hker]
  -- a uniform annihilator `s ∉ 𝔭`
  obtain ⟨s, hs, hsI⟩ : ∃ s ∈ 𝔭.primeCompl, ∀ m ∈ I, s • m ∈ Ideal.span {π ^ j} := by
    refine exists_smul_mem_of_fg' 𝔭.primeCompl (IsNoetherian.noetherian I) ?_
    intro m hm
    obtain ⟨s, hs, c, hsc⟩ := exists_mul_eq_pow_mul_of_mem_symbPow' hπ1 hπ2 hm
    exact ⟨s, hs, Ideal.mem_span_singleton.mpr ⟨c, hsc⟩⟩
  refine length_ne_top_of_smul_eq_zero 𝔭 hfl T s hs 1 ?_ ?_
  · intro z hz t
    rw [pow_one] at hz
    obtain ⟨⟨m, hm⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ t
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, mem_submoduleOf_iff']
    show z * m ∈ X
    exact Ideal.mem_sup_right (mul_mem_symbPow_succ 𝔭 hz hm)
  · intro t
    obtain ⟨⟨m, hm⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ t
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero, mem_submoduleOf_iff']
    show s * m ∈ X
    exact Ideal.mem_sup_left (hsI m hm)

/-- Proof: take `π ∈ 𝔭^(1) ∖ 𝔭^(2)` (`exists_uniformizer`) and `x := π^j ∈ 𝔭^(j) ∖ 𝔭^(j+1)`.
Write `I = 𝔭^(j)`, `N = 𝔭^(j+1)`, `X = xB + N`, `Y = N + yI`, `Z = xyB + N`; then `Z ≤ X ≤ I` and
`Z ≤ Y ≤ I`, and `relLength_add` gives `l(I/Z) = l(X/Z) + l(I/X) = l(Y/Z) + l(I/Y)`.
`l(X/Z) = l(B/(𝔭 + yB))`: `X = Z + xB`, and the second isomorphism theorem (`relLength_sup_left`,
`relLength_congr_inf`) reduces it to `l(xB/(xB ∩ Z))`, where `xB ∩ Z = x(𝔭 + yB)`
(`xb ∈ xyB + N ⇒ x(b − yd) ∈ N ⇒ b − yd ∈ 𝔭`, using `ord x = j`); injectivity of multiplication by `x`
(`relLength_map_of_injective`) gives `l(B/(𝔭 + yB))`.
`l(Y/Z) = l(I/X)`: `Y = Z + yI`, and likewise `yI ∩ Z = yX` (`ym ∈ xyB + N ⇒ y(m − xd) ∈ N ⇒ m − xd ∈ N`,
`y ∉ 𝔭`), with multiplication by `y` injective.
`T = I/X` has finite length (`relLength_span_pow_sup_symbPow_ne_top`, i.e.
`length_ne_top_of_smul_eq_zero`), so one can cancel in `ℕ∞`.
This is equivalent to the Herbrand-quotient argument via 0EA9 for `D → L`, but avoids Herbrand quotients
and module structures on quotient modules.
Edge cases: `j = 0`: `x = 1`, `X = I = B`, `T = 0`, same argument; if `𝔭` is maximal both sides are `0`. -/
theorem relLength_symbPow_succ
    (hfl : ∀ y ∉ 𝔭, Module.length A (B ⧸ (𝔭 ⊔ Ideal.span {y})) ≠ ⊤) (j : ℕ) {y : B} (hy : y ∉ 𝔭) :
    relLength ((symbPow 𝔭 (j + 1) ⊔ Ideal.span {y} * symbPow 𝔭 j).restrictScalars A)
        ((symbPow 𝔭 j).restrictScalars A)
      = Module.length A (B ⧸ (𝔭 ⊔ Ideal.span {y})) := by
  obtain ⟨π, hπ1, hπ2⟩ := exists_uniformizer 𝔭
  obtain ⟨hxI, hxN⟩ := pow_mem_symbPow_and_not_mem hπ1 hπ2 j
  have hfin := relLength_span_pow_sup_symbPow_ne_top 𝔭 hfl hπ1 hπ2 j
  set x := π ^ j with hx_def
  have hx0 : x ≠ 0 := fun h => hxN (h ▸ zero_mem _)
  have hy0 : y ≠ 0 := fun h => hy (h ▸ zero_mem _)
  set I := symbPow 𝔭 j with hI
  set N := symbPow 𝔭 (j + 1) with hN
  have hNI : N ≤ I := symbPow_succ_le 𝔭 j
  set X : Ideal B := Ideal.span {x} ⊔ N with hX
  set Y : Ideal B := N ⊔ Ideal.span {y} * I with hY
  set Z : Ideal B := Ideal.span {x * y} ⊔ N with hZ
  -- inclusions
  have hZX : Z ≤ X :=
    sup_le ((Ideal.span_singleton_le_span_singleton.mpr (dvd_mul_right x y)).trans le_sup_left)
      le_sup_right
  have hXI : X ≤ I := sup_le ((Ideal.span_singleton_le_iff_mem I).mpr hxI) hNI
  have hZY : Z ≤ Y :=
    sup_le ((Ideal.span_singleton_le_iff_mem _).mpr
      (Ideal.mem_sup_right (Ideal.mem_span_singleton_mul.mpr ⟨x, hxI, mul_comm y x⟩))) le_sup_left
  have hYI : Y ≤ I := sup_le hNI (Ideal.mul_le.mpr fun r hr s hs => I.mul_mem_left r hs)
  have hZX' : Z.restrictScalars A ≤ X.restrictScalars A := Submodule.restrictScalars_mono A hZX
  have hXI' : X.restrictScalars A ≤ I.restrictScalars A := Submodule.restrictScalars_mono A hXI
  have hZY' : Z.restrictScalars A ≤ Y.restrictScalars A := Submodule.restrictScalars_mono A hZY
  have hYI' : Y.restrictScalars A ≤ I.restrictScalars A := Submodule.restrictScalars_mono A hYI
  -- the `A`-linear maps "multiplication by `x`" and "multiplication by `y`"
  set fx : B →ₗ[A] B := LinearMap.mulLeft A x with hfx
  set fy : B →ₗ[A] B := LinearMap.mulLeft A y with hfy
  have hfx_inj : Function.Injective fx := fun a b h => mul_left_cancel₀ hx0 h
  have hfy_inj : Function.Injective fy := fun a b h => mul_left_cancel₀ hy0 h
  -- (1) l(X/Z) = l(B/(𝔭 + yB))
  have e3 : relLength (Z.restrictScalars A) (X.restrictScalars A)
      = Module.length A (B ⧸ (𝔭 ⊔ Ideal.span {y})) := by
    have hXZ : X.restrictScalars A = Z.restrictScalars A ⊔ (Ideal.span {x}).restrictScalars A := by
      rw [← Submodule.restrictScalars_sup]
      congr 1
      refine le_antisymm (sup_le le_sup_right (le_sup_right.trans le_sup_left))
        (sup_le (sup_le ?_ le_sup_right) le_sup_left)
      exact (Ideal.span_singleton_le_span_singleton.mpr (dvd_mul_right x y)).trans le_sup_left
    have hinf : Z.restrictScalars A ⊓ (Ideal.span {x}).restrictScalars A
        = Submodule.map fx ((𝔭 ⊔ Ideal.span {y}).restrictScalars A) := by
      ext b
      simp only [Submodule.mem_inf, Submodule.restrictScalars_mem, Submodule.mem_map, hfx,
        LinearMap.mulLeft_apply]
      constructor
      · rintro ⟨hbZ, hbx⟩
        obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton.mp hbx
        refine ⟨c, ?_, rfl⟩
        obtain ⟨z, hz, n, hn, hzn⟩ := Submodule.mem_sup.mp hbZ
        obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton.mp hz
        have hn' : x * (c - y * d) ∈ N := by
          have : x * (c - y * d) = n := by rw [mul_sub, ← hzn]; ring
          rw [this]; exact hn
        have hc : c - y * d ∈ 𝔭 := mem_of_mul_mem_symbPow_succ 𝔭 hxN hn'
        rw [Submodule.mem_sup]
        exact ⟨c - y * d, hc, y * d, Ideal.mem_span_singleton.mpr (dvd_mul_right y d), by ring⟩
      · rintro ⟨c, hc, rfl⟩
        obtain ⟨p, hp, z, hz, rfl⟩ := Submodule.mem_sup.mp hc
        obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton.mp hz
        refine ⟨?_, Ideal.mem_span_singleton.mpr (dvd_mul_right _ _)⟩
        rw [Submodule.mem_sup]
        refine ⟨x * y * d, Ideal.mem_span_singleton.mpr (dvd_mul_right _ _), x * p, ?_, by ring⟩
        rw [mul_comm]
        exact mul_mem_symbPow_succ 𝔭 hp hxI
    have htop : (Ideal.span {x}).restrictScalars A = Submodule.map fx ⊤ := by
      ext b
      simp only [Submodule.restrictScalars_mem, Submodule.mem_map, Submodule.mem_top, true_and,
        hfx, LinearMap.mulLeft_apply, Ideal.mem_span_singleton]
      constructor
      · rintro ⟨c, rfl⟩; exact ⟨c, rfl⟩
      · rintro ⟨c, rfl⟩; exact ⟨c, rfl⟩
    rw [hXZ, relLength_sup_left, ← relLength_congr_inf, hinf, htop,
      relLength_map_of_injective fx hfx_inj le_top, relLength_top]
    exact (Submodule.Quotient.restrictScalarsEquiv A (𝔭 ⊔ Ideal.span {y})).length_eq
  -- (2) l(Y/Z) = l(I/X)
  have e4 : relLength (Z.restrictScalars A) (Y.restrictScalars A)
      = relLength (X.restrictScalars A) (I.restrictScalars A) := by
    have hYZ : Y.restrictScalars A = Z.restrictScalars A ⊔ Submodule.map fy (I.restrictScalars A) := by
      ext b
      constructor
      · intro hb
        have hb' : b ∈ N ⊔ Ideal.span {y} * I := hb
        obtain ⟨n, hn, m, hm, rfl⟩ := Submodule.mem_sup.mp hb'
        obtain ⟨i, hi, rfl⟩ := Ideal.mem_span_singleton_mul.mp hm
        have hn' : n ∈ Z := Ideal.mem_sup_right hn
        have hi' : i ∈ I.restrictScalars A := hi
        exact Submodule.mem_sup.mpr ⟨n, hn', y * i, Submodule.mem_map.mpr ⟨i, hi', rfl⟩, rfl⟩
      · intro hb
        obtain ⟨z, hz, w, hw, rfl⟩ := Submodule.mem_sup.mp hb
        obtain ⟨i, hi, rfl⟩ := Submodule.mem_map.mp hw
        have hz' : z ∈ Z := hz
        obtain ⟨u, hu, n, hn, rfl⟩ := Submodule.mem_sup.mp hz'
        obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton.mp hu
        have hi' : i ∈ I := hi
        show x * y * d + n + fy i ∈ Y
        refine Submodule.mem_sup.mpr ⟨n, hn, x * y * d + y * i, ?_, ?_⟩
        · exact Ideal.mem_span_singleton_mul.mpr
            ⟨x * d + i, I.add_mem (I.mul_mem_right d hxI) hi', by ring⟩
        · rw [hfy, LinearMap.mulLeft_apply]; ring
    have hinf : Z.restrictScalars A ⊓ Submodule.map fy (I.restrictScalars A)
        = Submodule.map fy (X.restrictScalars A) := by
      ext b
      simp only [Submodule.mem_inf, Submodule.restrictScalars_mem, Submodule.mem_map, hfy,
        LinearMap.mulLeft_apply]
      constructor
      · rintro ⟨hbZ, m, hm, rfl⟩
        obtain ⟨u, hu, n, hn, hun⟩ := Submodule.mem_sup.mp hbZ
        obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton.mp hu
        have hn' : y * (m - x * d) ∈ N := by
          have : y * (m - x * d) = n := by rw [mul_sub, ← hun]; ring
          rw [this]; exact hn
        have hmN : m - x * d ∈ N := mem_symbPow_of_notMem_mul_mem' 𝔭 hy hn'
        refine ⟨m, ?_, rfl⟩
        rw [Submodule.mem_sup]
        exact ⟨x * d, Ideal.mem_span_singleton.mpr (dvd_mul_right _ _), m - x * d, hmN, by ring⟩
      · rintro ⟨m, hm, rfl⟩
        refine ⟨?_, m, hXI hm, rfl⟩
        obtain ⟨u, hu, n, hn, rfl⟩ := Submodule.mem_sup.mp hm
        obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton.mp hu
        rw [Submodule.mem_sup]
        exact ⟨x * y * d, Ideal.mem_span_singleton.mpr (dvd_mul_right _ _), y * n,
          N.mul_mem_left y hn, by ring⟩
    rw [hYZ, relLength_sup_left, ← relLength_congr_inf, hinf,
      relLength_map_of_injective fy hfy_inj hXI']
  -- (3) additivity along chains and cancellation
  have e1 := relLength_add hZX' hXI'
  have e2 := relLength_add hZY' hYI'
  rw [e3] at e1
  rw [e4] at e2
  have h : relLength (X.restrictScalars A) (I.restrictScalars A)
        + relLength (Y.restrictScalars A) (I.restrictScalars A)
      = relLength (X.restrictScalars A) (I.restrictScalars A)
        + Module.length A (B ⧸ (𝔭 ⊔ Ideal.span {y})) := by
    rw [← e2, e1, add_comm]
  exact ENat.add_right_injective_of_ne_top hfin h

end KeyLemma

end
