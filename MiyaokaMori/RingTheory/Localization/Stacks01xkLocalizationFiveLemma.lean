import MiyaokaMori.Prelude
import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.Algebra.Exact.Basic

/-! # A five lemma for localization maps

**Five lemma for localization maps** (pure commutative algebra; the algebraic core of the
Mayer–Vietoris induction step in Stacks 01XJ, proof paragraph 2).

Let `S ⊆ R` be a submonoid and
```
M₁ → M₂ → M₃ → M₄ → M₅
↓φ₁  ↓φ₂  ↓φ₃  ↓φ₄  ↓φ₅
N₁ → N₂ → N₃ → N₄ → N₅
```
a commutative ladder of `R`-modules whose rows are exact at `M₂, M₃, M₄` and `N₂, N₃, N₄`. If
`φ₁, φ₂, φ₄, φ₅` are localizations at `S` (`IsLocalizedModule S φᵢ`), then so is `φ₃`.

**Proof** (elementwise diagram chase; each of the three axioms of `IsLocalizedModule` separately).
Write `sᶜ` for "the endomorphism `y ↦ s • y`". On `Nᵢ` (`i ≠ 3`) each `s ∈ S` acts bijectively.
* *`s` acts bijectively on `N₃`.* Injective: if `s • y = 0` then `g₃ y = 0` (`s` injective on `N₄`),
  so `y = g₂ z`; `g₂ (s • z) = 0` gives `s • z = g₁ w`, `w = s • w'` (`s` surjective on `N₁`), so
  `s • z = s • g₁ w'` and `z = g₁ w'` (`s` injective on `N₂`), whence `y = g₂ g₁ w' = 0`.
  Surjective: given `y`, write `g₃ y = s • u`; then `g₄ u = 0` (`s` injective on `N₅`), so
  `u = g₃ v`, `g₃ (y - s • v) = 0`, `y - s • v = g₂ z`, `z = s • z'`, and `y = s • (v + g₂ z')`.
* *Every `y ∈ N₃` is `φ₃ m / s`.* `s • g₃ y = φ₄ m₄`; `φ₅ (f₄ m₄) = g₄ (s • g₃ y) = 0`, so
  `t • f₄ m₄ = 0` for some `t ∈ S`, i.e. `t • m₄ = f₃ m₃`; then `g₃ (φ₃ m₃ - (t s) • y) = 0`, so
  `φ₃ m₃ - (t s) • y = g₂ n₂` with `s' • n₂ = φ₂ m₂`; hence `(s' t s) • y = φ₃ (s' • m₃ - f₂ m₂)`.
* *`φ₃ m = φ₃ m'` implies `s • m = s • m'` for some `s ∈ S`.* Put `d = m - m'`. `φ₄ (f₃ d) = 0`
  gives `s • f₃ d = 0`, so `s • d = f₂ m₂`; `g₂ (φ₂ m₂) = φ₃ (s • d) = 0`, so `φ₂ m₂ = g₁ n₁`,
  `t • n₁ = φ₁ m₁`, `φ₂ (t • m₂ - f₁ m₁) = 0`, so `t' • (t • m₂ - f₁ m₁) = 0`; therefore
  `(t' t s) • d = f₂ (t' • (t • m₂)) = f₂ f₁ (t' • m₁) = 0`.

Source: Stacks 01XJ proof (the "five lemma" step), Weibel, *An introduction to homological
algebra*, Ex. 1.3.3 (five lemma) combined with exactness of localization (Stacks 00CH / Mathlib
`IsLocalizedModule.map_exact`). Used for Stacks 01XK. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

noncomputable section

namespace IsLocalizedModule

variable {R : Type*} [CommRing R] (S : Submonoid R)

/-- A linear map between subsingleton modules is a localization at any submonoid. -/
theorem of_subsingleton {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    [Subsingleton M] [Subsingleton N] (f : M →ₗ[R] N) : IsLocalizedModule S f where
  map_units s := by
    rw [Module.End.isUnit_iff]
    exact ⟨fun x y _ => Subsingleton.elim x y, fun y => ⟨y, Subsingleton.elim _ _⟩⟩
  surj y := ⟨⟨0, 1⟩, Subsingleton.elim _ _⟩
  exists_of_eq _ := ⟨1, Subsingleton.elim _ _⟩

/-- `s ∈ S` acts surjectively on the target of a localization map. -/
theorem exists_smul_eq {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (f : M →ₗ[R] N) [IsLocalizedModule S f] (s : S) (y : N) : ∃ x : N, (s : R) • x = y := by
  have h := IsLocalizedModule.map_units f s
  rw [Module.End.isUnit_iff] at h
  obtain ⟨x, hx⟩ := h.2 y
  exact ⟨x, by simpa using hx⟩

/-- `s ∈ S` acts injectively on the target of a localization map. -/
theorem smul_eq_zero_iff {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (f : M →ₗ[R] N) [IsLocalizedModule S f] (s : S) (y : N) : (s : R) • y = 0 ↔ y = 0 := by
  constructor
  · intro h
    have hinj := IsLocalizedModule.smul_injective f s
    have : (fun m : N => s • m) y = (fun m : N => s • m) 0 := by
      show s • y = s • (0 : N)
      rw [Submonoid.smul_def, h, smul_zero]
    exact hinj this
  · rintro rfl; simp

theorem smul_right_injective' {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module R M]
    [Module R N] (f : M →ₗ[R] N) [IsLocalizedModule S f] (s : S) {y y' : N}
    (h : (s : R) • y = (s : R) • y') : y = y' := by
  rw [← sub_eq_zero, ← smul_eq_zero_iff S f s, smul_sub, h, sub_self]

section FiveLemma

variable {M₁ M₂ M₃ M₄ M₅ N₁ N₂ N₃ N₄ N₅ : Type*}
  [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃] [AddCommGroup M₄] [AddCommGroup M₅]
  [AddCommGroup N₁] [AddCommGroup N₂] [AddCommGroup N₃] [AddCommGroup N₄] [AddCommGroup N₅]
  [Module R M₁] [Module R M₂] [Module R M₃] [Module R M₄] [Module R M₅]
  [Module R N₁] [Module R N₂] [Module R N₃] [Module R N₄] [Module R N₅]
  (f₁ : M₁ →ₗ[R] M₂) (f₂ : M₂ →ₗ[R] M₃) (f₃ : M₃ →ₗ[R] M₄) (f₄ : M₄ →ₗ[R] M₅)
  (g₁ : N₁ →ₗ[R] N₂) (g₂ : N₂ →ₗ[R] N₃) (g₃ : N₃ →ₗ[R] N₄) (g₄ : N₄ →ₗ[R] N₅)
  (φ₁ : M₁ →ₗ[R] N₁) (φ₂ : M₂ →ₗ[R] N₂) (φ₃ : M₃ →ₗ[R] N₃) (φ₄ : M₄ →ₗ[R] N₄) (φ₅ : M₅ →ₗ[R] N₅)

/-- **Five lemma for localization maps.** In a commutative ladder of `R`-modules with exact rows
(exact at the three middle spots), if the outer four vertical maps are localizations at `S`, so is
the middle one. -/
theorem of_exact_ladder
    (c₁ : ∀ x, g₁ (φ₁ x) = φ₂ (f₁ x)) (c₂ : ∀ x, g₂ (φ₂ x) = φ₃ (f₂ x))
    (c₃ : ∀ x, g₃ (φ₃ x) = φ₄ (f₃ x)) (c₄ : ∀ x, g₄ (φ₄ x) = φ₅ (f₄ x))
    (hf₁ : Function.Exact f₁ f₂) (hf₂ : Function.Exact f₂ f₃) (hf₃ : Function.Exact f₃ f₄)
    (hg₁ : Function.Exact g₁ g₂) (hg₂ : Function.Exact g₂ g₃) (hg₃ : Function.Exact g₃ g₄)
    [IsLocalizedModule S φ₁] [IsLocalizedModule S φ₂] [IsLocalizedModule S φ₄]
    [IsLocalizedModule S φ₅] :
    IsLocalizedModule S φ₃ where
  map_units s := by
    rw [Module.End.isUnit_iff]
    constructor
    · -- injectivity of `s •` on `N₃`
      intro y y' hyy'
      simp only [Module.algebraMap_end_apply] at hyy'
      suffices h : ∀ y : N₃, (s : R) • y = 0 → y = 0 by
        have := h (y - y') (by rw [smul_sub, hyy', sub_self])
        exact sub_eq_zero.1 this
      intro y hy
      have h1 : g₃ y = 0 := by
        rw [← smul_eq_zero_iff S φ₄ s, ← map_smul, hy, map_zero]
      obtain ⟨z, rfl⟩ := (hg₂ _).1 h1
      have h2 : g₂ ((s : R) • z) = 0 := by rw [map_smul, hy]
      obtain ⟨w, hw⟩ := (hg₁ _).1 h2
      obtain ⟨w', rfl⟩ := exists_smul_eq S φ₁ s w
      have h3 : (s : R) • z = (s : R) • g₁ w' := by rw [← hw, map_smul]
      rw [smul_right_injective' S φ₂ s h3]
      exact hg₁.apply_apply_eq_zero w'
    · -- surjectivity of `s •` on `N₃`
      intro y
      obtain ⟨u, hu⟩ := exists_smul_eq S φ₄ s (g₃ y)
      have h1 : g₄ u = 0 := by
        rw [← smul_eq_zero_iff S φ₅ s, ← map_smul, hu]
        exact hg₃.apply_apply_eq_zero y
      obtain ⟨v, rfl⟩ := (hg₃ _).1 h1
      have h2 : g₃ (y - (s : R) • v) = 0 := by
        rw [map_sub, map_smul, hu, sub_self]
      obtain ⟨z, hz⟩ := (hg₂ _).1 h2
      obtain ⟨z', rfl⟩ := exists_smul_eq S φ₂ s z
      refine ⟨v + g₂ z', ?_⟩
      simp only [Module.algebraMap_end_apply, smul_add]
      rw [map_smul] at hz
      rw [hz]; abel
  surj y := by
    obtain ⟨⟨m₄, s⟩, hs⟩ := IsLocalizedModule.surj S φ₄ (g₃ y)
    change (s : R) • g₃ y = φ₄ m₄ at hs
    have h1 : φ₅ (f₄ m₄) = 0 := by
      rw [← c₄, ← hs, map_smul, hg₃.apply_apply_eq_zero, smul_zero]
    obtain ⟨t, ht⟩ := IsLocalizedModule.exists_of_eq (S := S) (f := φ₅) (h1.trans (map_zero φ₅).symm)
    rw [Submonoid.smul_def, Submonoid.smul_def, smul_zero, ← map_smul] at ht
    obtain ⟨m₃, hm₃⟩ := (hf₃ _).1 ht
    have h2 : g₃ (φ₃ m₃ - ((t : R) * s) • y) = 0 := by
      rw [map_sub, c₃, hm₃, map_smul, mul_smul, map_smul, map_smul, hs, sub_self]
    obtain ⟨n₂, hn₂⟩ := (hg₂ _).1 h2
    obtain ⟨⟨m₂, s'⟩, hs'⟩ := IsLocalizedModule.surj S φ₂ n₂
    change (s' : R) • n₂ = φ₂ m₂ at hs'
    refine ⟨⟨(s' : R) • m₃ - f₂ m₂, s' * t * s⟩, ?_⟩
    show ((s' * t * s : S) : R) • y = φ₃ ((s' : R) • m₃ - f₂ m₂)
    have h3 : (s' : R) • (φ₃ m₃ - ((t : R) * s) • y) = φ₃ (f₂ m₂) := by
      rw [← hn₂, ← map_smul, hs', c₂]
    rw [smul_sub, smul_smul, sub_eq_iff_eq_add] at h3
    rw [map_sub, map_smul, Submonoid.coe_mul, Submonoid.coe_mul, mul_assoc, h3]
    abel
  exists_of_eq {m m'} h := by
    have hd : φ₃ (m - m') = 0 := by rw [map_sub, h, sub_self]
    have h1 : φ₄ (f₃ (m - m')) = 0 := by rw [← c₃, hd, map_zero]
    obtain ⟨s, hs⟩ := IsLocalizedModule.exists_of_eq (S := S) (f := φ₄) (h1.trans (map_zero φ₄).symm)
    rw [Submonoid.smul_def, Submonoid.smul_def, smul_zero, ← map_smul] at hs
    obtain ⟨m₂, hm₂⟩ := (hf₂ _).1 hs
    have h2 : g₂ (φ₂ m₂) = 0 := by
      rw [c₂, hm₂, map_smul, hd, smul_zero]
    obtain ⟨n₁, hn₁⟩ := (hg₁ _).1 h2
    obtain ⟨⟨m₁, t⟩, ht⟩ := IsLocalizedModule.surj S φ₁ n₁
    change (t : R) • n₁ = φ₁ m₁ at ht
    have h3 : φ₂ ((t : R) • m₂ - f₁ m₁) = 0 := by
      rw [map_sub, map_smul, ← hn₁, ← map_smul, ht, c₁, sub_self]
    obtain ⟨t', ht'⟩ := IsLocalizedModule.exists_of_eq (S := S) (f := φ₂) (h3.trans (map_zero φ₂).symm)
    rw [Submonoid.smul_def, Submonoid.smul_def, smul_zero, smul_sub, sub_eq_zero] at ht'
    refine ⟨t' * t * s, ?_⟩
    rw [Submonoid.smul_def, Submonoid.smul_def, ← sub_eq_zero, ← smul_sub]
    have h4 : ((t' * t * s : S) : R) • (m - m') = f₂ ((t' : R) • ((t : R) • m₂)) := by
      rw [Submonoid.coe_mul, Submonoid.coe_mul, mul_assoc, mul_smul, mul_smul, ← hm₂, map_smul,
        map_smul]
    rw [h4, ht', ← map_smul, hf₁.apply_apply_eq_zero]

end FiveLemma

end IsLocalizedModule

end
