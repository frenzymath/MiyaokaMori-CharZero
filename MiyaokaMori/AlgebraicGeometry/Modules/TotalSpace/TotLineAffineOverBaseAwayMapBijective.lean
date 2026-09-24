import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Morphisms.TotLineAffineOverBaseFromOfGlobalSectionsIso

/-! # Bijectivity of the degree-zero fraction map

**Bijectivity criterion for the degree-zero fraction map** `ρ = Proj.awayMapOfGlobalSections 𝒜 f t :
(A_t)_0 → Γ(X, ⊤)[1/f t]`, `a/t^k ↦ f(a)/f(t)^k` (Stacks 01O4, 01NS), for a
degree-one element `t ∈ 𝒜 1` with `f t = 1`:

if `f : A → Γ(X, ⊤)` is **surjective** and **injective on every homogeneous piece** (`a ∈ 𝒜 k`, `f a = 0 ⟹ a = 0`),
then `ρ` is bijective.

This is the shared algebraic core of `totalSpace.toProjBundle_awayMap_bijective` (`TotLineAffineOverBase`):
there `A = A(W)`, `t = T` is the `O`-coordinate, `f = φ_W` sends `T` to `1`, and the two hypotheses are read off
the graded polynomial model `A(W) ≅ Sym(L^∨)(W)[T]` (`TotLineAffineOverBaseSymPolynomialModel`).

The general form `awayMapOfGlobalSections_bijective_of_unit_scaling` allows `f t = u` to be any unit, provided
`f = u^k · g` on `𝒜 k` for a normalized `g` with `g t = 1` satisfying the two hypotheses (then `ρ(a/t^k) = g(a)/1`).
This is the form used for `Tot(L)`: the trivialization `e` of `O_Tot` enters `φ_W` only through the unit `φ_W(T)`.

## Proof (written for `u = 1`)

## Proof (self-contained; written for `u = 1`)
Since `f t = 1`, `Γ(X, ⊤) → Γ(X, ⊤)[1/f t]` is bijective (the localization at powers of `1`).
* `ρ(a/t^k) = f(a)/f(t)^k = f(a)/1` (`awayMapOfGlobalSections_mk`).
* **Injective**: a ring homomorphism is injective iff its kernel is zero. Every `x ∈ (A_t)_0` is `a/t^k` with
  `a ∈ 𝒜 k` (`HomogeneousLocalization.Away.mk_surjective`); `ρ x = 0` gives `f a / 1 = 0`, hence `f a = 0`
  (`IsLocalization.eq_iff_exists`, the powers of `1` being `1`), hence `a = 0` by homogeneous injectivity, hence
  `x = 0`.
* **Surjective**: `y ∈ Γ(X, ⊤)[1/f t]` is `c/1` for some `c` (`IsLocalization.surj`, denominators are powers of
  `1`); `c = f a` by surjectivity; **homogenization** (`exists_homogeneous_map_eq_of_map_eq_one`): every `a ∈ A` has
  a homogeneous `a' ∈ 𝒜 k` with `f a' = f a` — by induction on the decomposition of `a`
  (`DirectSum.Decomposition.inductionOn`): `0 ↦ (0, 0)`, a homogeneous `a ∈ 𝒜 m ↦ (m, a)`, and for a sum
  `x + y` with `(k₁, x')`, `(k₂, y')` take `k₁ + k₂` and `t^{k₂} x' + t^{k₁} y'` (homogeneous of degree `k₁ + k₂`,
  and `f` of it is `f x' + f y'` because `f t = 1`). Then `ρ(a'/t^k) = f a'/1 = c/1 = y`.

Edge cases: `A = 0` or `Γ(X, ⊤) = 0` (all rings zero, bijective); `t = 0` (then `f t = 0 ≠ 1` unless
`Γ(X, ⊤) = 0`, where everything is trivial). -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Proj

variable {σ : Type u} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable {X : AlgebraicGeometry.Scheme.{u}} (f : A →+* Γ(X, ⊤))

/-- `ρ(a / t^n) = f a / (f t)^n` on the fraction `Away.mk 𝒜 ht n a ha`. -/
theorem awayMapOfGlobalSections_mk {t : A} {d : ℕ} (ht : t ∈ 𝒜 d) (n : ℕ) (a : A) (ha : a ∈ 𝒜 (n • d)) :
    awayMapOfGlobalSections 𝒜 f t (HomogeneousLocalization.Away.mk 𝒜 ht n a ha) =
      IsLocalization.mk' (Localization.Away (f t)) (f a) ⟨(f t) ^ n, Submonoid.pow_mem _ (Submonoid.mem_powers _) n⟩ := by
  unfold awayMapOfGlobalSections
  rw [RingHom.comp_apply]
  have hval : algebraMap (HomogeneousLocalization.Away 𝒜 t) (Localization.Away t)
      (HomogeneousLocalization.Away.mk 𝒜 ht n a ha) = Localization.mk a ⟨t ^ n, Submonoid.pow_mem _ (Submonoid.mem_powers _) n⟩ :=
    HomogeneousLocalization.Away.val_mk 𝒜 n ht a ha
  rw [hval, Localization.mk_eq_mk']
  unfold AlgebraicGeometry.Scheme.projBundle.evalAway
  rw [IsLocalization.map_mk']
  congr 1
  exact Subtype.ext (map_pow f t n)

/-- **Homogenization**: if `f t = 1` for some `t ∈ 𝒜 1`, every `a : A` has a homogeneous `a' ∈ 𝒜 k` with
`f a' = f a` (replace each homogeneous component `a_m` by `t^{k-m} a_m`). -/
theorem exists_homogeneous_map_eq_of_map_eq_one {t : A} (ht : t ∈ 𝒜 1) (hft : f t = 1) (a : A) :
    ∃ (k : ℕ) (a' : A), a' ∈ 𝒜 k ∧ f a' = f a := by
  induction a using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => exact ⟨0, 0, zero_mem _, rfl⟩
  | homogeneous x => exact ⟨_, x, x.2, rfl⟩
  | add x y hx hy =>
    obtain ⟨k₁, x', hx', hfx⟩ := hx
    obtain ⟨k₂, y', hy', hfy⟩ := hy
    refine ⟨k₁ + k₂, t ^ k₂ * x' + t ^ k₁ * y', ?_, ?_⟩
    · refine add_mem ?_ ?_
      · have := SetLike.mul_mem_graded (SetLike.pow_mem_graded k₂ ht) hx'
        rwa [smul_eq_mul, mul_one, add_comm] at this
      · have := SetLike.mul_mem_graded (SetLike.pow_mem_graded k₁ ht) hy'
        rwa [smul_eq_mul, mul_one] at this
    · rw [map_add, map_mul, map_mul, map_pow, map_pow, hft, one_pow, one_pow, one_mul, one_mul, hfx, hfy, map_add]

/-- **Bijectivity criterion for the degree-zero fraction map, with a unit scaling.** Let `t ∈ 𝒜 1` with `f t = u`
a unit, and let `g : A →+* Γ(X, ⊤)` be a "normalized" ring homomorphism with `g t = 1` and `f a = u^k · g a` on
every `a ∈ 𝒜 k`. If `g` is surjective and injective on every homogeneous piece, then
`awayMapOfGlobalSections 𝒜 f t` is bijective: `ρ(a/t^k) = f(a)/u^k = g(a)/1`, and `Γ(X, ⊤) → Γ(X, ⊤)[1/u]` is
bijective. -/
theorem awayMapOfGlobalSections_bijective_of_unit_scaling {t : A} (ht : t ∈ 𝒜 1) (g : A →+* Γ(X, ⊤))
    {u : Γ(X, ⊤)} (hu : IsUnit u) (hft : f t = u) (hgt : g t = 1)
    (hfg : ∀ (k : ℕ) (a : A), a ∈ 𝒜 k → f a = u ^ k * g a)
    (hsurj : Function.Surjective g)
    (hinj : ∀ (k : ℕ) (a : A), a ∈ 𝒜 k → g a = 0 → a = 0) :
    Function.Bijective (awayMapOfGlobalSections 𝒜 f t) := by
  subst hft
  -- the localization map `Γ(X, ⊤) → Γ(X, ⊤)[1/u]` is bijective (`u` is a unit)
  have hinj₀ : Function.Injective (algebraMap Γ(X, ⊤) (Localization.Away (f t))) := by
    intro c c' hcc'
    obtain ⟨⟨v, n, rfl⟩, hv⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers (f t)) _).mp hcc'
    exact (hu.pow n).mul_left_cancel hv
  have hsurj₀ : Function.Surjective (algebraMap Γ(X, ⊤) (Localization.Away (f t))) := by
    intro y
    obtain ⟨⟨c, ⟨v, n, rfl⟩⟩, hy⟩ := IsLocalization.surj (Submonoid.powers (f t)) y
    obtain ⟨w, hw⟩ := hu.pow n
    refine ⟨c * ↑w⁻¹, ?_⟩
    rw [map_mul]
    have hy' : y * algebraMap Γ(X, ⊤) (Localization.Away (f t)) (f t ^ n) = algebraMap _ _ c := hy
    rw [← hy', mul_assoc, ← map_mul, ← hw, Units.mul_inv, map_one, mul_one]
  refine ⟨?_, ?_⟩
  · refine (injective_iff_map_eq_zero _).mpr fun x hx => ?_
    obtain ⟨n, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective 𝒜 ht x
    rw [awayMapOfGlobalSections_mk 𝒜 f ht n a ha, IsLocalization.mk'_eq_iff_eq_mul, zero_mul] at hx
    have hfa : f a = 0 := hinj₀ (hx.trans (map_zero _).symm)
    have hn : n • 1 = n := by rw [smul_eq_mul, mul_one]
    have hga : g a = 0 := by
      have h1 := hfg (n • 1) a ha
      rw [hfa, hn] at h1
      exact ((hu.pow n).mul_right_eq_zero).mp h1.symm
    have ha0 : a = 0 := hinj (n • 1) a ha hga
    subst ha0
    exact HomogeneousLocalization.val_injective _ (by
      rw [HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk', IsLocalization.mk'_eq_iff_eq_mul,
        map_zero, HomogeneousLocalization.val_zero, zero_mul])
  · intro y
    obtain ⟨c, rfl⟩ := hsurj₀ y
    obtain ⟨a, rfl⟩ := hsurj c
    obtain ⟨k, a', ha', hga'⟩ := exists_homogeneous_map_eq_of_map_eq_one 𝒜 g ht hgt a
    have ha'' : a' ∈ 𝒜 (k • 1) := by rwa [smul_eq_mul, mul_one]
    refine ⟨HomogeneousLocalization.Away.mk 𝒜 ht k a' ha'', ?_⟩
    rw [awayMapOfGlobalSections_mk 𝒜 f ht k a' ha'', IsLocalization.mk'_eq_iff_eq_mul, hfg k a' ha', hga',
      map_mul, mul_comm]

/-- **Bijectivity criterion for the degree-zero fraction map** (the case `u = 1`, `g = f`). Let `t ∈ 𝒜 1` with
`f t = 1`. If `f` is surjective and injective on every homogeneous piece, then `awayMapOfGlobalSections 𝒜 f t` is
bijective. -/
theorem awayMapOfGlobalSections_bijective_of_surjective_of_homogeneous_injective {t : A} (ht : t ∈ 𝒜 1)
    (hft : f t = 1) (hsurj : Function.Surjective f)
    (hinj : ∀ (k : ℕ) (a : A), a ∈ 𝒜 k → f a = 0 → a = 0) :
    Function.Bijective (awayMapOfGlobalSections 𝒜 f t) :=
  awayMapOfGlobalSections_bijective_of_unit_scaling 𝒜 f ht f isUnit_one hft hft
    (fun k a _ => by rw [one_pow, one_mul]) hsurj hinj

end AlgebraicGeometry.Proj

end
