import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.Stacks01n2TwistStalkSections
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.WeightedProjNegativeFrame

/-! # Stacks 01MN on a chart with a degree-one factor: bijectivity of `twistSection`

**Stacks 01MN on a chart with a degree-one factor**: for a graded `S`-algebra `𝒞`, `s ∈ 𝒞 i`, `0 < i`, and
`n : ℤ`, the map `twistSection : (C_s)_n → Γ(D₊(s), O(n))`, `m ↦ (z ↦ m ∈ C_z)`
(`Stacks01n2TwistStalkSections.lean`) is **bijective**, provided `s = g * c` with `g ∈ 𝒞 1`, `c ∈ 𝒞 (i - 1)`
(`twistSection_bijective`). This is the case for every product `T_σ = T_{σ 0} ⋯ T_{σ p}` of coordinates on
`P^N_R`, which is all that the alternating Čech complex of `O(d)` on `P^N` needs.

Also: `twistSectionOn U hU` (the same section restricted to an open `U ≤ D₊(s)`), its bijectivity when
`U = D₊(s)` (`twistSectionOn_bijective`), and the two pointwise bookkeeping facts used for the compatibility
clauses of the alternating Čech complex: `toFiber_map_eq` (a ring map `C_s → C_{s'}` over `C` does not change the value at a point) and
`toFiber_smul` (the `S`-action is multiplication by `algebraMap S C r / 1`).

## Natural-language proof (self-contained; the formalized route)

Let `U := D₊(s)`, `Φ₀ := awayToSection : 𝒞_(s) → Γ(U, O)` (Mathlib: bijective for `s` homogeneous of
positive degree, `Proj.basicOpenIsoAway`). Since `s = g c ∉ z` for `z ∈ U`, also `g ∉ z`, so `g^m` does not
vanish on `U` for every `m`.

*Case `n = m ≥ 0`.* The frame `g^m ∈ Γ(U, O(m))` gives the bijection
`Φ : Γ(U, O) → Γ(U, O(m))`, `r ↦ (z ↦ r(z) · g^m/1)` (`homogeneousFrameSectionEquiv`). Put
`e₀ := g^m / 1 ∈ (C_s)_m` and `E : 𝒞_(s) → (C_s)_m`, `u ↦ u · e₀`. Pointwise,
`twistSection (E u) (z) = u(z) · g^m/1 = Φ (Φ₀ u) (z)`, so `twistSection ∘ E = Φ ∘ Φ₀` is bijective.
`E` is surjective: `a / s^k` with `a ∈ 𝒞_{ki+m}` equals `E (a c^m / s^{k+m})` because
`a c^m g^m = a s^m` (and `a c^m ∈ 𝒞_{(k+m) i}`). A map whose composite with a surjection is bijective is
bijective.

*Case `n = -m < 0`.* Use the frame `1/g^m ∈ Γ(U, O(-m))` (`inverseFrameSectionEquiv`),
`e₀ := c^m / s^m = 1/g^m ∈ (C_s)_{-m}` (degree `m(i-1) = m i - m`), and `E u := u · e₀`; then
`a / s^k` with `a ∈ 𝒞_{ki-m}` equals `E (a g^m / s^k)` because `a g^m c^m = a s^m`. Same conclusion.

Edge cases: `n < 0` is allowed (all three modules may be `0`); the zero ring gives empty `Proj` and zero
modules on both sides; `i = 1` gives `c ∈ 𝒞 0`; `m = 0` gives the frame `1` and reduces to Mathlib's
`basicOpenIsoAway`.

Source: Stacks 01MN (`Γ(D₊(f), O(n)) = (S_f)_n`), 01M7; Hartshorne II.5.12; the paper uses this only
through Stacks 01XT (the cohomology of `O(d)` on `P^N`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite TopologicalSpace HomogeneousLocalization
open AlgebraicGeometry MiyaokaMori.WeightedJets.ProjTwisting MiyaokaMori.Stacks01n2 MiyaokaMori.Stacks01n2TwistStalk
open scoped AlgebraicGeometry

noncomputable section

namespace MiyaokaMori.Stacks01mn

variable {S : Type u} [CommRing S] {C : Type u} [CommRing C] [Algebra S C] (𝒞 : ℕ → Submodule S C)
  [GradedAlgebra 𝒞] {s : C} {i : ℕ} (hs : s ∈ 𝒞 i) (hi : 0 < i) (n : ℤ)

/-! ## `twistSection` on an open `U ≤ D₊(s)` -/

/-- The section of `O(n)` over an open `U ≤ D₊(s)` given by `m ∈ (C_s)_n`: `z ↦ m ∈ C_z`
(the restriction of `twistSection m` to `U`). -/
def twistSectionOn (U : (Proj 𝒞).Opens) (hU : U ≤ Proj.basicOpen 𝒞 s) (m : twistAway 𝒞 hs hi n) :
    sectionsSubmodule 𝒞 n U :=
  ⟨fun z ↦ (twistSection 𝒞 hs hi n m).1 ⟨z.1, hU z.2⟩,
    (locallyFraction 𝒞 n).res (homOfLE hU) _ (twistSection 𝒞 hs hi n m).2⟩

theorem twistSectionOn_apply (U : (Proj 𝒞).Opens) (hU : U ≤ Proj.basicOpen 𝒞 s)
    (m : twistAway 𝒞 hs hi n) (z : U) :
    (twistSectionOn 𝒞 hs hi n U hU m).1 z = toFiber 𝒞 ⟨z.1, hU z.2⟩ (m : Localization.Away s) := rfl

theorem twistSectionOn_eq_map (U : (Proj 𝒞).Opens) (hU : U ≤ Proj.basicOpen 𝒞 s)
    (m : twistAway 𝒞 hs hi n) :
    twistSectionOn 𝒞 hs hi n U hU m =
      (Proj.twist 𝒞 n).presheaf.map (homOfLE hU).op (twistSection 𝒞 hs hi n m) := rfl

theorem twistSectionOn_self (m : twistAway 𝒞 hs hi n) :
    twistSectionOn 𝒞 hs hi n (Proj.basicOpen 𝒞 s) le_rfl m = twistSection 𝒞 hs hi n m := rfl

theorem twistSectionOn_add (U : (Proj 𝒞).Opens) (hU : U ≤ Proj.basicOpen 𝒞 s)
    (m m' : twistAway 𝒞 hs hi n) :
    twistSectionOn 𝒞 hs hi n U hU (m + m') =
      twistSectionOn 𝒞 hs hi n U hU m + twistSectionOn 𝒞 hs hi n U hU m' :=
  Subtype.ext (funext fun z ↦ map_add (toFiber 𝒞 ⟨z.1, hU z.2⟩) (m : Localization.Away s) m')

theorem twistSectionOn_zero (U : (Proj 𝒞).Opens) (hU : U ≤ Proj.basicOpen 𝒞 s) :
    twistSectionOn 𝒞 hs hi n U hU 0 = 0 :=
  Subtype.ext (funext fun z ↦ map_zero (toFiber 𝒞 ⟨z.1, hU z.2⟩))

/-- A ring map `φ : C_s → C_{s'}` over `C` does not change the value of a fraction at a point
`x ∈ D₊(s) ∩ D₊(s')`. -/
theorem toFiber_map_eq {s' : C} (φ : Localization.Away s →+* Localization.Away s')
    (hφ : ∀ a : C, φ (algebraMap C _ a) = algebraMap C _ a) {x : Proj 𝒞}
    (hx : x ∈ Proj.basicOpen 𝒞 s) (hx' : x ∈ Proj.basicOpen 𝒞 s') (m : Localization.Away s) :
    toFiber 𝒞 ⟨x, hx'⟩ (φ m) = toFiber 𝒞 ⟨x, hx⟩ m := by
  have key : (toFiber 𝒞 ⟨x, hx'⟩).comp φ = toFiber 𝒞 ⟨x, hx⟩ := by
    apply IsLocalization.ringHom_ext (Submonoid.powers s)
    ext a
    simp only [RingHom.comp_apply, hφ, IsLocalization.map_eq, RingHom.id_apply]
  exact congrArg (fun ψ : Localization.Away s →+* Fiber 𝒞 x ↦ ψ m) key

/-- The `S`-action on `C_s` is, at every point, multiplication by the constant fraction
`algebraMap S C r / 1`. -/
theorem toFiber_smul (z : Proj.basicOpen 𝒞 s) (r : S) (w : Localization.Away s) :
    toFiber 𝒞 z (r • w) = Localization.mk (algebraMap S C r) 1 * toFiber 𝒞 z w := by
  rw [Algebra.smul_def, map_mul, IsScalarTower.algebraMap_apply S C (Localization.Away s),
    IsLocalization.map_eq, RingHom.id_apply, Localization.mk_one_eq_algebraMap]

/-! ## Bijectivity (Stacks 01MN) when `s = g * c` with `deg g = 1` -/

variable {g c : C} (hg : g ∈ 𝒞 1) (hc : c ∈ 𝒞 (i - 1)) (hsgc : s = g * c)

include hsgc in
/-- `g` does not vanish on `D₊(g c)`. -/
theorem not_mem_of_mem_basicOpen (z : Proj.basicOpen 𝒞 s) : g ∉ z.1.asHomogeneousIdeal := by
  intro h
  apply z.2
  subst hsgc
  exact Ideal.mul_mem_right c _ h

include hsgc in
theorem pow_not_mem_of_mem_basicOpen (m : ℕ) (z : Proj.basicOpen 𝒞 s) :
    g ^ m ∉ z.1.asHomogeneousIdeal :=
  fun hz ↦ not_mem_of_mem_basicOpen 𝒞 hsgc z (z.1.isPrime.mem_of_pow_mem m hz)

include hs hi in
/-- Mathlib's `basicOpenIsoAway`: `𝒞_(s) → Γ(D₊(s), O)` is bijective. -/
theorem awayToSection_bijective : Function.Bijective (Proj.awayToSection 𝒞 s) := by
  have : IsIso (Proj.awayToSection 𝒞 s) := by
    rw [← Proj.basicOpenIsoAway_hom 𝒞 s hs hi]
    infer_instance
  exact ConcreteCategory.bijective_of_isIso _

include hg hc hsgc in
/-- Case `n = m ≥ 0` of `twistSection_bijective`: frame `g^m`. -/
theorem twistSection_bijective_natCast (m : ℕ) :
    Function.Bijective (twistSection 𝒞 hs hi (m : ℤ)) := by
  subst hsgc
  have hgm : g ^ m ∈ 𝒞 m := by simpa using SetLike.pow_mem_graded m hg
  have hU : ∀ z : Proj.basicOpen 𝒞 (g * c), g ^ m ∉ z.1.asHomogeneousIdeal :=
    pow_not_mem_of_mem_basicOpen 𝒞 rfl m
  let Φ := homogeneousFrameSectionEquiv 𝒞 m (g ^ m) hgm hU
  have hA := awayToSection_bijective 𝒞 hs hi
  have he₀ : (Localization.mk (g ^ m) 1 : Localization.Away (g * c)) ∈ twistAway 𝒞 hs hi (m : ℤ) :=
    ⟨m, 0, g ^ m, hgm, by simp, by congr 1; exact Subtype.ext (pow_zero (g * c)).symm⟩
  let E : Away 𝒞 (g * c) → twistAway 𝒞 hs hi (m : ℤ) :=
    fun u ↦ ⟨u.val * Localization.mk (g ^ m) 1, val_mul_mem 𝒞 hs hi _ u he₀⟩
  have hE : Function.Surjective E := by
    rintro ⟨x, p, k, a, ha, hp, rfl⟩
    have hp' : p = k * i + m := by exact_mod_cast hp
    have hdeg : a * c ^ m ∈ 𝒞 ((k + m) • i) := by
      have := SetLike.mul_mem_graded ha (SetLike.pow_mem_graded m hc)
      convert this using 2
      simp only [smul_eq_mul]
      rw [Nat.mul_sub_one, add_mul, hp']
      have := Nat.le_mul_of_pos_right m hi
      omega
    refine ⟨Away.mk 𝒞 hs (k + m) (a * c ^ m) hdeg, Subtype.ext ?_⟩
    change (Away.mk 𝒞 hs (k + m) (a * c ^ m) hdeg).val * Localization.mk (g ^ m) 1 = _
    rw [Away.val_mk, Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    refine ⟨1, ?_⟩
    simp only [OneMemClass.coe_one, one_mul, mul_one]
    ring
  have hkey : ∀ u, twistSection 𝒞 hs hi (m : ℤ) (E u) = Φ (Proj.awayToSection 𝒞 (g * c) u) := by
    intro u
    apply Subtype.ext
    funext z
    change toFiber 𝒞 z (u.val * Localization.mk (g ^ m) 1) =
      ((Proj.awayToSection 𝒞 (g * c) u : (ProjectiveSpectrum.Proj.structureSheaf 𝒞).1.obj
        (op (Proj.basicOpen 𝒞 (g * c)))).1 z).val * Localization.mk (g ^ m) 1
    rw [map_mul, val_awayToSection_apply, Localization.mk_one_eq_algebraMap, IsLocalization.map_eq,
      RingHom.id_apply, Localization.mk_one_eq_algebraMap]
  have hcomp : Function.Bijective (twistSection 𝒞 hs hi (m : ℤ) ∘ E) := by
    have : twistSection 𝒞 hs hi (m : ℤ) ∘ E = Φ ∘ Proj.awayToSection 𝒞 (g * c) := funext hkey
    rw [this]
    exact Φ.bijective.comp hA
  exact ⟨hcomp.1.of_comp_right hE, hcomp.2.of_comp⟩

include hg hc hsgc in
/-- Case `n = -m < 0` of `twistSection_bijective`: frame `1 / g^m = c^m / s^m`. -/
theorem twistSection_bijective_neg (m : ℕ) :
    Function.Bijective (twistSection 𝒞 hs hi (-(m : ℤ))) := by
  subst hsgc
  have hgm : g ^ m ∈ 𝒞 m := by simpa using SetLike.pow_mem_graded m hg
  have hU : ∀ z : Proj.basicOpen 𝒞 (g * c), g ^ m ∉ z.1.asHomogeneousIdeal :=
    pow_not_mem_of_mem_basicOpen 𝒞 rfl m
  let Φ := inverseFrameSectionEquiv 𝒞 m (g ^ m) hgm hU
  have hA := awayToSection_bijective 𝒞 hs hi
  have hcm : c ^ m ∈ 𝒞 (m * (i - 1)) := by
    simpa [smul_eq_mul] using SetLike.pow_mem_graded m hc
  have hmi : m ≤ m * i := Nat.le_mul_of_pos_right m hi
  have he₀ : (Localization.mk (c ^ m) (⟨(g * c) ^ m, m, rfl⟩ : Submonoid.powers (g * c)) : Localization.Away (g * c)) ∈
      twistAway 𝒞 hs hi (-(m : ℤ)) :=
    ⟨m * (i - 1), m, c ^ m, hcm, by rw [Nat.mul_sub_one]; push_cast [Nat.cast_sub hmi]; ring, rfl⟩
  have he₀z : ∀ z : Proj.basicOpen 𝒞 (g * c),
      toFiber 𝒞 z (Localization.mk (c ^ m) (⟨(g * c) ^ m, m, rfl⟩ : Submonoid.powers (g * c))) = Localization.mk 1 ⟨g ^ m, hU z⟩ := by
    intro z
    rw [toFiber_mk, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    refine ⟨1, ?_⟩
    simp only [OneMemClass.coe_one, one_mul, mul_one]
    ring
  let E : Away 𝒞 (g * c) → twistAway 𝒞 hs hi (-(m : ℤ)) :=
    fun u ↦ ⟨u.val * Localization.mk (c ^ m) (⟨(g * c) ^ m, m, rfl⟩ : Submonoid.powers (g * c)), val_mul_mem 𝒞 hs hi _ u he₀⟩
  have hE : Function.Surjective E := by
    rintro ⟨x, p, k, a, ha, hp, rfl⟩
    have hp' : p + m = k * i := by omega
    have hdeg : a * g ^ m ∈ 𝒞 (k • i) := by
      have := SetLike.mul_mem_graded ha hgm
      rwa [hp', ← smul_eq_mul] at this
    refine ⟨Away.mk 𝒞 hs k (a * g ^ m) hdeg, Subtype.ext ?_⟩
    change (Away.mk 𝒞 hs k (a * g ^ m) hdeg).val * Localization.mk (c ^ m) (⟨(g * c) ^ m, m, rfl⟩ : Submonoid.powers (g * c)) = _
    rw [Away.val_mk, Localization.mk_mul, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
    refine ⟨1, ?_⟩
    simp only [OneMemClass.coe_one, one_mul, Submonoid.coe_mul]
    ring
  have hkey : ∀ u, twistSection 𝒞 hs hi (-(m : ℤ)) (E u) = Φ (Proj.awayToSection 𝒞 (g * c) u) := by
    intro u
    apply Subtype.ext
    funext z
    change toFiber 𝒞 z (u.val * Localization.mk (c ^ m) (⟨(g * c) ^ m, m, rfl⟩ : Submonoid.powers (g * c))) =
      ((Proj.awayToSection 𝒞 (g * c) u : (ProjectiveSpectrum.Proj.structureSheaf 𝒞).1.obj
        (op (Proj.basicOpen 𝒞 (g * c)))).1 z).val * Localization.mk 1 ⟨g ^ m, hU z⟩
    rw [map_mul, val_awayToSection_apply, he₀z]
  have hcomp : Function.Bijective (twistSection 𝒞 hs hi (-(m : ℤ)) ∘ E) := by
    have : twistSection 𝒞 hs hi (-(m : ℤ)) ∘ E = Φ ∘ Proj.awayToSection 𝒞 (g * c) := funext hkey
    rw [this]
    exact Φ.bijective.comp hA
  exact ⟨hcomp.1.of_comp_right hE, hcomp.2.of_comp⟩

include hg hc hsgc in
/-- **Stacks 01MN** on the chart `D₊(s)`, `s = g c` with `deg g = 1`: `(C_s)_n → Γ(D₊(s), O(n))`,
`m ↦ (z ↦ m ∈ C_z)`, is bijective. -/
theorem twistSection_bijective : Function.Bijective (twistSection 𝒞 hs hi n) := by
  rcases le_or_gt 0 n with hn | hn
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = m := ⟨n.toNat, (Int.toNat_of_nonneg hn).symm⟩
    exact twistSection_bijective_natCast 𝒞 hs hi hg hc hsgc m
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = -(m : ℤ) := ⟨n.natAbs, by omega⟩
    exact twistSection_bijective_neg 𝒞 hs hi hg hc hsgc m

include hg hc hsgc in
/-- `twistSectionOn` is bijective on any open equal to `D₊(s)`. -/
theorem twistSectionOn_bijective (U : (Proj 𝒞).Opens) (hU : U = Proj.basicOpen 𝒞 s) :
    Function.Bijective (twistSectionOn 𝒞 hs hi n U hU.le) := by
  subst hU
  exact twistSection_bijective 𝒞 hs hi n hg hc hsgc

end MiyaokaMori.Stacks01mn

end
