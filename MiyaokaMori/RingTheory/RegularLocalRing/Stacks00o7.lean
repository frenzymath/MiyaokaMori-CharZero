import MiyaokaMori.Prelude
import MiyaokaMori.RingTheory.RegularLocalRing.Stacks00o7GlobalDimension
import MiyaokaMori.RingTheory.RegularLocalRing.Stacks00o7FiniteFreeResolution

/-! # Stacks 00O7: finite free resolutions over a regular local ring

Stacks 00O7: for a finite module `M` over a regular local ring `R` of dimension `d`, if `𝔪` contains an
`M`-weakly regular sequence of length `e` (i.e. `e ≤ depth M`), then `M` has a finite free resolution
`0 → F_{d−e} → … → F_0 → M → 0` of length `≤ d − e`.

Reference: Stacks 00O7 (algebra-proposition-regular-finite-gl-dim), via 00NT, 00NG, 00NE.

The proof route differs from the original (depth / Cohen–Macaulay, 00NG/00NT): it is the elementary induction of
Matsumura, *Commutative Ring Theory*, Thm 19.2 / Bruns–Herzog Thm 2.2.7 in the direction "regular ⇒ finite global
dimension":

1. `Stacks00o7ChangeOfRings`: the change-of-rings inequality `pd_R N ≤ pd_{R/(x)} N + 1` (`x` a nonzerodivisor in
   the maximal ideal, `N` a finite `R/(x)`-module).
2. `Stacks00o7GlobalDimension`: induction on `dim R` (`x ∈ 𝔪 ∖ 𝔪²`, `R/(x)` regular of dimension one less: Stacks
   00NQ; regular local rings are domains: Stacks 00NP) gives **the case `e = 0`**: a finite module over a regular
   local ring of dimension `d` has projective dimension `≤ d` (`IsRegularLocalRing.hasProjectiveDimensionLE_of_finite`).
   This is the form actually used downstream (Stacks 00OC, 00OF, 0AFZ).
3. This file: Mathlib's `ModuleCat.projectiveDimension_quotient_eq_add_length_of_isWeaklyRegular`
   (`pd (M/(r₁,…,r_e)M) = pd M + e`) gives `pd M ≤ d − e`; then `Stacks00o7FiniteFreeResolution` (the syzygy
   construction: `pd M ≤ n` ⇒ there is a projective resolution with finite free terms, zero in degrees `i > n`)
   gives the object in the statement. For `M = 0` the projective dimension is `⊥` and the zero resolution works
   directly (no weakly regular sequence needed).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Arithmetic in `WithBot ℕ∞`: if `a ≠ ⊥` and `a + e ≤ d` (`d e : ℕ`) then `a ≤ d - e`. -/
theorem WithBot.le_natCast_sub_of_add_natCast_le {a : WithBot ℕ∞} (ha : a ≠ ⊥) {d e : ℕ}
    (h : a + (e : WithBot ℕ∞) ≤ (d : WithBot ℕ∞)) : a ≤ ((d - e : ℕ) : WithBot ℕ∞) := by
  obtain ⟨a', rfl⟩ := WithBot.ne_bot_iff_exists.mp ha
  have h1 : a' + (e : ℕ∞) ≤ (d : ℕ∞) := by
    rw [← WithBot.coe_natCast, ← WithBot.coe_natCast, ← WithBot.coe_add, WithBot.coe_le_coe] at h
    exact h
  have h2 : a' ≤ ((d - e : ℕ) : ℕ∞) := by
    induction a' using ENat.recTopCoe with
    | top => simp at h1
    | coe n =>
      have h3 : n + e ≤ d := by exact_mod_cast h1
      exact_mod_cast (show n ≤ d - e by omega)
  rw [← WithBot.coe_natCast, WithBot.coe_le_coe]
  exact h2

/-- **Stacks 00O7.** `pd M ≤ d − e` for a finite module `M` over a `d`-dimensional regular local ring
carrying an `M`-weakly-regular sequence of length `e` in the maximal ideal (for `M ≠ 0` this forces
`e ≤ d`; for `M = 0` the projective dimension is `⊥`). -/
theorem IsRegularLocalRing.hasProjectiveDimensionLE_sub_of_isWeaklyRegular {R : Type u} [CommRing R]
    [IsRegularLocalRing R] (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (d e : ℕ) (hd : ringKrullDim R = d)
    (he : ∃ rs : List R, rs.length = e ∧ (∀ r ∈ rs, r ∈ IsLocalRing.maximalIdeal R) ∧
      RingTheory.Sequence.IsWeaklyRegular M rs) :
    HasProjectiveDimensionLE (ModuleCat.of R M) (d - e) := by
  obtain ⟨rs, hlen, hmem, hreg⟩ := he
  by_cases hM : Subsingleton M
  · have h0 : IsZero (ModuleCat.of R M) := ModuleCat.isZero_of_subsingleton _
    have := h0.hasProjectiveDimensionLT_zero
    exact hasProjectiveDimensionLT_of_ge _ 0 (d - e + 1) (Nat.zero_le _)
  · have : Nontrivial M := not_subsingleton_iff_nontrivial.mp hM
    have h1 := ModuleCat.projectiveDimension_quotient_eq_add_length_of_isWeaklyRegular
      (ModuleCat.of R M) rs hreg hmem
    have hQ : HasProjectiveDimensionLE
        (ModuleCat.of R (M ⧸ Ideal.ofList rs • (⊤ : Submodule R M))) d :=
      IsRegularLocalRing.hasProjectiveDimensionLE_of_finite _ d hd
    have h2 : projectiveDimension (ModuleCat.of R M) + (e : WithBot ℕ∞) ≤ (d : WithBot ℕ∞) := by
      rw [← hlen, ← h1]
      exact (projectiveDimension_le_iff _ _).mpr hQ
    have hne : projectiveDimension (ModuleCat.of R M) ≠ ⊥ := by
      rw [Ne, projectiveDimension_eq_bot_iff, ModuleCat.isZero_iff_subsingleton]
      exact hM
    rw [← projectiveDimension_le_iff]
    exact WithBot.le_natCast_sub_of_add_natCast_le hne h2

theorem IsRegularLocalRing.exists_finite_free_resolution {R : Type u} [CommRing R]
    [IsRegularLocalRing R] (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M]
    (d e : ℕ) (hd : ringKrullDim R = d)
    (he : ∃ rs : List R, rs.length = e ∧ (∀ r ∈ rs, r ∈ IsLocalRing.maximalIdeal R) ∧
      RingTheory.Sequence.IsWeaklyRegular M rs) :
    ∃ P : CategoryTheory.ProjectiveResolution (ModuleCat.of R M),
      (∀ i, Module.Finite R (P.complex.X i) ∧ Module.Free R (P.complex.X i)) ∧
      ∀ i, d - e < i → CategoryTheory.Limits.IsZero (P.complex.X i) :=
  ModuleCat.exists_projectiveResolution_finite_free_of_hasProjectiveDimensionLE M (d - e)
    (IsRegularLocalRing.hasProjectiveDimensionLE_sub_of_isWeaklyRegular M d e hd he)

end
