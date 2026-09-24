import MiyaokaMori.Prelude

/-! # Primes over a prime with finite fibre ring

(1) Let `R → S` be a ring map, `𝔮 ⊂ R` a prime, and suppose the fibre ring `κ(𝔮) ⊗_R S` is finite
over `κ(𝔮)`. Then there are only finitely many primes of `S` lying over `𝔮`, and any two of them
that are comparable are equal. (2) If moreover `R`, `S` are Noetherian, then every prime `Q` lying
over `𝔮` satisfies `ht Q ≤ ht 𝔮`. (3) Single-generator case: `R` a Noetherian domain, `S` a domain,
`R → S` injective, `S = R[x]` with `x` algebraic over `R`, and `𝔮` a height-one prime of `R`; then
the fibre ring `κ(𝔮) ⊗_R S` is finite over `κ(𝔮)`.

Proof:
1. (1): a finite fibre ring is Artinian, so its prime spectrum is finite and discrete;
   `PrimeSpectrum.preimageEquivFiber`, `preimageHomeomorphFiber` transport this to `comap⁻¹{𝔮}`; in
   a discrete space specialization is equality.
2. (2): Mathlib `Ideal.height_le_height_add_of_liesOver` (Stacks 00OM): `ht Q ≤ ht 𝔮 + ht(Q/𝔮S)`.
   `Q/𝔮S` is a minimal prime of `S/𝔮S`: if `J ≤ Q/𝔮S` is prime, its preimage `Q''` satisfies
   `𝔮S ≤ Q'' ≤ Q`, so it also lies over `𝔮`, and by (1) `Q'' = Q`, `J = Q/𝔮S`. Hence `ht(Q/𝔮S) = 0`.
3. (3): `φ = aeval x : R[X] → S` is surjective, `P = ker φ` is a nonzero prime (`x` algebraic) with
   `P ∩ R = 0`. `𝔮[X]` is a prime lying over `𝔮`, and by 00OM
   `ht 𝔮[X] ≤ ht 𝔮 + ht(⊥ ⊂ R[X]/𝔮[X]) = 1`. If `P ≤ 𝔮[X]` then `P ≠ 𝔮[X]` (take `0 ≠ a ∈ 𝔮`,
   `C a ∈ 𝔮[X] ∖ P`), so `1 ≤ ht P < ht 𝔮[X] ≤ 1`, a contradiction. Hence there is `g ∈ P`,
   `g ∉ 𝔮[X]`, whose image in `κ(𝔮)[X]` is nonzero; the fibre ring `≅ κ(𝔮)[X]/(image of P)`
   (`Polynomial.fiberEquivQuotient`) is a quotient of `κ(𝔮)[X]/(ḡ)`, which is finite-dimensional.

Reference: the single-generator step in the proof of Stacks 02MA (which cites the dimension
inequality 02IJ; here only the special case `ht 𝔮 = 1`, algebraic extension, is needed and proved
directly).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false

universe u

open Polynomial

noncomputable section

namespace Ideal

section Fiber

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (𝔮 : Ideal R) [𝔮.IsPrime]

theorem finite_comap_preimage_singleton_of_finite_fiber
    [Module.Finite 𝔮.ResidueField (𝔮.Fiber S)] :
    (PrimeSpectrum.comap (algebraMap R S) ⁻¹' {⟨𝔮, inferInstance⟩}).Finite :=
  have : IsArtinianRing (𝔮.Fiber S) := .of_finite 𝔮.ResidueField _
  (PrimeSpectrum.preimageEquivFiber R S ⟨𝔮, inferInstance⟩).finite_iff.mpr
    finite_of_compact_of_discrete

theorem finite_primesOver_of_finite_fiber [Module.Finite 𝔮.ResidueField (𝔮.Fiber S)] :
    (𝔮.primesOver S).Finite := by
  refine ((finite_comap_preimage_singleton_of_finite_fiber (S := S) 𝔮).image
    PrimeSpectrum.asIdeal).subset ?_
  exact fun J hJ ↦ ⟨⟨_, hJ.1⟩, PrimeSpectrum.ext hJ.2.1.symm, rfl⟩

theorem eq_of_le_of_liesOver_of_finite_fiber [Module.Finite 𝔮.ResidueField (𝔮.Fiber S)]
    (P Q : Ideal S) [P.IsPrime] [Q.IsPrime] [P.LiesOver 𝔮] [Q.LiesOver 𝔮] (h : P ≤ Q) :
    P = Q := by
  have : IsArtinianRing (𝔮.Fiber S) := .of_finite 𝔮.ResidueField _
  have hd : IsDiscrete (PrimeSpectrum.comap (algebraMap R S) ⁻¹' {⟨𝔮, inferInstance⟩}) :=
    ⟨(PrimeSpectrum.preimageHomeomorphFiber R S ⟨𝔮, inferInstance⟩).symm.discreteTopology⟩
  exact congr($(hd.eq_of_specializes
    (a := ⟨P, ‹_›⟩) (b := ⟨Q, ‹_›⟩) (by simpa [← PrimeSpectrum.le_iff_specializes])
    (PrimeSpectrum.ext (P.over_def 𝔮).symm) (PrimeSpectrum.ext (Q.over_def 𝔮).symm)).1)

theorem height_le_of_liesOver_of_finite_fiber [IsNoetherianRing R] [IsNoetherianRing S]
    [Module.Finite 𝔮.ResidueField (𝔮.Fiber S)]
    (Q : Ideal S) [Q.IsPrime] [Q.LiesOver 𝔮] : Q.height ≤ 𝔮.height := by
  refine (Ideal.height_le_height_add_of_liesOver 𝔮 Q).trans ?_
  have hle : 𝔮.map (algebraMap R S) ≤ Q := by
    rw [Ideal.map_le_iff_le_comap, ← Ideal.under_def, ← Q.over_def 𝔮]
  have hprime : (Q.map (Ideal.Quotient.mk (𝔮.map (algebraMap R S)))).IsPrime :=
    Ideal.isPrime_map_quotientMk_of_isPrime hle
  suffices h0 : (Q.map (Ideal.Quotient.mk (𝔮.map (algebraMap R S)))).height = 0 by
    rw [h0, add_zero]
  rw [Ideal.height_eq_zero_iff]
  refine ⟨⟨hprime, bot_le⟩, fun J ⟨hJ, _⟩ hJQ ↦ ?_⟩
  have hsurj : Function.Surjective (Ideal.Quotient.mk (𝔮.map (algebraMap R S))) :=
    Ideal.Quotient.mk_surjective
  set Q'' := J.comap (Ideal.Quotient.mk (𝔮.map (algebraMap R S))) with hQ''
  have : Q''.IsPrime := Ideal.comap_isPrime _ _
  have hQ''Q : Q'' ≤ Q := by
    intro s hs
    have h1 : Ideal.Quotient.mk _ s ∈ Q.map (Ideal.Quotient.mk (𝔮.map (algebraMap R S))) :=
      hJQ hs
    rw [Ideal.mem_map_iff_of_surjective _ hsurj] at h1
    obtain ⟨t, ht, hts⟩ := h1
    have : t - s ∈ 𝔮.map (algebraMap R S) := by
      rw [← Ideal.Quotient.eq]; exact hts
    have := Q.sub_mem ht (hle this)
    simpa using this
  have hle'' : 𝔮.map (algebraMap R S) ≤ Q'' := by
    intro s hs
    show Ideal.Quotient.mk _ s ∈ J
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hs]; exact J.zero_mem
  have : Q''.LiesOver 𝔮 := by
    refine ⟨le_antisymm ?_ ?_⟩
    · rw [Ideal.under_def, ← Ideal.map_le_iff_le_comap]; exact hle''
    · rw [Q.over_def 𝔮]; exact Ideal.comap_mono hQ''Q
  have heq : Q'' = Q := eq_of_le_of_liesOver_of_finite_fiber 𝔮 Q'' Q hQ''Q
  rw [← heq, hQ'', Ideal.map_comap_of_surjective _ hsurj]

end Fiber

section Step

variable {R S : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] [CommRing S] [IsDomain S]
  [Algebra R S] [FaithfulSMul R S]

theorem liesOver_map_C (𝔮 : Ideal R) : (𝔮.map (C : R →+* R[X])).LiesOver 𝔮 := ⟨by
  ext a
  rw [Ideal.under_def, Ideal.mem_comap, Polynomial.algebraMap_eq, Ideal.mem_map_C_iff]
  refine ⟨fun h n ↦ ?_, fun h ↦ by simpa using h 0⟩
  rw [Polynomial.coeff_C]; split_ifs
  · exact h
  · exact 𝔮.zero_mem⟩

theorem height_map_C_le_one (𝔮 : Ideal R) [𝔮.IsPrime] (h𝔮 : 𝔮.height = 1) :
    (𝔮.map (C : R →+* R[X])).height ≤ 1 := by
  have hprime : (𝔮.map (C : R →+* R[X])).IsPrime := Ideal.isPrime_map_C_of_isPrime
  have hlo : (𝔮.map (C : R →+* R[X])).LiesOver 𝔮 := liesOver_map_C 𝔮
  refine (Ideal.height_le_height_add_of_liesOver 𝔮 (𝔮.map (C : R →+* R[X]))).trans ?_
  rw [h𝔮, Polynomial.algebraMap_eq, Ideal.map_quotient_self]
  have : Nontrivial (R[X] ⧸ 𝔮.map (C : R →+* R[X])) :=
    Ideal.Quotient.nontrivial_iff.mpr hprime.ne_top
  rw [Ideal.height_bot, add_zero]

/-- The single-generator step: the fibre ring is finite. -/
theorem finite_fiber_of_adjoin_singleton (x : S) (hx : Algebra.adjoin R {x} = ⊤)
    (halg : IsAlgebraic R x) (𝔮 : Ideal R) [𝔮.IsPrime] (h𝔮 : 𝔮.height = 1) :
    Module.Finite 𝔮.ResidueField (𝔮.Fiber S) := by
  let φ : R[X] →ₐ[R] S := Polynomial.aeval x
  have hφ : Function.Surjective φ := by
    rw [← AlgHom.range_eq_top, ← Algebra.adjoin_singleton_eq_range_aeval, hx]
  have hPprime : (RingHom.ker (φ : R[X] →+* S)).IsPrime := RingHom.ker_isPrime _
  have hPne : RingHom.ker (φ : R[X] →+* S) ≠ ⊥ := by
    obtain ⟨g, hg0, hg⟩ := halg
    intro h
    have : g ∈ RingHom.ker (φ : R[X] →+* S) := hg
    rw [h, Ideal.mem_bot] at this
    exact hg0 this
  -- `P` is not contained in `𝔮[X]`
  have hnot : ¬ RingHom.ker (φ : R[X] →+* S) ≤ 𝔮.map (C : R →+* R[X]) := by
    intro hle
    have hprime : (𝔮.map (C : R →+* R[X])).IsPrime := Ideal.isPrime_map_C_of_isPrime
    have h𝔮ne : 𝔮 ≠ ⊥ := by
      rintro rfl; simp at h𝔮
    obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h𝔮ne
    have hlt : RingHom.ker (φ : R[X] →+* S) < 𝔮.map (C : R →+* R[X]) := by
      refine lt_of_le_of_ne hle fun heq ↦ ?_
      have h1 : C a ∈ RingHom.ker (φ : R[X] →+* S) := heq ▸ Ideal.mem_map_of_mem _ ha
      rw [RingHom.mem_ker] at h1
      have h2 : algebraMap R S a = 0 := by simpa [φ] using h1
      exact ha0 ((FaithfulSMul.algebraMap_injective R S) (by simpa using h2))
    have h1 : (1 : ℕ∞) ≤ (RingHom.ker (φ : R[X] →+* S)).height := by
      rw [Order.one_le_iff_pos, pos_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]
      exact hPne
    have h2 := height_map_C_le_one 𝔮 h𝔮
    have hfin : (RingHom.ker (φ : R[X] →+* S)).height ≠ ⊤ := Ideal.height_ne_top hPprime.ne_top
    have h3 := Ideal.height_strict_mono_of_isPrime hlt
    exact absurd (h1.trans_lt (h3.trans_le h2)) (lt_irrefl _)
  obtain ⟨g, hgP, hg𝔮⟩ := Set.not_subset.mp hnot
  let κ := 𝔮.ResidueField
  let I : Ideal κ[X] := (RingHom.ker (φ : R[X] →+* S)).map (mapRingHom (algebraMap R κ))
  let gb : κ[X] := g.map (algebraMap R κ)
  have hgb0 : gb ≠ 0 := by
    intro h0
    apply hg𝔮
    rw [SetLike.mem_coe, Ideal.mem_map_C_iff]
    intro n
    have : (gb.coeff n) = 0 := by rw [h0]; simp
    rw [Polynomial.coeff_map] at this
    exact (Ideal.algebraMap_residueField_eq_zero).mp this
  have hgbI : gb ∈ I := Ideal.mem_map_of_mem _ hgP
  have hfin1 : Module.Finite κ (κ[X] ⧸ Ideal.span {gb}) :=
    (AdjoinRoot.powerBasis hgb0).finite
  have hle : Ideal.span {gb} ≤ I := (Ideal.span_singleton_le_iff_mem I).mpr hgbI
  have hfin2 : Module.Finite κ (κ[X] ⧸ I) :=
    Module.Finite.of_surjective (Ideal.Quotient.factorₐ κ hle).toLinearMap
      (Ideal.Quotient.factor_surjective hle)
  exact Module.Finite.equiv (Polynomial.fiberEquivQuotient φ hφ 𝔮).symm.toLinearEquiv

end Step

end Ideal

end
