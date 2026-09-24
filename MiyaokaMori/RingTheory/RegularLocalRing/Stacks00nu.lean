import MiyaokaMori.Prelude
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.KrullDimension.Regular

/-! # Stacks 00NU: regularity descends from `R/xR` to `R`

Stacks 00NU (Lemma 10.106.7, `algebra-lemma-regular-mod-x`): `(R, 𝔪)` a Noetherian local ring, `x ∈ 𝔪` a
nonzerodivisor, `R/xR` regular ⇒ `R` regular.

References: Stacks 00NU; Matsumura Thm 14.2 / Bruns–Herzog 2.2.4; used in the conclusion of Stacks 0AGR
(`A[𝔪/x]_𝔮 / x ≅ κ[T]_𝔮̄` regular ⇒ `A[𝔪/x]_𝔮` regular).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

noncomputable section

open IsLocalRing

/-- The number of generators of `𝔪` is `≤` the number of generators of `𝔪/x` `+ 1`: lift a system of generators
of `𝔪/xR` to `𝔪` and add `x`. -/
theorem IsLocalRing.spanFinrank_maximalIdeal_le_spanFinrank_quotient_span_singleton_add_one
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] {x : R}
    (hx : x ∈ maximalIdeal R) [IsLocalRing (R ⧸ Ideal.span {x})] :
    (maximalIdeal R).spanFinrank ≤ (maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank + 1 := by
  classical
  set f := Ideal.Quotient.mk (Ideal.span {x}) with hf
  have hfs : Function.Surjective f := Ideal.Quotient.mk_surjective
  have hker : RingHom.ker f = Ideal.span {x} := Ideal.mk_ker
  -- 𝔪̄ = map f 𝔪
  have hmap : (maximalIdeal R).map f = maximalIdeal (R ⧸ Ideal.span {x}) :=
    IsLocalRing.map_maximalIdeal_of_surjective f hfs
  have hfg : (maximalIdeal (R ⧸ Ideal.span {x})).FG := IsNoetherian.noetherian _
  obtain ⟨s, hcard, hspan⟩ := Submodule.FG.exists_span_finset_card_eq_spanFinrank hfg
  -- lift
  have hlift : ∀ b ∈ s, ∃ a ∈ maximalIdeal R, f a = b := by
    intro b hb
    have hb' : b ∈ maximalIdeal (R ⧸ Ideal.span {x}) := hspan ▸ Submodule.subset_span hb
    rw [← hmap] at hb'
    exact (Ideal.mem_map_iff_of_surjective f hfs).mp hb'
  choose! g hg using hlift
  have hgs : f '' (g '' (s : Set (R ⧸ Ideal.span {x}))) = (s : Set (R ⧸ Ideal.span {x})) := by
    ext b
    constructor
    · rintro ⟨a, ⟨b', hb', rfl⟩, rfl⟩
      rw [(hg b' hb').2]
      exact hb'
    · intro hb
      exact ⟨g b, ⟨b, hb, rfl⟩, (hg b hb).2⟩
  have hJ : (Ideal.span (g '' (s : Set (R ⧸ Ideal.span {x})))).map f = (maximalIdeal R).map f := by
    rw [Ideal.map_span, hgs, hmap]
    exact hspan
  have hle : Ideal.span {x} ≤ maximalIdeal R := (Ideal.span_singleton_le_iff_mem _).mpr hx
  have hgen : maximalIdeal R = Ideal.span (insert x (g '' (s : Set (R ⧸ Ideal.span {x})))) := by
    have := congrArg (Ideal.comap f) hJ
    rw [Ideal.comap_map_of_surjective f hfs, Ideal.comap_map_of_surjective f hfs,
      ← RingHom.ker_eq_comap_bot, hker, sup_eq_left.mpr hle] at this
    rw [← this, Ideal.span_insert, sup_comm]
  have hfin : (g '' (s : Set (R ⧸ Ideal.span {x}))).Finite := s.finite_toSet.image g
  calc (maximalIdeal R).spanFinrank
      = (Ideal.span (insert x (g '' (s : Set (R ⧸ Ideal.span {x}))))).spanFinrank := by rw [hgen]
    _ ≤ (insert x (g '' (s : Set (R ⧸ Ideal.span {x})))).ncard :=
        Submodule.spanFinrank_span_le_ncard_of_finite (hfin.insert x)
    _ ≤ (g '' (s : Set (R ⧸ Ideal.span {x}))).ncard + 1 := Set.ncard_insert_le _ _
    _ ≤ s.card + 1 := by
        have := Set.ncard_image_le (f := g) s.finite_toSet
        rw [Set.ncard_coe_finset] at this
        omega
    _ = (maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank + 1 := by rw [hcard]

/-- **Stacks 00NU** (Lemma 10.106.7): `(R, 𝔪)` a Noetherian local ring, `x ∈ 𝔪` a nonzerodivisor, `R/xR` regular
⇒ `R` regular.

Proof: `dim R = dim(R/xR) + 1` (Stacks 00KW, `x` a nonzerodivisor: Mathlib
`ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors`); the number of generators of
`𝔪` is `≤` the number of generators of `𝔪/xR` `+ 1`
(`spanFinrank_maximalIdeal_le_spanFinrank_quotient_span_singleton_add_one`) `= dim(R/xR) + 1` (`R/xR` regular)
`= dim R`; and always `dim R ≤` number of generators (Krull's height theorem), so equality holds and `R` is regular
(Mathlib `IsRegularLocalRing.of_spanFinrank_maximalIdeal_le`). -/
theorem IsRegularLocalRing.of_quotient_span_singleton_of_mem_nonZeroDivisors
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] {x : R}
    (hx : x ∈ maximalIdeal R) (hreg : x ∈ nonZeroDivisors R)
    [IsRegularLocalRing (R ⧸ Ideal.span {x})] : IsRegularLocalRing R := by
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  have h1 := IsLocalRing.spanFinrank_maximalIdeal_le_spanFinrank_quotient_span_singleton_add_one hx
  have h2 : ((maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank : WithBot ℕ∞) =
      ringKrullDim (R ⧸ Ideal.span {x}) := (isRegularLocalRing_iff _).mp inferInstance
  have h3 := ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim_of_mem_nonZeroDivisors hreg hx
  calc ((maximalIdeal R).spanFinrank : WithBot ℕ∞)
      ≤ (((maximalIdeal (R ⧸ Ideal.span {x})).spanFinrank + 1 : ℕ) : WithBot ℕ∞) := by
        exact_mod_cast h1
    _ = ringKrullDim (R ⧸ Ideal.span {x}) + 1 := by push_cast; rw [h2]
    _ = ringKrullDim R := h3

end
