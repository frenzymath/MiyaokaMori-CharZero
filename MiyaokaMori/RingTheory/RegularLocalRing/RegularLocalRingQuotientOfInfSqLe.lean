import MiyaokaMori.Prelude
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.Algebra.Module.SpanRankOperations

/-! # Quotients of a regular local ring by an ideal with `I ∩ 𝔪² ⊆ 𝔪I` are regular

**Quotient of a regular local ring by an ideal transverse to `m²` is regular.**

Let `(B, m)` be a regular local ring and `K ⊆ B` an ideal with `K ∩ m² = m·K`
(equivalently: `K/mK → m/m²` is injective, i.e. a minimal generating set of `K` stays
linearly independent in `m/m²`).  Then `B/K` is again a regular local ring.

This is the commutative-algebra core of Stacks 00TT (smooth over a field ⇒ regular),
in the form used by `MiyaokaMori.Stacks.Algebra.Stacks00tt`: there `B` is a localization of a
polynomial ring over the field and `K` the kernel of the presentation of `S_q`; the hypothesis
`K ∩ m² = mK` comes from the Jacobian criterion (Mathlib
`Algebra.FormallySmooth.iff_injective_cotangentComplexBaseChange`).

Source: Stacks 00NU (`algebra-lemma-regular-quotient`, "if `x₁,…,x_c ∈ m` map to linearly
independent elements of `m/m²` then `R/(x₁,…,x_c)` is regular"), stated here without choosing
generators.

Natural-language proof (self-contained; only Mathlib input is Krull's height theorem in the
form `dim B ≤ dim (B/K) + spanFinrank K`, `ringKrullDim_le_ringKrullDim_quotient_add_spanFinrank`):
write `κ = B/m`, `V = m/m²`, `W ⊆ V` the image of `K`, `c' = spanFinrank K`, `d = dim B`.
1. `c' ≤ dim_κ W`: pick a `κ`-basis of `W` consisting of images of elements `g₁,…,g_r ∈ K`
   (`exists_linearIndependent`). For `x ∈ K`, `[x] ∈ W` gives `x − Σ bᵢ gᵢ ∈ K ∩ m² = mK`, so
   `K = (g₁,…,g_r) + mK` and by Nakayama `K = (g₁,…,g_r)`; hence `c' ≤ r = dim_κ W`.
2. `spanFinrank m_{B/K} ≤ dim_κ (V/W)`: pick a basis of `V/W`, lift it to `u₁,…,u_{r'} ∈ m`.
   For `x ∈ m`, `[x] ≡ Σ λᵢ [uᵢ] mod W`, so `x − Σ bᵢ uᵢ − w ∈ m²` for some `w ∈ K`; thus
   `m = (u₁,…,u_{r'}) + K + m²`, i.e. in `B/K` the maximal ideal `m'` satisfies
   `m' = (ū₁,…,ū_{r'}) + m'²`, and Nakayama gives `m' = (ū₁,…,ū_{r'})`.
3. `d = spanFinrank m = dim_κ V = dim_κ (V/W) + dim_κ W ≥ spanFinrank m_{B/K} + c'`
   (regularity of `B` for the first equality), while Krull's height theorem gives
   `d ≤ dim (B/K) + c'`. Cancelling the finite `c'` yields `spanFinrank m_{B/K} ≤ dim (B/K)`,
   which is regularity of `B/K` (`IsRegularLocalRing.of_spanFinrank_maximalIdeal_le`).

Edge cases: `K = ⊤` is excluded by hypothesis (`B/K = 0` is not local). `K = ⊥` is fine
(`W = 0`). `B` a field: `m = 0`, `K = 0`, `B/K = B` regular.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open IsLocalRing Submodule

noncomputable section

namespace IsRegularLocalRing

variable {B : Type u} [CommRing B] [IsLocalRing B] [IsNoetherianRing B]

/-- The image of the ideal `K` in the cotangent space `m/m²`, as a `κ = B/m`-subspace. -/
def cotangentImage (K : Ideal B) : Submodule (ResidueField B) (CotangentSpace B) :=
  span (ResidueField B)
    ((maximalIdeal B).toCotangent '' ((comap (maximalIdeal B).subtype K : Submodule B _) : Set _))

omit [IsNoetherianRing B] in
private lemma residue_surj : Function.Surjective (algebraMap B (ResidueField B)) :=
  Ideal.Quotient.mk_surjective

omit [IsNoetherianRing B] in
lemma restrictScalars_cotangentImage (K : Ideal B) :
    (cotangentImage K).restrictScalars B =
      (comap (maximalIdeal B).subtype K).map (maximalIdeal B).toCotangent := by
  rw [cotangentImage, restrictScalars_span B (ResidueField B) residue_surj, span_image, span_eq]

omit [IsNoetherianRing B] in
lemma mem_cotangentImage_iff (K : Ideal B) {v : CotangentSpace B} :
    v ∈ cotangentImage K ↔
      ∃ x : maximalIdeal B, (x : B) ∈ K ∧ (maximalIdeal B).toCotangent x = v := by
  rw [← restrictScalars_mem B, restrictScalars_cotangentImage, mem_map]
  simp only [mem_comap, coe_subtype]

/-- Step 1 of the proof: `spanFinrank K ≤ dim_κ (image of K in m/m²)` when `K ∩ m² ≤ mK`. -/
theorem spanFinrank_le_finrank_cotangentImage (K : Ideal B) (hK : K ≠ ⊤)
    (h : K ⊓ maximalIdeal B ^ 2 ≤ maximalIdeal B * K) :
    K.spanFinrank ≤ Module.finrank (ResidueField B) (cotangentImage K) := by
  classical
  set κ := ResidueField B
  set m := maximalIdeal B
  set T : Set (CotangentSpace B) :=
    m.toCotangent '' ((comap m.subtype K : Submodule B m) : Set m) with hT
  obtain ⟨b, hbT, hbspan, hbind⟩ := exists_linearIndependent κ T
  have hbfin : b.Finite := hbind.set_finite_of_isNoetherian
  let _ := hbfin.fintype
  have hcard : Module.finrank κ (cotangentImage K) = b.toFinset.card := by
    rw [cotangentImage, ← hT, ← hbspan]
    exact finrank_span_set_eq_card hbind
  -- lift the basis vectors to elements of `K`
  have hlift : ∀ v ∈ b, ∃ x : m, (x : B) ∈ K ∧ m.toCotangent x = v := fun v hv => by
    obtain ⟨x, hx, rfl⟩ := hbT hv
    exact ⟨x, hx, rfl⟩
  choose! g hg using hlift
  set u : Set B := (fun v => ((g v : m) : B)) '' b with hu
  have hufin : u.Finite := hbfin.image _
  have huK : u ⊆ K := by
    rintro _ ⟨v, hv, rfl⟩
    exact (hg v hv).1
  have hb_eq : b = m.toCotangent '' (g '' b) := by
    ext v
    constructor
    · intro hv
      exact ⟨g v, ⟨v, hv, rfl⟩, (hg v hv).2⟩
    · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
      rw [(hg w hw).2]
      exact hw
  have hKspan : K = Ideal.span u := by
    apply le_antisymm
    · refine le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian K)
        (maximalIdeal_le_jacobson ⊥) ?_
      intro x hx
      have hxm : x ∈ m := le_maximalIdeal hK hx
      have hv : m.toCotangent ⟨x, hxm⟩ ∈ span B b := by
        have h0 : m.toCotangent ⟨x, hxm⟩ ∈ cotangentImage K :=
          subset_span (Set.mem_image_of_mem m.toCotangent
            (show (⟨x, hxm⟩ : m) ∈ ((comap m.subtype K : Submodule B m) : Set m) by
              simpa [mem_comap] using hx))
        rwa [cotangentImage, ← hT, ← hbspan, ← restrictScalars_mem B,
          restrictScalars_span B κ residue_surj] at h0
      rw [hb_eq, span_image, mem_map] at hv
      obtain ⟨z, hz, hzx⟩ := hv
      have hzK : (z : B) ∈ K := by
        have : span B (g '' b) ≤ comap m.subtype K := by
          rw [span_le]
          rintro _ ⟨w, hw, rfl⟩
          simpa [mem_comap] using (hg w hw).1
        simpa [mem_comap] using this hz
      have hzu : (z : B) ∈ Ideal.span u := by
        have := apply_mem_span_image_of_mem_span m.subtype hz
        rw [hu]
        simpa [Set.image_image] using this
      have hxz : x - z ∈ m ^ 2 := by
        simpa [neg_sub] using neg_mem ((m.toCotangent_eq).mp hzx)
      have hmk : x - z ∈ m • K := by
        rw [Ideal.smul_eq_mul]
        exact h ⟨sub_mem hx hzK, hxz⟩
      exact mem_sup.mpr ⟨z, hzu, x - z, hmk, by ring⟩
    · exact Ideal.span_le.mpr huK
  have hKs : K.spanFinrank = (Ideal.span u).spanFinrank := congrArg Submodule.spanFinrank hKspan
  rw [hKs, hcard]
  calc (Ideal.span u).spanFinrank ≤ u.ncard := spanFinrank_span_le_ncard_of_finite hufin
    _ ≤ b.ncard := Set.ncard_image_le hbfin
    _ = b.toFinset.card := Set.ncard_eq_toFinset_card' b

variable (K : Ideal B) [IsLocalRing (B ⧸ K)]

omit [IsNoetherianRing B] in
/-- The maximal ideal of `B` maps into the maximal ideal of `B/K` (the quotient map of a local
ring is a local homomorphism). -/
lemma map_maximalIdeal_le_maximalIdeal_quotient :
    (maximalIdeal B).map (Ideal.Quotient.mk K) ≤ maximalIdeal (B ⧸ K) := by
  have := IsLocalHom.of_surjective (Ideal.Quotient.mk K) Ideal.Quotient.mk_surjective
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  rw [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
  intro hunit
  exact (mem_maximalIdeal a).mp ha (this.map_nonunit a hunit)

/-- Step 2 of the proof: `spanFinrank m_{B/K} ≤ dim_κ ((m/m²) / image of K)`. -/
theorem spanFinrank_maximalIdeal_quotient_le :
    (maximalIdeal (B ⧸ K)).spanFinrank ≤
      Module.finrank (ResidueField B) (CotangentSpace B ⧸ cotangentImage K) := by
  classical
  set κ := ResidueField B
  set m := maximalIdeal B
  set W := cotangentImage K with hWdef
  set r := Module.finrank κ (CotangentSpace B ⧸ W)
  let bs := Module.finBasis κ (CotangentSpace B ⧸ W)
  have hlift : ∀ i : Fin r, ∃ x : m, W.mkQ (m.toCotangent x) = bs i := fun i => by
    obtain ⟨v, hv⟩ := W.mkQ_surjective (bs i)
    obtain ⟨x, hx⟩ := m.toCotangent_surjective v
    exact ⟨x, by rw [hx, hv]⟩
  choose u hu using hlift
  set U : Finset (B ⧸ K) := Finset.univ.image fun i => Ideal.Quotient.mk K (u i : B) with hUdef
  have hmap := map_maximalIdeal_le_maximalIdeal_quotient K
  have hU : maximalIdeal (B ⧸ K) = Ideal.span (U : Set (B ⧸ K)) := by
    apply le_antisymm
    · refine le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian _)
        (maximalIdeal_le_jacobson ⊥) ?_
      intro y hy
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
      have hxm : x ∈ m := by
        rw [mem_maximalIdeal, mem_nonunits_iff] at hy ⊢
        exact fun hx => hy (hx.map (Ideal.Quotient.mk K))
      have h1 : W.mkQ (m.toCotangent ⟨x, hxm⟩) ∈ span B (Set.range bs) := by
        have h0 : W.mkQ (m.toCotangent ⟨x, hxm⟩) ∈ (⊤ : Submodule κ (CotangentSpace B ⧸ W)) :=
          trivial
        rwa [← bs.span_eq, ← restrictScalars_mem B, restrictScalars_span B κ residue_surj] at h0
      have hrange : Set.range bs = (W.mkQ.restrictScalars B ∘ₗ m.toCotangent) '' Set.range u := by
        ext v
        constructor
        · rintro ⟨i, rfl⟩
          exact ⟨u i, ⟨i, rfl⟩, hu i⟩
        · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
          exact ⟨i, (hu i).symm⟩
      rw [hrange, span_image, mem_map] at h1
      obtain ⟨z, hz, hzx⟩ := h1
      have hW : m.toCotangent (⟨x, hxm⟩ - z) ∈ W := by
        rw [map_sub]
        have := (Submodule.Quotient.eq W).mp hzx
        simpa using neg_mem this
      obtain ⟨w, hwK, hw⟩ := (mem_cotangentImage_iff K).mp hW
      have hsq : ((⟨x, hxm⟩ - z - w : m) : B) ∈ m ^ 2 := by
        have := (m.toCotangent_eq).mp hw.symm
        simpa using this
      have hz' : (z : B) ∈ Ideal.span (Set.range fun i => (u i : B)) := by
        have := apply_mem_span_image_of_mem_span m.subtype hz
        rwa [← Set.range_comp] at this
      have e : Ideal.Quotient.mk K x =
          Ideal.Quotient.mk K z + Ideal.Quotient.mk K ((⟨x, hxm⟩ - z - w : m) : B) := by
        have hx' : x = (z : B) + (((⟨x, hxm⟩ - z - w : m) : B) + (w : B)) := by
          simp only [AddSubgroupClass.coe_sub]
          ring
        conv_lhs => rw [hx']
        rw [map_add, map_add, Ideal.Quotient.eq_zero_iff_mem.mpr hwK, add_zero]
      rw [e]
      refine add_mem_sup ?_ ?_
      · have : Ideal.span (U : Set (B ⧸ K)) =
            (Ideal.span (Set.range fun i => (u i : B))).map (Ideal.Quotient.mk K) := by
          rw [Ideal.map_span]
          congr 1
          ext y
          simp [hUdef]
        rw [this]
        exact Ideal.mem_map_of_mem _ hz'
      · rw [Ideal.smul_eq_mul, ← pow_two]
        have := Ideal.mem_map_of_mem (Ideal.Quotient.mk K) hsq
        rw [Ideal.map_pow] at this
        exact pow_le_pow_left' hmap 2 this
    · rw [Ideal.span_le]
      intro y hy
      simp only [hUdef, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hy
      obtain ⟨i, rfl⟩ := hy
      exact hmap (Ideal.mem_map_of_mem _ (u i).2)
  rw [hU]
  calc (Ideal.span (U : Set (B ⧸ K))).spanFinrank ≤ (U : Set (B ⧸ K)).ncard :=
        spanFinrank_span_le_ncard_of_finite U.finite_toSet
    _ = U.card := Set.ncard_coe_finset U
    _ ≤ (Finset.univ : Finset (Fin r)).card := Finset.card_image_le
    _ = r := by simp

end IsRegularLocalRing

/-- **Quotient of a regular local ring by an ideal transverse to `m²`.**
`B` regular local, `K ≠ ⊤` an ideal with `K ∩ m² ≤ m·K`; then `B/K` is a regular local ring.
Source: Stacks 00NU, generator-free form; proof in the module docstring. -/
theorem IsRegularLocalRing.quotient_of_inf_sq_le {B : Type u} [CommRing B] [IsRegularLocalRing B]
    (K : Ideal B) (hK : K ≠ ⊤)
    (h : K ⊓ maximalIdeal B ^ 2 ≤ maximalIdeal B * K) : IsRegularLocalRing (B ⧸ K) := by
  have : Nontrivial (B ⧸ K) := Ideal.Quotient.nontrivial_iff.mpr hK
  have : IsLocalRing (B ⧸ K) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk K) Ideal.Quotient.mk_surjective
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  have h1 := ringKrullDim_le_ringKrullDim_quotient_add_spanFinrank K
    (by rw [IsLocalRing.ringJacobson_eq_maximalIdeal]; exact IsLocalRing.le_maximalIdeal hK)
  have h2 : ((maximalIdeal B).spanFinrank : WithBot ℕ∞) = ringKrullDim B :=
    IsRegularLocalRing.spanFinrank_maximalIdeal
  have h3 : (maximalIdeal B).spanFinrank =
      Module.finrank (ResidueField B) (CotangentSpace B ⧸ IsRegularLocalRing.cotangentImage K) +
        Module.finrank (ResidueField B) (IsRegularLocalRing.cotangentImage K) := by
    rw [IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace,
      finrank_quotient_add_finrank]
  have ha := IsRegularLocalRing.spanFinrank_le_finrank_cotangentImage K hK h
  have hb := IsRegularLocalRing.spanFinrank_maximalIdeal_quotient_le K
  have h4 : (maximalIdeal (B ⧸ K)).spanFinrank + K.spanFinrank ≤ (maximalIdeal B).spanFinrank := by
    omega
  have h5 : (((maximalIdeal (B ⧸ K)).spanFinrank + K.spanFinrank : ℕ) : WithBot ℕ∞) ≤
      ringKrullDim (B ⧸ K) + (K.spanFinrank : WithBot ℕ∞) := by
    calc (((maximalIdeal (B ⧸ K)).spanFinrank + K.spanFinrank : ℕ) : WithBot ℕ∞)
        ≤ ((maximalIdeal B).spanFinrank : WithBot ℕ∞) := by exact_mod_cast h4
      _ = ringKrullDim B := h2
      _ ≤ _ := h1
  obtain ⟨a, ha', -⟩ := WithBot.coe_le_iff.mp
    (ringKrullDim_nonneg_of_nontrivial (R := B ⧸ K))
  rw [ha'] at h5 ⊢
  have h6 : (((maximalIdeal (B ⧸ K)).spanFinrank + K.spanFinrank : ℕ) : ℕ∞) ≤
      a + (K.spanFinrank : ℕ∞) := by exact_mod_cast h5
  rw [Nat.cast_add] at h6
  have h7 := (ENat.add_le_add_iff_right (by simp)).mp h6
  exact_mod_cast h7

end
