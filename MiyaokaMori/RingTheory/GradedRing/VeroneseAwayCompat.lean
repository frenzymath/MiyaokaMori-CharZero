import MiyaokaMori.Prelude
import MiyaokaMori.RingTheory.VeroneseAwayIso
import MiyaokaMori.RingTheory.GradedRing.VeroneseGradedRing

/-! # Compatibility of the Veronese isomorphism with the restriction maps

The compatibility in step 3 of Stacks 0B5J (pure commutative algebra): the degree-zero localization
isomorphism `veroneseAwayEquiv` of the Veronese subring commutes with
`HomogeneousLocalization.awayMap` (the restriction map for `D_+(fg) ⊆ D_+(f)`).

Route:
1. `veroneseAwayEquiv_val`: at the level of `val`, `veroneseAwayEquiv` is the `IsLocalization.map`
   between ordinary localizations induced by the subring inclusion `S^{(d)} ↪ S` (literally the same
   on `mk`).
2. `HomogeneousLocalization.val_awayMap` writes `awayMap` at the level of `val` as
   `Localization.awayLift`.
3. Hence both paths are, at the level of `val`, ring homomorphisms
   `Localization.Away (f^d) → Localization.Away (fg)` that agree on `algebraMap` (`a ↦ a/1`), so they
   are equal by `IsLocalization.ringHom_ext`; conclude with `HomogeneousLocalization.val_injective`.

Reference: Stacks 0B5J (`constructions.tex`, lemma-d-uple), end of the first paragraph of the proof
("Since these isomorphisms are compatible with the restrictions mappings of Lemma standard-open").
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- `f^d` (with membership witness `(veronese_pow_mem …).1`) lies in `veroneseGrading 𝒜 d m`.
The witness in the `∃ h, …` of `veronese_pow_mem` is replaced by `.1`, so that the carrier and the
degree witness refer syntactically to the same term (otherwise the instance search of `Proj.awayι`
does not match). -/
theorem veronese_pow_mem_grading {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℕ) (hd : 0 < d) {f : A} {m : ℕ} (hf : f ∈ 𝒜 m) :
    (⟨f ^ d, (veronese_pow_mem 𝒜 d hd hf).1⟩ : veroneseSubring 𝒜 d) ∈ veroneseGrading 𝒜 d m :=
  (veronese_pow_mem 𝒜 d hd hf).2.choose_spec

/-- The value of `veroneseAwayEquiv` on `mk` (definitional equality; the same fact appears in
`ProjVeroneseIso`, which is downstream of this file, hence the restatement here). -/
theorem veroneseAwayEquiv_toRingHom_mk' {A σ : Type*} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℕ) (hd : 0 < d) {f : A} {i : ℕ}
    (hf : f ∈ 𝒜 i)
    (c : HomogeneousLocalization.NumDenSameDeg (veroneseGrading 𝒜 d)
      (Submonoid.powers (⟨f ^ d, (veronese_pow_mem 𝒜 d hd hf).1⟩ : veroneseSubring 𝒜 d))) :
    (veroneseAwayEquiv 𝒜 d hd hf).toRingHom (HomogeneousLocalization.mk c) =
      HomogeneousLocalization.mk (veroneseAwayEquiv.toNumDen 𝒜 d hd hf c) := rfl

/-- `powers ⟨f^d⟩ ⊆ S^{(d)}` lands in `powers f ⊆ S` along the inclusion map. -/
theorem veronese_powers_le_comap {A σ : Type*} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℕ) (hd : 0 < d) {f : A} {i : ℕ}
    (hf : f ∈ 𝒜 i) :
    Submonoid.powers (⟨f ^ d, (veronese_pow_mem 𝒜 d hd hf).1⟩ : veroneseSubring 𝒜 d) ≤
      (Submonoid.powers f).comap (Subring.subtype (veroneseSubring 𝒜 d)) := by
  rintro y ⟨k, rfl⟩
  refine ⟨d * k, ?_⟩
  simp [pow_mul]

/-- **`veroneseAwayEquiv` at the level of `val` is the `IsLocalization.map` of ordinary localizations**:
`(veroneseAwayEquiv z).val = map (S^{(d)} ↪ S) z.val`. -/
theorem veroneseAwayEquiv_val {A σ : Type*} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℕ) (hd : 0 < d) {f : A} {i : ℕ}
    (hf : f ∈ 𝒜 i)
    (z : HomogeneousLocalization.Away (veroneseGrading 𝒜 d)
      (⟨f ^ d, (veronese_pow_mem 𝒜 d hd hf).1⟩ : veroneseSubring 𝒜 d)) :
    ((veroneseAwayEquiv 𝒜 d hd hf).toRingHom z).val =
      IsLocalization.map (Localization.Away f) (Subring.subtype (veroneseSubring 𝒜 d))
        (veronese_powers_le_comap 𝒜 d hd hf) z.val := by
  obtain ⟨c, rfl⟩ := HomogeneousLocalization.mk_surjective z
  rw [veroneseAwayEquiv_toRingHom_mk', HomogeneousLocalization.val_mk,
    HomogeneousLocalization.val_mk, Localization.mk_eq_mk', Localization.mk_eq_mk',
    IsLocalization.map_mk']
  rfl

/-- `x = f g` ⟹ `⟨x^d⟩ = ⟨f^d⟩ * ⟨g^d⟩` in `S^{(d)}`. -/
theorem veronese_pow_mul_eq {A σ : Type*} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℕ) (hd : 0 < d) {f g x : A}
    {i j k : ℕ} (hf : f ∈ 𝒜 i) (hg : g ∈ 𝒜 j) (hx : x = f * g) (hxk : x ∈ 𝒜 k) :
    (⟨x ^ d, (veronese_pow_mem 𝒜 d hd hxk).1⟩ : veroneseSubring 𝒜 d) =
      ⟨f ^ d, (veronese_pow_mem 𝒜 d hd hf).1⟩ * ⟨g ^ d, (veronese_pow_mem 𝒜 d hd hg).1⟩ :=
  Subtype.ext (show x ^ d = f ^ d * g ^ d by rw [hx, mul_pow])

/-- **Compatibility in general form** (`x = f * g` with arbitrary factorization and arbitrary degree
witness for `x`): `awayMap 𝒜 ∘ veroneseAwayEquiv_f = veroneseAwayEquiv_x ∘ awayMap S^{(d)}`. -/
theorem veroneseAwayEquiv_awayMap_general {A σ : Type*} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℕ) (hd : 0 < d) {f g x : A}
    {i j k : ℕ} (hf : f ∈ 𝒜 i) (hg : g ∈ 𝒜 j) (hx : x = f * g) (hxk : x ∈ 𝒜 k) :
    ((HomogeneousLocalization.awayMap 𝒜 hg hx).comp
        (veroneseAwayEquiv 𝒜 d hd hf).toRingHom) =
      (veroneseAwayEquiv 𝒜 d hd hxk).toRingHom.comp
        (HomogeneousLocalization.awayMap (veroneseGrading 𝒜 d)
          (g := (⟨g ^ d, (veronese_pow_mem 𝒜 d hd hg).1⟩ : veroneseSubring 𝒜 d))
          (veronese_pow_mem_grading 𝒜 d hd hg)
          (x := (⟨x ^ d, (veronese_pow_mem 𝒜 d hd hxk).1⟩ : veroneseSubring 𝒜 d))
          (veronese_pow_mul_eq 𝒜 d hd hf hg hx hxk)) := by
  -- the two paths as ring homomorphisms at the level of `val`
  let R1 : Localization.Away f →+* Localization.Away x :=
    Localization.awayLift (algebraMap A (Localization.Away x)) f
      (isUnit_of_dvd_unit (map_dvd _ ⟨_, hx⟩) (IsLocalization.Away.algebraMap_isUnit x))
  let R2 : Localization.Away (⟨f ^ d, (veronese_pow_mem 𝒜 d hd hf).1⟩ : veroneseSubring 𝒜 d) →+*
      Localization.Away f :=
    IsLocalization.map (Localization.Away f) (Subring.subtype (veroneseSubring 𝒜 d))
      (veronese_powers_le_comap 𝒜 d hd hf)
  let R3 : Localization.Away (⟨x ^ d, (veronese_pow_mem 𝒜 d hd hxk).1⟩ : veroneseSubring 𝒜 d) →+*
      Localization.Away x :=
    IsLocalization.map (Localization.Away x) (Subring.subtype (veroneseSubring 𝒜 d))
      (veronese_powers_le_comap 𝒜 d hd hxk)
  let R4 : Localization.Away (⟨f ^ d, (veronese_pow_mem 𝒜 d hd hf).1⟩ : veroneseSubring 𝒜 d) →+*
      Localization.Away (⟨x ^ d, (veronese_pow_mem 𝒜 d hd hxk).1⟩ : veroneseSubring 𝒜 d) :=
    Localization.awayLift (algebraMap (veroneseSubring 𝒜 d) _) _
      (isUnit_of_dvd_unit (map_dvd _ ⟨_, veronese_pow_mul_eq 𝒜 d hd hf hg hx hxk⟩)
        (IsLocalization.Away.algebraMap_isUnit _))
  have key : R1.comp R2 = R3.comp R4 := by
    refine IsLocalization.ringHom_ext
      (Submonoid.powers (⟨f ^ d, (veronese_pow_mem 𝒜 d hd hf).1⟩ : veroneseSubring 𝒜 d)) ?_
    ext a
    simp only [RingHom.coe_comp, Function.comp_apply, R1, R2, R3, R4]
    rw [IsLocalization.map_eq, IsLocalization.Away.lift_eq, IsLocalization.Away.lift_eq,
      IsLocalization.map_eq]
  ext z
  simp only [RingHom.coe_comp, Function.comp_apply]
  rw [HomogeneousLocalization.val_awayMap, veroneseAwayEquiv_val, veroneseAwayEquiv_val,
    HomogeneousLocalization.val_awayMap]
  exact DFunLike.congr_fun key z.val

end
