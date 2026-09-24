import MiyaokaMori.Prelude
import MiyaokaMori.RingTheory.VeroneseAwayIso
import MiyaokaMori.RingTheory.GradedRing.VeroneseGradedRing
import MiyaokaMori.RingTheory.GradedRing.VeroneseAwayCompat

/-! # The Veronese morphism on points: the chart description

The chart version of step 1 of Stacks 0B5J, "`veroneseHom` acts on points as the contraction
`𝔭 ↦ 𝔭 ∩ S^{(d)}`". On the chart `D_+(h)`, `veroneseHom` is `Spec.map (veroneseAwayEquiv) ≫ awayι S^{(d)} ⟨h^d⟩`
(`awayι_comp_veroneseHom` + `veroneseChart_eq` in `Stacks0b5j.lean`), so it suffices to compare the point maps
of the two `awayι`. Mathlib has no explicit description of the point map of `awayι`, but it has
`Proj.awayι_preimage_basicOpen`: `awayι 𝒜 f ⁻¹ᵁ D_+(g) = D(g^{deg f}/f^{deg g})` (`g` homogeneous of positive
degree), which is exactly "a homogeneous `g` of positive degree lies in `awayι(q)` iff `g^{deg f}/f^{deg g} ∈ q`"
(`mem_awayι_base_iff`).

Source: the first paragraph of the proof of Stacks 0B5J (`constructions.tex`, lemma-d-uple).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The pointwise form of Mathlib's `Proj.awayι_preimage_basicOpen`: for `g ∈ 𝒜 m'` with `m' > 0`,
`g ∈ awayι(q) ↔ g^{m}/f^{m'} ∈ q` (`Away.isLocalizationElem f_deg g_deg = mk (g^m / f^{m'})`). -/
theorem AlgebraicGeometry.Proj.mem_awayι_base_iff {A σ : Type*} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] {f : A} {m : ℕ} (f_deg : f ∈ 𝒜 m)
    (hm : 0 < m) {g : A} {m' : ℕ} (g_deg : g ∈ 𝒜 m') (hm' : 0 < m')
    (q : AlgebraicGeometry.Spec (CommRingCat.of (HomogeneousLocalization.Away 𝒜 f))) :
    g ∈ ((AlgebraicGeometry.Proj.awayι 𝒜 f f_deg hm).base q).asHomogeneousIdeal ↔
      HomogeneousLocalization.Away.isLocalizationElem f_deg g_deg ∈ q.asIdeal := by
  have h := AlgebraicGeometry.Proj.awayι_preimage_basicOpen 𝒜 f_deg hm g_deg hm'
  have h1 : g ∉ ((AlgebraicGeometry.Proj.awayι 𝒜 f f_deg hm).base q).asHomogeneousIdeal ↔
      HomogeneousLocalization.Away.isLocalizationElem f_deg g_deg ∉ q.asIdeal :=
    Iff.of_eq (congrArg (fun U : (AlgebraicGeometry.Spec
      (CommRingCat.of (HomogeneousLocalization.Away 𝒜 f))).Opens => q ∈ U) h)
  exact not_iff_not.mp h1

/-- `awayι(q)` does not contain `f`. -/
theorem AlgebraicGeometry.Proj.notMem_awayι_base {A σ : Type*} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] {f : A} {m : ℕ} (f_deg : f ∈ 𝒜 m)
    (hm : 0 < m) (q : AlgebraicGeometry.Spec (CommRingCat.of (HomogeneousLocalization.Away 𝒜 f))) :
    f ∉ ((AlgebraicGeometry.Proj.awayι 𝒜 f f_deg hm).base q).asHomogeneousIdeal := by
  have h : (AlgebraicGeometry.Proj.awayι 𝒜 f f_deg hm).base q ∈
      (AlgebraicGeometry.Proj.awayι 𝒜 f f_deg hm).opensRange :=
    AlgebraicGeometry.Scheme.Hom.mem_opensRange.mpr ⟨q, rfl⟩
  rw [AlgebraicGeometry.Proj.opensRange_awayι, AlgebraicGeometry.Proj.mem_basicOpen] at h
  exact h

/-- `veroneseAwayEquiv` sends the `isLocalizationElem` on the `S^{(d)}` side (`c^m / (h^d)^{n}`) to the
`isLocalizationElem` on the `S` side (`c^m / h^{nd}`): the same fraction. -/
theorem veroneseAwayEquiv_isLocalizationElem {A σ : Type*} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℕ) (hd : 0 < d) {h : A} {m : ℕ}
    (hh : h ∈ 𝒜 m) {c : veroneseSubring 𝒜 d} {n : ℕ} (hc : c ∈ veroneseGrading 𝒜 d n) :
    (veroneseAwayEquiv 𝒜 d hd hh).toRingHom
        (HomogeneousLocalization.Away.isLocalizationElem (veronese_pow_mem_grading 𝒜 d hd hh) hc) =
      HomogeneousLocalization.Away.isLocalizationElem hh (hc.1 : (c : A) ∈ 𝒜 (n * d)) := by
  unfold HomogeneousLocalization.Away.isLocalizationElem HomogeneousLocalization.Away.mk
  rw [veroneseAwayEquiv_toRingHom_mk']
  refine congrArg HomogeneousLocalization.mk (HomogeneousLocalization.NumDenSameDeg.ext _ ?_ ?_ ?_)
  · show n • m * d = (n * d) • m
    simp only [smul_eq_mul]; ring
  · show ((c ^ m : veroneseSubring 𝒜 d) : A) = (c : A) ^ m
    exact SubmonoidClass.coe_pow c m
  · show (((⟨h ^ d, (veronese_pow_mem 𝒜 d hd hh).1⟩ : veroneseSubring 𝒜 d) ^ n :
      veroneseSubring 𝒜 d) : A) = h ^ (n * d)
    rw [SubmonoidClass.coe_pow]
    show (h ^ d) ^ n = h ^ (n * d)
    rw [← pow_mul, Nat.mul_comm]

/-- **The contraction formula on a chart (homogeneous elements)**: let `h ∈ 𝒜 m` with `m > 0`, `q ∈ Spec S_(h)`,
and `b ∈ S^{(d)}` an `S^{(d)}`-homogeneous element (of any degree `n`, including `n = 0`). Then
`b ∈ awayι S^{(d)} ⟨h^d⟩ (comap (veroneseAwayEquiv) q) ↔ (b : A) ∈ awayι 𝒜 h q`.

Proof: both points are prime ideals not containing `⟨h^d⟩` (`notMem_awayι_base`, and `h ∉ awayι(q)` implies
`h^d ∉`), so `b ∈ · ↔ b·⟨h^d⟩ ∈ ·`; `c := b·⟨h^d⟩` is homogeneous of positive degree `n+m`, and
`mem_awayι_base_iff` reduces both sides to the fractions `c^m/(h^d)^{n+m}` and `c^m/h^{(n+m)d}` over `q`, which
correspond under `veroneseAwayEquiv` (`veroneseAwayEquiv_isLocalizationElem`), the point map of `Spec.map`
being `PrimeSpectrum.comap`. -/
theorem AlgebraicGeometry.Proj.mem_veroneseChart_base_iff {A σ : Type*} [CommRing A]
    [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℕ) (hd : 0 < d)
    {h : A} {m : ℕ} (hh : h ∈ 𝒜 m) (hm : 0 < m)
    (q : AlgebraicGeometry.Spec (CommRingCat.of (HomogeneousLocalization.Away 𝒜 h)))
    (b : veroneseSubring 𝒜 d) {n : ℕ} (hb : b ∈ veroneseGrading 𝒜 d n) :
    b ∈ ((AlgebraicGeometry.Proj.awayι (veroneseGrading 𝒜 d)
          (⟨h ^ d, (veronese_pow_mem 𝒜 d hd hh).1⟩ : veroneseSubring 𝒜 d)
          (veronese_pow_mem_grading 𝒜 d hd hh) hm).base
        (PrimeSpectrum.comap (veroneseAwayEquiv 𝒜 d hd hh).toRingHom q)).asHomogeneousIdeal ↔
      (b : A) ∈ ((AlgebraicGeometry.Proj.awayι 𝒜 h hh hm).base q).asHomogeneousIdeal := by
  set hpow : veroneseSubring 𝒜 d := ⟨h ^ d, (veronese_pow_mem 𝒜 d hd hh).1⟩ with hpow_def
  set P := (AlgebraicGeometry.Proj.awayι (veroneseGrading 𝒜 d) hpow
      (veronese_pow_mem_grading 𝒜 d hd hh) hm).base
        (PrimeSpectrum.comap (veroneseAwayEquiv 𝒜 d hd hh).toRingHom q) with hP
  set Q := (AlgebraicGeometry.Proj.awayι 𝒜 h hh hm).base q with hQ
  -- neither point contains h^d
  have hP' : hpow ∉ P.asHomogeneousIdeal :=
    AlgebraicGeometry.Proj.notMem_awayι_base (veroneseGrading 𝒜 d) _ hm _
  have hQ' : h ^ d ∉ Q.asHomogeneousIdeal := fun hmem =>
    AlgebraicGeometry.Proj.notMem_awayι_base 𝒜 hh hm q
      ((Q.isPrime.pow_mem_iff_mem d hd).mp hmem)
  -- c := b * h^d
  have hc : b * hpow ∈ veroneseGrading 𝒜 d (n + m) :=
    SetLike.mul_mem_graded hb (veronese_pow_mem_grading 𝒜 d hd hh)
  have step1 : b ∈ P.asHomogeneousIdeal ↔ b * hpow ∈ P.asHomogeneousIdeal := by
    constructor
    · intro hb'; exact Ideal.mul_mem_right _ _ hb'
    · intro hb'
      rcases P.isPrime.mem_or_mem hb' with h1 | h1
      · exact h1
      · exact absurd h1 hP'
  have step5 : (b : A) ∈ Q.asHomogeneousIdeal ↔ (b : A) * h ^ d ∈ Q.asHomogeneousIdeal := by
    constructor
    · intro hb'; exact Ideal.mul_mem_right _ _ hb'
    · intro hb'
      rcases Q.isPrime.mem_or_mem hb' with h1 | h1
      · exact h1
      · exact absurd h1 hQ'
  have step2 : b * hpow ∈ P.asHomogeneousIdeal ↔
      HomogeneousLocalization.Away.isLocalizationElem (veronese_pow_mem_grading 𝒜 d hd hh) hc ∈
        (PrimeSpectrum.comap (veroneseAwayEquiv 𝒜 d hd hh).toRingHom q).asIdeal :=
    AlgebraicGeometry.Proj.mem_awayι_base_iff (veroneseGrading 𝒜 d)
      (veronese_pow_mem_grading 𝒜 d hd hh) hm hc (Nat.add_pos_right n hm) _
  have step4 : ((b * hpow : veroneseSubring 𝒜 d) : A) ∈ Q.asHomogeneousIdeal ↔
      HomogeneousLocalization.Away.isLocalizationElem hh
        (hc.1 : ((b * hpow : veroneseSubring 𝒜 d) : A) ∈ 𝒜 ((n + m) * d)) ∈ q.asIdeal :=
    AlgebraicGeometry.Proj.mem_awayι_base_iff 𝒜 hh hm hc.1
      (Nat.mul_pos (Nat.add_pos_right n hm) hd) q
  have step3 : HomogeneousLocalization.Away.isLocalizationElem
        (veronese_pow_mem_grading 𝒜 d hd hh) hc ∈
        (PrimeSpectrum.comap (veroneseAwayEquiv 𝒜 d hd hh).toRingHom q).asIdeal ↔
      HomogeneousLocalization.Away.isLocalizationElem hh
        (hc.1 : ((b * hpow : veroneseSubring 𝒜 d) : A) ∈ 𝒜 ((n + m) * d)) ∈ q.asIdeal := by
    rw [← veroneseAwayEquiv_isLocalizationElem]
    exact Iff.rfl
  have hcoe : ((b * hpow : veroneseSubring 𝒜 d) : A) = (b : A) * h ^ d := rfl
  rw [step1, step2, step3, ← step4, hcoe, ← step5]


/-- **Homogeneous elements decide everything**: let `I` be a homogeneous ideal of `S^{(d)}` and `J` a
homogeneous ideal of `S`. If `b ∈ I ↔ (b : A) ∈ J` for every `S^{(d)}`-homogeneous `b`, then the same holds
for all `a ∈ S^{(d)}`.

Proof: (→) `a = Σ_n a_n` (`DirectSum.sum_support_decompose`, the grading of `S^{(d)}`); `I` is homogeneous so
each `a_n ∈ I` (`Ideal.IsHomogeneous.mem_iff`), by hypothesis each `(a_n : A) ∈ J`; sum.
(←) In `A`, `a = Σ_i proj_i a`, and `a ∈ S^{(d)}` means the components with `d ∤ i` vanish, so
`a = Σ_{i, d ∣ i} ⟨proj_i a, _⟩` (`Subtype.ext` + termwise comparison); each `⟨proj_i a, _⟩` is
`S^{(d)}`-homogeneous of degree `i/d` (`veroneseGrading.proj_mem`), its image `proj_i a ∈ J` (`J` homogeneous),
so by hypothesis it lies in `I`; sum. -/
theorem veroneseSubring.mem_iff_of_homogeneous {A σ : Type*} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℕ)
    (I : HomogeneousIdeal (veroneseGrading 𝒜 d)) (J : HomogeneousIdeal 𝒜)
    (hom : ∀ (b : veroneseSubring 𝒜 d) (n : ℕ), b ∈ veroneseGrading 𝒜 d n → (b ∈ I ↔ (b : A) ∈ J))
    (a : veroneseSubring 𝒜 d) : a ∈ I ↔ (a : A) ∈ J := by
  classical
  constructor
  · intro ha
    have hI : ∀ n, (DirectSum.decompose (veroneseGrading 𝒜 d) a n : veroneseSubring 𝒜 d) ∈ I :=
      I.2.mem_iff.mp ha
    rw [← DirectSum.sum_support_decompose (veroneseGrading 𝒜 d) a, AddSubmonoidClass.coe_finsetSum]
    exact Ideal.sum_mem J.toIdeal fun n _ => (hom _ n (SetLike.coe_mem _)).mp (hI n)
  · intro ha
    have hJ : ∀ i, (DirectSum.decompose 𝒜 (a : A) i : A) ∈ J := J.2.mem_iff.mp ha
    have key : a = ∑ i ∈ (DirectSum.decompose 𝒜 (a : A)).support,
        if h : d ∣ i then
          (⟨GradedRing.proj 𝒜 i (a : A), veroneseSubring.proj_mem 𝒜 d (a : A) h⟩ :
            veroneseSubring 𝒜 d)
        else 0 := by
      apply Subtype.ext
      rw [AddSubmonoidClass.coe_finsetSum]
      conv_lhs => rw [← DirectSum.sum_support_decompose 𝒜 (a : A)]
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs with h
      · exact (GradedRing.proj_apply 𝒜 i (a : A)).symm
      · rw [Subring.coe_zero, ← GradedRing.proj_apply]
        exact a.2 i h
    rw [key]
    refine Ideal.sum_mem I.toIdeal fun i _ => ?_
    split_ifs with h
    · refine (hom _ (i / d) (veroneseGrading.proj_mem 𝒜 d (a : A) h)).mpr ?_
      show GradedRing.proj 𝒜 i (a : A) ∈ J
      rw [GradedRing.proj_apply]
      exact hJ i
    · exact zero_mem _

end
