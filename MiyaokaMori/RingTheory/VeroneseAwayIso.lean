import MiyaokaMori.Prelude
import MiyaokaMori.RingTheory.GradedRing.VeroneseGradedRing

/-! # Veronese subring and degree-zero homogeneous localization

For `f` homogeneous of positive degree and `d ≥ 1`, the inclusion `S^{(d)} ⊆ S` induces an isomorphism
`S^{(d)}_{(f^d)} ≅ S_{(f)}` (`a/f^{dk} ↦ a/f^{dk}`), compatible with the restriction maps on
`D_+(f) ∩ D_+(g)`. (Used for the Veronese polarization, §2 of the paper.)
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/- The two directions of `veroneseAwayEquiv` are given by explicit formulas on the triples
   (numerator, denominator, degree); the maps on triples are separate definitions and each
   proof obligation (membership of denominators, numerators and denominators landing in `S^{(d)}` and
   its graded pieces, compatibility of both directions with the equivalence relation on fractions,
   mutual inverses, preservation of `*` and `+`) is a separate named theorem. -/

/-- `(f^d)^j`, as an element of `A`, is a power of `f`. Route: `den ∈ powers (f^d)` gives `j` with
`den = (f^d)^j`; its value in `A` is `f^{dj}`. -/
theorem veroneseAwayEquiv.den_mem_powers {σ A : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℕ) (hd : 0 < d) {f : A} {m : ℕ} (hf : f ∈ 𝒜 m)
    (x : HomogeneousLocalization.NumDenSameDeg (veroneseGrading 𝒜 d) (Submonoid.powers (⟨f ^ d, (veronese_pow_mem 𝒜 d hd hf).1⟩ : veroneseSubring 𝒜 d))) :
    (((x.den : veroneseSubring 𝒜 d) : A)) ∈ Submonoid.powers f := by
  obtain ⟨j, hj⟩ := x.den_mem
  refine ⟨d * j, ?_⟩
  have h := congrArg (fun y : veroneseSubring 𝒜 d => (y : A)) hj
  simp only [SubmonoidClass.coe_pow] at h
  show f ^ (d * j) = _
  rw [pow_mul]
  exact h

/-- The forward map: `a / (f^d)^j` (`a` in the `n`-th piece of `S^{(d)}`, i.e. `S_{nd}`) `↦ a / f^{dj}`;
numerator and denominator are regarded as elements of `S` of degree `nd`. -/

noncomputable def veroneseAwayEquiv.toNumDen {σ A : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℕ) (hd : 0 < d) {f : A} {m : ℕ} (hf : f ∈ 𝒜 m)
    (x : HomogeneousLocalization.NumDenSameDeg (veroneseGrading 𝒜 d) (Submonoid.powers (⟨f ^ d, (veronese_pow_mem 𝒜 d hd hf).1⟩ : veroneseSubring 𝒜 d))) : HomogeneousLocalization.NumDenSameDeg 𝒜 (Submonoid.powers f) :=
  ⟨x.deg * d, ⟨((x.num : veroneseSubring 𝒜 d) : A), x.num.2.1⟩,
    ⟨((x.den : veroneseSubring 𝒜 d) : A), x.den.2.1⟩, veroneseAwayEquiv.den_mem_powers 𝒜 d hd hf x⟩

/-- Degree computation on the numerator side: `a ∈ 𝒜_i`, `b ∈ 𝒜_i`, `d ≥ 1 ⟹ a·b^{d-1} ∈ 𝒜_{i·d}`
(writing `d = d'+1`, the degree is `i + d'·i = i(d'+1)`). -/
theorem veroneseAwayEquiv.num_mul_den_pow_mem_graded {σ A : Type*} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℕ) (hd : 0 < d) {S : Submonoid A}
    (y : HomogeneousLocalization.NumDenSameDeg 𝒜 S) :
    (y.num : A) * (y.den : A) ^ (d - 1) ∈ 𝒜 (y.deg * d) := by
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  have h2 : ((y.den : A)) ^ d' ∈ 𝒜 (d' • y.deg) :=
    SetLike.pow_mem_graded d' (SetLike.coe_mem y.den)
  have he : y.deg * (d' + 1) = y.deg + d' • y.deg := by rw [smul_eq_mul]; ring
  simp only [Nat.add_sub_cancel, he]
  exact SetLike.GradedMul.mul_mem (SetLike.coe_mem y.num) h2

/-- Degree computation on the denominator side: `b ∈ 𝒜_i ⟹ b^d ∈ 𝒜_{i·d}`. -/
theorem veroneseAwayEquiv.den_pow_mem_graded {σ A : Type*} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℕ) {S : Submonoid A}
    (y : HomogeneousLocalization.NumDenSameDeg 𝒜 S) :
    (y.den : A) ^ d ∈ 𝒜 (y.deg * d) := by
  have h := SetLike.pow_mem_graded d (SetLike.coe_mem y.den)
  rwa [smul_eq_mul, Nat.mul_comm] at h

/-- Route: `a·den^{d-1}` with `a`, `den ∈ 𝒜_i` homogeneous has product in `𝒜_{id}` and `d ∣ id`; a
homogeneous element lies in `S^{(d)}` iff its degree is divisible by `d`
(`veroneseSubring.mem_of_mem_graded`). -/
theorem veroneseAwayEquiv.inv_num_mem_subring {σ A : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℕ) (hd : 0 < d) {f : A} {m : ℕ} (hf : f ∈ 𝒜 m)
    (y : HomogeneousLocalization.NumDenSameDeg 𝒜 (Submonoid.powers f)) :
    (y.num : A) * (y.den : A) ^ (d - 1) ∈ veroneseSubring 𝒜 d :=
  veroneseSubring.mem_of_mem_graded 𝒜 d (dvd_mul_left d y.deg)
    (veroneseAwayEquiv.num_mul_den_pow_mem_graded 𝒜 d hd y)

/-- Route: `den^d ∈ 𝒜_{id}` and `d ∣ id`. -/
theorem veroneseAwayEquiv.inv_den_mem_subring {σ A : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℕ) (hd : 0 < d) {f : A} {m : ℕ} (hf : f ∈ 𝒜 m)
    (y : HomogeneousLocalization.NumDenSameDeg 𝒜 (Submonoid.powers f)) :
    (y.den : A) ^ d ∈ veroneseSubring 𝒜 d :=
  veroneseSubring.mem_of_mem_graded 𝒜 d (dvd_mul_left d y.deg)
    (veroneseAwayEquiv.den_pow_mem_graded 𝒜 d y)

/-- Route: the degree is `i + i(d-1) = i·d` (`SetLike.GradedMul.mul_mem` + `SetLike.pow_mem_graded`);
since `d > 0`, the clause "`d = 0 → …`" in the carrier of `veroneseGrading` is vacuous. -/
theorem veroneseAwayEquiv.inv_num_mem_grading {σ A : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℕ) (hd : 0 < d) {f : A} {m : ℕ} (hf : f ∈ 𝒜 m)
    (y : HomogeneousLocalization.NumDenSameDeg 𝒜 (Submonoid.powers f)) :
    (⟨(y.num : A) * (y.den : A) ^ (d - 1), veroneseAwayEquiv.inv_num_mem_subring 𝒜 d hd hf y⟩ :
      veroneseSubring 𝒜 d) ∈ veroneseGrading 𝒜 d y.deg :=
  ⟨veroneseAwayEquiv.num_mul_den_pow_mem_graded 𝒜 d hd y, fun h0 => absurd h0 hd.ne'⟩

/-- Same route as above; the degree is `i·d`. -/
theorem veroneseAwayEquiv.inv_den_mem_grading {σ A : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℕ) (hd : 0 < d) {f : A} {m : ℕ} (hf : f ∈ 𝒜 m)
    (y : HomogeneousLocalization.NumDenSameDeg 𝒜 (Submonoid.powers f)) :
    (⟨(y.den : A) ^ d, veroneseAwayEquiv.inv_den_mem_subring 𝒜 d hd hf y⟩ :
      veroneseSubring 𝒜 d) ∈ veroneseGrading 𝒜 d y.deg :=
  ⟨veroneseAwayEquiv.den_pow_mem_graded 𝒜 d y, fun h0 => absurd h0 hd.ne'⟩

/-- Route: `den = f^j ⇒ den^d = (f^d)^j`. -/
theorem veroneseAwayEquiv.inv_den_mem_powers {σ A : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℕ) (hd : 0 < d) {f : A} {m : ℕ} (hf : f ∈ 𝒜 m)
    (y : HomogeneousLocalization.NumDenSameDeg 𝒜 (Submonoid.powers f)) :
    (⟨(y.den : A) ^ d, veroneseAwayEquiv.inv_den_mem_subring 𝒜 d hd hf y⟩ : veroneseSubring 𝒜 d) ∈
      Submonoid.powers (⟨f ^ d, (veronese_pow_mem 𝒜 d hd hf).1⟩ : veroneseSubring 𝒜 d) := by
  obtain ⟨j, hj⟩ := y.den_mem
  refine ⟨j, Subtype.ext ?_⟩
  simp only [SubmonoidClass.coe_pow]
  rw [← hj, ← pow_mul, ← pow_mul, Nat.mul_comm]

/-- The inverse map: `a / f^j` (`a ∈ S_i`) `↦ a·f^{j(d-1)} / f^{jd}`; numerator and denominator are
multiplied by the `(d-1)`-st power of the denominator and land in the `i`-th piece of `S^{(d)}`. -/

noncomputable def veroneseAwayEquiv.invNumDen {σ A : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℕ) (hd : 0 < d) {f : A} {m : ℕ} (hf : f ∈ 𝒜 m)
    (y : HomogeneousLocalization.NumDenSameDeg 𝒜 (Submonoid.powers f)) : HomogeneousLocalization.NumDenSameDeg (veroneseGrading 𝒜 d) (Submonoid.powers (⟨f ^ d, (veronese_pow_mem 𝒜 d hd hf).1⟩ : veroneseSubring 𝒜 d)) :=
  ⟨y.deg, ⟨⟨(y.num : A) * (y.den : A) ^ (d - 1), veroneseAwayEquiv.inv_num_mem_subring 𝒜 d hd hf y⟩,
      veroneseAwayEquiv.inv_num_mem_grading 𝒜 d hd hf y⟩,
    ⟨⟨(y.den : A) ^ d, veroneseAwayEquiv.inv_den_mem_subring 𝒜 d hd hf y⟩,
      veroneseAwayEquiv.inv_den_mem_grading 𝒜 d hd hf y⟩,
    veroneseAwayEquiv.inv_den_mem_powers 𝒜 d hd hf y⟩

/-- A ring identity in `A` (used in `left_inv` / `right_inv`): for `d ≥ 1`, `x·(y·x^{d-1}) = x^d·y`. -/
theorem veroneseAwayEquiv.mul_mul_pow_sub_one {A : Type*} [CommRing A] (d : ℕ) (hd : 0 < d)
    (x y : A) : x * (y * x ^ (d - 1)) = x ^ d * y := by
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  rw [Nat.add_sub_cancel, pow_succ]; ring

/-- A ring identity in `A` (used in `invNumDen_compat`): from `f^k·(bd·an) = f^k·(ad·bn)` deduce
`(f^d)^k·(bd^d·(an·ad^{d-1})) = (f^d)^k·(ad^d·(bn·bd^{d-1}))`.
Route: write `d = d'+1`, `(f^{d'+1})^k = (f^{d'})^k·f^k`, factor out `ad^{d'}·bd^{d'}·(f^{d'})^k` and
use the hypothesis. -/
theorem veroneseAwayEquiv.compat_aux {A : Type*} [CommRing A] (d : ℕ) (hd : 0 < d) (k : ℕ)
    (f an ad bn bd : A) (hc : f ^ k * (bd * an) = f ^ k * (ad * bn)) :
    (f ^ d) ^ k * (bd ^ d * (an * ad ^ (d - 1))) = (f ^ d) ^ k * (ad ^ d * (bn * bd ^ (d - 1))) := by
  obtain ⟨d', rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  calc (f ^ (d' + 1)) ^ k * (bd ^ (d' + 1) * (an * ad ^ d'))
      = ((f ^ d') ^ k * ad ^ d' * bd ^ d') * (f ^ k * (bd * an)) := by ring
    _ = ((f ^ d') ^ k * ad ^ d' * bd ^ d') * (f ^ k * (ad * bn)) := by rw [hc]
    _ = (f ^ (d' + 1)) ^ k * (ad ^ (d' + 1) * (bn * bd ^ d')) := by ring

/-- The forward map is compatible with the equivalence relation on fractions (the hypothesis of
`Quotient.map'`).

Reference: first paragraph of the proof of Stacks 0B5J.

Proof: `NumDenSameDeg.embedding` is `Localization.mk num ⟨den, den_mem⟩`, and
`Localization.mk_eq_mk_iff` / `Localization.r_iff_exists` say
`mk n₁ d₁ = mk n₂ d₂ ⟺ ∃ c ∈ S, c·(n₁·d₂ − n₂·d₁) = 0` (in a commutative ring: `c*(d₂*n₁) = c*(d₁*n₂)`).
The hypothesis gives a witness `c = (f^d)^k` in `S^{(d)}` with `c·(a.den·b.num) = c·(b.den·a.num)`
(an equation in `S^{(d)}`). Push it along the injective ring map `S^{(d)} ↪ A` (`Subring.subtype`,
`Subtype.val_injective`) to get `f^{dk}·(a.den·b.num) = f^{dk}·(b.den·a.num)` in `A`, where the
num/den on both sides are exactly those of `toNumDen a`, `toNumDen b` (`toNumDen` regards them as
elements of `A`, with degree `deg·d`). Since `f^{dk} = (f^d)^k ∈ Submonoid.powers f` (exponent `d*k`,
`pow_mul`), this is the required witness. Lemmas: `Localization.mk_eq_mk_iff`,
`Localization.r_iff_exists`, `Submonoid.powers`, `pow_mul`, `Subtype.ext_iff`. -/
theorem veroneseAwayEquiv.toNumDen_compat {σ A : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℕ) (hd : 0 < d) {f : A} {m : ℕ} (hf : f ∈ 𝒜 m)
    (a b : HomogeneousLocalization.NumDenSameDeg (veroneseGrading 𝒜 d) (Submonoid.powers (⟨f ^ d, (veronese_pow_mem 𝒜 d hd hf).1⟩ : veroneseSubring 𝒜 d)))
    (h : HomogeneousLocalization.NumDenSameDeg.embedding (veroneseGrading 𝒜 d) _ a =
      HomogeneousLocalization.NumDenSameDeg.embedding (veroneseGrading 𝒜 d) _ b) :
    HomogeneousLocalization.NumDenSameDeg.embedding 𝒜 _ (veroneseAwayEquiv.toNumDen 𝒜 d hd hf a) =
      HomogeneousLocalization.NumDenSameDeg.embedding 𝒜 _ (veroneseAwayEquiv.toNumDen 𝒜 d hd hf b) := by
  obtain ⟨⟨c, k, hk⟩, hc⟩ := Localization.r_iff_exists.mp (Localization.mk_eq_mk_iff.mp h)
  have hA : (c : A) * (((b.den : veroneseSubring 𝒜 d) : A) * ((a.num : veroneseSubring 𝒜 d) : A)) =
      (c : A) * (((a.den : veroneseSubring 𝒜 d) : A) * ((b.num : veroneseSubring 𝒜 d) : A)) :=
    congrArg Subtype.val hc
  have hcA : (c : A) = f ^ (d * k) := by
    rw [pow_mul]; exact (congrArg Subtype.val hk).symm
  refine Localization.mk_eq_mk_iff.mpr (Localization.r_iff_exists.mpr ⟨⟨f ^ (d * k), d * k, rfl⟩, ?_⟩)
  show f ^ (d * k) * (((b.den : veroneseSubring 𝒜 d) : A) * ((a.num : veroneseSubring 𝒜 d) : A)) =
    f ^ (d * k) * (((a.den : veroneseSubring 𝒜 d) : A) * ((b.num : veroneseSubring 𝒜 d) : A))
  rw [← hcA]; exact hA

/-- The inverse map is compatible with the equivalence relation on fractions (the hypothesis of
`Quotient.map'`).

Reference: first paragraph of the proof of Stacks 0B5J.

Proof: the hypothesis gives `c = f^k ∈ powers f` with `f^k·(a.den·b.num) = f^k·(b.den·a.num)` in `A`.
We need the embeddings of `invNumDen a` and `invNumDen b` to agree, i.e. a witness `c′` in `S^{(d)}`
with `c′·(a.den^d·(b.num·b.den^{d-1})) = c′·(b.den^d·(a.num·a.den^{d-1}))`.
Key identity (in the commutative ring `A`, by `ring`):
`a.den^d · b.num · b.den^{d-1} − b.den^d · a.num · a.den^{d-1}
 = a.den^{d-1} · b.den^{d-1} · (a.den · b.num − b.den · a.num)`.
Take `c′ := (f^d)^k` (in `S^{(d)}`, with image `f^{dk}` in `A`). Since `d ≥ 1` we have `dk ≥ k`;
write `f^{dk} = f^{dk-k}·f^k`, so `f^{dk}` times the right-hand side above is
`a.den^{d-1} b.den^{d-1} f^{dk-k} · (f^k·(a.den b.num − b.den a.num)) = 0`.
Hence the two embeddings agree; an equation in `A` holds in `S^{(d)}` (`Subtype.ext`, the inclusion
is injective). Lemmas: `Localization.mk_eq_mk_iff`, `Localization.r_iff_exists`, `pow_mul`,
`Nat.sub_add_cancel` (with `hd : 0 < d` giving `k ≤ d*k`), `Subtype.ext`. -/
theorem veroneseAwayEquiv.invNumDen_compat {σ A : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℕ) (hd : 0 < d) {f : A} {m : ℕ} (hf : f ∈ 𝒜 m)
    (a b : HomogeneousLocalization.NumDenSameDeg 𝒜 (Submonoid.powers f))
    (h : HomogeneousLocalization.NumDenSameDeg.embedding 𝒜 _ a =
      HomogeneousLocalization.NumDenSameDeg.embedding 𝒜 _ b) :
    HomogeneousLocalization.NumDenSameDeg.embedding (veroneseGrading 𝒜 d) _
        (veroneseAwayEquiv.invNumDen 𝒜 d hd hf a) =
      HomogeneousLocalization.NumDenSameDeg.embedding (veroneseGrading 𝒜 d) _
        (veroneseAwayEquiv.invNumDen 𝒜 d hd hf b) := by
  obtain ⟨⟨c, k, hk⟩, hc⟩ := Localization.r_iff_exists.mp (Localization.mk_eq_mk_iff.mp h)
  have hc' : f ^ k * ((b.den : A) * (a.num : A)) = f ^ k * ((a.den : A) * (b.num : A)) := by
    subst hk; exact hc
  refine Localization.mk_eq_mk_iff.mpr (Localization.r_iff_exists.mpr
    ⟨⟨(⟨f ^ d, (veronese_pow_mem 𝒜 d hd hf).1⟩ : veroneseSubring 𝒜 d) ^ k, k, rfl⟩, Subtype.ext ?_⟩)
  show (f ^ d) ^ k * ((b.den : A) ^ d * ((a.num : A) * (a.den : A) ^ (d - 1))) =
    (f ^ d) ^ k * ((a.den : A) ^ d * ((b.num : A) * (b.den : A) ^ (d - 1)))
  exact veroneseAwayEquiv.compat_aux d hd k f _ _ _ _ hc'

noncomputable def veroneseAwayEquiv.toFun {σ A : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℕ) (hd : 0 < d) {f : A} {m : ℕ} (hf : f ∈ 𝒜 m) :
    HomogeneousLocalization.Away (veroneseGrading 𝒜 d) (⟨f ^ d, (veronese_pow_mem 𝒜 d hd hf).1⟩ : veroneseSubring 𝒜 d) →
      HomogeneousLocalization.Away 𝒜 f :=
  Quotient.map' (veroneseAwayEquiv.toNumDen 𝒜 d hd hf) (veroneseAwayEquiv.toNumDen_compat 𝒜 d hd hf)

noncomputable def veroneseAwayEquiv.invFun {σ A : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℕ) (hd : 0 < d) {f : A} {m : ℕ} (hf : f ∈ 𝒜 m) :
    HomogeneousLocalization.Away 𝒜 f →
      HomogeneousLocalization.Away (veroneseGrading 𝒜 d) (⟨f ^ d, (veronese_pow_mem 𝒜 d hd hf).1⟩ : veroneseSubring 𝒜 d) :=
  Quotient.map' (veroneseAwayEquiv.invNumDen 𝒜 d hd hf) (veroneseAwayEquiv.invNumDen_compat 𝒜 d hd hf)

/-- `invFun ∘ toFun = id`.

Reference: first paragraph of the proof of Stacks 0B5J.

Proof: `Quotient.inductionOn'` writes `x` as `⟦a⟧` with
`a ∈ NumDenSameDeg (veroneseGrading 𝒜 d) (powers (f^d))`. The composite of the two `Quotient.map'`s
gives `⟦invNumDen (toNumDen a)⟧`, with num `a.num · a.den^{d-1}` and den `a.den^d` (both elements of
`S^{(d)}`, deg `a.deg`). We must show it equals `⟦a⟧` (num `a.num`, den `a.den`). By
`HomogeneousLocalization.ext_iff_val` and `val_mk` this reduces to
`Localization.mk (a.num·a.den^{d-1}) ⟨a.den^d, _⟩ = Localization.mk a.num ⟨a.den, _⟩`, and by
`Localization.mk_eq_mk_iff` / `r_iff_exists` to finding a witness `c` with
`c·(a.den · (a.num·a.den^{d-1})) = c·(a.den^d · a.num)`.
Take `c = 1`: both sides are `a.num · a.den^d` (`a.den · a.den^{d-1} = a.den^d` since `d ≥ 1`,
`pow_succ`/`ring`); no power of `f` is needed as witness. -/
theorem veroneseAwayEquiv.left_inv {σ A : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℕ) (hd : 0 < d) {f : A} {m : ℕ} (hf : f ∈ 𝒜 m) :
    Function.LeftInverse (veroneseAwayEquiv.invFun 𝒜 d hd hf) (veroneseAwayEquiv.toFun 𝒜 d hd hf) := by
  intro x
  refine Quotient.inductionOn' x fun a => ?_
  refine Quotient.sound' (Localization.mk_eq_mk_iff.mpr (Localization.r_iff_exists.mpr
    ⟨1, Subtype.ext ?_⟩))
  show (1 : A) * (((a.den : veroneseSubring 𝒜 d) : A) * (((a.num : veroneseSubring 𝒜 d) : A) *
      ((a.den : veroneseSubring 𝒜 d) : A) ^ (d - 1))) =
    (1 : A) * (((a.den : veroneseSubring 𝒜 d) : A) ^ d * ((a.num : veroneseSubring 𝒜 d) : A))
  rw [veroneseAwayEquiv.mul_mul_pow_sub_one d hd]

/-- `toFun ∘ invFun = id`.

Reference: first paragraph of the proof of Stacks 0B5J.

Proof: `Quotient.inductionOn'` writes `y` as `⟦b⟧` with `b ∈ NumDenSameDeg 𝒜 (powers f)`.
`toNumDen (invNumDen b)` has num `b.num·b.den^{d-1}` and den `b.den^d` (elements of `A`,
deg `b.deg·d`). Comparing with `b` (num `b.num`, den `b.den`) reduces as in `left_inv` to finding `c`
with `c·(b.den·(b.num·b.den^{d-1})) = c·(b.den^d·b.num)`; take `c = 1`, both sides being `b.num·b.den^d`.
Here `d ≥ 1` is used: for `d = 0` one would have `b.den^{d-1} = b.den^0 = 1` and `b.den^d = 1`, and the
equation would become `b.den·b.num = b.num`, which is false in general — so `hd` is a genuine
hypothesis. -/
theorem veroneseAwayEquiv.right_inv {σ A : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℕ) (hd : 0 < d) {f : A} {m : ℕ} (hf : f ∈ 𝒜 m) :
    Function.RightInverse (veroneseAwayEquiv.invFun 𝒜 d hd hf) (veroneseAwayEquiv.toFun 𝒜 d hd hf) := by
  intro y
  refine Quotient.inductionOn' y fun b => ?_
  refine Quotient.sound' (Localization.mk_eq_mk_iff.mpr (Localization.r_iff_exists.mpr ⟨1, ?_⟩))
  show (1 : A) * ((b.den : A) * ((b.num : A) * (b.den : A) ^ (d - 1))) =
    (1 : A) * ((b.den : A) ^ d * (b.num : A))
  rw [veroneseAwayEquiv.mul_mul_pow_sub_one d hd]

/-- The forward map preserves multiplication.

Reference: first paragraph of the proof of Stacks 0B5J (the comparison map is given on numerators and
denominators, hence is obviously a ring homomorphism).

Proof: `Quotient.inductionOn₂'` writes `x`, `y` as `⟦a⟧`, `⟦b⟧`. Multiplication on `NumDenSameDeg` is
`⟨deg₁+deg₂, num₁·num₂, den₁·den₂, _⟩`, so `toNumDen (a*b)` has num/den `(a.num·b.num, a.den·b.den)`
and deg `(a.deg+b.deg)·d`, while `toNumDen a * toNumDen b` has the same num/den and deg
`a.deg·d + b.deg·d`. The degrees agree (`Nat.add_mul`), but this is not even needed: equality in
`HomogeneousLocalization` is tested by `ext_iff_val` on the fractions in `Localization`, and the
numerators and denominators coincide literally, so the `val`s agree (`val_mk`, `val_mul`,
`Localization.mk_mul`). -/
theorem veroneseAwayEquiv.map_mul {σ A : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℕ) (hd : 0 < d) {f : A} {m : ℕ} (hf : f ∈ 𝒜 m)
    (x y : HomogeneousLocalization.Away (veroneseGrading 𝒜 d) (⟨f ^ d, (veronese_pow_mem 𝒜 d hd hf).1⟩ : veroneseSubring 𝒜 d)) :
    veroneseAwayEquiv.toFun 𝒜 d hd hf (x * y) =
      veroneseAwayEquiv.toFun 𝒜 d hd hf x * veroneseAwayEquiv.toFun 𝒜 d hd hf y := by
  refine Quotient.inductionOn₂' x y fun a b => ?_
  exact Quotient.sound' rfl

/-- The forward map preserves addition.

Proof: as for `map_mul`. Addition on `NumDenSameDeg` is `⟨deg₁+deg₂, den₂·num₁ + den₁·num₂, den₁·den₂, _⟩`;
`toNumDen` does not change the values of numerator and denominator (only the bookkeeping of `deg`),
so `toNumDen (a+b)` and `toNumDen a + toNumDen b` have literally the same num/den and equal `val`
(`Quotient.inductionOn₂'`, `ext_iff_val`, `val_mk`, `val_add`, `Localization.add_mk`). -/
theorem veroneseAwayEquiv.map_add {σ A : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℕ) (hd : 0 < d) {f : A} {m : ℕ} (hf : f ∈ 𝒜 m)
    (x y : HomogeneousLocalization.Away (veroneseGrading 𝒜 d) (⟨f ^ d, (veronese_pow_mem 𝒜 d hd hf).1⟩ : veroneseSubring 𝒜 d)) :
    veroneseAwayEquiv.toFun 𝒜 d hd hf (x + y) =
      veroneseAwayEquiv.toFun 𝒜 d hd hf x + veroneseAwayEquiv.toFun 𝒜 d hd hf y := by
  refine Quotient.inductionOn₂' x y fun a b => ?_
  exact Quotient.sound' rfl

noncomputable def veroneseAwayEquiv {σ A : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℕ) (hd : 0 < d) {f : A} {m : ℕ} (hf : f ∈ 𝒜 m) :
    HomogeneousLocalization.Away (veroneseGrading 𝒜 d) ⟨f ^ d, (veronese_pow_mem 𝒜 d hd hf).1⟩ ≃+*
      HomogeneousLocalization.Away 𝒜 f where
  toFun := veroneseAwayEquiv.toFun 𝒜 d hd hf
  invFun := veroneseAwayEquiv.invFun 𝒜 d hd hf
  left_inv := veroneseAwayEquiv.left_inv 𝒜 d hd hf
  right_inv := veroneseAwayEquiv.right_inv 𝒜 d hd hf
  map_mul' := veroneseAwayEquiv.map_mul 𝒜 d hd hf
  map_add' := veroneseAwayEquiv.map_add 𝒜 d hd hf

end
