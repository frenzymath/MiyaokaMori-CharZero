import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.RelativeProjLiftEvaluationTwistFamilyAbsoluteChartFractions
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.ProjFromGlobalSectionsCharts

/-! # Fractions of `O(n)` under `φ = Proj.fromOfGlobalSections`: germ-level identities

Helper module for `RelativeProjLiftEvaluationTwistFamilyAbsolute.lean` (existence of the twist family). Setting: `𝒜` a graded ring, `Φ : A →+* Γ(Y, O)` with
`Φ(irrelevant) = (1)`, `φ := Proj.fromOfGlobalSections 𝒜 Φ hΦ : Y ⟶ Proj 𝒜`.

The twist family `χ_n : φ^*O(n) ⟶ O_Y` of Stacks 01O4 (2) is `a/d ↦ Φ(a)Φ(d)⁻¹` on `φ⁻¹D₊(d)`. Everything needed
to make this well defined is a statement about germs of sections of `O_Y` at a point `t ∈ Y`:

* `exists_pos_deg_not_mem_mul_eq_zero`: if `u ∉ φ(t)` kills the homogeneous element `c`, then so does some
  homogeneous `v` of positive degree with `t ∈ Y.basicOpen (Φ v)` (a homogeneous component of `u`, times a chart
  element `s` with `t ∈ Y_s`; `φ⁻¹D₊(v) = Y.basicOpen (Φ v)` is Mathlib `fromOfGlobalSections_preimage_basicOpen`).
* `germ_eq_zero_of_mul_eq_zero`: hence `germ_t Φ(c) = 0` (`Φ(v)` is a unit at `t`).
* `germ_mul_eq_of_res_fracSection_eq`: **the key identity**: if `a/d = a'/d'` as sections of `O(n)` on an open
  `W ∋ φ(t)`, then `germ_t Φ(a) · germ_t Φ(d') = germ_t Φ(a') · germ_t Φ(d)` in `O_{Y,t}` (Stacks 01MN: the equality of
  fractions at `φ(t)` means `u(ad' − a'd) = 0` for some `u ∉ φ(t)`).
* `exists_res_eq_res_fracSection`: every section of `O(n)` is, near `φ(t)`, a fraction `a/d` with `d` of positive
  degree (`0 = 0/s`; `exists_res_eq_fracSection`, `…AbsoluteChartFractions.lean`).
* `germ_app_mul_eq_of_res_eq_mk`: **the bridge to Mathlib's `fromOfGlobalSections`**: if the structure-sheaf section
  `r` is the degree-zero fraction `c/e` near `φ(t)` (`c, e ∈ 𝒜 k`, `k > 0`), then `germ_t(φ^♯ r) · germ_t Φ(e) =
  germ_t Φ(c)` (through `fromOfGlobalSections_appLE_awayToSection_mk_mul`,
  `Stacks07rm_LiftSymImmersionOfCharts_ProjChart.lean`).
* `isUnit_germ_of_not_mem`: `Φ(d)` is a unit at `t` when `d ∉ φ(t)` is homogeneous of positive degree. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Proj.TwistFamily

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
  {Y : AlgebraicGeometry.Scheme.{u}} (Φ : A →+* Γ(Y, ⊤))
  (hΦ : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map Φ = ⊤)

/-- If `u * c = 0` with `c` homogeneous and `u ∉ 𝔭` (a point of `Proj 𝒜`), some homogeneous component of `u` is
not in `𝔭` and still kills `c` (the components of `u * c = 0` are `u_i * c`). -/
theorem exists_decompose_not_mem_mul_eq_zero {c : A} {m : ℕ} (hc : c ∈ 𝒜 m) {u : A} (huc : u * c = 0)
    (z : AlgebraicGeometry.Proj 𝒜) (hu : u ∉ z.asHomogeneousIdeal) :
    ∃ i : ℕ, (DirectSum.decompose 𝒜 u i : A) ∉ z.asHomogeneousIdeal ∧ (DirectSum.decompose 𝒜 u i : A) * c = 0 := by
  classical
  have hkill : ∀ i : ℕ, (DirectSum.decompose 𝒜 u i : A) * c = 0 := by
    intro i
    have h := DirectSum.coe_decompose_mul_of_right_mem_of_le 𝒜 (a := u) (b := c) (i := m) (n := i + m) hc
      (Nat.le_add_left m i)
    rw [huc, DirectSum.decompose_zero, DirectSum.zero_apply, ZeroMemClass.coe_zero, Nat.add_sub_cancel] at h
    exact h.symm
  by_contra hcon
  apply hu
  rw [← DirectSum.sum_support_decompose 𝒜 u]
  refine Ideal.sum_mem _ fun i _ => ?_
  by_contra hi
  exact hcon ⟨i, hi, hkill i⟩

include hΦ in
/-- Every point of `Y` lies in some `Y.basicOpen (Φ s)` with `s` homogeneous of positive degree (the cover
`openCoverOfMapIrrelevantEqTop`, from `hΦ`). Same as `exists_mem_basicOpen_of_irrelevant` in the main module;
repeated here to keep this helper independent. -/
theorem exists_mem_basicOpen_of_irrelevant' (t : Y) :
    ∃ (e : ℕ) (s : A), 0 < e ∧ s ∈ 𝒜 e ∧ t ∈ Y.basicOpen (Φ s) := by
  obtain ⟨⟨e, s, he, hs⟩, y, hy⟩ := (AlgebraicGeometry.Proj.openCoverOfMapIrrelevantEqTop 𝒜 Φ hΦ).exists_eq t
  refine ⟨e, s, he, hs, ?_⟩
  have h : t ∈ (Y.basicOpen (Φ s)).ι.opensRange := ⟨y, hy⟩
  rwa [AlgebraicGeometry.Scheme.Opens.opensRange_ι] at h

/-- `t ∈ Y.basicOpen (Φ v)` iff `v ∉ φ(t)`, for `v` homogeneous of positive degree
(Mathlib `fromOfGlobalSections_preimage_basicOpen`). -/
theorem mem_basicOpen_iff_not_mem {v : A} {k : ℕ} (hk : 0 < k) (hv : v ∈ 𝒜 k) (t : Y) :
    t ∈ Y.basicOpen (Φ v) ↔
      v ∉ ((AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ).base t).asHomogeneousIdeal := by
  rw [← AlgebraicGeometry.Proj.fromOfGlobalSections_preimage_basicOpen 𝒜 Φ hΦ hk hv]
  exact Iff.rfl

/-- If `u ∉ φ(t)` kills the homogeneous `c`, so does some homogeneous `v` of **positive** degree with
`t ∈ Y.basicOpen (Φ v)`: take a homogeneous component `u_i ∉ φ(t)` of `u` and multiply by a chart element `s`
(`t ∈ Y_s`). -/
theorem exists_pos_deg_not_mem_mul_eq_zero {c : A} {m : ℕ} (hc : c ∈ 𝒜 m) {u : A} (huc : u * c = 0) (t : Y)
    (hu : u ∉ ((AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ).base t).asHomogeneousIdeal) :
    ∃ (k : ℕ) (v : A), 0 < k ∧ v ∈ 𝒜 k ∧ t ∈ Y.basicOpen (Φ v) ∧ v * c = 0 := by
  obtain ⟨i, hi, hic⟩ := exists_decompose_not_mem_mul_eq_zero 𝒜 hc huc _ hu
  obtain ⟨e, s, he, hs, hts⟩ := exists_mem_basicOpen_of_irrelevant' 𝒜 Φ hΦ t
  have hs' : s ∉ ((AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ).base t).asHomogeneousIdeal :=
    (mem_basicOpen_iff_not_mem 𝒜 Φ hΦ he hs t).mp hts
  refine ⟨i + e, (DirectSum.decompose 𝒜 u i : A) * s, by omega,
    SetLike.mul_mem_graded (SetLike.coe_mem _) hs, ?_, ?_⟩
  · rw [mem_basicOpen_iff_not_mem 𝒜 Φ hΦ (by omega) (SetLike.mul_mem_graded (SetLike.coe_mem _) hs)]
    have hprime : Ideal.IsPrime ((AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ).base
      t).asHomogeneousIdeal.toIdeal := ProjectiveSpectrum.isPrime _
    exact fun h => (hprime.mem_or_mem h).elim hi hs'
  · rw [mul_right_comm, hic, zero_mul]

omit [SetLike σ A] [AddSubgroupClass σ A] 𝒜 [GradedRing 𝒜] in
/-- `germ_t Φ(c) = 0` when some `v` with `t ∈ Y.basicOpen (Φ v)` (so `Φ(v)` is a unit at `t`) kills `c`. -/
theorem germ_eq_zero_of_mul_eq_zero {c v : A} (t : Y) (htv : t ∈ Y.basicOpen (Φ v)) (hvc : v * c = 0) :
    Y.presheaf.germ ⊤ t trivial (Φ c) = 0 := by
  have hu : IsUnit (Y.presheaf.germ ⊤ t trivial (Φ v)) := (Y.mem_basicOpen (Φ v) t trivial).mp htv
  have h : Y.presheaf.germ ⊤ t trivial (Φ v) * Y.presheaf.germ ⊤ t trivial (Φ c) = 0 := by
    rw [← map_mul, ← map_mul, hvc, map_zero, map_zero]
  exact (hu.mul_right_eq_zero).mp h

/-- **The key identity (Stacks 01MN).** If the fractions `a/d` and `a'/d'` (`a ∈ 𝒜 p`, `d ∈ 𝒜 q`, `p = q + n`, and
likewise for `a', d'`) agree as sections of `O(n)` on an open `W ∋ φ(t)`, then
`germ_t Φ(a) · germ_t Φ(d') = germ_t Φ(a') · germ_t Φ(d)` in `O_{Y,t}`. Proof: at `φ(t)` the equality of fractions
means `u · (a d' − a' d) = 0` for some `u ∉ φ(t)`; `a d' − a' d` is homogeneous of degree `p + q' = p' + q`, so
`germ_t Φ(a d' − a' d) = 0` (`germ_eq_zero_of_mul_eq_zero`). -/
theorem germ_mul_eq_of_res_fracSection_eq (n : ℤ) {p q p' q' : ℕ} {a d a' d' : A} (ha : a ∈ 𝒜 p) (hd : d ∈ 𝒜 q)
    (hpq : (p : ℤ) = q + n) (ha' : a' ∈ 𝒜 p') (hd' : d' ∈ 𝒜 q') (hpq' : (p' : ℤ) = q' + n)
    {W : (AlgebraicGeometry.Proj 𝒜).Opens} (hW : W ≤ AlgebraicGeometry.Proj.basicOpen 𝒜 d)
    (hW' : W ≤ AlgebraicGeometry.Proj.basicOpen 𝒜 d')
    (h : (AlgebraicGeometry.Proj.twist 𝒜 n).presheaf.map (homOfLE hW).op
        (AlgebraicGeometry.Proj.fracSection 𝒜 n a d ha hd hpq) =
      (AlgebraicGeometry.Proj.twist 𝒜 n).presheaf.map (homOfLE hW').op
        (AlgebraicGeometry.Proj.fracSection 𝒜 n a' d' ha' hd' hpq'))
    (t : Y) (ht : (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ).base t ∈ W) :
    Y.presheaf.germ ⊤ t trivial (Φ a) * Y.presheaf.germ ⊤ t trivial (Φ d') =
      Y.presheaf.germ ⊤ t trivial (Φ a') * Y.presheaf.germ ⊤ t trivial (Φ d) := by
  have hpt := congrArg (fun s => s.1 ⟨(AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ).base t, ht⟩) h
  change (Localization.mk a ⟨d, hW ht⟩ : MiyaokaMori.WeightedJets.ProjTwisting.Fiber 𝒜 _) =
    Localization.mk a' ⟨d', hW' ht⟩ at hpt
  rw [Localization.mk_eq_mk_iff, Localization.r_iff_exists] at hpt
  obtain ⟨⟨u, hu⟩, hu'⟩ := hpt
  simp only at hu'
  have hpq'' : p + q' = p' + q := by omega
  have hc : a * d' - a' * d ∈ 𝒜 (p + q') :=
    sub_mem (SetLike.mul_mem_graded ha hd') (hpq'' ▸ SetLike.mul_mem_graded ha' hd)
  have huc : u * (a * d' - a' * d) = 0 := by
    rw [mul_sub, sub_eq_zero]
    linear_combination hu'
  obtain ⟨k, v, _, _, htv, hvc⟩ := exists_pos_deg_not_mem_mul_eq_zero 𝒜 Φ hΦ hc huc t hu
  have h0 := germ_eq_zero_of_mul_eq_zero Φ t htv hvc
  rw [map_sub, map_mul, map_mul, map_sub, map_mul, map_mul, sub_eq_zero] at h0
  exact h0

/-- **Sections of `O(n)` are, near `φ(t)`, fractions with denominators of positive degree** (Stacks 01MN): for
`g ∈ Γ(U, O(n))` and `t ∈ φ⁻¹U` there is an open `W ∋ φ(t)`, `W ≤ U`, on which `g` is the fraction `a/d`
(`a ∈ 𝒜 p`, `d ∈ 𝒜 q`, `p = q + n`, `0 < q`, `W ≤ D₊(d)`). The zero case is `0 = 0/s` for a chart element `s`. -/
theorem exists_res_eq_res_fracSection (n : ℕ) {U : (AlgebraicGeometry.Proj 𝒜).Opens}
    (g : Γ(AlgebraicGeometry.Proj.twist 𝒜 (n : ℤ), U)) (t : Y)
    (ht : (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ).base t ∈ U) :
    ∃ (W : (AlgebraicGeometry.Proj 𝒜).Opens) (_ : (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ).base t ∈ W)
      (hWU : W ≤ U) (p q : ℕ) (a d : A) (ha : a ∈ 𝒜 p) (hd : d ∈ 𝒜 q) (hpq : (p : ℤ) = q + n) (_ : 0 < q)
      (hW : W ≤ AlgebraicGeometry.Proj.basicOpen 𝒜 d),
      (AlgebraicGeometry.Proj.twist 𝒜 (n : ℤ)).presheaf.map (homOfLE hWU).op g =
        (AlgebraicGeometry.Proj.twist 𝒜 (n : ℤ)).presheaf.map (homOfLE hW).op
          (AlgebraicGeometry.Proj.fracSection 𝒜 (n : ℤ) a d ha hd hpq) := by
  obtain ⟨e, s, he, hs, hts⟩ := exists_mem_basicOpen_of_irrelevant' 𝒜 Φ hΦ t
  have hφs : (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ).base t ∈ AlgebraicGeometry.Proj.basicOpen 𝒜 s :=
    (mem_basicOpen_iff_not_mem 𝒜 Φ hΦ he hs t).mp hts
  obtain ⟨W₀, hxW₀, hW₀U, hcase⟩ := AlgebraicGeometry.Proj.exists_res_eq_fracSection 𝒜 (n : ℤ) g ht hs hφs
  rcases hcase with h0 | ⟨p, q, a, d, ha, hd, hpq, heq, hW, hfrac⟩
  · have hpq : ((e + n : ℕ) : ℤ) = (e : ℤ) + n := by push_cast; ring
    refine ⟨W₀ ⊓ AlgebraicGeometry.Proj.basicOpen 𝒜 s, ⟨hxW₀, hφs⟩, inf_le_left.trans hW₀U, e + n, e, 0, s,
      zero_mem _, hs, hpq, he, inf_le_right, ?_⟩
    apply Subtype.ext
    funext w
    have h1 := congrArg (fun z => z.1 ⟨w.1, w.2.1⟩) h0
    change g.1 ⟨w.1, hW₀U w.2.1⟩ = 0 at h1
    change g.1 ⟨w.1, hW₀U w.2.1⟩ = Localization.mk (0 : A) ⟨s, w.2.2⟩
    rw [h1, Localization.mk_zero]
  · exact ⟨W₀, hxW₀, hW₀U, p, q, a, d, ha, hd, hpq, lt_of_lt_of_le he heq, hW, hfrac⟩

set_option backward.isDefEq.respectTransparency false in
/-- The chart section `c / e ∈ A_{(e)} = Γ(D₊(e), O)` (`awayToSection`, `Away.mk … 1 c`) restricted to `W ≤ D₊(e)` is
the structure-sheaf section whose value at every `w ∈ W` is the fraction `c / e`. -/
theorem res_awayToSection_mk_one {U W : (AlgebraicGeometry.Proj 𝒜).Opens} (r : Γ(AlgebraicGeometry.Proj 𝒜, U))
    {k : ℕ} {c e : A} (hc : c ∈ 𝒜 k) (he : e ∈ 𝒜 k) (hc' : c ∈ 𝒜 (1 • k))
    (hWU : W ≤ U) (hWe : W ≤ AlgebraicGeometry.Proj.basicOpen 𝒜 e)
    (hr : ∀ w : W, r.1 ⟨w.1, hWU w.2⟩ = HomogeneousLocalization.mk ⟨k, ⟨c, hc⟩, ⟨e, he⟩, hWe w.2⟩) :
    (AlgebraicGeometry.Proj 𝒜).presheaf.map (homOfLE hWe).op
        (AlgebraicGeometry.Proj.awayToSection 𝒜 e (HomogeneousLocalization.Away.mk 𝒜 he 1 c hc')) =
      (AlgebraicGeometry.Proj 𝒜).presheaf.map (homOfLE hWU).op r := by
  apply Subtype.ext
  funext w
  apply HomogeneousLocalization.val_injective
  change ((AlgebraicGeometry.Proj.awayToSection 𝒜 e (HomogeneousLocalization.Away.mk 𝒜 he 1 c hc')).1
    ⟨w.1, hWe w.2⟩).val = (r.1 ⟨w.1, hWU w.2⟩).val
  rw [hr w, HomogeneousLocalization.val_mk]
  have h := ProjectiveSpectrum.Proj.awayToSection_apply 𝒜 e (HomogeneousLocalization.Away.mk 𝒜 he 1 c hc')
    ⟨w.1, hWe w.2⟩
  refine h.trans ?_
  rw [HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk', IsLocalization.map_mk', ← Localization.mk_eq_mk',
    Localization.mk_eq_mk_iff]
  apply Localization.r_of_eq
  simp only [RingHom.id_apply, pow_one]

/-- Restriction of the structure sheaf of `Y` in two steps. -/
theorem ring_res_res {B B' B'' : Y.Opens} (h : B' ≤ B) (h' : B'' ≤ B') (r : Γ(Y, B)) :
    Y.presheaf.map (homOfLE h').op (Y.presheaf.map (homOfLE h).op r) =
      Y.presheaf.map (homOfLE (h'.trans h)).op r := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- `φ^♯` commutes with restriction: `(φ^♯_U r)|_{φ⁻¹W} = φ^♯_W (r|_W)`. -/
theorem app_res {U W : (AlgebraicGeometry.Proj 𝒜).Opens} (hWU : W ≤ U) (r : Γ(AlgebraicGeometry.Proj 𝒜, U)) :
    Y.presheaf.map (homOfLE (show AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ ⁻¹ᵁ W ≤
        AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ ⁻¹ᵁ U from fun _ hx => hWU hx)).op
        ((AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ).app U r) =
      (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ).app W ((AlgebraicGeometry.Proj 𝒜).presheaf.map (homOfLE hWU).op r) := by
  have h := ConcreteCategory.congr_hom
    ((AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ).naturality (homOfLE hWU).op) r
  rw [CommRingCat.comp_apply, CommRingCat.comp_apply] at h
  exact h.symm

set_option backward.isDefEq.respectTransparency false in
/-- **`φ^♯` on a local fraction, germ form (Stacks 01O4 (2)).** If the structure-sheaf section `r ∈ Γ(U, O_Proj)` is
the degree-zero fraction `c / e` (`c, e ∈ 𝒜 k`, `0 < k`) on an open `W ≤ U ∩ D₊(e)` containing `φ(t)`, then
`germ_t(φ^♯ r) · germ_t Φ(e) = germ_t Φ(c)` in `O_{Y,t}`. Proof: `r|_W = (c/e)|_W` with `c/e ∈ A_{(e)}`
(`res_awayToSection_mk_one`), `φ^♯` commutes with restriction, and on `φ⁻¹D₊(e)` the ring map of `φ` sends `c/e` to
the element `g` with `g · Φ(e) = Φ(c)` (`fromOfGlobalSections_appLE_awayToSection_mk_mul`,
`Stacks07rm_LiftSymImmersionOfCharts_ProjChart.lean`). -/
theorem germ_app_mul_eq_of_res_eq_mk {U W : (AlgebraicGeometry.Proj 𝒜).Opens} (r : Γ(AlgebraicGeometry.Proj 𝒜, U))
    {k : ℕ} (hk : 0 < k) {c e : A} (hc : c ∈ 𝒜 k) (he : e ∈ 𝒜 k)
    (hWU : W ≤ U) (hWe : W ≤ AlgebraicGeometry.Proj.basicOpen 𝒜 e)
    (hr : ∀ w : W, r.1 ⟨w.1, hWU w.2⟩ = HomogeneousLocalization.mk ⟨k, ⟨c, hc⟩, ⟨e, he⟩, hWe w.2⟩)
    (t : Y) (ht : t ∈ AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ ⁻¹ᵁ U)
    (htW : (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ).base t ∈ W) :
    Y.presheaf.germ (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ ⁻¹ᵁ U) t ht
        ((AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ).app U r) *
      Y.presheaf.germ ⊤ t trivial (Φ e) = Y.presheaf.germ ⊤ t trivial (Φ c) := by
  have hc' : c ∈ 𝒜 (1 • k) := by rw [one_smul]; exact hc
  have hpre : AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ ⁻¹ᵁ W ≤
      AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ ⁻¹ᵁ U := fun _ hx => hWU hx
  have hpre' : AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ ⁻¹ᵁ W ≤
      AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 e :=
    fun _ hx => hWe hx
  have key := AlgebraicGeometry.Proj.fromOfGlobalSections_appLE_awayToSection_mk_mul 𝒜 Φ hΦ he hk 1 hc' hpre'
  -- rewrite the left factor as the restriction of `φ^♯ r`
  have h1 : (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ).appLE (AlgebraicGeometry.Proj.basicOpen 𝒜 e)
        (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ ⁻¹ᵁ W) hpre'
        (AlgebraicGeometry.Proj.awayToSection 𝒜 e (HomogeneousLocalization.Away.mk 𝒜 he 1 c hc')) =
      Y.presheaf.map (homOfLE hpre).op ((AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ).app U r) := by
    rw [app_res 𝒜 Φ hΦ hWU r, ← res_awayToSection_mk_one 𝒜 r hc he hc' hWU hWe hr, ← app_res 𝒜 Φ hΦ hWe]
    rfl
  rw [h1, pow_one] at key
  have hg := congrArg (Y.presheaf.germ (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ ⁻¹ᵁ W) t htW) key
  rw [map_mul, TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply] at hg
  exact hg


/-- `Φ(d)` is a unit at `t` when `d ∉ φ(t)` is homogeneous of positive degree (`t ∈ Y.basicOpen (Φ d)`). -/
theorem isUnit_germ_of_not_mem {d : A} {q : ℕ} (hq : 0 < q) (hd : d ∈ 𝒜 q) (t : Y)
    (ht : d ∉ ((AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ).base t).asHomogeneousIdeal) :
    IsUnit (Y.presheaf.germ ⊤ t trivial (Φ d)) :=
  (Y.mem_basicOpen (Φ d) t trivial).mp ((mem_basicOpen_iff_not_mem 𝒜 Φ hΦ hq hd t).mpr ht)

/-- `Φ(d)` restricted to any open `B ≤ φ⁻¹D₊(d)` is a unit, for `d` homogeneous of positive degree
(`φ⁻¹D₊(d) = Y.basicOpen (Φ d)`, `RingedSpace.isUnit_res_basicOpen`). -/
theorem isUnit_res_of_le_preimage_basicOpen {d : A} {q : ℕ} (hq : 0 < q) (hd : d ∈ 𝒜 q) {B : Y.Opens}
    (hB : B ≤ AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 d) :
    IsUnit (Y.presheaf.map (homOfLE le_top).op (Φ d) : Γ(Y, B)) := by
  have hB' : B ≤ Y.basicOpen (Φ d) := by
    rwa [AlgebraicGeometry.Proj.fromOfGlobalSections_preimage_basicOpen 𝒜 Φ hΦ hq hd] at hB
  have hu : IsUnit (Y.presheaf.map (homOfLE (Y.basicOpen_le (Φ d))).op (Φ d)) :=
    AlgebraicGeometry.RingedSpace.isUnit_res_basicOpen (X := Y.toLocallyRingedSpace.toRingedSpace) (Φ d)
  have := hu.map (Y.presheaf.map (homOfLE hB').op).hom
  change IsUnit (Y.presheaf.map (homOfLE hB').op (Y.presheaf.map (homOfLE le_top).op (Φ d))) at this
  rwa [ring_res_res] at this

end AlgebraicGeometry.Proj.TwistFamily

end
