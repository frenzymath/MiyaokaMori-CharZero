import MiyaokaMori.AlgebraicGeometry.Proj.Twist.Stacks01n2TwistStalkAlgebra
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.ProjTwistingSheaf

/-! # Sections and germs of `O(n)` over a chart `D₊(s)`

**Sections and germs of `O_{Proj 𝒞}(n)` over the chart `D₊(s)`**, the sheaf-theoretic bookkeeping for
`Stacks01n2TwistStalk`.

Setting: `𝒞 : ℕ → Submodule S C` graded, `s ∈ 𝒞 i`, `0 < i`, `n : ℤ`, `U := D₊(s) = Proj.basicOpen 𝒞 s`.

* `twistSection m` (`m ∈ (C_s)_n = twistAway 𝒞 hs hi n`, `Stacks01n2TwistStalkAlgebra.lean`): the section of
  `O(n)` over `D₊(s)` given by `z ↦ m ∈ C_z` (`toFiber`, Mathlib's `IsLocalization.map`); it is additive
  (`twistSection_add`) and `Proj.awayToSection u • twistSection m = twistSection (u • m)` on germs
  (`germ_awayToSection_smul_germ_twistSection`), where `Proj.awayToSection : 𝒞_(s) → Γ(D₊(s), O)` is Mathlib's.
* `fracSection`, `twistFracSection`: the sections `c / d` of `O` resp. `a / d` of `O(n)` given by one homogeneous
  fraction on an open `W` on which `d` does not vanish.
* `isUnit_germ_iff`: a germ of `O` is a unit iff its value at the point is (Mathlib `Proj.stalkIso'`);
  `isUnit_germ_awayToSection_mk`: the germ of `c / s ^ q` at `y` is a unit if `c ∉ y`.
* Normalization at a point `y ∈ D₊(s)`, `i = deg s`:
  - `exists_unit_germ_mul_eq_germ_awayToSection`: every `b ∈ O_y` satisfies `germ τ · b = germ σ` with
    `τ, σ ∈ 𝒞_(s)` and `germ τ` a unit (write `b = c / d` near `y`, `c, d ∈ 𝒞_q`; then `τ := d^i / s^q`,
    `σ := c d^{i-1} / s^q`);
  - `exists_smul_germ_twistSection_eq`: every `μ ∈ O(n)_y` is `v • germ (twistSection m)` with `v ∈ O_y`,
    `m ∈ (C_s)_n` (write `μ = a / t` near `y`, `a ∈ 𝒞_p`, `t ∈ 𝒞_q`, `p = q + n`; then `v := s^q / t^i`,
    `m := a t^{i-1} / s^q`);
  - `exists_unit_mul_eq_zero_of_germ_eq_zero`: if `germ_y (twistSection m) = 0` then `u • m = 0` for some
    `u ∈ 𝒞_(s)` whose germ at `y` is a unit (evaluate at `y`: `m = c / s^k = 0` in `C_y`, so `t c = 0` for some
    `t ∉ y`, and a homogeneous component `t_q ∉ y` of `t` still kills `c`; `u := t_q^i / s^q`).

Source: Stacks 01M7/01MN (sections of `O(n)` on `D₊(s)`), Mathlib `AlgebraicGeometry/ProjectiveSpectrum`
(`awayToSection`, `stalkIso'`); the paper uses this only through Stacks 01N2.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite TopologicalSpace HomogeneousLocalization
open AlgebraicGeometry MiyaokaMori.WeightedJets.ProjTwisting MiyaokaMori.Stacks01n2
open scoped AlgebraicGeometry

noncomputable section

namespace MiyaokaMori.Stacks01n2TwistStalk

/-- `germ (r • m) = germ r • germ m` for a module sheaf on a scheme. -/
theorem germ_smul' {X : Scheme.{u}} (M : X.Modules) {V : X.Opens} {y : X} (hy : y ∈ V) (r : Γ(X, V))
    (m : M.val.obj (op V)) :
    M.presheaf.germ V y hy (r • m) = X.presheaf.germ V y hy r • M.presheaf.germ V y hy m :=
  PresheafOfModules.germ_smul (R := X.presheaf) M.val y V hy r m

section Graded

variable {S : Type u} [CommRing S] {C : Type u} [CommRing C] [Algebra S C] (𝒞 : ℕ → Submodule S C)
  [GradedAlgebra 𝒞]

/-- A germ of the structure sheaf of `Proj 𝒞` is a unit iff its value at the point is
(Mathlib `Proj.stalkIso'`). -/
theorem isUnit_germ_iff {U : (Proj 𝒞).Opens} {x : Proj 𝒞} (hx : x ∈ U)
    (r : (ProjectiveSpectrum.Proj.structureSheaf 𝒞).1.obj (op U)) :
    IsUnit ((Proj 𝒞).presheaf.germ U x hx r) ↔ IsUnit (r.1 ⟨x, hx⟩) := by
  have h := Proj.stalkIso'_germ 𝒞 U x hx r
  constructor
  · intro hu
    have := hu.map (Proj.stalkIso' 𝒞 x)
    erw [h] at this
    exact this
  · intro hu
    have := hu.map (Proj.stalkIso' 𝒞 x).symm
    erw [← h, RingEquiv.symm_apply_apply] at this
    exact this

/-- The section `c / d` of the structure sheaf over an open `U` on which `d` does not vanish. -/
def fracSection (U : (Proj 𝒞).Opens) {q : ℕ} (c d : 𝒞 q)
    (hd : ∀ z : U, (d : C) ∉ z.1.asHomogeneousIdeal) :
    (ProjectiveSpectrum.Proj.structureSheaf 𝒞).1.obj (op U) :=
  ⟨fun z ↦ HomogeneousLocalization.mk ⟨q, c, d, hd z⟩, fun z ↦ ⟨U, z.2, 𝟙 _, q, c, d, hd, fun _ ↦ rfl⟩⟩

theorem fracSection_apply (U : (Proj 𝒞).Opens) {q : ℕ} (c d : 𝒞 q)
    (hd : ∀ z : U, (d : C) ∉ z.1.asHomogeneousIdeal) (z : U) :
    (fracSection 𝒞 U c d hd).1 z = HomogeneousLocalization.mk ⟨q, c, d, hd z⟩ := rfl

theorem isUnit_germ_fracSection (U : (Proj 𝒞).Opens) {q : ℕ} (c d : 𝒞 q)
    (hd : ∀ z : U, (d : C) ∉ z.1.asHomogeneousIdeal) {x : Proj 𝒞} (hx : x ∈ U)
    (hc : (c : C) ∉ x.asHomogeneousIdeal) :
    IsUnit ((Proj 𝒞).presheaf.germ U x hx (fracSection 𝒞 U c d hd)) := by
  rw [isUnit_germ_iff, fracSection_apply, ← HomogeneousLocalization.isUnit_iff_isUnit_val,
    HomogeneousLocalization.val_mk, Localization.mk_eq_mk']
  exact (IsLocalization.AtPrime.isUnit_mk'_iff _ _ _ _).mpr hc

/-- The section `a / d` of `O(n)` over an open `U` on which `d` does not vanish (`deg a = deg d + n`). -/
def twistFracSection (n : ℤ) (U : (Proj 𝒞).Opens) {p q : ℕ} (a : 𝒞 p) (d : 𝒞 q) (hpq : (p : ℤ) = q + n)
    (hd : ∀ z : U, (d : C) ∉ z.1.asHomogeneousIdeal) : sectionsSubmodule 𝒞 n U :=
  ⟨fun z ↦ Localization.mk (a : C) ⟨d, hd z⟩,
    TopCat.PrelocalPredicate.sheafifyOf (P := fractionPrelocal 𝒞 n) (Or.inr ⟨p, q, a, d, hpq, hd, fun _ ↦ rfl⟩)⟩

theorem twistFracSection_apply (n : ℤ) (U : (Proj 𝒞).Opens) {p q : ℕ} (a : 𝒞 p) (d : 𝒞 q)
    (hpq : (p : ℤ) = q + n) (hd : ∀ z : U, (d : C) ∉ z.1.asHomogeneousIdeal) (z : U) :
    (twistFracSection 𝒞 n U a d hpq hd).1 z = Localization.mk (a : C) ⟨d, hd z⟩ := rfl

/-- If the germ of a section of `O(n)` at `x` vanishes, so does its value at `x`. -/
theorem apply_eq_zero_of_germ_eq_zero (n : ℤ) {U : (Proj 𝒞).Opens} {x : Proj 𝒞} (hx : x ∈ U)
    (m : sectionsSubmodule 𝒞 n U) (h : (Proj.twist 𝒞 n).presheaf.germ U x hx m = 0) :
    m.1 ⟨x, hx⟩ = 0 := by
  have h' : (Proj.twist 𝒞 n).presheaf.germ U x hx m =
      (Proj.twist 𝒞 n).presheaf.germ U x hx (0 : sectionsSubmodule 𝒞 n U) :=
    h.trans (map_zero ((Proj.twist 𝒞 n).presheaf.germ U x hx).hom).symm
  obtain ⟨W, hxW, iU, iV, he⟩ := (Proj.twist 𝒞 n).presheaf.germ_eq x hx hx m 0 h'
  exact congrArg (fun t : sectionsSubmodule 𝒞 n W ↦ t.1 ⟨x, hxW⟩) he

/-! ## The chart `D₊(s)` -/

variable {s : C} {i : ℕ} (hs : s ∈ 𝒞 i) (hi : 0 < i) (n : ℤ)

/-- `C_s → C_z` for `z ∈ D₊(s)` (Mathlib's `IsLocalization.map`, as in `awayToSection_apply`). -/
abbrev toFiber (z : Proj.basicOpen 𝒞 s) : Localization.Away s →+* Fiber 𝒞 z.1 :=
  IsLocalization.map (M := Submonoid.powers s) (T := z.1.asHomogeneousIdeal.toIdeal.primeCompl) _
    (RingHom.id C) (Submonoid.powers_le.mpr z.2)

theorem toFiber_mk (z : Proj.basicOpen 𝒞 s) (a : C) (k : ℕ) :
    toFiber 𝒞 z (Localization.mk a (⟨s ^ k, k, rfl⟩ : Submonoid.powers s)) =
      Localization.mk a ⟨s ^ k, Submonoid.powers_le.mpr z.2 ⟨k, rfl⟩⟩ := by
  rw [Localization.mk_eq_mk', Localization.mk_eq_mk', IsLocalization.map_mk']
  rfl

theorem val_awayToSection_apply (u : Away 𝒞 s) (z : Proj.basicOpen 𝒞 s) :
    ((Proj.awayToSection 𝒞 s u : (ProjectiveSpectrum.Proj.structureSheaf 𝒞).1.obj
      (op (Proj.basicOpen 𝒞 s))).1 z).val = toFiber 𝒞 z u.val :=
  ProjectiveSpectrum.Proj.awayToSection_apply 𝒞 s u z

/-- The section of `O(n)` over `D₊(s)` given by `m ∈ (C_s)_n`. -/
def twistSection (m : twistAway 𝒞 hs hi n) : sectionsSubmodule 𝒞 n (Proj.basicOpen 𝒞 s) :=
  have hpred : (locallyFraction 𝒞 n).pred
      (fun z : Proj.basicOpen 𝒞 s ↦ toFiber 𝒞 z (m : Localization.Away s)) := by
    obtain ⟨p, k, a, ha, hp, hm⟩ := m.2
    have hden : ∀ z : Proj.basicOpen 𝒞 s, s ^ k ∉ z.1.asHomogeneousIdeal :=
      fun z hz ↦ z.2 (z.1.isPrime.mem_of_pow_mem k hz)
    refine TopCat.PrelocalPredicate.sheafifyOf (P := fractionPrelocal 𝒞 n) (Or.inr ⟨p, k * i, ⟨a, ha⟩,
      ⟨s ^ k, by simpa [smul_eq_mul] using SetLike.pow_mem_graded k hs⟩, by push_cast; exact hp,
      hden, fun z ↦ ?_⟩)
    change toFiber 𝒞 z (m : Localization.Away s) = _
    rw [hm, toFiber_mk]
  ⟨fun z ↦ toFiber 𝒞 z (m : Localization.Away s), hpred⟩

theorem twistSection_apply (m : twistAway 𝒞 hs hi n) (z : Proj.basicOpen 𝒞 s) :
    (twistSection 𝒞 hs hi n m).1 z = toFiber 𝒞 z (m : Localization.Away s) := rfl

theorem twistSection_add (m m' : twistAway 𝒞 hs hi n) :
    twistSection 𝒞 hs hi n (m + m') = twistSection 𝒞 hs hi n m + twistSection 𝒞 hs hi n m' :=
  Subtype.ext (funext fun z ↦ map_add (toFiber 𝒞 z) (m : Localization.Away s) m')

theorem twistSection_zero : twistSection 𝒞 hs hi n 0 = 0 :=
  Subtype.ext (funext fun z ↦ map_zero (toFiber 𝒞 z))

/-- `germ (awayToSection u) • germ (twistSection m) = germ (twistSection (u • m))` at `x ∈ D₊(s)`. -/
theorem germ_awayToSection_smul_germ_twistSection {x : Proj 𝒞} (hx : x ∈ Proj.basicOpen 𝒞 s)
    (u : Away 𝒞 s) (m : twistAway 𝒞 hs hi n) :
    (Proj 𝒞).presheaf.germ _ x hx (Proj.awayToSection 𝒞 s u) •
        (Proj.twist 𝒞 n).presheaf.germ _ x hx (twistSection 𝒞 hs hi n m) =
      (Proj.twist 𝒞 n).presheaf.germ _ x hx
        (twistSection 𝒞 hs hi n ⟨u.val * m, val_mul_mem 𝒞 hs hi n u m.2⟩) := by
  rw [← germ_smul']
  congr 1
  apply Subtype.ext
  funext z
  change ((Proj.awayToSection 𝒞 s u : (ProjectiveSpectrum.Proj.structureSheaf 𝒞).1.obj
    (op (Proj.basicOpen 𝒞 s))).1 z).val * toFiber 𝒞 z (m : Localization.Away s) =
    toFiber 𝒞 z (u.val * (m : Localization.Away s))
  rw [val_awayToSection_apply, map_mul]

/-- `S → O_{Proj 𝒞, y}` through `S → 𝒞_(s) → Γ(D₊(s), O) → O_y` (`y ∈ D₊(s)`). -/
def constGerm {y : Proj 𝒞} (hy : y ∈ Proj.basicOpen 𝒞 s) : S →+* (Proj 𝒞).presheaf.stalk y :=
  ((Proj 𝒞).presheaf.germ (Proj.basicOpen 𝒞 s) y hy).hom.comp
    ((Proj.awayToSection 𝒞 s).hom.comp (awayAlgebraMap 𝒞 s))

theorem constGerm_apply {y : Proj 𝒞} (hy : y ∈ Proj.basicOpen 𝒞 s) (r : S) :
    constGerm 𝒞 hy r =
      (Proj 𝒞).presheaf.germ (Proj.basicOpen 𝒞 s) y hy
        (Proj.awayToSection 𝒞 s (awayAlgebraMap 𝒞 s r)) := rfl

attribute [local instance] awayAlgebra in
theorem germ_awayToSection_smul {y : Proj 𝒞} (hy : y ∈ Proj.basicOpen 𝒞 s) (r : S) (w : Away 𝒞 s) :
    (Proj 𝒞).presheaf.germ (Proj.basicOpen 𝒞 s) y hy (Proj.awayToSection 𝒞 s (r • w)) =
      constGerm 𝒞 hy r * (Proj 𝒞).presheaf.germ (Proj.basicOpen 𝒞 s) y hy (Proj.awayToSection 𝒞 s w) := by
  rw [constGerm_apply, ← map_mul, ← map_mul]
  exact congrArg _ (congrArg _ (Algebra.smul_def r w))

theorem isUnit_germ_awayToSection_mk {y : Proj 𝒞} (hy : y ∈ Proj.basicOpen 𝒞 s) (q : ℕ) (c : C)
    (hc : c ∈ 𝒞 (q • i)) (hcy : c ∉ y.asHomogeneousIdeal) :
    IsUnit ((Proj 𝒞).presheaf.germ _ y hy (Proj.awayToSection 𝒞 s (Away.mk 𝒞 hs q c hc))) := by
  rw [isUnit_germ_iff, ← HomogeneousLocalization.isUnit_iff_isUnit_val, val_awayToSection_apply,
    Away.val_mk, toFiber_mk, Localization.mk_eq_mk']
  exact (IsLocalization.AtPrime.isUnit_mk'_iff _ _ _ _).mpr hcy

/-- If `germ_y (twistSection m) = 0` then `u • m = 0` for some `u ∈ 𝒞_(s)` whose germ at `y` is a unit. -/
theorem exists_unit_mul_eq_zero_of_germ_eq_zero {y : Proj 𝒞} (hy : y ∈ Proj.basicOpen 𝒞 s)
    (m : twistAway 𝒞 hs hi n)
    (h : (Proj.twist 𝒞 n).presheaf.germ _ y hy (twistSection 𝒞 hs hi n m) = 0) :
    ∃ u : Away 𝒞 s, IsUnit ((Proj 𝒞).presheaf.germ _ y hy (Proj.awayToSection 𝒞 s u)) ∧
      u.val * (m : Localization.Away s) = 0 := by
  have h0 := apply_eq_zero_of_germ_eq_zero 𝒞 n hy _ h
  rw [twistSection_apply] at h0
  obtain ⟨p, k, a, ha, hp, hm⟩ := m.2
  rw [hm, toFiber_mk, Localization.mk_eq_mk', IsLocalization.mk'_eq_zero_iff] at h0
  obtain ⟨⟨t, ht⟩, htc⟩ := h0
  change t * a = 0 at htc
  have hnot : ¬ ∀ q, (DirectSum.decompose 𝒞 t q : C) ∈ y.asHomogeneousIdeal.toIdeal :=
    fun hall ↦ ht ((y.asHomogeneousIdeal.isHomogeneous.mem_iff).mpr hall)
  simp only [not_forall] at hnot
  obtain ⟨q, hq⟩ := hnot
  have htq : (DirectSum.decompose 𝒞 t q : C) * a = 0 := by
    have h1 := DirectSum.coe_decompose_mul_of_right_mem_of_le 𝒞 (a := t) ha (Nat.le_add_left p q)
    rw [Nat.add_sub_cancel] at h1
    rw [← h1, htc, DirectSum.decompose_zero]
    simp
  obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  have hdeg : (DirectSum.decompose 𝒞 t q : C) ^ (i' + 1) ∈ 𝒞 (q • (i' + 1)) := by
    have := SetLike.pow_mem_graded (i' + 1) (DirectSum.decompose 𝒞 t q).2
    rwa [smul_eq_mul, mul_comm, ← smul_eq_mul] at this
  refine ⟨Away.mk 𝒞 hs q _ hdeg, isUnit_germ_awayToSection_mk 𝒞 hs hy q _ hdeg
    (fun h ↦ hq (y.isPrime.mem_of_pow_mem _ h)), ?_⟩
  rw [Away.val_mk, hm, Localization.mk_mul, pow_succ, mul_assoc, htq, mul_zero, Localization.mk_zero]

include hs hi in
/-- Every `b ∈ O_y`, `y ∈ D₊(s)`, satisfies `germ τ * b = germ σ` with `τ, σ ∈ 𝒞_(s)` and `germ τ` a unit. -/
theorem exists_unit_germ_mul_eq_germ_awayToSection {y : Proj 𝒞} (hy : y ∈ Proj.basicOpen 𝒞 s)
    (b : (Proj 𝒞).presheaf.stalk y) :
    ∃ τ σ : Away 𝒞 s, IsUnit ((Proj 𝒞).presheaf.germ _ y hy (Proj.awayToSection 𝒞 s τ)) ∧
      (Proj 𝒞).presheaf.germ _ y hy (Proj.awayToSection 𝒞 s τ) * b =
        (Proj 𝒞).presheaf.germ _ y hy (Proj.awayToSection 𝒞 s σ) := by
  obtain ⟨W₁, hy₁, β, rfl⟩ := (Proj 𝒞).presheaf.exists_germ_eq b
  obtain ⟨W₂, hy₂, iW, q, c, d, hd, hβ⟩ :=
    (show (ProjectiveSpectrum.Proj.structureSheaf 𝒞).1.obj (op W₁) from β).2 ⟨y, hy₁⟩
  obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
  have hdi : (d : C) ^ (i' + 1) ∈ 𝒞 (q • (i' + 1)) := by
    have := SetLike.pow_mem_graded (i' + 1) d.2
    rwa [smul_eq_mul, mul_comm, ← smul_eq_mul] at this
  have hcd : (c : C) * d ^ i' ∈ 𝒞 (q • (i' + 1)) := by
    have := SetLike.mul_mem_graded c.2 (SetLike.pow_mem_graded i' d.2)
    rwa [show q + i' • q = q • (i' + 1) by simp only [smul_eq_mul]; ring] at this
  refine ⟨Away.mk 𝒞 hs q _ hdi, Away.mk 𝒞 hs q _ hcd, isUnit_germ_awayToSection_mk 𝒞 hs hy q _ hdi
    (fun h ↦ hd ⟨y, hy₂⟩ (y.isPrime.mem_of_pow_mem _ h)), ?_⟩
  let W₃ : (Proj 𝒞).Opens := W₂ ⊓ Proj.basicOpen 𝒞 s
  have hy₃ : y ∈ W₃ := ⟨hy₂, hy⟩
  have hW₁ : W₃ ≤ W₁ := inf_le_left.trans (leOfHom iW)
  have hWs : W₃ ≤ Proj.basicOpen 𝒞 s := inf_le_right
  rw [← (Proj 𝒞).presheaf.germ_res_apply (homOfLE hWs) y hy₃ (Proj.awayToSection 𝒞 s (Away.mk 𝒞 hs q _ hdi)),
    ← (Proj 𝒞).presheaf.germ_res_apply (homOfLE hWs) y hy₃ (Proj.awayToSection 𝒞 s (Away.mk 𝒞 hs q _ hcd)),
    ← (Proj 𝒞).presheaf.germ_res_apply (homOfLE hW₁) y hy₃ β, ← map_mul]
  congr 1
  apply Subtype.ext
  funext z
  change ((Proj.awayToSection 𝒞 s (Away.mk 𝒞 hs q _ hdi) : (ProjectiveSpectrum.Proj.structureSheaf 𝒞).1.obj
      (op (Proj.basicOpen 𝒞 s))).1 ⟨z.1, hWs z.2⟩) * β.1 ⟨z.1, hW₁ z.2⟩ =
    (Proj.awayToSection 𝒞 s (Away.mk 𝒞 hs q _ hcd) : (ProjectiveSpectrum.Proj.structureSheaf 𝒞).1.obj
      (op (Proj.basicOpen 𝒞 s))).1 ⟨z.1, hWs z.2⟩
  rw [show β.1 ⟨z.1, hW₁ z.2⟩ = HomogeneousLocalization.mk ⟨q, c, d, hd ⟨z.1, z.2.1⟩⟩ from hβ ⟨z.1, z.2.1⟩]
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_mul, val_awayToSection_apply, val_awayToSection_apply, Away.val_mk,
    Away.val_mk, toFiber_mk, toFiber_mk, HomogeneousLocalization.val_mk, Localization.mk_mul,
    Localization.mk_eq_mk_iff]
  apply Localization.r_of_eq
  simp only [Submonoid.coe_mul]
  ring

/-- Every `μ ∈ O(n)_x`, `x ∈ D₊(s)`, is `v • germ (twistSection m)` with `v ∈ O_x`, `m ∈ (C_s)_n`. -/
theorem exists_smul_germ_twistSection_eq {x : Proj 𝒞} (hx : x ∈ Proj.basicOpen 𝒞 s)
    (μ : (Proj.twist 𝒞 n).presheaf.stalk x) :
    ∃ (v : (Proj 𝒞).presheaf.stalk x) (m : twistAway 𝒞 hs hi n),
      μ = v • (Proj.twist 𝒞 n).presheaf.germ _ x hx (twistSection 𝒞 hs hi n m) := by
  obtain ⟨W₁, hx₁, m₁, rfl⟩ := (Proj.twist 𝒞 n).presheaf.exists_germ_eq μ
  obtain ⟨W₂, hx₂, iW, hfrac⟩ := (show sectionsSubmodule 𝒞 n W₁ from m₁).2 ⟨x, hx₁⟩
  let W₃ : (Proj 𝒞).Opens := W₂ ⊓ Proj.basicOpen 𝒞 s
  have hx₃ : x ∈ W₃ := ⟨hx₂, hx⟩
  have hW₁ : W₃ ≤ W₁ := inf_le_left.trans (leOfHom iW)
  have hWs : W₃ ≤ Proj.basicOpen 𝒞 s := inf_le_right
  rcases hfrac with h0 | ⟨p, q, a, t, hpq, ht, hrep⟩
  · refine ⟨0, 0, ?_⟩
    have h1 : (Proj.twist 𝒞 n).presheaf.map (homOfLE hW₁).op m₁ = 0 :=
      Subtype.ext (funext fun z ↦ congrFun h0 ⟨z.1, z.2.1⟩)
    rw [zero_smul, ← (Proj.twist 𝒞 n).presheaf.germ_res_apply (homOfLE hW₁) x hx₃ m₁, h1, map_zero]
  · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    have hsq : (s ^ q : C) ∈ 𝒞 (q * (i' + 1)) := by
      simpa [smul_eq_mul] using SetLike.pow_mem_graded q hs
    have hti : (t : C) ^ (i' + 1) ∈ 𝒞 (q * (i' + 1)) := by
      have := SetLike.pow_mem_graded (i' + 1) t.2
      rwa [smul_eq_mul, mul_comm] at this
    have ht₃ : ∀ z : W₃, ((⟨(t : C) ^ (i' + 1), hti⟩ : 𝒞 (q * (i' + 1))) : C) ∉ z.1.asHomogeneousIdeal :=
      fun z hz ↦ ht ⟨z.1, z.2.1⟩ (z.1.isPrime.mem_of_pow_mem _ hz)
    have hp' : ((p + i' * q : ℕ) : ℤ) = q * (i' + 1) + n := by push_cast; linarith
    have hat : (a : C) * t ^ i' ∈ 𝒞 (p + i' * q) := by
      simpa [smul_eq_mul] using SetLike.mul_mem_graded a.2 (SetLike.pow_mem_graded i' t.2)
    refine ⟨(Proj 𝒞).presheaf.germ W₃ x hx₃ (fracSection 𝒞 W₃ ⟨s ^ q, hsq⟩ ⟨t ^ (i' + 1), hti⟩ ht₃),
      mkTwist 𝒞 hs hi n (p + i' * q) q hp' ⟨a * t ^ i', hat⟩, ?_⟩
    rw [← (Proj.twist 𝒞 n).presheaf.germ_res_apply (homOfLE hW₁) x hx₃ m₁,
      ← (Proj.twist 𝒞 n).presheaf.germ_res_apply (homOfLE hWs) x hx₃ (twistSection 𝒞 hs hi n _),
      ← germ_smul']
    congr 1
    apply Subtype.ext
    funext z
    change m₁.1 ⟨z.1, hW₁ z.2⟩ =
      (HomogeneousLocalization.mk ⟨q * (i' + 1), ⟨s ^ q, hsq⟩, ⟨t ^ (i' + 1), hti⟩, ht₃ z⟩).val *
        toFiber 𝒞 ⟨z.1, hWs z.2⟩ (Localization.mk ((a : C) * t ^ i') (⟨s ^ q, q, rfl⟩ : Submonoid.powers s))
    rw [show m₁.1 ⟨z.1, hW₁ z.2⟩ = Localization.mk (a : C) ⟨t, ht ⟨z.1, z.2.1⟩⟩ from hrep ⟨z.1, z.2.1⟩,
      HomogeneousLocalization.val_mk, toFiber_mk, Localization.mk_mul, Localization.mk_eq_mk_iff]
    apply Localization.r_of_eq
    simp only [Submonoid.coe_mul]
    ring

end Graded

/-! ## Compatibility with `Proj.map` -/

section Map

variable {R R' A B : Type u} [CommRing R] [CommRing R'] [Algebra R R'] [CommRing A] [Algebra R A]
  [CommRing B] [Algebra R B] [Algebra R' B] [IsScalarTower R R' B]
  (𝒜 : ℕ → Submodule R A) (ℬ : ℕ → Submodule R' B) [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
  (f : 𝒜 →+*ᵍ ℬ) (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
  {s : A} {i : ℕ} (hs : s ∈ 𝒜 i)

include hs in
/-- The stalk map of `ρ = Proj.map f hf` sends the germ of `awayToSection u` (`u ∈ 𝒜_(s)`) to the germ of
`awayToSection (Away.map f s u)` (Mathlib `Proj.awayToSection_comp_appLE`). -/
theorem stalkMap_germ_awayToSection (y : Proj ℬ) (hy : y ∈ Proj.basicOpen ℬ (f s)) (u : Away 𝒜 s) :
    (Proj.map f hf).stalkMap y ((Proj 𝒜).presheaf.germ (Proj.basicOpen 𝒜 s) ((Proj.map f hf).base y) hy
        (Proj.awayToSection 𝒜 s u)) =
      (Proj ℬ).presheaf.germ (Proj.basicOpen ℬ (f s)) y hy (Proj.awayToSection ℬ (f s) (Away.map f s u)) := by
  rw [Scheme.Hom.germ_stalkMap_apply]
  have h := Proj.awayToSection_comp_appLE f hf hs
  have h' := congrArg (fun φ : CommRingCat.of (Away 𝒜 s) ⟶ Γ(Proj ℬ, Proj.basicOpen ℬ (f s)) ↦ φ u) h
  rw [← Scheme.Hom.appLE_eq_app]
  exact congrArg _ h'

end Map

end MiyaokaMori.Stacks01n2TwistStalk

end
