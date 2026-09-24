import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotLineAffineOverBaseAwayMapBijective

/-! # Points of `V₊(T)` in the image of `fromOfGlobalSections`

Used for `totalSpace.mem_range_lSection_of_not_mem_basicOpen_oCoordinate` (`TotLineAffineOverBase.lean`:
`Tot(L) ⊂ P(O ⊕ L)` is the complement of a section, Corollary 4.3 of the paper; Stacks 01O4,
01M9): "`V₊(T) ⊆ σ_L(W)` on a chart".

Setting: `A` a graded ring, `Y` an affine scheme, `f : A →+* Γ(Y, ⊤)` with `f(A₊) = ⊤`, `T, s ∈ A₁` with
`f(T) = 0` (implicitly), `f(s)` a unit, such that
* (`h0`) every global function on `Y` is `f` of a degree-zero element,
* (`hker`) the kernel of `f` on every homogeneous piece lies in `(T)`.
(In the application `A = A(W) = R[T, s]`, `R = Γ(W, O)`, `f = ψ_W` the local piece of the `L`-section: `T ↦ 0`,
`s ↦ 1`, identity on `R`.)

**Statement** (`mem_range_fromOfGlobalSections_of_forall_mem_span`): every `q ∈ Proj A` with `q ∉ D₊(T)` is in the
image of `fromOfGlobalSections f : Y ⟶ Proj A`.

**Proof.**
1. `q ∈ D₊(s)`: otherwise `T, s ∈ q`, and every homogeneous `a` of positive degree `k` is `(a - r s^k) + r s^k`
   with `f(r) = f(a) f(s)^{-k}` (`h0`), where `a - r s^k ∈ ker f ∩ A_k ⊆ (T)` (`hker`); so `A₊ ⊆ q`, contradicting
   the relevance of `q` (`mem_span_pair_of_forall_mem_span`, `mem_basicOpen_of_not_mem_basicOpen`).
2. Under `basicOpenIsoSpec : D₊(s) ≅ Spec (A_s)_0`, `q` goes to a prime `𝔮`; a fraction `a/s^n` with `a ∈ q` lies in
   `𝔮` (`mem_asIdeal_of_mem`; Mathlib `Proj.awayι_preimage_basicOpen` for `n > 0`, and `a/1 = as/s` for `n = 0`).
3. The degree-zero fraction map `ρ : (A_s)_0 → Γ(Y, ⊤)[1/f s]`, `a/s^n ↦ f(a)/f(s)^n`, is surjective
   (`awayMapOfGlobalSections_surjective`: `f(s)` is a unit and `h0`), so `range (Spec ρ) = V(ker ρ)`
   (`PrimeSpectrum.range_comap_of_surjective`); `ker ρ ⊆ 𝔮` because `ρ(a/s^n) = 0` forces `f(a) = 0`, hence
   `a ∈ (T) ⊆ q`, hence `a/s^n ∈ 𝔮` (step 2). So `𝔮 = Spec(ρ)(p)` for some `p`.
4. `fromOfGlobalSections f` restricted to `D(f s) = Y` is `toSpecAway ≫ Spec ρ ≫ basicOpenIsoSpec⁻¹` followed by
   `D₊(s).ι` (`basicOpen_ι_comp_fromOfGlobalSections`, `toBasicOpenOfGlobalSections_eq`), and `toSpecAway` is an
   isomorphism on the affine `Y` (`isIso_toSpecAway`), so `p = toSpecAway(y)` and `fromOfGlobalSections f (y) = q`.

Edge cases: `A = 0` or `Y = ∅` (no points, vacuous); `k = 0` in `hker` is allowed (then `a ∈ (T)` means
`f a = 0 → a = 0` on `A_0` when `A_0 ∩ (T) = 0`, which is what the application provides). -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Proj

variable {σ : Type u} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]
variable {X : AlgebraicGeometry.Scheme.{u}} (f : A →+* Γ(X, ⊤))

/-- Every homogeneous element of positive degree lies in `(T, s)` when `ker f ∩ A_k ⊆ (T)`, `f s` is a unit and
`f` is onto in degree zero: `a = (a - r s^k) + r s^k` with `f r = f a · f(s)^{-k}`. -/
theorem mem_span_pair_of_forall_mem_span {T s : A} (hs : s ∈ 𝒜 1) (hfs : IsUnit (f s))
    (h0 : ∀ r : Γ(X, ⊤), ∃ a ∈ 𝒜 0, f a = r)
    (hker : ∀ (k : ℕ) (a : A), a ∈ 𝒜 k → f a = 0 → a ∈ Ideal.span {T})
    (k : ℕ) (hk : 0 < k) (a : A) (ha : a ∈ 𝒜 k) : a ∈ Ideal.span {T, s} := by
  obtain ⟨r, hr, hfr⟩ := h0 (f a * ((hfs.unit⁻¹ : Γ(X, ⊤)ˣ) : Γ(X, ⊤)) ^ k)
  have hrs : r * s ^ k ∈ 𝒜 k := by
    have h := SetLike.mul_mem_graded hr (SetLike.pow_mem_graded k hs)
    rwa [zero_add, smul_eq_mul, mul_one] at h
  have hdiff : a - r * s ^ k ∈ Ideal.span {T} := by
    refine hker k _ (sub_mem ha hrs) ?_
    rw [map_sub, map_mul, map_pow, hfr, mul_assoc, ← mul_pow, IsUnit.val_inv_mul, one_pow, mul_one, sub_self]
  have h1 : Ideal.span ({T} : Set A) ≤ Ideal.span {T, s} :=
    Ideal.span_mono (Set.singleton_subset_iff.mpr (Set.mem_insert T {s}))
  have h2 : s ∈ Ideal.span ({T, s} : Set A) := Ideal.subset_span (Set.mem_insert_of_mem T rfl)
  have h3 : r * s ^ k ∈ Ideal.span ({T, s} : Set A) :=
    Ideal.mul_mem_left _ r (Ideal.pow_mem_of_mem _ h2 k hk)
  have h4 : a - r * s ^ k ∈ Ideal.span ({T, s} : Set A) := h1 hdiff
  have h5 := Ideal.add_mem _ h4 h3
  rwa [sub_add_cancel] at h5

/-- **`q ∉ D₊(T)` implies `q ∈ D₊(s)`**: a relevant prime cannot contain both `T` and `s` when `A₊ ⊆ (T, s)`. -/
theorem mem_basicOpen_of_not_mem_basicOpen {T s : A} (hT : T ∈ 𝒜 1) (hs : s ∈ 𝒜 1) (hfs : IsUnit (f s))
    (h0 : ∀ r : Γ(X, ⊤), ∃ a ∈ 𝒜 0, f a = r)
    (hker : ∀ (k : ℕ) (a : A), a ∈ 𝒜 k → f a = 0 → a ∈ Ideal.span {T})
    (q : AlgebraicGeometry.Proj 𝒜) (hq : q ∉ AlgebraicGeometry.Proj.basicOpen 𝒜 T) :
    q ∈ AlgebraicGeometry.Proj.basicOpen 𝒜 s := by
  have hTq : T ∈ q.asHomogeneousIdeal := by
    by_contra h
    exact hq ((AlgebraicGeometry.Proj.mem_basicOpen 𝒜 T q).mpr h)
  rw [AlgebraicGeometry.Proj.mem_basicOpen]
  intro hsq
  apply ProjectiveSpectrum.not_irrelevant_le q
  rw [HomogeneousIdeal.irrelevant_le]
  intro i hi a ha
  have hTs : Ideal.span {T, s} ≤ q.asHomogeneousIdeal.toIdeal := by
    rw [Ideal.span_le]
    rintro x hx
    rcases hx with rfl | rfl
    · exact hTq
    · exact hsq
  exact hTs (mem_span_pair_of_forall_mem_span 𝒜 f hs hfs h0 hker i hi a ha)

/-- **The degree-zero fraction map is surjective** when `f s` is a unit and `f` is onto in degree zero. -/
theorem awayMapOfGlobalSections_surjective {s : A} (hs : s ∈ 𝒜 1) (hfs : IsUnit (f s))
    (h0 : ∀ r : Γ(X, ⊤), ∃ a ∈ 𝒜 0, f a = r) :
    Function.Surjective (awayMapOfGlobalSections 𝒜 f s) := by
  intro z
  obtain ⟨⟨r, m⟩, hz⟩ := IsLocalization.surj (Submonoid.powers (f s)) z
  obtain ⟨n, hn⟩ := m.2
  simp only at hz
  obtain ⟨a, ha, hfa⟩ := h0 (r * ((hfs.unit⁻¹ : Γ(X, ⊤)ˣ) : Γ(X, ⊤)) ^ n)
  have ha0 : a ∈ 𝒜 (0 • 1) := by rwa [zero_smul]
  refine ⟨HomogeneousLocalization.Away.mk 𝒜 hs 0 a ha0, ?_⟩
  rw [awayMapOfGlobalSections_mk, hfa, IsLocalization.mk'_eq_iff_eq_mul]
  have hm : (m : Γ(X, ⊤)) = f s ^ n := hn.symm
  change algebraMap Γ(X, ⊤) (Localization.Away (f s)) (r * ((hfs.unit⁻¹ : Γ(X, ⊤)ˣ) : Γ(X, ⊤)) ^ n) =
    z * algebraMap Γ(X, ⊤) (Localization.Away (f s)) (f s ^ 0)
  rw [pow_zero, map_one, mul_one, map_mul, ← hz, hm, mul_assoc, ← map_mul, ← mul_pow, IsUnit.mul_val_inv, one_pow,
    map_one, mul_one]

/-- A fraction `a / s^n` (`n > 0`) with `a ∈ q` lies in the prime `𝔮` corresponding to `q ∈ D₊(s)` under
`basicOpenIsoSpec` (Mathlib `Proj.awayι_preimage_basicOpen`). -/
theorem mem_asIdeal_of_mem_of_pos {s : A} (hs : s ∈ 𝒜 1) (q : AlgebraicGeometry.Proj 𝒜)
    (hqs : q ∈ AlgebraicGeometry.Proj.basicOpen 𝒜 s) (n : ℕ) (hn : 0 < n) (a : A) (ha : a ∈ 𝒜 (n • 1))
    (haq : a ∈ q.asHomogeneousIdeal) :
    HomogeneousLocalization.Away.mk 𝒜 hs n a ha ∈
      ((AlgebraicGeometry.Proj.basicOpenIsoSpec 𝒜 s hs one_pos).hom.base ⟨q, hqs⟩).asIdeal := by
  set 𝔮 := (AlgebraicGeometry.Proj.basicOpenIsoSpec 𝒜 s hs one_pos).hom.base ⟨q, hqs⟩ with h𝔮
  have ha' : a ∈ 𝒜 n := by simpa using ha
  have hq' : (AlgebraicGeometry.Proj.awayι 𝒜 s hs one_pos).base 𝔮 = q := by
    show ((AlgebraicGeometry.Proj.basicOpenIsoSpec 𝒜 s hs one_pos).hom ≫
      (AlgebraicGeometry.Proj.basicOpenIsoSpec 𝒜 s hs one_pos).inv ≫
        (AlgebraicGeometry.Proj.basicOpen 𝒜 s).ι).base ⟨q, hqs⟩ = q
    rw [Iso.hom_inv_id_assoc]
    rfl
  have hpre := AlgebraicGeometry.Proj.awayι_preimage_basicOpen 𝒜 hs one_pos ha' hn
  have hx : HomogeneousLocalization.Away.mk 𝒜 hs n a ha =
      HomogeneousLocalization.Away.isLocalizationElem hs ha' := by
    apply HomogeneousLocalization.val_injective
    rw [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.isLocalizationElem,
      HomogeneousLocalization.Away.val_mk, pow_one]
  rw [hx]
  by_contra hnot
  have hmem : 𝔮 ∈ PrimeSpectrum.basicOpen (HomogeneousLocalization.Away.isLocalizationElem hs ha') := hnot
  rw [← hpre] at hmem
  have : (AlgebraicGeometry.Proj.awayι 𝒜 s hs one_pos).base 𝔮 ∈ AlgebraicGeometry.Proj.basicOpen 𝒜 a := hmem
  rw [hq', AlgebraicGeometry.Proj.mem_basicOpen] at this
  exact this haq

/-- A fraction `a / s^n` with `a ∈ q` lies in the prime corresponding to `q ∈ D₊(s)` (all `n`; for `n = 0` use
`a / 1 = a s / s`). -/
theorem mem_asIdeal_of_mem {s : A} (hs : s ∈ 𝒜 1) (q : AlgebraicGeometry.Proj 𝒜)
    (hqs : q ∈ AlgebraicGeometry.Proj.basicOpen 𝒜 s) (n : ℕ) (a : A) (ha : a ∈ 𝒜 (n • 1))
    (haq : a ∈ q.asHomogeneousIdeal) :
    HomogeneousLocalization.Away.mk 𝒜 hs n a ha ∈
      ((AlgebraicGeometry.Proj.basicOpenIsoSpec 𝒜 s hs one_pos).hom.base ⟨q, hqs⟩).asIdeal := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have h' : a * s ∈ 𝒜 (1 • 1) := by
      have := SetLike.mul_mem_graded ha hs
      simpa using this
    have hx : HomogeneousLocalization.Away.mk 𝒜 hs 0 a ha = HomogeneousLocalization.Away.mk 𝒜 hs 1 (a * s) h' := by
      apply HomogeneousLocalization.val_injective
      rw [HomogeneousLocalization.Away.val_mk, HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk_iff,
        Localization.r_iff_exists]
      exact ⟨1, by simp [mul_comm]⟩
    rw [hx]
    exact mem_asIdeal_of_mem_of_pos 𝒜 hs q hqs 1 one_pos (a * s) h' (Ideal.mul_mem_right s _ haq)
  · exact mem_asIdeal_of_mem_of_pos 𝒜 hs q hqs n hn a ha haq

/-- **Points outside `D₊(T)` are in the image of `fromOfGlobalSections`** (see the module docstring). -/
theorem mem_range_fromOfGlobalSections_of_forall_mem_span [AlgebraicGeometry.IsAffine X]
    (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤) {T s : A} (hT : T ∈ 𝒜 1) (hs : s ∈ 𝒜 1)
    (hfs : IsUnit (f s)) (h0 : ∀ r : Γ(X, ⊤), ∃ a ∈ 𝒜 0, f a = r)
    (hker : ∀ (k : ℕ) (a : A), a ∈ 𝒜 k → f a = 0 → a ∈ Ideal.span {T})
    (q : AlgebraicGeometry.Proj 𝒜) (hq : q ∉ AlgebraicGeometry.Proj.basicOpen 𝒜 T) :
    q ∈ Set.range (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 f hf).base := by
  have hTq : T ∈ q.asHomogeneousIdeal := by
    by_contra h
    exact hq ((AlgebraicGeometry.Proj.mem_basicOpen 𝒜 T q).mpr h)
  have hqs : q ∈ AlgebraicGeometry.Proj.basicOpen 𝒜 s :=
    mem_basicOpen_of_not_mem_basicOpen 𝒜 f hT hs hfs h0 hker q hq
  set ρ := awayMapOfGlobalSections 𝒜 f s with hρ
  set 𝔮 := (AlgebraicGeometry.Proj.basicOpenIsoSpec 𝒜 s hs one_pos).hom.base ⟨q, hqs⟩ with h𝔮
  have hsurj : Function.Surjective ρ := awayMapOfGlobalSections_surjective 𝒜 f hs hfs h0
  -- `𝔮` is in the image of `Spec ρ`
  have hmem : 𝔮 ∈ Set.range (AlgebraicGeometry.Spec.map (CommRingCat.ofHom ρ)).base := by
    have hr : Set.range (AlgebraicGeometry.Spec.map (CommRingCat.ofHom ρ)).base =
        PrimeSpectrum.zeroLocus (RingHom.ker ρ : Set (HomogeneousLocalization.Away 𝒜 s)) :=
      range_comap_of_surjective _ _ hsurj
    rw [hr]
    refine (PrimeSpectrum.mem_zeroLocus _ _).mpr (fun x hx => ?_)
    obtain ⟨n, a, ha, rfl⟩ := HomogeneousLocalization.Away.mk_surjective 𝒜 hs x
    have hx' : ρ (HomogeneousLocalization.Away.mk 𝒜 hs n a ha) = 0 := hx
    rw [hρ, awayMapOfGlobalSections_mk, IsLocalization.mk'_eq_zero_iff] at hx'
    obtain ⟨⟨m, j, rfl⟩, hm⟩ := hx'
    have hfa : f a = 0 := ((hfs.pow j).mul_right_eq_zero).mp hm
    have haT : a ∈ Ideal.span {T} := hker (n • 1) a ha hfa
    have haq : a ∈ q.asHomogeneousIdeal := by
      have hle : Ideal.span {T} ≤ q.asHomogeneousIdeal.toIdeal := by
        rw [Ideal.span_le, Set.singleton_subset_iff]
        exact hTq
      exact hle haT
    exact mem_asIdeal_of_mem 𝒜 hs q hqs n a ha haq
  obtain ⟨p, hp⟩ := hmem
  have hiso := isIso_toSpecAway (X := X) (f s)
  obtain ⟨y, hy⟩ := (AlgebraicGeometry.Scheme.Hom.homeomorph
    (AlgebraicGeometry.Scheme.projBundle.toSpecAway X (f s))).surjective p
  refine ⟨(X.basicOpen (f s)).ι.base y, ?_⟩
  have h1 := congrArg (fun k => k.base y) (basicOpen_ι_comp_fromOfGlobalSections 𝒜 f hf one_pos hs)
  simp only at h1
  change ((X.basicOpen (f s)).ι ≫ AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 f hf).base y = q
  rw [h1, toBasicOpenOfGlobalSections_eq]
  change (AlgebraicGeometry.Proj.basicOpen 𝒜 s).ι.base
    ((AlgebraicGeometry.Proj.basicOpenIsoSpec 𝒜 s hs one_pos).inv.base
      ((AlgebraicGeometry.Spec.map (CommRingCat.ofHom ρ)).base
        ((AlgebraicGeometry.Scheme.projBundle.toSpecAway X (f s)).base y))) = q
  have hy' : (AlgebraicGeometry.Scheme.projBundle.toSpecAway X (f s)).base y = p := hy
  rw [hy', hp, h𝔮]
  change (AlgebraicGeometry.Proj.basicOpen 𝒜 s).ι.base
    (((AlgebraicGeometry.Proj.basicOpenIsoSpec 𝒜 s hs one_pos).hom ≫
      (AlgebraicGeometry.Proj.basicOpenIsoSpec 𝒜 s hs one_pos).inv).base ⟨q, hqs⟩) = q
  rw [Iso.hom_inv_id]
  rfl

end AlgebraicGeometry.Proj

end
