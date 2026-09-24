import MiyaokaMori.Prelude
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.Ideal.Cotangent
import Mathlib.RingTheory.QuotSMulTop
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! # Nagata's retraction lemma for the maximal ideal

**Nagata's lemma** (Matsumura, *Commutative Ring Theory*, §19 Lemma 3 / the "𝔪/x𝔪 ≅ 𝔪/(x) ⊕ κ"
step in the proof of Thm 19.2; Bruns–Herzog, proof of Thm 2.2.7): let `(R, 𝔪, κ)` be a local
ring and `x ∈ 𝔪 ∖ 𝔪²`. Then the natural surjection `𝔪/x𝔪 → 𝔪/(x) = 𝔪 · (R/(x))` of `R/(x)`-modules
has an `R/(x)`-linear section; i.e. `𝔪/(x)` is a direct summand (retract) of `𝔪/x𝔪`.

Proof (self-contained). Write `A = 𝔪/x𝔪`, `B = 𝔪·R̄ ⊆ R̄ = R/(x)`, `π : A → B` the natural map
(`m mod x𝔪 ↦ m mod x`). Since `x ∉ 𝔪²`, its class in the `κ`-vector space `𝔪/𝔪²` is nonzero, so
there is a `κ`-linear functional `φ` on `𝔪/𝔪²` with `φ(x̄) = 1`; let `ℓ : 𝔪 → κ`, `ℓ = φ ∘ (𝔪 → 𝔪/𝔪²)`.
As `x𝔪 ⊆ 𝔪²`, `ℓ` factors through `ρ : A → κ`. Let `i : κ → A`, `i(c mod 𝔪) = (c x) mod x𝔪`
(well defined because `c ∈ 𝔪 ⇒ c x = x c ∈ x𝔪`). Then `ρ ∘ i = id_κ` (as `ℓ(c x) = c ℓ(x) = c̄`),
`π ∘ i = 0` (as `x ≡ 0 mod (x)`), and `ker π = im i` (if `m ≡ 0 mod (x)` then `m = c x`).
Hence `p = id_A − i ∘ ρ` kills `ker π`, so it factors through `A/ker π ≅ B` as `s : B → A`, and
`π ∘ s = π ∘ p = π − (π ∘ i) ∘ ρ = π` on `A`, i.e. `π ∘ s = id_B`. All maps are `R`-linear
between `R̄`-modules, hence `R̄`-linear since `R → R̄` is surjective.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open IsLocalRing
open scoped Pointwise

noncomputable section

/-- **Nagata's lemma**: for `x ∈ 𝔪 ∖ 𝔪²`, the natural `R/(x)`-linear surjection
`𝔪/x𝔪 → 𝔪 · (R/(x))` has a section (`π ∘ s = id`), so `𝔪 · (R/(x))` is a retract of `𝔪/x𝔪`
(Matsumura CRT §19, proof of Thm 19.2). -/
theorem IsLocalRing.exists_retraction_quotSMulTop_maximalIdeal
    {R : Type u} [CommRing R] [IsLocalRing R] {x : R} (hx : x ∈ maximalIdeal R)
    (hx2 : x ∉ maximalIdeal R ^ 2) :
    ∃ (π : QuotSMulTop x (maximalIdeal R) →ₗ[R ⧸ Ideal.span {x}]
          (maximalIdeal R).map (Ideal.Quotient.mk (Ideal.span {x})))
      (s : (maximalIdeal R).map (Ideal.Quotient.mk (Ideal.span {x})) →ₗ[R ⧸ Ideal.span {x}]
          QuotSMulTop x (maximalIdeal R)),
      π ∘ₗ s = LinearMap.id := by
  classical
  set mk := Ideal.Quotient.mk (Ideal.span {x}) with hmk
  have hsurj : Function.Surjective (algebraMap R (R ⧸ Ideal.span {x})) :=
    Ideal.Quotient.mk_surjective
  have hmkx : mk x = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self x)
  have hmkx' : Ideal.Quotient.mk (Ideal.span {x}) x = 0 := hmkx
  -- `π₀ : 𝔪 → 𝔪·R̄`
  let π₀ : maximalIdeal R →ₗ[R] (maximalIdeal R).map mk :=
    { toFun := fun m => ⟨mk m, Ideal.mem_map_of_mem mk m.2⟩
      map_add' := fun a b => by ext; simp
      map_smul' := fun r a => by ext; simp [Algebra.smul_def, hmk] }
  have hπ₀ : x • (⊤ : Submodule R (maximalIdeal R)) ≤ LinearMap.ker π₀ := by
    intro a ha
    obtain ⟨b, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists a x ⊤).mp ha
    ext
    simp [π₀, Algebra.smul_def, hmkx']
  let πR : QuotSMulTop x (maximalIdeal R) →ₗ[R] (maximalIdeal R).map mk :=
    Submodule.liftQ _ π₀ hπ₀
  have hπR : ∀ m : maximalIdeal R, (πR (Submodule.Quotient.mk m) : R ⧸ Ideal.span {x}) = mk m :=
    fun m => rfl
  have hπsurj : Function.Surjective πR := by
    rintro ⟨b, hb⟩
    obtain ⟨m, hm, rfl⟩ := (Ideal.mem_map_iff_of_surjective mk Ideal.Quotient.mk_surjective).mp hb
    exact ⟨Submodule.Quotient.mk ⟨m, hm⟩, rfl⟩
  -- a functional `ℓ : 𝔪 → κ` with `ℓ x = 1` and `ℓ (𝔪²) = 0`
  have hxbar : (maximalIdeal R).toCotangent ⟨x, hx⟩ ≠ 0 := by
    rw [Ne, Ideal.toCotangent_eq_zero]; exact hx2
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual (ResidueField R) (CotangentSpace R),
      φ ((maximalIdeal R).toCotangent ⟨x, hx⟩) = 1 := by
    have := (Module.forall_dual_apply_eq_zero_iff (ResidueField R)
      ((maximalIdeal R).toCotangent ⟨x, hx⟩)).not.mpr hxbar
    push Not at this
    obtain ⟨φ₀, hφ₀⟩ := this
    refine ⟨(φ₀ ((maximalIdeal R).toCotangent ⟨x, hx⟩))⁻¹ • φ₀, ?_⟩
    rw [LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hφ₀]
  let ℓ : maximalIdeal R →ₗ[R] ResidueField R :=
    (φ.restrictScalars R) ∘ₗ (maximalIdeal R).toCotangent
  have hℓx : ℓ ⟨x, hx⟩ = 1 := hφ
  have hresx : residue R x = 0 := (residue_eq_zero_iff x).mpr hx
  have hℓ : x • (⊤ : Submodule R (maximalIdeal R)) ≤ LinearMap.ker ℓ := by
    intro a ha
    obtain ⟨b, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists a x ⊤).mp ha
    rw [LinearMap.mem_ker, map_smul, Algebra.smul_def, ResidueField.algebraMap_eq, hresx, zero_mul]
  let ρ : QuotSMulTop x (maximalIdeal R) →ₗ[R] ResidueField R := Submodule.liftQ _ ℓ hℓ
  -- `i : κ → 𝔪/x𝔪`, `i (c mod 𝔪) = [c x]`
  let i₀ : R →ₗ[R] QuotSMulTop x (maximalIdeal R) :=
    (Submodule.mkQ _) ∘ₗ (LinearMap.toSpanSingleton R (maximalIdeal R) ⟨x, hx⟩)
  have hi₀ : maximalIdeal R ≤ LinearMap.ker i₀ := by
    intro c hc
    rw [LinearMap.mem_ker]
    show Submodule.Quotient.mk (c • (⟨x, hx⟩ : maximalIdeal R)) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    have : c • (⟨x, hx⟩ : maximalIdeal R) = x • ⟨c, hc⟩ := Subtype.ext (mul_comm c x)
    rw [this]
    exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top
  let i : ResidueField R →ₗ[R] QuotSMulTop x (maximalIdeal R) :=
    Submodule.liftQ (maximalIdeal R) i₀ hi₀
  have hi : ∀ c : R, i (residue R c) = Submodule.Quotient.mk (c • (⟨x, hx⟩ : maximalIdeal R)) :=
    fun c => rfl
  have hρi : ∀ q, ρ (i q) = q := by
    intro q
    obtain ⟨c, rfl⟩ := residue_surjective (R := R) q
    rw [hi]
    show ℓ (c • ⟨x, hx⟩) = residue R c
    rw [map_smul, hℓx, Algebra.smul_def, ResidueField.algebraMap_eq, mul_one]
  have hπi : ∀ q, πR (i q) = 0 := by
    intro q
    obtain ⟨c, rfl⟩ := residue_surjective (R := R) q
    rw [hi]
    ext
    show mk (c * x) = 0
    rw [map_mul, hmkx, mul_zero]
  let p : QuotSMulTop x (maximalIdeal R) →ₗ[R] QuotSMulTop x (maximalIdeal R) :=
    LinearMap.id - i ∘ₗ ρ
  have hpi : ∀ q, p (i q) = 0 := by
    intro q
    simp [p, hρi]
  have hker : LinearMap.ker πR ≤ LinearMap.ker p := by
    intro a ha
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    have hm : mk (m : R) = 0 := by
      have := congrArg Subtype.val ha
      simpa [hπR] using this
    rw [hmk, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton'] at hm
    obtain ⟨c, hc⟩ := hm
    have hmi : (Submodule.Quotient.mk m : QuotSMulTop x (maximalIdeal R)) = i (residue R c) := by
      rw [hi]
      congr 1
      ext
      simp [hc]
    rw [LinearMap.mem_ker, hmi, hpi]
  let pbar : (QuotSMulTop x (maximalIdeal R) ⧸ LinearMap.ker πR) →ₗ[R]
      QuotSMulTop x (maximalIdeal R) := Submodule.liftQ _ p hker
  let e := LinearMap.quotKerEquivOfSurjective πR hπsurj
  let sR : (maximalIdeal R).map mk →ₗ[R] QuotSMulTop x (maximalIdeal R) :=
    pbar ∘ₗ e.symm.toLinearMap
  have hsec : πR ∘ₗ sR = LinearMap.id := by
    apply LinearMap.ext
    intro b
    obtain ⟨a, rfl⟩ := hπsurj b
    have h1 : sR (πR a) = p a := by
      simp only [sR, e, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearMap.quotKerEquivOfSurjective_symm_apply]
      rfl
    rw [LinearMap.comp_apply, h1, LinearMap.id_apply]
    simp [p, hπi]
  refine ⟨πR.extendScalarsOfSurjective hsurj, sR.extendScalarsOfSurjective hsurj, ?_⟩
  apply LinearMap.ext
  intro b
  exact LinearMap.congr_fun hsec b

end
