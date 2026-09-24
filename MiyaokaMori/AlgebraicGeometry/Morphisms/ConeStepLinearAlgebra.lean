import MiyaokaMori.Prelude

/-! # Linear algebra of one step of a mapping cone

Over a commutative ring `R`, consider `U --b--> X₁ --d--> X₀` and `φ : F → X₀`, let `M = X₁ ⊕ F`
(given by abstract biproduct data `inl`, `inr`, `fst`, `snd`), let `g = (d, φ) : M → X₀` be
surjective, let `ι : Z → M` be injective with `range ι = ker g`, and let `a : U → Z` satisfy
`ι ∘ a = inl ∘ b` (i.e. `a = (b, 0)`). Then
(1) `ker a = ker b`;
(2) there is a four-term exact sequence
    `0 → ker d / im b --σ--> Z / im a --π--> F --ψ--> X₀ / im d → 0`;
(3) if `R` is a field and `F`, `Z / im a` are finite-dimensional, then `ker d / im b` and
    `X₀ / im d` are finite-dimensional and
    `dim(Z/im a) + dim(X₀/im d) = dim(ker d/im b) + dim F`;
(4) if `R` is Noetherian and `F`, `ker d / im b` are finite, then `Z / im a` is finite.

Proof.
1. (1): `ι` and `inl` are injective, so `ker a = ker (ι ∘ a) = ker (inl ∘ b) = ker b`.
2. (2): `π[z] := snd (ι z)` (zero on `im a` since `snd ∘ inl = 0`); `ψ := (X₀ → X₀/im d) ∘ φ`;
   `σ[x] := [z]`, where `z` is the unique solution of `ι z = inl x` (note `inl x ∈ ker g = range ι`
   because `g (inl x) = d x = 0`). Pointwise verification: `σ` is injective (`ι z = inl x` and
   `z = a u` give `inl x = inl (b u)`, so `x = b u`); `range σ = ker π` (`snd (ι z) = 0` gives
   `ι z = inl (fst (ι z))` by `inl ∘ fst + inr ∘ snd = id`); `range π = ker ψ` (`φ y = d x₁` gives
   `inr y − inl x₁ ∈ ker g = range ι`); `ψ` is surjective (`g` is surjective and
   `g m = d (fst m) + φ (snd m)`).
3. (3): rank–nullity for `π` and `ψ`; (4): `Module.Finite.of_exact`, since `range π ≤ F` is finite
   over a Noetherian ring.

This is the top two degrees of the long exact sequence of a mapping cone, a step in the proof of
Hartshorne III.12.3; it is used for the Euler characteristic of the fibres of the top complex.
-/

set_option autoImplicit false

universe u v

open LinearMap

/-- The homology `ker g / im f` at the middle term. -/
abbrev LinearMap.midHomology {R : Type u} [CommRing R] {U V W : Type v}
    [AddCommGroup U] [AddCommGroup V] [AddCommGroup W] [Module R U] [Module R V] [Module R W]
    (f : U →ₗ[R] V) (g : V →ₗ[R] W) : Type v :=
  LinearMap.ker g ⧸ (LinearMap.range f).submoduleOf (LinearMap.ker g)

namespace ConeStep

/-- Numerical consequence of a four-term exact sequence `0 → H → S → F → C → 0` over a field. -/
theorem finrank_of_four_term_exact {k : Type u} [Field k] {H S F C : Type v}
    [AddCommGroup H] [AddCommGroup S] [AddCommGroup F] [AddCommGroup C]
    [Module k H] [Module k S] [Module k F] [Module k C]
    (σ : H →ₗ[k] S) (π : S →ₗ[k] F) (ψ : F →ₗ[k] C)
    (hσ : Function.Injective σ) (h1 : Function.Exact σ π) (h2 : Function.Exact π ψ)
    (hψ : Function.Surjective ψ) [Module.Finite k F] [Module.Finite k S] :
    Module.Finite k H ∧ Module.Finite k C ∧
      Module.finrank k S + Module.finrank k C = Module.finrank k H + Module.finrank k F := by
  have hH : Module.Finite k H := Module.Finite.of_injective σ hσ
  have hC : Module.Finite k C := Module.Finite.of_surjective ψ hψ
  refine ⟨hH, hC, ?_⟩
  have e1 := LinearMap.finrank_range_add_finrank_ker π
  have e2 := LinearMap.finrank_range_add_finrank_ker ψ
  rw [LinearMap.exact_iff.mp h1, LinearMap.finrank_range_of_inj hσ] at e1
  rw [LinearMap.exact_iff.mp h2, LinearMap.range_eq_top.mpr hψ, finrank_top] at e2
  omega

/-- Finiteness consequence of a four-term exact sequence over a Noetherian ring. -/
theorem finite_of_four_term_exact {R : Type u} [CommRing R] [IsNoetherianRing R] {H S F : Type v}
    [AddCommGroup H] [AddCommGroup S] [AddCommGroup F]
    [Module R H] [Module R S] [Module R F]
    (σ : H →ₗ[R] S) (π : S →ₗ[R] F) (h1 : Function.Exact σ π)
    [Module.Finite R F] [Module.Finite R H] : Module.Finite R S := by
  have : IsNoetherian R F := isNoetherian_of_isNoetherianRing_of_finite R F
  have : Module.Finite R (LinearMap.range π) := Module.IsNoetherian.finite R _
  refine Module.Finite.of_exact (f := σ) (g := π.rangeRestrict) ?_ π.surjective_rangeRestrict
  intro s
  rw [← h1 s]
  constructor
  · intro h; simpa using congrArg Subtype.val h
  · intro h; exact Subtype.ext (by simpa using h)

section Main

variable {R : Type u} [CommRing R] {U Z M X₁ F X₀ : Type v}
  [AddCommGroup U] [AddCommGroup Z] [AddCommGroup M] [AddCommGroup X₁] [AddCommGroup F]
  [AddCommGroup X₀] [Module R U] [Module R Z] [Module R M] [Module R X₁] [Module R F] [Module R X₀]
  (a : U →ₗ[R] Z) (ι : Z →ₗ[R] M) (g : M →ₗ[R] X₀) (b : U →ₗ[R] X₁)
  (inl : X₁ →ₗ[R] M) (inr : F →ₗ[R] M) (fst : M →ₗ[R] X₁) (snd : M →ₗ[R] F)

/-- The hypotheses of the cone step: `ι` injective with `range ι = ker g`, `g` surjective,
`ι ∘ a = inl ∘ b`, and `inl`, `inr`, `fst`, `snd` biproduct data for `M = X₁ ⊕ F`. -/
structure Hyp : Prop where
  ι_inj : Function.Injective ι
  exact : Function.Exact ι g
  g_surj : Function.Surjective g
  comm : ι ∘ₗ a = inl ∘ₗ b
  fst_inl : fst ∘ₗ inl = LinearMap.id
  snd_inl : snd ∘ₗ inl = 0
  snd_inr : snd ∘ₗ inr = LinearMap.id
  total : inl ∘ₗ fst + inr ∘ₗ snd = LinearMap.id

variable {a ι g b inl inr fst snd}

theorem Hyp.inl_inj (h : Hyp a ι g b inl inr fst snd) : Function.Injective inl := by
  intro x y hxy
  have := congrArg fst hxy
  simpa [← LinearMap.comp_apply, h.fst_inl] using this

theorem Hyp.ker_eq (h : Hyp a ι g b inl inr fst snd) : LinearMap.ker a = LinearMap.ker b := by
  ext u
  simp only [LinearMap.mem_ker]
  constructor
  · intro hu
    apply h.inl_inj
    have := LinearMap.congr_fun h.comm u
    simp only [LinearMap.comp_apply] at this
    rw [← this, hu, map_zero, map_zero]
  · intro hu
    apply h.ι_inj
    have := LinearMap.congr_fun h.comm u
    simp only [LinearMap.comp_apply] at this
    rw [this, hu, map_zero, map_zero]


section Seq

/-- `ψ : F → X₀ / im d`, the composite of `φ = g ∘ inr` with the quotient map. -/
def Hyp.ψ (_h : Hyp a ι g b inl inr fst snd) : F →ₗ[R] (X₀ ⧸ LinearMap.range (g ∘ₗ inl)) :=
  (LinearMap.range (g ∘ₗ inl)).mkQ ∘ₗ g ∘ₗ inr

variable (h : Hyp a ι g b inl inr fst snd)
include h

theorem Hyp.g_decomp (m : M) : g m = g (inl (fst m)) + g (inr (snd m)) := by
  have := LinearMap.congr_fun h.total m
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply] at this
  rw [← map_add, this]

theorem Hyp.snd_ι_a (u : U) : snd (ι (a u)) = 0 := by
  have := LinearMap.congr_fun h.comm u
  simp only [LinearMap.comp_apply] at this
  rw [this]
  exact LinearMap.congr_fun h.snd_inl (b u)

/-- `π : Z / im a → F`, `[z] ↦ snd (ι z)`. -/
def Hyp.π : (Z ⧸ LinearMap.range a) →ₗ[R] F :=
  (LinearMap.range a).liftQ (snd ∘ₗ ι) (by
    rintro _ ⟨u, rfl⟩
    simpa using h.snd_ι_a u)

theorem Hyp.inl_mem_range (x : LinearMap.ker (g ∘ₗ inl)) : inl x.1 ∈ LinearMap.range ι := by
  rw [← LinearMap.exact_iff.mp h.exact]
  exact x.2

/-- `θ : ker d → Z`, characterised by `ι (θ x) = inl x`. -/
noncomputable def Hyp.θ : LinearMap.ker (g ∘ₗ inl) →ₗ[R] Z :=
  (LinearEquiv.ofInjective ι h.ι_inj).symm.toLinearMap ∘ₗ
    LinearMap.codRestrict (LinearMap.range ι) (inl ∘ₗ (LinearMap.ker (g ∘ₗ inl)).subtype)
      (fun x => h.inl_mem_range x)

theorem Hyp.ι_θ (x : LinearMap.ker (g ∘ₗ inl)) : ι (h.θ x) = inl x.1 := by
  unfold Hyp.θ
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [LinearEquiv.ofInjective_symm_apply]
  rfl

theorem Hyp.θ_mem (x : LinearMap.ker (g ∘ₗ inl))
    (hx : x ∈ (LinearMap.range b).submoduleOf (LinearMap.ker (g ∘ₗ inl))) :
    h.θ x ∈ LinearMap.range a := by
  obtain ⟨u, hu⟩ := hx
  refine ⟨u, h.ι_inj ?_⟩
  rw [h.ι_θ]
  have := LinearMap.congr_fun h.comm u
  simp only [LinearMap.comp_apply] at this
  rw [this]
  exact congrArg inl hu

/-- `σ : ker d / im b → Z / im a`, induced by `θ`. -/
noncomputable def Hyp.σ : LinearMap.midHomology b (g ∘ₗ inl) →ₗ[R] (Z ⧸ LinearMap.range a) :=
  Submodule.mapQ _ _ h.θ (fun x hx => h.θ_mem x hx)

theorem Hyp.σ_inj : Function.Injective h.σ := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro q hq
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  have hq' : h.θ x ∈ LinearMap.range a := by
    simpa [Hyp.σ, Submodule.mapQ_apply, Submodule.Quotient.mk_eq_zero] using hq
  obtain ⟨u, hu⟩ := hq'
  rw [Submodule.Quotient.mk_eq_zero]
  refine ⟨u, h.inl_inj ?_⟩
  have := LinearMap.congr_fun h.comm u
  simp only [LinearMap.comp_apply] at this
  rw [← this, hu, h.ι_θ]
  rfl

theorem Hyp.exact_σ_π : Function.Exact h.σ h.π := by
  intro s
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ s
  constructor
  · intro hz
    have hz' : snd (ι z) = 0 := by simpa [Hyp.π] using hz
    have hιz : ι z = inl (fst (ι z)) := by
      have := LinearMap.congr_fun h.total (ι z)
      simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply, hz', map_zero,
        add_zero] at this
      exact this.symm
    have hker : fst (ι z) ∈ LinearMap.ker (g ∘ₗ inl) := by
      rw [LinearMap.mem_ker, LinearMap.comp_apply, ← hιz]
      exact h.exact.apply_apply_eq_zero z
    refine ⟨Submodule.Quotient.mk ⟨fst (ι z), hker⟩, ?_⟩
    simp only [Hyp.σ, Submodule.mapQ_apply]
    congr 1
    apply h.ι_inj
    rw [h.ι_θ, ← hιz]
  · rintro ⟨q, hq⟩
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    rw [← hq]
    simp only [Hyp.σ, Submodule.mapQ_apply, Hyp.π, Submodule.liftQ_apply, LinearMap.comp_apply]
    rw [h.ι_θ]
    exact LinearMap.congr_fun h.snd_inl x.1

theorem Hyp.exact_π_ψ : Function.Exact h.π h.ψ := by
  intro y
  constructor
  · intro hy
    have hy' : g (inr y) ∈ LinearMap.range (g ∘ₗ inl) := by
      simpa [Hyp.ψ, Submodule.Quotient.mk_eq_zero] using hy
    obtain ⟨x₁, hx₁⟩ := hy'
    have hm : inr y - inl x₁ ∈ LinearMap.range ι := by
      rw [← LinearMap.exact_iff.mp h.exact, LinearMap.mem_ker, map_sub, ← hx₁]
      simp
    obtain ⟨z, hz⟩ := hm
    refine ⟨Submodule.Quotient.mk z, ?_⟩
    simp only [Hyp.π, Submodule.liftQ_apply, LinearMap.comp_apply, hz, map_sub]
    have e1 : snd (inl x₁) = 0 := LinearMap.congr_fun h.snd_inl x₁
    have e2 : snd (inr y) = y := LinearMap.congr_fun h.snd_inr y
    rw [e1, e2, sub_zero]
  · rintro ⟨s, rfl⟩
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ s
    have h0 : g (inl (fst (ι z))) + g (inr (snd (ι z))) = 0 := by
      rw [← h.g_decomp]; exact h.exact.apply_apply_eq_zero z
    show (LinearMap.range (g ∘ₗ inl)).mkQ (g (inr (snd (ι z)))) = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    refine ⟨-(fst (ι z)), ?_⟩
    rw [map_neg, LinearMap.comp_apply]
    exact (eq_neg_of_add_eq_zero_right h0).symm

theorem Hyp.ψ_surj : Function.Surjective h.ψ := by
  intro c
  obtain ⟨x₀, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  obtain ⟨m, rfl⟩ := h.g_surj x₀
  refine ⟨snd m, ?_⟩
  simp only [Hyp.ψ, LinearMap.comp_apply, Submodule.mkQ_apply]
  rw [h.g_decomp m, Submodule.Quotient.mk_add]
  have : Submodule.Quotient.mk (p := LinearMap.range (g ∘ₗ inl)) (g (inl (fst m))) = 0 := by
    rw [Submodule.Quotient.mk_eq_zero]; exact ⟨fst m, rfl⟩
  rw [this, zero_add]

/-- (4): over a Noetherian ring, `Z / im a` is finite. -/
theorem Hyp.finite_quotient [IsNoetherianRing R] [Module.Finite R F]
    [Module.Finite R (LinearMap.midHomology b (g ∘ₗ inl))] :
    Module.Finite R (Z ⧸ LinearMap.range a) :=
  finite_of_four_term_exact h.σ h.π h.exact_σ_π

end Seq

end Main

/-- (3): the dimension relation over a field. -/
theorem Hyp.finrank_eq {k : Type u} [Field k] {U Z M X₁ F X₀ : Type v}
    [AddCommGroup U] [AddCommGroup Z] [AddCommGroup M] [AddCommGroup X₁] [AddCommGroup F]
    [AddCommGroup X₀] [Module k U] [Module k Z] [Module k M] [Module k X₁] [Module k F] [Module k X₀]
    {a : U →ₗ[k] Z} {ι : Z →ₗ[k] M} {g : M →ₗ[k] X₀} {b : U →ₗ[k] X₁}
    {inl : X₁ →ₗ[k] M} {inr : F →ₗ[k] M} {fst : M →ₗ[k] X₁} {snd : M →ₗ[k] F}
    (h : Hyp a ι g b inl inr fst snd) [Module.Finite k F]
    [Module.Finite k (Z ⧸ LinearMap.range a)] :
    Module.Finite k (LinearMap.midHomology b (g ∘ₗ inl)) ∧
    Module.Finite k (X₀ ⧸ LinearMap.range (g ∘ₗ inl)) ∧
    Module.finrank k (Z ⧸ LinearMap.range a) + Module.finrank k (X₀ ⧸ LinearMap.range (g ∘ₗ inl))
      = Module.finrank k (LinearMap.midHomology b (g ∘ₗ inl)) + Module.finrank k F :=
  finrank_of_four_term_exact h.σ h.π h.ψ h.σ_inj h.exact_σ_π h.exact_π_ψ h.ψ_surj

end ConeStep
