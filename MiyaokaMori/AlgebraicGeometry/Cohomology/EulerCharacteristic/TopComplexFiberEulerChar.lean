import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Morphisms.ConeStepLinearAlgebra
import MiyaokaMori.RingTheory.Localization.FlatKernelOfSurjection

/-! # Euler characteristic of the fibres of a flat complex numbered from the top

Let `A` be a Noetherian ring and `T` a bounded complex of `A`-modules numbered from the top,
`X_0 ← X_1 ← X_2 ← …` (`d_j : X_{j+1} → X_j`, `d_j ∘ d_{j+1} = 0`; `X_0` is the top cohomological term),
with flat terms, `X_j = 0` for `j > ℓ`, and finite `A`-modules as homology (after the trivial base change to
`A`). Then for every prime `p` the homology of `T ⊗_A κ(p)` is finite-dimensional, and
`p ↦ Σ_{j ≤ ℓ} (−1)^j dim_{κ(p)} H_j(T ⊗ κ(p))` is locally constant on `Spec A`.

Proof: induction on `ℓ`.
1. `ℓ = 0`: `H_0 = X_0` is finite and flat, `A` Noetherian ⇒ finitely presented ⇒ projective;
   `dim κ(p) ⊗ X_0 = rankAtStalk X_0 p` (Mathlib `Module.rankAtStalk_eq`), locally constant
   (`Module.isLocallyConstant_rankAtStalk`).
2. `ℓ → ℓ+1`: `H_0(T) = X_0 / im d_0` is finite; choose a finite free `F = A^r` and `φ : F → X_0` with
   `F → H_0` surjective, so `g := (d_0, φ) : X_1 ⊕ F → X_0` is surjective. `Z := ker g` is flat (kernel of a
   surjection between flat modules). The new complex `T'`: `Z ← X_2 ← X_3 ← …` (`a := (d_1, 0) : X_2 → Z`)
   has length one less.
3. For every `A`-algebra `B`: `X_0` flat ⇒ `B ⊗ Z → B ⊗ (X_1 ⊕ F)` injective (Mathlib
   `LinearMap.lTensor_injective_of_exact_of_flat`), and right exactness of the tensor product ⇒ image
   `= ker (B ⊗ g)` and `B ⊗ g` surjective. Hence the cone-step linear algebra applies to the data after
   `B ⊗ (−)`: `H_{j+1}(T' ⊗ B) = H_{j+2}(T ⊗ B)` (by definition for `j ≥ 1`; for `j = 0` use
   `ker (B ⊗ a) = ker (B ⊗ d_1)`), and `0 → H_1(T ⊗ B) → H_0(T' ⊗ B) → B ⊗ F → H_0(T ⊗ B) → 0` is exact.
4. With `B = A`: the homology of `T'` is finite (`A` Noetherian), so the induction hypothesis applies to
   `T'`. With `B = κ(p)`: the homology of `T ⊗ κ(p)` is finite-dimensional, `h_0(T') + h_0(T) = h_1(T) + r`,
   so `Σ_{j ≤ ℓ+1} (−1)^j h_j(T) = r − Σ_{j ≤ ℓ} (−1)^j h_j(T')`, locally constant.

Source: Hartshorne III.12.2–12.3; Mumford, *Abelian Varieties*, §5; an elementary form of Stacks 0BDJ
(local constancy of `χ` for perfect complexes).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open TensorProduct

noncomputable section

/-- A complex numbered from the top: `X_0 ← X_1 ← X_2 ← …`. -/
structure TopCx (A : Type u) [CommRing A] where
  X : ℕ → ModuleCat.{u} A
  d : ∀ j, X (j + 1) →ₗ[A] X j
  d_comp : ∀ j, d j ∘ₗ d (j + 1) = 0

namespace TopCx

variable {A : Type u} [CommRing A] (T : TopCx A) (B : Type u) [CommRing B] [Algebra A B]

/-- The differential after base change. -/
abbrev dB (j : ℕ) : B ⊗[A] T.X (j + 1) →ₗ[B] B ⊗[A] T.X j := (T.d j).baseChange B

/-- The dimension of the `j`-th homology after base change. -/
def hdim : ℕ → ℕ
  | 0 => Module.finrank B ((B ⊗[A] T.X 0) ⧸ LinearMap.range (T.dB B 0))
  | j + 1 => Module.finrank B (LinearMap.midHomology (T.dB B (j + 1)) (T.dB B j))

/-- The `j`-th homology after base change is a finite `B`-module. -/
def hfin : ℕ → Prop
  | 0 => Module.Finite B ((B ⊗[A] T.X 0) ⧸ LinearMap.range (T.dB B 0))
  | j + 1 => Module.Finite B (LinearMap.midHomology (T.dB B (j + 1)) (T.dB B j))

/-- The `j`-th homology (before base change) is a finite `A`-module. -/
def fin0 : ℕ → Prop
  | 0 => Module.Finite A (T.X 0 ⧸ LinearMap.range (T.d 0))
  | j + 1 => Module.Finite A (LinearMap.midHomology (T.d (j + 1)) (T.d j))

end TopCx

/-- Two outgoing maps with the same kernel give the same middle homology. -/
theorem LinearMap.midHomology_congr_ker {R : Type u} [CommRing R] {U V W W' : Type u}
    [AddCommGroup U] [AddCommGroup V] [AddCommGroup W] [AddCommGroup W']
    [Module R U] [Module R V] [Module R W] [Module R W']
    (f : U →ₗ[R] V) (g : V →ₗ[R] W) (g' : V →ₗ[R] W') (hk : LinearMap.ker g = LinearMap.ker g') :
    Module.finrank R (LinearMap.midHomology f g) = Module.finrank R (LinearMap.midHomology f g') ∧
    (Module.Finite R (LinearMap.midHomology f g) ↔ Module.Finite R (LinearMap.midHomology f g')) := by
  unfold LinearMap.midHomology
  rw [hk]
  exact ⟨rfl, Iff.rfl⟩

namespace TopCx.Step

variable {A : Type u} [CommRing A] (T : TopCx A) {r : ℕ} (φ : (Fin r → A) →ₗ[A] T.X 0)

/-- `g = (d_0, φ) : X_1 ⊕ F → X_0`. -/
abbrev g : (T.X 1 × (Fin r → A)) →ₗ[A] T.X 0 := (T.d 0).coprod φ

/-- `a = (d_1, 0) : X_2 → Z = ker g`. -/
def a : T.X 2 →ₗ[A] LinearMap.ker (g T φ) :=
  LinearMap.codRestrict _ (LinearMap.inl A (T.X 1) (Fin r → A) ∘ₗ T.d 1) (fun u => by
    have := LinearMap.congr_fun (T.d_comp 0) u
    simpa [LinearMap.mem_ker] using this)

theorem subtype_comp_a :
    (LinearMap.ker (g T φ)).subtype ∘ₗ a T φ = LinearMap.inl A (T.X 1) (Fin r → A) ∘ₗ T.d 1 := by
  ext u <;> rfl

/-- The new complex `T'`: `Z ← X_2 ← X_3 ← …`. -/
def next : TopCx A where
  X := fun j => match j with
    | 0 => ModuleCat.of A (LinearMap.ker (g T φ))
    | j + 1 => T.X (j + 2)
  d := fun j => match j with
    | 0 => a T φ
    | j + 1 => T.d (j + 2)
  d_comp := fun j => match j with
    | 0 => by
      apply LinearMap.ext; intro u
      apply Subtype.ext
      have := LinearMap.congr_fun (T.d_comp 1) u
      simp only [LinearMap.comp_apply, LinearMap.zero_apply] at this
      show (LinearMap.inl A (T.X 1) (Fin r → A)) (T.d 1 (T.d 2 u)) = 0
      rw [this, map_zero]
    | j + 1 => T.d_comp (j + 2)

theorem hyp0 (hsurj : Function.Surjective (g T φ)) :
    ConeStep.Hyp (a T φ) (LinearMap.ker (g T φ)).subtype (g T φ) (T.d 1)
      (LinearMap.inl A (T.X 1) (Fin r → A)) (LinearMap.inr A (T.X 1) (Fin r → A))
      (LinearMap.fst A (T.X 1) (Fin r → A)) (LinearMap.snd A (T.X 1) (Fin r → A)) where
  ι_inj := (LinearMap.ker (g T φ)).subtype_injective
  exact := LinearMap.exact_subtype_ker_map (g T φ)
  g_surj := hsurj
  comm := subtype_comp_a T φ
  fst_inl := LinearMap.fst_comp_inl _ _ _
  snd_inl := LinearMap.snd_comp_inl _ _ _
  snd_inr := LinearMap.snd_comp_inr _ _ _
  total := by ext x <;> simp

/-- There are a finite free `F` and `φ` with `(d_0, φ)` surjective. -/
theorem exists_φ (h0 : T.fin0 0) :
    ∃ (r : ℕ) (φ : (Fin r → A) →ₗ[A] T.X 0), Function.Surjective (g T φ) := by
  have : Module.Finite A (T.X 0 ⧸ LinearMap.range (T.d 0)) := h0
  obtain ⟨r, f, hf⟩ := Module.Finite.exists_fin' A (T.X 0 ⧸ LinearMap.range (T.d 0))
  obtain ⟨φ, hφ⟩ := Module.projective_lifting_property (LinearMap.range (T.d 0)).mkQ f
    (Submodule.mkQ_surjective _)
  refine ⟨r, φ, fun x₀ => ?_⟩
  obtain ⟨c, hc⟩ := hf (Submodule.Quotient.mk x₀)
  have hmem : x₀ - φ c ∈ LinearMap.range (T.d 0) := by
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, ← hc, ← hφ]
    simp
  obtain ⟨x₁, hx₁⟩ := hmem
  refine ⟨(x₁, c), ?_⟩
  simp [hx₁]

section BaseChange

variable (B : Type u) [CommRing B] [Algebra A B]

theorem hyp (hsurj : Function.Surjective (g T φ)) [Module.Flat A (T.X 0)] :
    ConeStep.Hyp ((a T φ).baseChange B) ((LinearMap.ker (g T φ)).subtype.baseChange B)
      ((g T φ).baseChange B) ((T.d 1).baseChange B)
      ((LinearMap.inl A (T.X 1) (Fin r → A)).baseChange B)
      ((LinearMap.inr A (T.X 1) (Fin r → A)).baseChange B)
      ((LinearMap.fst A (T.X 1) (Fin r → A)).baseChange B)
      ((LinearMap.snd A (T.X 1) (Fin r → A)).baseChange B) where
  ι_inj := LinearMap.lTensor_injective_of_exact_of_flat (g T φ) hsurj _
    (LinearMap.ker (g T φ)).subtype_injective (LinearMap.exact_subtype_ker_map (g T φ)) B
  exact := lTensor_exact B (LinearMap.exact_subtype_ker_map (g T φ)) hsurj
  g_surj := LinearMap.lTensor_surjective B hsurj
  comm := by rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, subtype_comp_a]
  fst_inl := by rw [← LinearMap.baseChange_comp, LinearMap.fst_comp_inl, LinearMap.baseChange_id]
  snd_inl := by rw [← LinearMap.baseChange_comp, LinearMap.snd_comp_inl, LinearMap.baseChange_zero]
  snd_inr := by rw [← LinearMap.baseChange_comp, LinearMap.snd_comp_inr, LinearMap.baseChange_id]
  total := by
    rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, ← LinearMap.baseChange_add,
      ← LinearMap.baseChange_id]
    congr 1
    ext x <;> simp

theorem g_comp_inl :
    (g T φ).baseChange B ∘ₗ (LinearMap.inl A (T.X 1) (Fin r → A)).baseChange B = T.dB B 0 := by
  rw [← LinearMap.baseChange_comp, LinearMap.coprod_inl]

end BaseChange

section Relations

variable (hsurj : Function.Surjective (g T φ))
include hsurj

theorem next_fin0 [IsNoetherianRing A] (hfin : ∀ j, T.fin0 j) : ∀ j, (next T φ).fin0 j
  | 0 => by
    have : Module.Finite A (LinearMap.midHomology (T.d 1)
        (g T φ ∘ₗ LinearMap.inl A (T.X 1) (Fin r → A))) := by
      rw [LinearMap.coprod_inl]; exact hfin 1
    exact (hyp0 T φ hsurj).finite_quotient
  | 1 => ((LinearMap.midHomology_congr_ker (T.d 2) (a T φ) (T.d 1)
      (hyp0 T φ hsurj).ker_eq).2).mpr (hfin 2)
  | j + 2 => hfin (j + 3)

variable (B : Type u) [CommRing B] [Algebra A B] [Module.Flat A (T.X 0)]

theorem next_hfin_one : (next T φ).hfin B 1 ↔ T.hfin B 2 :=
  (LinearMap.midHomology_congr_ker (T.dB B 2) ((a T φ).baseChange B) (T.dB B 1)
    (hyp T φ B hsurj).ker_eq).2

theorem next_hdim_one : (next T φ).hdim B 1 = T.hdim B 2 :=
  (LinearMap.midHomology_congr_ker (T.dB B 2) ((a T φ).baseChange B) (T.dB B 1)
    (hyp T φ B hsurj).ker_eq).1

omit hsurj [Module.Flat A (T.X 0)] in
theorem next_hfin_succ (j : ℕ) : (next T φ).hfin B (j + 2) ↔ T.hfin B (j + 3) := Iff.rfl

omit hsurj [Module.Flat A (T.X 0)] in
theorem next_hdim_succ (j : ℕ) : (next T φ).hdim B (j + 2) = T.hdim B (j + 3) := rfl

end Relations

theorem key_field (hsurj : Function.Surjective (g T φ)) [Module.Flat A (T.X 0)]
    (κ : Type u) [Field κ] [Algebra A κ] (h0 : (next T φ).hfin κ 0) :
    T.hfin κ 0 ∧ T.hfin κ 1 ∧ (next T φ).hdim κ 0 + T.hdim κ 0 = T.hdim κ 1 + r := by
  have : Module.Finite κ ((κ ⊗[A] LinearMap.ker (g T φ)) ⧸
      LinearMap.range ((a T φ).baseChange κ)) := h0
  have h := (hyp T φ κ hsurj).finrank_eq
  rw [g_comp_inl] at h
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h2, h1, ?_⟩
  have : Nontrivial A := RingHom.domain_nontrivial (algebraMap A κ)
  have hr : Module.finrank κ (κ ⊗[A] (Fin r → A)) = r := by
    rw [Module.finrank_baseChange]; simp
  rw [hr] at h3
  exact h3

end TopCx.Step

namespace TopCx

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/-- Base of the induction: only `X_0` is nonzero. -/
theorem fiberEulerChar_base (T : TopCx A) (hflat : ∀ j, Module.Flat A (T.X j))
    (hbdd : ∀ j, 0 < j → Subsingleton (T.X j)) (hfin : ∀ j, T.fin0 j) :
    (∀ (p : PrimeSpectrum A) (j : ℕ), T.hfin p.asIdeal.ResidueField j) ∧
    IsLocallyConstant (fun p : PrimeSpectrum A =>
      ∑ j ∈ Finset.range (0 + 1), (-1 : ℤ) ^ j * (T.hdim p.asIdeal.ResidueField j : ℤ)) := by
  have := hflat 0
  have hX1 : Subsingleton (T.X 1) := hbdd 1 Nat.one_pos
  -- `X_0` is finite
  have hr0 : LinearMap.range (T.d 0) = ⊥ := by
    rw [LinearMap.range_eq_bot]
    exact LinearMap.ext fun x => by rw [Subsingleton.elim x 0]; simp
  have hX0 : Module.Finite A (T.X 0) := by
    have h0 : Module.Finite A (T.X 0 ⧸ LinearMap.range (T.d 0)) := hfin 0
    exact Module.Finite.equiv (Submodule.quotEquivOfEqBot _ hr0)
  have : Module.FinitePresentation A (T.X 0) := Module.finitePresentation_of_finite A _
  have hrange : ∀ p : PrimeSpectrum A, LinearMap.range (T.dB p.asIdeal.ResidueField 0) = ⊥ := by
    intro p
    rw [LinearMap.range_eq_bot]
    exact LinearMap.ext fun x => by rw [Subsingleton.elim x 0]; simp
  refine ⟨fun p j => ?_, ?_⟩
  · cases j with
    | zero =>
      show Module.Finite _ ((p.asIdeal.ResidueField ⊗[A] T.X 0) ⧸ _)
      infer_instance
    | succ j =>
      have : Subsingleton (T.X (j + 1)) := hbdd (j + 1) (Nat.succ_pos j)
      show Module.Finite _ (LinearMap.midHomology _ _)
      infer_instance
  · have hlc := (Module.isLocallyConstant_rankAtStalk (R := A) (M := T.X 0)).comp
      (fun n : ℕ => (n : ℤ))
    refine cast (congrArg IsLocallyConstant (funext fun p => ?_)) hlc
    simp only [zero_add, Finset.sum_range_one, pow_zero, one_mul, Function.comp_apply]
    congr 1
    rw [Module.rankAtStalk_eq]
    show _ = Module.finrank _ ((p.asIdeal.ResidueField ⊗[A] T.X 0) ⧸ _)
    exact (LinearEquiv.finrank_eq (Submodule.quotEquivOfEqBot _ (hrange p))).symm

/-- The main induction. -/
theorem fiberEulerChar_isLocallyConstant : ∀ (ℓ : ℕ) (T : TopCx A),
    (∀ j, Module.Flat A (T.X j)) → (∀ j, ℓ < j → Subsingleton (T.X j)) → (∀ j, T.fin0 j) →
    (∀ (p : PrimeSpectrum A) (j : ℕ), T.hfin p.asIdeal.ResidueField j) ∧
    IsLocallyConstant (fun p : PrimeSpectrum A =>
      ∑ j ∈ Finset.range (ℓ + 1), (-1 : ℤ) ^ j * (T.hdim p.asIdeal.ResidueField j : ℤ))
  | 0, T, hflat, hbdd, hfin => fiberEulerChar_base T hflat hbdd hfin
  | ℓ + 1, T, hflat, hbdd, hfin => by
    obtain ⟨r, φ, hsurj⟩ := Step.exists_φ T (hfin 0)
    have := hflat 0
    have := hflat 1
    have hflat' : ∀ j, Module.Flat A ((Step.next T φ).X j) := by
      intro j
      cases j with
      | zero =>
        show Module.Flat A (LinearMap.ker (Step.g T φ))
        have : Module.Flat A (T.X 1 × (Fin r → A)) := Module.Flat.prod_of_flat
        exact Module.Flat.of_exact_of_flat_of_flat (LinearMap.ker (Step.g T φ)).subtype
          (Step.g T φ) (LinearMap.ker (Step.g T φ)).subtype_injective hsurj
          (LinearMap.exact_subtype_ker_map _)
      | succ j => exact hflat (j + 2)
    have hbdd' : ∀ j, ℓ < j → Subsingleton ((Step.next T φ).X j) := by
      intro j hj
      cases j with
      | zero => omega
      | succ j => exact hbdd (j + 2) (by omega)
    have hfin' := Step.next_fin0 T φ hsurj hfin
    obtain ⟨ih1, ih2⟩ := fiberEulerChar_isLocallyConstant ℓ (Step.next T φ) hflat' hbdd' hfin'
    refine ⟨fun p j => ?_, ?_⟩
    · match j with
      | 0 => exact (Step.key_field T φ hsurj _ (ih1 p 0)).1
      | 1 => exact (Step.key_field T φ hsurj _ (ih1 p 0)).2.1
      | 2 => exact (Step.next_hfin_one T φ hsurj _).mp (ih1 p 1)
      | j + 3 => exact ih1 p (j + 2)
    · have hdim_succ : ∀ (p : PrimeSpectrum A) (j : ℕ),
          (Step.next T φ).hdim p.asIdeal.ResidueField (j + 1)
            = T.hdim p.asIdeal.ResidueField (j + 2) := by
        intro p j
        cases j with
        | zero => exact Step.next_hdim_one T φ hsurj _
        | succ j => rfl
      have hfun : (fun p : PrimeSpectrum A =>
          ∑ j ∈ Finset.range (ℓ + 1 + 1), (-1 : ℤ) ^ j * (T.hdim p.asIdeal.ResidueField j : ℤ))
          = fun p => (r : ℤ) - ∑ j ∈ Finset.range (ℓ + 1),
              (-1 : ℤ) ^ j * ((Step.next T φ).hdim p.asIdeal.ResidueField j : ℤ) := by
        funext p
        have hk := (Step.key_field T φ hsurj p.asIdeal.ResidueField (ih1 p 0)).2.2
        have hk' : (((Step.next T φ).hdim p.asIdeal.ResidueField 0 : ℕ) : ℤ)
            + (T.hdim p.asIdeal.ResidueField 0 : ℤ)
            = (T.hdim p.asIdeal.ResidueField 1 : ℤ) + (r : ℤ) := by exact_mod_cast hk
        rw [Finset.sum_range_succ', Finset.sum_range_succ', Finset.sum_range_succ' _ ℓ]
        have hs : ∑ j ∈ Finset.range ℓ, (-1 : ℤ) ^ (j + 1 + 1) *
              (T.hdim p.asIdeal.ResidueField (j + 1 + 1) : ℤ)
            = - ∑ j ∈ Finset.range ℓ, (-1 : ℤ) ^ (j + 1) *
              ((Step.next T φ).hdim p.asIdeal.ResidueField (j + 1) : ℤ) := by
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [hdim_succ p j, pow_succ (-1 : ℤ) (j + 1)]
          ring
        rw [hs]
        simp only [pow_zero, one_mul, zero_add, pow_one]
        linarith
      rw [hfun]
      exact (IsLocallyConstant.const (r : ℤ)).sub ih2

end TopCx

end
