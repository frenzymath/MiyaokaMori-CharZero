import MiyaokaMori.Prelude
import Mathlib.RingTheory.Regular.ProjectiveDimension

/-! # Tools on projective dimension over a local ring

Elementary tools on projective dimension over a (Noetherian) local ring used by the proof of
Stacks 00OC (Auslander–Buchsbaum–Serre) along the route of
Matsumura, *Commutative Ring Theory*, Theorem 19.2:

* `ModuleCat.hasProjectiveDimensionLE_of_linearEquiv_of`, `ModuleCat.projectiveDimension_eq_of_linearEquiv_of`:
  Mathlib's transport lemmas with the objects `ModuleCat.of R _` spelled out.
* `ModuleCat.hasProjectiveDimensionLE_succ_iff_ker`: dimension shifting along a surjection from a
  projective module, `pd N ≤ n + 1 ↔ pd (ker f) ≤ n` (Mathlib
  `ShortComplex.ShortExact.hasProjectiveDimensionLT_X₃_iff`).
* `IsLocalRing.hasProjectiveDimensionLE_residueField_succ_iff`: `pd κ ≤ n + 1 ↔ pd 𝔪 ≤ n`
  (the sequence `0 → 𝔪 → R → κ → 0`).
* `IsLocalRing.exists_surjective_ker_le_maximalIdeal_smul`: a *minimal presentation*
  `R^ι → M` of a finite module, with kernel inside `𝔪 R^ι` (lift a `κ`-basis of `κ ⊗ M`;
  Stacks 00NZ / Matsumura Thm 2.3 proof).
* `IsLocalRing.free_of_hasProjectiveDimensionLE_of_mul_maximalIdeal_eq_zero`: **the depth-zero
  argument** of Matsumura 19.2 / Stacks 00OB-style: if some `y ≠ 0` kills `𝔪` (i.e. `𝔪 ∈ Ass R`,
  "depth R = 0") then every finite module of finite projective dimension is free. Proof by induction
  on `pd M ≤ n`: for `n = 0`, `M` is projective hence free (Mathlib `free_of_flat_of_isLocalRing`).
  For `n + 1`, take a minimal presentation `0 → K → R^ι → M → 0`, `K ⊆ 𝔪 R^ι`; `pd K ≤ n` so `K` is
  free by induction; but `y K ⊆ y 𝔪 R^ι = 0`, and a nonzero free module is faithful, so `K = 0` and
  `M ≅ R^ι`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory IsLocalRing
open scoped TensorProduct

noncomputable section

/-- `ModuleCat.hasProjectiveDimensionLE_of_linearEquiv` with the objects `ModuleCat.of R _` spelled
out (the Mathlib lemma is stated for `M N : ModuleCat R`, which unification does not find) and the
hypothesis explicit. -/
theorem ModuleCat.hasProjectiveDimensionLE_of_linearEquiv_of {R : Type u} [CommRing R]
    {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) (n : ℕ) (h : HasProjectiveDimensionLE (ModuleCat.of R M) n) :
    HasProjectiveDimensionLE (ModuleCat.of R N) n :=
  ModuleCat.hasProjectiveDimensionLE_of_linearEquiv (M := ModuleCat.of R M) (N := ModuleCat.of R N)
    e n

/-- `ModuleCat.projectiveDimension_eq_of_linearEquiv` with the objects `ModuleCat.of R _` spelled
out. -/
theorem ModuleCat.projectiveDimension_eq_of_linearEquiv_of {R : Type u} [CommRing R]
    {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (e : M ≃ₗ[R] N) :
    projectiveDimension (ModuleCat.of R M) = projectiveDimension (ModuleCat.of R N) :=
  ModuleCat.projectiveDimension_eq_of_linearEquiv (M := ModuleCat.of R M) (N := ModuleCat.of R N) e

/-- Dimension shifting along a surjection `f : M → N` from a projective module:
`pd N ≤ n + 1 ↔ pd (ker f) ≤ n`. -/
theorem ModuleCat.hasProjectiveDimensionLE_succ_iff_ker {R : Type u} [CommRing R]
    {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (hf : Function.Surjective f) [Module.Projective R M] (n : ℕ) :
    HasProjectiveDimensionLE (ModuleCat.of R N) (n + 1) ↔
      HasProjectiveDimensionLE (ModuleCat.of R (LinearMap.ker f)) n := by
  have hS := LinearMap.shortExact_shortComplexKer hf
  have hP : Projective (f.shortComplexKer.X₂) := by
    rw [← IsProjective.iff_projective]; infer_instance
  exact hS.hasProjectiveDimensionLT_X₃_iff n hP

/-- `pd κ ≤ n + 1 ↔ pd 𝔪 ≤ n` over a local ring (`0 → 𝔪 → R → κ → 0`, `R` free). -/
theorem IsLocalRing.hasProjectiveDimensionLE_residueField_succ_iff {R : Type u} [CommRing R]
    [IsLocalRing R] (n : ℕ) :
    HasProjectiveDimensionLE (ModuleCat.of R (ResidueField R)) (n + 1) ↔
      HasProjectiveDimensionLE (ModuleCat.of R (maximalIdeal R)) n := by
  rw [ModuleCat.hasProjectiveDimensionLE_succ_iff_ker
    (show R →ₗ[R] ResidueField R from (maximalIdeal R).mkQ) (Submodule.mkQ_surjective _) n]
  have hker : LinearMap.ker (show R →ₗ[R] ResidueField R from (maximalIdeal R).mkQ) =
      maximalIdeal R := Submodule.ker_mkQ _
  exact ⟨fun h => ModuleCat.hasProjectiveDimensionLE_of_linearEquiv_of (LinearEquiv.ofEq _ _ hker) n h,
    fun h => ModuleCat.hasProjectiveDimensionLE_of_linearEquiv_of (LinearEquiv.ofEq _ _ hker.symm) n h⟩

/-- **Minimal presentation** of a finite module over a local ring: a surjection from a finite free
module `ι → R` whose kernel is contained in `𝔪 · (ι → R)`. Lift a `κ`-basis of `κ ⊗ M` to `M`
(Nakayama, Mathlib `IsLocalRing.span_eq_top_of_tmul_eq_basis`); a relation `∑ cᵢ vᵢ = 0` maps to
`∑ c̄ᵢ wᵢ = 0` in `κ ⊗ M`, so all `c̄ᵢ = 0`, i.e. all `cᵢ ∈ 𝔪`. -/
theorem IsLocalRing.exists_surjective_ker_le_maximalIdeal_smul {R : Type u} [CommRing R]
    [IsLocalRing R] (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] :
    ∃ (ι : Type u) (_ : Fintype ι) (f : (ι → R) →ₗ[R] M), Function.Surjective f ∧
      LinearMap.ker f ≤ (maximalIdeal R) • (⊤ : Submodule R (ι → R)) := by
  classical
  let k := ResidueField R
  let w := Module.Free.chooseBasis k (k ⊗[R] M)
  obtain ⟨v, hv⟩ := (TensorProduct.mk_surjective R M k Ideal.Quotient.mk_surjective).comp_left w
  have hv' : ∀ i, (1 : k) ⊗ₜ[R] v i = w i := fun i => congr_fun hv i
  have hspan : Submodule.span R (Set.range v) = ⊤ :=
    IsLocalRing.span_eq_top_of_tmul_eq_basis v w hv'
  refine ⟨Module.Free.ChooseBasisIndex k (k ⊗[R] M), inferInstance,
    Fintype.linearCombination R v, ?_, ?_⟩
  · rw [← LinearMap.range_eq_top, Fintype.range_linearCombination]
    exact hspan
  · intro c hc
    rw [LinearMap.mem_ker, Fintype.linearCombination_apply] at hc
    have h1 : ∑ i, (algebraMap R k (c i)) • w i = 0 := by
      have := congrArg (TensorProduct.mk R k M 1) hc
      rw [map_sum, map_zero] at this
      rw [← this]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, TensorProduct.mk_apply, hv' i, algebraMap_smul]
    have h2 : ∀ i, algebraMap R k (c i) = 0 :=
      Fintype.linearIndependent_iff.mp w.linearIndependent _ h1
    have h3 : ∀ i, c i ∈ maximalIdeal R := fun i => by
      have := h2 i
      rwa [IsLocalRing.ResidueField.algebraMap_eq, IsLocalRing.residue_eq_zero_iff] at this
    rw [pi_eq_sum_univ c]
    refine Submodule.sum_mem _ fun i _ => ?_
    exact Submodule.smul_mem_smul (h3 i) Submodule.mem_top

/-- **Depth zero ⇒ finite projective dimension forces freeness** (Matsumura, *Commutative Ring
Theory*, proof of Thm 19.2, case `depth R = 0`; Stacks 00OB-style minimal resolution argument).
If `y ≠ 0` annihilates `𝔪` (equivalently `𝔪 ∈ Ass R`), then every finite `R`-module of finite
projective dimension is free. Induction on `n` with `pd M ≤ n`: for `n = 0`, `M` is projective,
hence free (`Module.free_of_flat_of_isLocalRing`); for `n + 1`, choose a minimal presentation
`0 → K → R^ι → M → 0` with `K ⊆ 𝔪 R^ι`; then `pd K ≤ n`, `K` is finite (Noetherian), so `K` is free
by induction; `y K ⊆ y 𝔪 R^ι = 0` and a nonzero free module is faithful, so `K = 0`, i.e.
`M ≅ R^ι` is free. -/
theorem IsLocalRing.free_of_hasProjectiveDimensionLE_of_mul_maximalIdeal_eq_zero
    {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {y : R} (hy : y ≠ 0) (hym : ∀ m ∈ maximalIdeal R, y * m = 0)
    (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M] (n : ℕ)
    (hM : HasProjectiveDimensionLE (ModuleCat.of R M) n) : Module.Free R M := by
  induction n generalizing M with
  | zero =>
    have hproj : Module.Projective R M := by
      rw [IsProjective.iff_projective]
      exact (projective_iff_hasProjectiveDimensionLE_zero _).mpr hM
    exact Module.free_of_flat_of_isLocalRing
  | succ n ih =>
    obtain ⟨ι, _, f, hf, hker⟩ := IsLocalRing.exists_surjective_ker_le_maximalIdeal_smul (R := R) M
    have hK : HasProjectiveDimensionLE (ModuleCat.of R (LinearMap.ker f)) n :=
      (ModuleCat.hasProjectiveDimensionLE_succ_iff_ker f hf n).mp hM
    have : Module.Finite R (LinearMap.ker f) :=
      Module.Finite.iff_fg.mpr (IsNoetherian.noetherian _)
    have hKfree : Module.Free R (LinearMap.ker f) := ih _ hK
    have hyK : ∀ z : LinearMap.ker f, y • z = 0 := by
      intro z
      have hz : (z : ι → R) ∈ maximalIdeal R • (⊤ : Submodule R (ι → R)) := hker z.2
      apply Subtype.ext
      show y • (z : ι → R) = 0
      refine Submodule.smul_induction_on hz ?_ ?_
      · intro m hm v _
        rw [smul_smul, hym m hm, zero_smul]
      · intro a b ha hb
        rw [smul_add, ha, hb, add_zero]
    have hsub : Subsingleton (LinearMap.ker f) := by
      by_contra hns
      rw [not_subsingleton_iff_nontrivial] at hns
      have hann : y ∈ Module.annihilator R (LinearMap.ker f) := Module.mem_annihilator.mpr hyK
      rw [Module.annihilator_eq_bot.mpr inferInstance] at hann
      exact hy ((Submodule.mem_bot R).mp hann)
    have hinj : Function.Injective f := by
      rw [← LinearMap.ker_eq_bot, eq_bot_iff]
      intro z hz
      have : (⟨z, hz⟩ : LinearMap.ker f) = 0 := Subsingleton.elim _ _
      simpa using congrArg Subtype.val this
    exact Module.Free.of_equiv (LinearEquiv.ofBijective f ⟨hinj, hf⟩)

end
