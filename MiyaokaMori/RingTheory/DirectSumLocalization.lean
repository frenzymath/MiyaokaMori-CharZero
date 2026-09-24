import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.Module.LocalizedModule.IsLocalization

/-! # Localization commutes with infinite direct sums

Let `R` be a commutative semiring, `S : Submonoid R`, `{Mᵢ}`, `{Nᵢ}` two families of `R`-modules
and `fᵢ : Mᵢ →ₗ[R] Nᵢ`. If every `fᵢ` realizes `Nᵢ` as the localization of `Mᵢ` at `S`
(`IsLocalizedModule S fᵢ`), then the componentwise map

`DirectSum.lmap f : (⨁ i, Mᵢ) →ₗ[R] (⨁ i, Nᵢ)`

realizes `⨁ᵢ Nᵢ` as the localization of `⨁ᵢ Mᵢ` at `S`.

Proof (three obligations):
* `map_units`: `s` is invertible on every `Nᵢ`; the inverse is assembled componentwise from
  `(hu i).unit⁻¹` via `DirectSum.lmap` (the inverse preserves zero, so finite support is kept).
* `surj`: induction on `y` via `DirectSum.induction_on`. A generator `of i a` uses surjectivity in
  the `i`-th component; the addition step multiplies the two denominators (`a * b`) and lifts to
  `b • u + a • v`. Surjectivity is an additive property of `y`, so induction is legitimate here.
* `exists_of_eq`: `DirectSum.lmap f x₁ = DirectSum.lmap f x₂` gives `fᵢ (x₁ i) = fᵢ (x₂ i)`
  componentwise, hence some `cᵢ ∈ S` for each `i`; a common denominator is the `Finset.prod` over the
  finite set `x₁.support ∪ x₂.support`. This step cannot be done by induction: "each component is
  killed by `c`" is not an additive property of `x` (`(x+y) i = x i + y i = 0` does not give
  vanishing of both sides), so the support has to be taken explicitly.

Mathlib has the tensor-product version (`RingTheory/Localization/BaseChange.lean`) and the finite
Pi version (`RingTheory/TensorProduct/IsBaseChangePi.lean`); the infinite direct-sum version is what
the quasi-coherence of "⊕-shaped" algebras (section rings `⨁ₘ Γ(U, Sₘ)` of graded quasi-coherent
algebras, Rees algebras, symmetric algebras) needs. The statement is independent of geometry.
-/

set_option autoImplicit false

universe u v w

open DirectSum

/-- **Localization commutes with direct sums**: if every `f i : M i →ₗ[R] N i` is the localization
of modules at `S`, then so is `DirectSum.lmap f : (⨁ i, M i) →ₗ[R] (⨁ i, N i)`.

Mathlib has the tensor-product and finite Pi versions, but not this infinite direct-sum version. -/
theorem IsLocalizedModule.directSum {R : Type u} [CommSemiring R] (S : Submonoid R)
    {ι : Type v} [DecidableEq ι] {M N : ι → Type w}
    [∀ i, AddCommMonoid (M i)] [∀ i, Module R (M i)]
    [∀ i, AddCommMonoid (N i)] [∀ i, Module R (N i)]
    (f : ∀ i, M i →ₗ[R] N i) [∀ i, IsLocalizedModule S (f i)] :
    IsLocalizedModule S (DirectSum.lmap f) where
  map_units s := by
    have hu : ∀ i, IsUnit (algebraMap R (Module.End R (N i)) (s : R)) :=
      fun i => IsLocalizedModule.map_units (f i) s
    set g : ∀ i, N i →ₗ[R] N i := fun i => (↑(hu i).unit⁻¹ : Module.End R (N i)) with hgdef
    have hsg : ∀ (i : ι) (z : N i), (s : R) • g i z = z := fun i z =>
      ((Module.End.algebraMap_isUnit_inv_apply_eq_iff R (hu i) z (g i z)).mp rfl).symm
    have hgs : ∀ (i : ι) (z : N i), g i ((s : R) • z) = z := fun i z =>
      (Module.End.algebraMap_isUnit_inv_apply_eq_iff R (hu i) ((s : R) • z) z).mpr rfl
    refine ⟨⟨algebraMap R (Module.End R (⨁ i, N i)) (s : R), DirectSum.lmap g, ?_, ?_⟩, rfl⟩
    · refine LinearMap.ext fun x => DirectSum.ext fun i => ?_
      show ((s : R) • DirectSum.lmap g x) i = x i
      rw [DirectSum.smul_apply, DirectSum.lmap_apply, hsg]
    · refine LinearMap.ext fun x => DirectSum.ext fun i => ?_
      show (DirectSum.lmap g ((s : R) • x)) i = x i
      rw [DirectSum.lmap_apply, DirectSum.smul_apply, hgs]
  surj y := by
    induction y using DirectSum.induction_on with
    | zero => exact ⟨⟨0, 1⟩, by simp⟩
    | of i a =>
      obtain ⟨⟨m, t⟩, hm⟩ := IsLocalizedModule.surj S (f i) a
      refine ⟨⟨DirectSum.of M i m, t⟩, ?_⟩
      rw [DirectSum.lmap_of, ← hm, Submonoid.smul_def, Submonoid.smul_def]
      exact ((DirectSum.lof R ι N i).map_smul (t : R) a).symm
    | add x y hx hy =>
      obtain ⟨⟨u, a⟩, hu⟩ := hx
      obtain ⟨⟨v, b⟩, hv⟩ := hy
      refine ⟨⟨(b : R) • u + (a : R) • v, a * b⟩, ?_⟩
      rw [Submonoid.smul_def] at hu hv
      have key : ((a * b : S) : R) • (x + y)
          = (b : R) • ((a : R) • x) + (a : R) • ((b : R) • y) := by
        simp only [Submonoid.coe_mul, smul_add, ← mul_smul, mul_comm]
      rw [Submonoid.smul_def, key, hu, hv, ← LinearMap.map_smul, ← LinearMap.map_smul,
        ← map_add]
  exists_of_eq {x₁ x₂} h := by
    classical
    have hcomp : ∀ i, f i (x₁ i) = f i (x₂ i) := by
      intro i
      have h1 := congrArg (fun z : ⨁ i, N i => z i) h
      simpa using h1
    choose c hc using fun i => IsLocalizedModule.exists_of_eq (S := S) (f := f i) (hcomp i)
    have hap : ∀ (P : S) (x : ⨁ i, M i) (i : ι), (P • x) i = P • x i := by
      intro P x i
      rw [Submonoid.smul_def, Submonoid.smul_def, DirectSum.smul_apply]
    refine ⟨∏ j ∈ (DFinsupp.support x₁ ∪ DFinsupp.support x₂), c j, DirectSum.ext fun i => ?_⟩
    rw [hap, hap]
    by_cases hi : i ∈ (DFinsupp.support x₁ ∪ DFinsupp.support x₂)
    · rw [← Finset.prod_erase_mul _ c hi, mul_smul, mul_smul, hc]
    · have h1 : x₁ i = 0 := by
        by_contra hne
        exact hi (Finset.mem_union_left _ (DFinsupp.mem_support_iff.mpr hne))
      have h2 : x₂ i = 0 := by
        by_contra hne
        exact hi (Finset.mem_union_right _ (DFinsupp.mem_support_iff.mpr hne))
      rw [h1, h2]
