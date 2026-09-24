import MiyaokaMori.Prelude

/-! # The kernel of a surjection of flat modules is flat

For a short exact sequence `0 → Z → M → Q → 0` over a commutative ring `R` with `M` and `Q` flat, `Z` is flat.

Proof:
1. Take any injective `f : N → N'`. Mathlib `LinearMap.lTensor_injective_of_exact_of_flat` (`Q` flat ⇒
   `N ⊗ Z → N ⊗ M` injective; proved by the snake lemma, equivalent to `Tor_1(N, Q) = 0`).
2. `M` flat ⇒ `N ⊗ M → N' ⊗ M` injective; in the commutative square
   `(N' ⊗ ι) ∘ (f ⊗ Z) = (f ⊗ M) ∘ (N ⊗ ι)` the right-hand side is a composite of injections, so `f ⊗ Z` is
   injective.
3. `Module.Flat.iff_rTensor_preserves_injective_linearMap` gives that `Z` is flat.

Reference: Stacks 00HM / Hartshorne III.9.1A(e).
-/

set_option autoImplicit false

universe u

open TensorProduct

theorem Module.Flat.of_exact_of_flat_of_flat {R : Type u} [CommRing R]
    {Z M Q : Type u} [AddCommGroup Z] [AddCommGroup M] [AddCommGroup Q]
    [Module R Z] [Module R M] [Module R Q] [Module.Flat R M] [Module.Flat R Q]
    (ι : Z →ₗ[R] M) (g : M →ₗ[R] Q) (hι : Function.Injective ι) (hg : Function.Surjective g)
    (H : Function.Exact ι g) : Module.Flat R Z := by
  rw [Module.Flat.iff_rTensor_preserves_injective_linearMap]
  intro N N' _ _ _ _ f hf
  have h1 : Function.Injective (ι.lTensor N) :=
    LinearMap.lTensor_injective_of_exact_of_flat g hg ι hι H N
  have h2 : Function.Injective (f.rTensor M) :=
    Module.Flat.rTensor_preserves_injective_linearMap f hf
  have hsq : (ι.lTensor N') ∘ₗ (f.rTensor Z) = (f.rTensor M) ∘ₗ (ι.lTensor N) := by
    ext x z; simp
  have : Function.Injective ((ι.lTensor N') ∘ₗ (f.rTensor Z)) := by
    rw [hsq]; exact h2.comp h1
  exact Function.Injective.of_comp this

/-- The product of two flat modules is flat (Mathlib has only the `⨁` and `Π₀` versions). -/
theorem Module.Flat.prod_of_flat {R : Type u} [CommRing R] {M N : Type u}
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    [Module.Flat R M] [Module.Flat R N] : Module.Flat R (M × N) := by
  rw [Module.Flat.iff_rTensor_preserves_injective_linearMap]
  intro P Q _ _ _ _ f hf
  have h1 : Function.Injective (f.rTensor M) :=
    Module.Flat.rTensor_preserves_injective_linearMap f hf
  have h2 : Function.Injective (f.rTensor N) :=
    Module.Flat.rTensor_preserves_injective_linearMap f hf
  have hsq : (TensorProduct.prodRight R R Q M N).toLinearMap ∘ₗ f.rTensor (M × N)
      = (LinearMap.prodMap (f.rTensor M) (f.rTensor N)) ∘ₗ
        (TensorProduct.prodRight R R P M N).toLinearMap := by
    ext p m <;> simp
  have hinj : Function.Injective ((TensorProduct.prodRight R R Q M N).toLinearMap ∘ₗ
      f.rTensor (M × N)) := by
    rw [hsq]
    exact (Function.Injective.prodMap h1 h2).comp (TensorProduct.prodRight R R P M N).injective
  exact Function.Injective.of_comp hinj
