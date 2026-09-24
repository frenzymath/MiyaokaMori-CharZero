import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.ModulesBiproductLocallyFree

/-! # Finite direct sums of finite type modules

A finite direct sum of finite type sheaves of modules is of finite type (Stacks, Sheaves of Modules,
section "Modules of finite type"). Needed for the coherence of `M^{⊕ n}` in Stacks 0AYT.

The content is already in the library: `Scheme.Modules.biproduct_isFiniteType`
(`ModulesBiproductLocallyFree`) proves it for a `Fintype` index with instance hypotheses; this module only repackages it for a
`Finite` index and an explicit hypothesis `hM`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- **A finite direct sum of finite type modules is of finite type** (Stacks, Sheaves of Modules,
section "Modules of finite type": finite direct sums of finite type modules are of finite type — the
lemma listing the closure properties of finite type modules; tag not verified offline).

Proof: fix a `Fintype` structure on `J` (`Fintype.ofFinite`) and turn the hypotheses `hM j` into local
instances; then this is exactly `Scheme.Modules.biproduct_isFiniteType`
(`ModulesBiproductLocallyFree`): for every `x`, choose a common open
`V ∋ x` on which each `M j|_V` receives an epimorphism from a finite free module `free (I j)`
(`exists_common_open`, `exists_epi_free_pullback_of_isFiniteType`); `pullback V.ι` preserves finite
biproducts (`Functor.mapBiproduct`) and `⨁ free (I j) ≅ free (Σ j, I j)` (`biproductLF.freeSigmaIso`),
so `free (Σ j, I j) → (⨁ M)|_V` is an epimorphism (`biproduct.map_epi`) with `Σ j, I j` finite, and
`isFiniteType_of_epi_free_pullback` concludes. `HasBiproduct M` is a `Prop`, so the biproduct
`⨁ M` formed with the `Finite J` instance is definitionally the one formed with the chosen `Fintype J`. -/
theorem isFiniteType_biproduct {J : Type} [Finite J] (M : J → X.Modules)
    (hM : ∀ j, (M j).IsFiniteType) : (⨁ M).IsFiniteType := by
  have : Fintype J := Fintype.ofFinite J
  have : ∀ j, (M j).IsFiniteType := hM
  exact AlgebraicGeometry.Scheme.Modules.biproduct_isFiniteType M

end AlgebraicGeometry.Scheme.Modules

end
