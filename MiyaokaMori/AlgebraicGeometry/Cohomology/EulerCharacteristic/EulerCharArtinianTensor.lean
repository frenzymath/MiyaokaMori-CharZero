import Mathlib.AlgebraicGeometry.Artinian
import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModuleTensorPowerIsoTensorPow
import MiyaokaMori.AlgebraicGeometry.Cohomology.EulerCharacteristic.EulerCharArtinianRankZero
import MiyaokaMori.AlgebraicGeometry.Cohomology.EulerCharacteristic.EulerCharBiproductPow
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.LocallyFreeOnArtinianIsFree
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.TensorFreePowIso

/-! # Stacks 0AYT on an Artinian scheme

Stacks 0AYT on the zero-dimensional scheme itself: `Z` Artinian and proper over `k`, `G` coherent, `E`
locally free with `rankAtStalk E = n` everywhere; then `χ(Z, G ⊗ E) = n · χ(Z, G)`.

* `n > 0`: `E ≅ O_Z^{⊕ n}` (`nonempty_iso_pow_unit_of_isLocallyFree_of_isArtinianScheme`),
  `G ⊗ O_Z^{⊕ n} ≅ G^{⊕ n}` (`nonempty_tensor_pow_unit_iso`), `χ(G^{⊕ n}) = n χ(G)`
  (`sheafEulerCharacteristic_pow`).
* `n = 0`: the degenerate case (`EulerCharArtinianRankZero.lean`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- **Stacks 0AYT on an Artinian scheme**: `Z` Artinian and proper over `k`, `G` coherent, `E` locally
free with `rankAtStalk E z = n` for all `z`; then `χ(Z, G ⊗ E) = n · χ(Z, G)`.

Proof: for `n = 0` this is `sheafEulerCharacteristic_tensor_eq_zero_of_rankAtStalk_eq_zero_of_isArtinianScheme`.
For `n > 0`, `E ≅ O_Z^{⊕ n}` (`nonempty_iso_pow_unit_of_isLocallyFree_of_isArtinianScheme`), hence
`G ⊗ E ≅ G ⊗ O_Z^{⊕ n}` (`tensorIsoRight`) `≅ G^{⊕ n}` (`nonempty_tensor_pow_unit_iso`), and
`χ(G^{⊕ n}) = n χ(G)` (`sheafEulerCharacteristic_pow`); `χ` is invariant under isomorphism
(`sheafEulerCharacteristic_eq_of_iso`). -/
theorem AlgebraicGeometry.sheafEulerCharacteristic_tensor_of_isArtinianScheme
    {k : Type u} [Field k] (Z : AlgebraicGeometry.Scheme.{u})
    [Z.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (hZ : IsProperOver k Z)
    [AlgebraicGeometry.IsArtinianScheme Z] (G : Z.Modules) [G.IsCoherent]
    (E : Z.Modules) [E.IsLocallyFree] (n : ℕ)
    (hE : ∀ z, AlgebraicGeometry.Scheme.Modules.rankAtStalk E z = n) :
    AlgebraicGeometry.sheafEulerCharacteristic (k := k) Z (G.tensor E) =
      n * AlgebraicGeometry.sheafEulerCharacteristic (k := k) Z G := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [AlgebraicGeometry.sheafEulerCharacteristic_tensor_eq_zero_of_rankAtStalk_eq_zero_of_isArtinianScheme
      Z hZ G E hE]
    simp
  · obtain ⟨e⟩ :=
      AlgebraicGeometry.Scheme.Modules.nonempty_iso_pow_unit_of_isLocallyFree_of_isArtinianScheme E n hn hE
    obtain ⟨e'⟩ := AlgebraicGeometry.Scheme.Modules.nonempty_tensor_pow_unit_iso G n
    rw [AlgebraicGeometry.sheafEulerCharacteristic_eq_of_iso
        (AlgebraicGeometry.Scheme.Modules.tensorIsoRight G e),
      AlgebraicGeometry.sheafEulerCharacteristic_eq_of_iso e',
      AlgebraicGeometry.sheafEulerCharacteristic_pow Z hZ G n]

end
