import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.ExteriorPower.Pairing
import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-!
# Nondegeneracy of the exterior-power dual pairing

For a finite free module, the canonical pairing between the exterior power of the dual
and the dual of the exterior power is an isomorphism.  The proof uses the exterior-power
basis and its dual basis, so it does not invert `n!`, assume a field, or impose any
condition on the characteristic.  The determinant formula is the underlying Mathlib
pairing formula on pure wedges.
-/

noncomputable section

open Module Set
open scoped TensorProduct

namespace MiyaokaMori.Algebra

universe u v

variable {R : Type u} {M : Type v} {r : ℕ} [CommRing R] [AddCommGroup M] [Module R M]

/-- The basis-defined equivalence underlying `exteriorPower.pairingDual`.

The domain basis is the exterior-power basis induced by the dual basis of `b`; the
codomain basis is the dual basis of the exterior-power basis induced by `b`.
-/
def exteriorPowerPairingDualEquiv (b : Basis (Fin r) R M) (n : ℕ) :
    (⋀[R]^n (Module.Dual R M)) ≃ₗ[R] Module.Dual R (⋀[R]^n M) :=
  (b.dualBasis.exteriorPower n).equiv
    ((b.exteriorPower n).dualBasis) (Equiv.refl _)

/-- The basis-defined equivalence agrees with Mathlib's canonical pairing map. -/
theorem exteriorPowerPairingDualEquiv_toLinearMap
    (b : Basis (Fin r) R M) (n : ℕ) :
    (exteriorPowerPairingDualEquiv b n).toLinearMap = exteriorPower.pairingDual R M n := by
  classical
  apply (b.dualBasis.exteriorPower n).ext
  intro s
  change (b.dualBasis.exteriorPower n).equiv
    ((b.exteriorPower n).dualBasis) (Equiv.refl _)
      ((b.dualBasis.exteriorPower n) s) = _
  rw [Basis.equiv_apply]
  change (b.exteriorPower n).dualBasis s = _
  rw [show (b.exteriorPower n).dualBasis s = (b.exteriorPower n).coord s from
    congrFun (b.exteriorPower n).coe_dualBasis s]
  rw [exteriorPower.basis_coord, exteriorPower.basis_apply]
  dsimp only [exteriorPower.ιMultiDual]
  rw [Basis.coe_dualBasis]

/-- The exterior-power pairing is bijective for every exterior degree. -/
theorem exteriorPowerPairingDual_bijective
    (b : Basis (Fin r) R M) (n : ℕ) :
    Function.Bijective (exteriorPower.pairingDual R M n) := by
  rw [← exteriorPowerPairingDualEquiv_toLinearMap b n]
  exact (exteriorPowerPairingDualEquiv b n).bijective

/-- Determinant formula for the canonical pairing on pure exterior products. -/
theorem exteriorPowerPairingDual_determinant
    (n : ℕ) (f : Fin n → Module.Dual R M) (v : Fin n → M) :
    exteriorPower.pairingDual R M n (exteriorPower.ιMulti R n f)
        (exteriorPower.ιMulti R n v) =
      Matrix.det (n := Fin n) (.of (fun i j ↦ f j (v i))) := by
  exact exteriorPower.pairingDual_ιMulti_ιMulti f v

end MiyaokaMori.Algebra
