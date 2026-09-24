import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Points.StalkPrimeOfGenerization
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Local ring of an integral closed subscheme at a point

`j : Z ⟶ X` a closed immersion with `Z` integral, `z' : Z`, `x := j z'`, `w := j η_Z`. The kernel of
the surjection `O_{X,x} → O_{Z,z'}` is the prime `q_w` of `O_{X,x}` corresponding to the generization
`w ⤳ x` (`stalkPrimeOfSpecializes`), so `O_{Z,z'} ≃ O_{X,x} ⧸ q_w`.

Proof of the kernel statement: `O_{Z,z'} → O_{Z,η} = K(Z)` is injective (`Z` integral), and by
naturality of `stalkSpecializes` the composite `O_{X,x} → O_{Z,z'} → K(Z)` equals
`O_{X,x} → O_{X,w} → K(Z)`. The second map `O_{X,w} → K(Z)` is a surjection (closed immersion) onto a
field, so its kernel is the maximal ideal `𝔪_w`; hence `ker = 𝔪_w.comap (O_{X,x} → O_{X,w}) = q_w`.

Source: Stacks 01J3 / 0AYC ("`O_{W,z} = A/q`").
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory TopologicalSpace AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme

variable {Z X : Scheme.{u}} [IsIntegral Z] (j : Z ⟶ X) [IsClosedImmersion j] (z' : Z)

/-- The generic point specializes to every point. -/
theorem genericPoint_specializes' (z' : Z) : genericPoint Z ⤳ z' :=
  (genericPoint_spec Z).specializes trivial

/-- The kernel of `O_{X, j z'} → O_{Z, z'}` is the prime of `O_{X, j z'}` at the generization `j η_Z`. -/
theorem ker_stalkMap_eq_stalkPrimeOfSpecializes :
    RingHom.ker (j.stalkMap z').hom =
      (stalkPrimeOfSpecializes (j.base.hom.map_specializes (genericPoint_specializes' z'))).asIdeal := by
  have hη : genericPoint Z ⤳ z' := genericPoint_specializes' z'
  have hinj : Function.Injective (Z.presheaf.stalkSpecializes hη).hom :=
    IsFractionRing.injective (Z.presheaf.stalk z') Z.functionField
  have hker : RingHom.ker (j.stalkMap (genericPoint Z)).hom =
      IsLocalRing.maximalIdeal (X.presheaf.stalk (j.base (genericPoint Z))) :=
    IsLocalRing.eq_maximalIdeal
      (RingHom.ker_isMaximal_of_surjective _ (j.stalkMap_surjective (genericPoint Z)))
  ext a
  rw [RingHom.mem_ker, mem_stalkPrimeOfSpecializes_iff]
  have hnat := Scheme.Hom.stalkSpecializes_stalkMap_apply j (genericPoint Z) z' hη a
  constructor
  · intro h0
    have h1 : j.stalkMap (genericPoint Z)
        (X.presheaf.stalkSpecializes (j.base.hom.map_specializes hη) a) = 0 := by
      rw [hnat, h0, map_zero]
    have h2 : X.presheaf.stalkSpecializes (j.base.hom.map_specializes hη) a ∈
        IsLocalRing.maximalIdeal (X.presheaf.stalk (j.base (genericPoint Z))) := by
      rw [← hker]; exact h1
    exact h2
  · intro hnu
    have h2 : X.presheaf.stalkSpecializes (j.base.hom.map_specializes hη) a ∈
        RingHom.ker (j.stalkMap (genericPoint Z)).hom := by
      rw [hker]; exact hnu
    have h3 : Z.presheaf.stalkSpecializes hη (j.stalkMap z' a) = 0 := by
      rw [← hnat]; exact h2
    exact hinj (h3.trans (map_zero _).symm)

/-- `O_{Z,z'} ≃ O_{X, j z'} ⧸ q_{j η}`. -/
def stalkQuotEquivOfIsClosedImmersion :
    Z.presheaf.stalk z' ≃+*
      X.presheaf.stalk (j.base z') ⧸
        (stalkPrimeOfSpecializes (j.base.hom.map_specializes (genericPoint_specializes' z'))).asIdeal :=
  (RingHom.quotientKerEquivOfSurjective (j.stalkMap_surjective z')).symm.trans
    (Ideal.quotEquivOfEq (ker_stalkMap_eq_stalkPrimeOfSpecializes j z'))

theorem stalkQuotEquivOfIsClosedImmersion_stalkMap (a : X.presheaf.stalk (j.base z')) :
    stalkQuotEquivOfIsClosedImmersion j z' (j.stalkMap z' a) = Ideal.Quotient.mk _ a := by
  unfold stalkQuotEquivOfIsClosedImmersion
  have h1 : (RingHom.quotientKerEquivOfSurjective (j.stalkMap_surjective z')).symm
      (j.stalkMap z' a) = Ideal.Quotient.mk _ a := by
    rw [RingEquiv.symm_apply_eq]; rfl
  rw [RingEquiv.trans_apply, h1, Ideal.quotEquivOfEq_mk]

theorem stalkQuotEquivOfIsClosedImmersion_symm_mk (a : X.presheaf.stalk (j.base z')) :
    (stalkQuotEquivOfIsClosedImmersion j z').symm (Ideal.Quotient.mk _ a) = j.stalkMap z' a := by
  rw [RingEquiv.symm_apply_eq, stalkQuotEquivOfIsClosedImmersion_stalkMap]

end AlgebraicGeometry.Scheme

end
