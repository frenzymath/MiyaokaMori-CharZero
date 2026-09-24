import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Differentials.RelativeDifferentials
import MiyaokaMori.AlgebraicGeometry.Modules.OmegaOpenImmersionSquare

/-! # Relative differentials and open subschemes (Stacks 01US)

Stacks 01US: `Ω` is compatible with open subschemes — for `f : X → S` and opens `U ⊆ X`, `V ⊆ S` with
`f(U) ⊆ V`, `Ω_{X/S}|_U ≅ Ω_{U/V}` (compatibly with `d`). Used for `E = s^*T_{Z/C}` which only sees `Z^×`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open scoped AlgebraicGeometry

theorem AlgebraicGeometry.Omega_restrict_open {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
    (U : X.Opens) (V : S.Opens) (e : U ≤ f ⁻¹ᵁ V) :
    Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback U.ι).obj (AlgebraicGeometry.Omega f) ≅
      AlgebraicGeometry.Omega (f.resLE V U e)) :=
  ⟨(AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback U.ι).symm.app _ ≪≫
    AlgebraicGeometry.Omega.restrictIso f (f.resLE V U e) U.ι V.ι
      (AlgebraicGeometry.Scheme.Hom.resLE_comp_ι f e)⟩

end
