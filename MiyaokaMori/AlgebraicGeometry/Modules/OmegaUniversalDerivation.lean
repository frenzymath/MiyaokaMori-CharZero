import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Differentials.RelativeDifferentials

/-! # The universal property of the sheaf of relative differentials

The universal property of `Ω_{X/S}`: for every `O_X`-module `F`,
`Hom_{O_X}(Ω_{X/S}, F) ≃ Der_{f⁻¹O_S}(O_X, F)` (by composition with `d_{X/S}`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

noncomputable def AlgebraicGeometry.Omega.homEquivDerivation {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S)
    (F : X.Modules) :
    (AlgebraicGeometry.Omega f ⟶ F) ≃
      ((F.val).Derivation' (AlgebraicGeometry.Scheme.inverseImageStructureMap f)) :=
  -- the sheafification adjunction (`restrictScalars (𝟙 _)` is the identity by definition) followed by
  -- the universal property of presheaf Kähler differentials
  (PresheafOfModules.sheafificationHomEquiv (𝟙 X.ringCatSheaf.obj)).trans
    { toFun := fun g => (PresheafOfModules.DifferentialsConstruction.derivation'
          (AlgebraicGeometry.Scheme.inverseImageStructureMap f)).postcomp (N := F.val) g
      invFun := fun d => (PresheafOfModules.DifferentialsConstruction.isUniversal'
          (AlgebraicGeometry.Scheme.inverseImageStructureMap f)).desc (M' := F.val) d
      left_inv := fun _ => (PresheafOfModules.DifferentialsConstruction.isUniversal'
          (AlgebraicGeometry.Scheme.inverseImageStructureMap f)).postcomp_injective _ _
            ((PresheafOfModules.DifferentialsConstruction.isUniversal'
              (AlgebraicGeometry.Scheme.inverseImageStructureMap f)).fac _)
      right_inv := fun d => (PresheafOfModules.DifferentialsConstruction.isUniversal'
          (AlgebraicGeometry.Scheme.inverseImageStructureMap f)).fac d }

end
