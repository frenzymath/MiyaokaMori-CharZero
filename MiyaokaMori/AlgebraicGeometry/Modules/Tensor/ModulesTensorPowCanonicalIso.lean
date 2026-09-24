import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPullbackMonoidal
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorMonoidalIso
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorPower
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.SheafOfModulesMonoidal

/-! # Canonical isomorphisms for tensor powers

Pullback commutes with tensor powers: `θ_e : g^*(A^{⊗e}) ≅ (g^*A)^{⊗e}` (assembled degree by degree
from the comparison isomorphism of Stacks 01CD); and the tensor powers of the structure sheaf are
trivial, `O^{⊗e} ≅ O` (iterated left unitors).

Source: Stacks 01CD (pullback commutes with tensor products).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open scoped CategoryTheory.MonoidalCategory

/-- The canonical isomorphism `θ_e : g^*(A^{⊗e}) ≅ (g^*A)^{⊗e}`, by recursion following the
right-multiplication recursion of `tensorPow`: for `e = 0` it is `g^*O_Y ≅ O_X` (`pullbackUnitIso`);
for `e + 1` it is `g^*(A^{⊗e} ⊗ A) ≅ g^*A^{⊗e} ⊗ g^*A` (`pullbackTensorIso`, Stacks 01CD) followed
by `θ_e ⊗ 𝟙` (as a right whiskering in the monoidal structure, via `Modules.tensor ≅ ⊗`). -/
noncomputable def AlgebraicGeometry.Scheme.Modules.pullbackTensorPowIso {X Y : AlgebraicGeometry.Scheme.{u}}
    (g : Y ⟶ X) (A : X.Modules) : (e : ℕ) →
    ((AlgebraicGeometry.Scheme.Modules.pullback g).obj (AlgebraicGeometry.Scheme.Modules.tensorPow A e) ≅
      AlgebraicGeometry.Scheme.Modules.tensorPow ((AlgebraicGeometry.Scheme.Modules.pullback g).obj A) e)
  | 0 => AlgebraicGeometry.Scheme.Modules.pullbackUnitIso g
  | e + 1 =>
    AlgebraicGeometry.Scheme.Modules.pullbackTensorIso g (AlgebraicGeometry.Scheme.Modules.tensorPow A e) A ≪≫
      AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _ ≪≫
      CategoryTheory.MonoidalCategory.whiskerRightIso
        (AlgebraicGeometry.Scheme.Modules.pullbackTensorPowIso g A e)
        ((AlgebraicGeometry.Scheme.Modules.pullback g).obj A) ≪≫
      (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _).symm

/-- The tensor powers of the structure sheaf are trivial, `O^{⊗e} ≅ O`: for `e = 0` the identity; for
`e + 1`, `O^{⊗e} ⊗ O ≅ O ⊗ O` (induction) followed by the left unitor. (The unit object of the
localized monoidal structure on `X.Modules` is by construction `SheafOfModules.unit`; the two agree
only after unfolding all definitions, so an explicit `eqToIso` is used, whose proof is `rfl`.) -/
noncomputable def AlgebraicGeometry.Scheme.Modules.unitTensorPowIso (X : AlgebraicGeometry.Scheme.{u}) : (e : ℕ) →
    (AlgebraicGeometry.Scheme.Modules.tensorPow (SheafOfModules.unit X.ringCatSheaf) e ≅
      SheafOfModules.unit X.ringCatSheaf)
  | 0 => CategoryTheory.Iso.refl _
  | e + 1 =>
    AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _ ≪≫
      CategoryTheory.MonoidalCategory.whiskerRightIso (C := X.Modules)
        (AlgebraicGeometry.Scheme.Modules.unitTensorPowIso X e ≪≫
          CategoryTheory.eqToIso (show (show X.Modules from SheafOfModules.unit X.ringCatSheaf) = 𝟙_ X.Modules by
            with_unfolding_all rfl))
        (show X.Modules from SheafOfModules.unit X.ringCatSheaf) ≪≫
      λ_ (show X.Modules from SheafOfModules.unit X.ringCatSheaf)

end
