import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedAlgebraTotal
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModulesDual
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.ModulesFiniteTypeInstances
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.RelativeSpec
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.RelativeSpecUniversalProperty
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.SheafOfModulesMonoidal
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.SheafSymmetricAlgebra
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotalSpaceVectorBundle
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpaceZeroSectionData
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotalSpaceZeroSectionMul
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpaceZeroSectionOne

/-! # The zero section of the total space

The zero section `σ_0 : X ⟶ Tot(V)` of the total space (corresponding to the augmentation
`Sym(V^∨) → O_X`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open scoped CategoryTheory.MonoidalCategory

/-- The augmentation `Sym(W) → O_X = (𝟙_X)_*O_X` is an `O_X`-algebra map.
    This holds for every `W` (both branches are true). Proof route:
    1. Split according to whether `W` is quasi-coherent (the `dite` of `symGradedAlgebra`;
       `symAugmentationZero` makes the same branch choice). Quasi-coherent branch: part 0 = `Sym^0 W`,
       `symAugmentationZero = symPowDesc W 0 (𝟙 _) _`; trivial branch: part 0 = `𝟙_`, take `𝟙`.
    2. Unit: `total.one = S.one ≫ Sigma.ι 0`, `Sigma.ι 0 ≫ Sigma.desc = symAugmentationZero`; in the
       quasi-coherent branch `S.one = symPowπ W 0` and `symPowπ_desc` gives
       `symPowπ 0 ≫ symPowDesc 0 (𝟙) = 𝟙`; in the trivial branch `𝟙 ≫ 𝟙 = 𝟙`. The section map of
       `(pushforwardId X).inv` on `U` is the identity of `Γ(X, U) = Γ(X, 𝟙⁻¹U)`, so `1 ↦ 1`.
    3. Multiplication: by `mul` of `GradedQCAlgebra.total` (curried in the two coproduct variables, with
       component `(m, n)` equal to `S.mul m n ≫ Sigma.ι (m+n)`) and bilinearity of `tensorSections`, it
       suffices to argue componentwise: for `(m, n) ≠ (0, 0)` one has `m + n > 0`, the positive-degree
       component of the left-hand side through `Sigma.desc` is `0`, and one factor on the right is `0`;
       for `(0, 0)` one shows `S.mul 0 0 ≫ ε_0 = (ε_0 ⊗ ε_0) ≫ λ_{𝟙}`: in the quasi-coherent branch,
       after precomposing with the epimorphism `symPowπ 0 ⊗ symPowπ 0`, `symPowMul 0 0` is descended from
       `monoidalPowCat W 0 0 = λ_{𝟙}` (or `ρ`; they agree on `𝟙`), so both sides are `λ_{𝟙}`; in the
       trivial branch it is `λ_{𝟙}` by definition.
    4. "`𝟙 ⊗ 𝟙 → 𝟙` (left unitor) is multiplication on sections": `tensorSections (𝟙_) (𝟙_) U a b ↦ a * b`. -/
theorem AlgebraicGeometry.Scheme.Modules.symAugmentation_isAlgebraMap {X : AlgebraicGeometry.Scheme.{u}}
    (W : X.Modules) :
    (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra W).total.IsAlgebraMapToPushforward
      (CategoryTheory.CategoryStruct.id X)
      (AlgebraicGeometry.Scheme.Modules.symAugmentation W ≫
        (AlgebraicGeometry.Scheme.Modules.pushforwardId X).inv.app (SheafOfModules.unit X.ringCatSheaf)) := by
  constructor
  · intro U a b
    exact AlgebraicGeometry.Scheme.Modules.symAugmentation_mul W U a b
  · intro U
    exact AlgebraicGeometry.Scheme.Modules.symAugmentation_one W U

/- The zero section: the `X`-morphism `X → Tot(V)` corresponding to the augmentation
   `Sym(V^∨) → O_X = (𝟙_X)_* O_X` under the universal property of the relative Spec (`T = (X, 𝟙)`).
   `𝟙_ X.Modules` is `SheafOfModules.unit` (the unit of the monoidal structure is the structure sheaf). -/

noncomputable def AlgebraicGeometry.Scheme.zeroSection {X : AlgebraicGeometry.Scheme.{u}}
    (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType] : X ⟶ (AlgebraicGeometry.Scheme.totalSpace V).left :=
  ((AlgebraicGeometry.Scheme.relativeSpecHomEquiv
      (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual V)).total
      (CategoryTheory.Over.mk (CategoryTheory.CategoryStruct.id X))).symm
    ⟨AlgebraicGeometry.Scheme.Modules.symAugmentation (AlgebraicGeometry.Scheme.Modules.dual V) ≫
        (AlgebraicGeometry.Scheme.Modules.pushforwardId X).inv.app (SheafOfModules.unit X.ringCatSheaf),
      AlgebraicGeometry.Scheme.Modules.symAugmentation_isAlgebraMap
        (AlgebraicGeometry.Scheme.Modules.dual V)⟩).left

theorem AlgebraicGeometry.Scheme.zeroSection_comp {X : AlgebraicGeometry.Scheme.{u}}
    (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType] :
    AlgebraicGeometry.Scheme.zeroSection V ≫ (AlgebraicGeometry.Scheme.totalSpace V).hom =
      CategoryTheory.CategoryStruct.id X := by
  unfold AlgebraicGeometry.Scheme.zeroSection AlgebraicGeometry.Scheme.totalSpace
  exact CategoryTheory.Over.w _

end
