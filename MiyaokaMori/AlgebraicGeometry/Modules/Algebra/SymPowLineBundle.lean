import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.LocallyFreeQuasicoherent
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorMonoidalIso
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensor
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.SheafOfModulesMonoidal
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.SheafSymmetricAlgebra
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveBundle.ProjectiveBundleUniversalProperty

/-! # Symmetric powers of a line bundle

The symmetric powers of a line bundle `W` are its tensor powers: the quotient map `W^{⊗m} → Sym^m W`
is an isomorphism. Also here: the morphism from the `m`-th piece of `Sym(W)` to the monoidal tensor
power, and the comparison isomorphism between the monoidal tensor power (right-multiplication
recursion) and `AlgebraicGeometry.Scheme.Modules.moduleTensorPower` (left-multiplication recursion). Used for
`Sym^q(L^∨) = L^{-q}` in the paper.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open scoped CategoryTheory.MonoidalCategory

/-- For a line bundle `W`, the quotient map `W^{⊗m} → Sym^m W` is an isomorphism (locally `W ≅ O`, where
the transpositions act trivially). -/
instance AlgebraicGeometry.Scheme.Modules.symPowπ_isIso_of_isLineBundle {X : AlgebraicGeometry.Scheme.{u}}
    (W : X.Modules) [W.IsLineBundle] (m : ℕ) :
    CategoryTheory.IsIso (AlgebraicGeometry.Scheme.Modules.symPowπ W m) := by
  let inv := AlgebraicGeometry.Scheme.Modules.symPowDesc W m (𝟙 _)
    (fun i => by
      rw [AlgebraicGeometry.Scheme.Modules.monoidalPowTransp_eq_id_of_isLineBundle,
        Category.id_comp])
  have h₁ : AlgebraicGeometry.Scheme.Modules.symPowπ W m ≫ inv = 𝟙 _ := by
    dsimp [inv]
    rw [AlgebraicGeometry.Scheme.Modules.symPowπ_desc]
  have h₂ : inv ≫ AlgebraicGeometry.Scheme.Modules.symPowπ W m = 𝟙 _ := by
    apply (cancel_epi (AlgebraicGeometry.Scheme.Modules.symPowπ W m)).1
    rw [← Category.assoc, h₁, Category.id_comp, Category.comp_id]
  exact ⟨inv, h₁, h₂⟩

/-- The `m`-th piece of `Sym(W)` back to the tensor power `W^{⊗m}` (`W` a line bundle): a line bundle is
quasi-coherent (`IsLineBundle.isQuasicoherent`), so `symGradedAlgebra` is in the quasi-coherent branch,
and we take the inverse of the quotient map. -/
noncomputable def AlgebraicGeometry.Scheme.Modules.symPartToMonoidalPow {X : AlgebraicGeometry.Scheme.{u}}
    (W : X.Modules) [W.IsLineBundle] (m : ℕ) :
    (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra W).part m ⟶
      AlgebraicGeometry.Scheme.Modules.monoidalPow W m := by
  have hW : W.IsQuasicoherent := inferInstance
  unfold AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
  rw [dif_pos hW]
  exact @CategoryTheory.inv _ _ _ _ (AlgebraicGeometry.Scheme.Modules.symPowπ W m)
    (AlgebraicGeometry.Scheme.Modules.symPowπ_isIso_of_isLineBundle W m)

/-- Comparison of the two encodings of tensor powers: `monoidalPow V n` (right-multiplication recursion in
the monoidal structure) and `AlgebraicGeometry.Scheme.Modules.moduleTensorPower V n` (left-multiplication recursion,
`= Modules.tensor V (…)`). In degree `0` both are `O_X`; in degree `n + 1` use the braiding, the
induction hypothesis, and `Modules.tensor ≅ ⊗`. -/
noncomputable def AlgebraicGeometry.Scheme.Modules.monoidalPowIsoTensorPower {X : AlgebraicGeometry.Scheme.{u}}
    (V : X.Modules) : (n : ℕ) →
    (AlgebraicGeometry.Scheme.Modules.monoidalPow V n ≅ AlgebraicGeometry.Scheme.Modules.moduleTensorPower V n)
  | 0 => CategoryTheory.Iso.refl _
  | n + 1 =>
    (β_ (AlgebraicGeometry.Scheme.Modules.monoidalPow V n) V) ≪≫
      CategoryTheory.MonoidalCategory.whiskerLeftIso V
        (AlgebraicGeometry.Scheme.Modules.monoidalPowIsoTensorPower V n) ≪≫
      (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj V (AlgebraicGeometry.Scheme.Modules.moduleTensorPower V n)).symm

end
