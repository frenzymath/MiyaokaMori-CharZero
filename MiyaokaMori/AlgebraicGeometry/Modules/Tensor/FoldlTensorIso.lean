import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPullbackMonoidal
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorMonoidalIso
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.ModulesLineBundleZpow
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensor
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModuleTensorPowerIsoTensorPow
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.Stacks01ct
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModuleTensorUnit

/-! # Isomorphism lemmas for iterated tensor products

In the Snapper intersection numbers (Stacks 0BEP) and in Stacks 0BEM the tensor products are written
as `List.foldl (fun G i => G.tensor (L i ^ n i)) O_X l`. This module gives several isomorphism lemmas
about such folds (all stated as `Nonempty (_ ≅ _)`, used only to transfer equalities of `χ` through
`sheafEulerCharacteristic_eq_of_iso`):

* `nonempty_foldl_tensor_iso_of_iso`: isomorphic starting points give isomorphic folds;
* `nonempty_foldl_tensor_tensor_iso`: `foldl f (A ⊗ E) l ≅ (foldl f A l) ⊗ E` (pushing an outer tensor
  factor to the starting point);
* `nonempty_pullback_foldl_tensor_iso`: `f^*(foldl … A l) ≅ foldl … (f^*A) l` (pullback commutes with
  the fold, given pullback isomorphisms for each factor);
* `nonempty_pullback_zpow_indicator_iso`: `f^*(L^{e}) ≅ (f^*L)^{e}` for `e ∈ {0, 1}` (the definition
  in 0BEP only uses exponents 0/1; general integer exponents would need pullback to commute with
  duals, which is not needed here);
* `isLineBundle_foldl_tensor`: a fold of line bundles is a line bundle.

Used in Stacks 0BEU. The isomorphisms in the left/right factor `tensorIsoLeft` / `tensorIsoRight` are
those of `ModuleTensorPowerIsoTensorPow`. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v

open CategoryTheory CategoryTheory.Limits
open scoped AlgebraicGeometry
open scoped CategoryTheory.MonoidalCategory

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

/- Isomorphisms in the left/right factor of `Modules.tensor`: `tensorIsoLeft` / `tensorIsoRight` from
   `ModuleTensorPowerIsoTensorPow`. -/

/-- `(A ⊗ E) ⊗ C ≅ (A ⊗ C) ⊗ E` (associator and braiding). -/
def tensorSwapRightIso (A E C : X.Modules) :
    AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.Modules.tensor A E) C ≅
      AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.Modules.tensor A C) E :=
  AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ C ≪≫
    CategoryTheory.MonoidalCategory.whiskerRightIso
      (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj A E) C ≪≫
    α_ A E C ≪≫
    CategoryTheory.MonoidalCategory.whiskerLeftIso A (β_ E C) ≪≫
    (α_ A C E).symm ≪≫
    CategoryTheory.MonoidalCategory.whiskerRightIso
      (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj A C).symm E ≪≫
    (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ E).symm

section Fold

variable {ι : Type v} (C : ι → X.Modules)

/-- Isomorphic starting points give isomorphic folds. -/
theorem nonempty_foldl_tensor_iso_of_iso :
    ∀ (l : List ι) {A A' : X.Modules}, (A ≅ A') →
      Nonempty (l.foldl (fun G i => AlgebraicGeometry.Scheme.Modules.tensor G (C i)) A ≅
        l.foldl (fun G i => AlgebraicGeometry.Scheme.Modules.tensor G (C i)) A')
  | [], _, _, e => ⟨e⟩
  | i :: l, _, _, e => nonempty_foldl_tensor_iso_of_iso l (tensorIsoLeft e (C i))

/-- An outer tensor factor can be pushed to the starting point: `foldl f (A ⊗ E) l ≅ (foldl f A l) ⊗ E`. -/
theorem nonempty_foldl_tensor_tensor_iso :
    ∀ (l : List ι) (A E : X.Modules),
      Nonempty (l.foldl (fun G i => AlgebraicGeometry.Scheme.Modules.tensor G (C i))
          (AlgebraicGeometry.Scheme.Modules.tensor A E) ≅
        AlgebraicGeometry.Scheme.Modules.tensor
          (l.foldl (fun G i => AlgebraicGeometry.Scheme.Modules.tensor G (C i)) A) E)
  | [], A, E => ⟨Iso.refl _⟩
  | i :: l, A, E => by
    obtain ⟨e₁⟩ := nonempty_foldl_tensor_iso_of_iso C l (tensorSwapRightIso A E (C i))
    obtain ⟨e₂⟩ := nonempty_foldl_tensor_tensor_iso l (AlgebraicGeometry.Scheme.Modules.tensor A (C i)) E
    exact ⟨e₁ ≪≫ e₂⟩

/-- `L^e` is a line bundle for `e ∈ {0, 1}` (without going through `IsLineBundleZpow`). -/
theorem isLineBundle_zpow_indicator (L : X.Modules) [L.IsLineBundle] (p : Prop) [Decidable p] :
    (L ^ (if p then (1 : ℤ) else 0)).IsLineBundle := by
  split_ifs
  · exact SheafOfModules.IsLineBundle.tensor L (SheafOfModules.unit X.ringCatSheaf)
  · exact SheafOfModules.IsLineBundle.unit X

/-- A fold of line bundles is a line bundle. -/
theorem isLineBundle_foldl_tensor [∀ i, (C i).IsLineBundle] :
    ∀ (l : List ι) (A : X.Modules) [A.IsLineBundle],
      (l.foldl (fun G i => AlgebraicGeometry.Scheme.Modules.tensor G (C i)) A).IsLineBundle
  | [], _, h => h
  | i :: l, A, _ => isLineBundle_foldl_tensor l (AlgebraicGeometry.Scheme.Modules.tensor A (C i))

variable {Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)

/-- Pullback commutes with the fold, given pullback isomorphisms `f^*(C i) ≅ C' i` for each factor. -/
theorem nonempty_pullback_foldl_tensor_iso (C : ι → Y.Modules) (C' : ι → X.Modules)
    (hC : ∀ i, Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback f).obj (C i) ≅ C' i)) :
    ∀ (l : List ι) (A : Y.Modules),
      Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback f).obj
          (l.foldl (fun G i => AlgebraicGeometry.Scheme.Modules.tensor G (C i)) A) ≅
        l.foldl (fun G i => AlgebraicGeometry.Scheme.Modules.tensor G (C' i))
          ((AlgebraicGeometry.Scheme.Modules.pullback f).obj A))
  | [], A => ⟨Iso.refl _⟩
  | i :: l, A => by
    obtain ⟨e₁⟩ := nonempty_pullback_foldl_tensor_iso C C' hC l
      (AlgebraicGeometry.Scheme.Modules.tensor A (C i))
    obtain ⟨ei⟩ := hC i
    obtain ⟨e₂⟩ := nonempty_foldl_tensor_iso_of_iso C' l
      (AlgebraicGeometry.Scheme.Modules.pullbackTensorIso f A (C i) ≪≫
        tensorIsoRight ((AlgebraicGeometry.Scheme.Modules.pullback f).obj A) ei)
    exact ⟨e₁ ≪≫ e₂⟩

/-- `f^*(L^e) ≅ (f^*L)^e` for `e ∈ {0, 1}` (`L^0 = O` and `L^1 = L ⊗ O` by definition). -/
theorem nonempty_pullback_zpow_indicator_iso (L : Y.Modules) (p : Prop) [Decidable p] :
    Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback f).obj (L ^ (if p then (1 : ℤ) else 0)) ≅
      ((AlgebraicGeometry.Scheme.Modules.pullback f).obj L) ^ (if p then (1 : ℤ) else 0)) := by
  split_ifs
  · exact ⟨AlgebraicGeometry.Scheme.Modules.pullbackTensorIso f L (SheafOfModules.unit Y.ringCatSheaf) ≪≫
      tensorIsoRight _ (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso f)⟩
  · exact ⟨AlgebraicGeometry.Scheme.Modules.pullbackUnitIso f⟩

end Fold

end AlgebraicGeometry.Scheme.Modules

end
