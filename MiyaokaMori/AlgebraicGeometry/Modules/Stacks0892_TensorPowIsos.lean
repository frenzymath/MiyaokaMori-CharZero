import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleSectionRing
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorMonoidalIso
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorPowCanonicalIso
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorPowMapIso
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorUnitIso
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensor
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorPower
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.SheafOfModulesMonoidal
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.Stacks01ct

/-! # Rearrangement isomorphisms for tensor powers

The rearrangement isomorphisms of tensor powers needed in the second and third paragraphs of the proof
of Stacks 0892 (all built from genuine isomorphisms):
* `tensorPowTensorIso`: `(A ⊗ B)^{⊗n} ≅ A^{⊗n} ⊗ B^{⊗n}` (induction on `n`; the inductive step uses
  `(P ⊗ Q) ⊗ (A ⊗ B) ≅ (P ⊗ A) ⊗ (Q ⊗ B)` of a symmetric monoidal category, i.e. the associators and
  braiding of `tensorμ`);
* `tensorPowMulIso`: `(A^{⊗k})^{⊗n} ≅ A^{⊗(k·n)}` (induction on `n`, the inductive step uses
  `tensorPowAddIso`; `k * (n+1) = k*n + k` holds by definition);
* `tensorCongrRightIso`: `A ≅ B ⇒ tensor L A ≅ tensor L B`;
* `tensorAssocIso`: `tensor (tensor A B) C ≅ tensor A (tensor B C)`;
* `unitTensorLeftIso`: `tensor O_X P ≅ P`.

Reference: the proof of Stacks 0892 ("`L^{⊗n} ⊗ f^*M^{⊗(e+b)m}` is the `n`-th power of
`L ⊗ f^*M^{⊗a}`"); coherence of monoidal categories.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
open scoped CategoryTheory.MonoidalCategory

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- `A ≅ B ⇒ tensor L A ≅ tensor L B` (left whiskering in the monoidal `⊗`, transported along
`tensorIsoTensorObj`). -/
noncomputable def tensorCongrRightIso (L : X.Modules) {A B : X.Modules} (e : A ≅ B) :
    AlgebraicGeometry.Scheme.Modules.tensor L A ≅ AlgebraicGeometry.Scheme.Modules.tensor L B :=
  AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj L A ≪≫
    CategoryTheory.MonoidalCategory.whiskerLeftIso L e ≪≫
    (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj L B).symm

/-- `A ≅ B ⇒ tensor A L ≅ tensor B L`. -/
noncomputable def tensorCongrLeftIso {A B : X.Modules} (e : A ≅ B) (L : X.Modules) :
    AlgebraicGeometry.Scheme.Modules.tensor A L ≅ AlgebraicGeometry.Scheme.Modules.tensor B L :=
  AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj A L ≪≫
    CategoryTheory.MonoidalCategory.whiskerRightIso e L ≪≫
    (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj B L).symm

/-- Associator: `tensor (tensor A B) C ≅ tensor A (tensor B C)`. -/
noncomputable def tensorAssocIso (A B C : X.Modules) :
    AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.Modules.tensor A B) C ≅
      AlgebraicGeometry.Scheme.Modules.tensor A (AlgebraicGeometry.Scheme.Modules.tensor B C) :=
  AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ C ≪≫
    CategoryTheory.MonoidalCategory.whiskerRightIso (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj A B) C ≪≫
    α_ A B C ≪≫
    CategoryTheory.MonoidalCategory.whiskerLeftIso A (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj B C).symm ≪≫
    (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj A _).symm

/-- Left unitor: `tensor O_X P ≅ P`. -/
noncomputable def unitTensorLeftIso (P : X.Modules) :
    AlgebraicGeometry.Scheme.Modules.tensor (SheafOfModules.unit X.ringCatSheaf) P ≅ P :=
  AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ P ≪≫
    CategoryTheory.MonoidalCategory.whiskerRightIso
      (CategoryTheory.eqToIso (AlgebraicGeometry.Scheme.Modules.unit_eq_tensorUnit X)) P ≪≫
    λ_ P

/-- Swapping the two middle factors: `(P ⊗ Q) ⊗ (A ⊗ B) ≅ (P ⊗ A) ⊗ (Q ⊗ B)` (associators and braiding). -/
noncomputable def tensorMiddleSwapIso (P Q A B : X.Modules) :
    (P ⊗ Q) ⊗ (A ⊗ B) ≅ (P ⊗ A) ⊗ (Q ⊗ B) :=
  α_ P Q (A ⊗ B) ≪≫
    CategoryTheory.MonoidalCategory.whiskerLeftIso P
      ((α_ Q A B).symm ≪≫ CategoryTheory.MonoidalCategory.whiskerRightIso (β_ Q A) B ≪≫ α_ A Q B) ≪≫
    (α_ P A (Q ⊗ B)).symm

/-- `(A ⊗ B)^{⊗n} ≅ A^{⊗n} ⊗ B^{⊗n}` (`tensorPow` is right-recursive). -/
noncomputable def tensorPowTensorIso (A B : X.Modules) : (n : ℕ) →
    (AlgebraicGeometry.Scheme.Modules.tensorPow (AlgebraicGeometry.Scheme.Modules.tensor A B) n ≅
      AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.Modules.tensorPow A n)
        (AlgebraicGeometry.Scheme.Modules.tensorPow B n))
  | 0 =>
    (AlgebraicGeometry.Scheme.Modules.unitTensorUnitIso X).symm ≪≫
      (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _).symm
  | n + 1 =>
    AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _ ≪≫
      CategoryTheory.MonoidalCategory.tensorIso
        (AlgebraicGeometry.Scheme.Modules.tensorPowTensorIso A B n ≪≫
          AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _)
        (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj A B) ≪≫
      AlgebraicGeometry.Scheme.Modules.tensorMiddleSwapIso _ _ A B ≪≫
      CategoryTheory.MonoidalCategory.tensorIso
        (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ A).symm
        (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ B).symm ≪≫
      (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _).symm

/-- `(A^{⊗k})^{⊗n} ≅ A^{⊗(k * n)}`. -/
noncomputable def tensorPowMulIso (A : X.Modules) (k : ℕ) : (n : ℕ) →
    (AlgebraicGeometry.Scheme.Modules.tensorPow (AlgebraicGeometry.Scheme.Modules.tensorPow A k) n ≅
      AlgebraicGeometry.Scheme.Modules.tensorPow A (k * n))
  | 0 => CategoryTheory.Iso.refl _
  | n + 1 =>
    AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _ ≪≫
      CategoryTheory.MonoidalCategory.whiskerRightIso
        (AlgebraicGeometry.Scheme.Modules.tensorPowMulIso A k n) _ ≪≫
      (AlgebraicGeometry.Scheme.Modules.tensorPowAddIso A (k * n) k).symm

end AlgebraicGeometry.Scheme.Modules

end
