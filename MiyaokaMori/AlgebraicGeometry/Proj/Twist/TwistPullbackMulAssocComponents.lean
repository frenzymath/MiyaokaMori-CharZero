import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.TwistPullbackPowBlock
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.RelativeProjTwistMulAssoc

/-! # Associativity of `twistPullbackMul`: the two components

`twistPullbackMul_assoc'` (`TwistPullbackMulAssoc`; `twistPullbackMul_assoc` in `TwistPullbackPow` is an
alias of it) is derived from the two components proved here:

* twist side: `twistPairMul_assoc_add_assoc` — the associativity step of `twistPairMul` with the index transport
  `eqToHom (congrArg (twist S) (add_assoc a b c).symm)` exactly as it is spelled in the statement; proved by the
  double-ext lemma `assoc_of_app_tensorSections` (`TensorTripleHomExt`) and the section-level `twistMul_app_assoc`
  (`RelativeProjTwistMulAssoc`);
* pullback side: `pullbackPairMul_assoc_tensorAssocIso` — from `pullbackPairMul_assoc_general`
  (`PullbackTensorPowMul`) and the definition of `tensorAssocIso`;
* the two are combined by the abstract coherence lemma `combMul_assoc_conj` (`TensorPairMul`), whose statement
  has the shape of the target after unfolding `tensorMapHom` and `tensorAssocIso`.

Compile-time note: the twist component is *not* obtained from the transport form `twistPairMul_assoc`
(`TwistPullbackPowBlock`): identifying an `eqToHom (congrArg (twist S) (add_assoc a b c).symm)` with an `eqToHom` built
from a different proof or spelling of `a + b + c = a + (b + c)` costs about 20 s of kernel type checking per occurrence in
this category, so the derivation re-elaborates the target spelling and only ever meets the section-level statement
syntactically.

Source: Stacks 01MO, 01CD. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- `tensorAssocIso` unfolded, `hom`. -/
theorem tensorAssocIso_hom_eq (A B C : X.Modules) :
    (tensorAssocIso A B C).hom =
      (tensorIsoTensorObj _ C).hom ≫ ((tensorIsoTensorObj A B).hom ▷ C) ≫ (α_ A B C).hom ≫
        (A ◁ (tensorIsoTensorObj B C).inv) ≫ (tensorIsoTensorObj A _).inv := rfl

/-- `tensorAssocIso` unfolded, `inv`. -/
theorem tensorAssocIso_inv_eq (A B C : X.Modules) :
    (tensorAssocIso A B C).inv =
      (tensorIsoTensorObj A _).hom ≫ (A ◁ (tensorIsoTensorObj B C).hom) ≫ (α_ A B C).inv ≫
        ((tensorIsoTensorObj A B).inv ▷ C) ≫ (tensorIsoTensorObj _ C).inv := by
  show (((_ ≫ _) ≫ _) ≫ _) ≫ _ = _
  simp only [Category.assoc]
  rfl

variable {Y : AlgebraicGeometry.Scheme.{u}} (π : Y ⟶ X)

/-- Pullback component of the associativity of `twistPullbackMul`. -/
theorem pullbackPairMul_assoc_tensorAssocIso (M N R : X.Modules) :
    ((AlgebraicGeometry.Scheme.Modules.pullback π).obj M ◁ pullbackPairMul π N R) ≫
        pullbackPairMul π M (AlgebraicGeometry.Scheme.Modules.tensor N R) ≫
        (AlgebraicGeometry.Scheme.Modules.pullback π).map (tensorAssocIso M N R).inv =
      (α_ _ _ _).inv ≫ (pullbackPairMul π M N ▷ (AlgebraicGeometry.Scheme.Modules.pullback π).obj R) ≫
        pullbackPairMul π (AlgebraicGeometry.Scheme.Modules.tensor M N) R := by
  have h := pullbackPairMul_assoc_general π M N R (AlgebraicGeometry.Scheme.Modules.tensor M N) (tensorIsoTensorObj M N).inv
  have e : pullbackPairMul π M (AlgebraicGeometry.Scheme.Modules.tensor N R) ≫
      (AlgebraicGeometry.Scheme.Modules.pullback π).map (tensorAssocIso M N R).inv =
      (pullbackTensorObjIso π M (AlgebraicGeometry.Scheme.Modules.tensor N R)).inv ≫
        (AlgebraicGeometry.Scheme.Modules.pullback π).map ((M ◁ (tensorIsoTensorObj N R).hom) ≫ (α_ M N R).inv ≫
          ((tensorIsoTensorObj M N).inv ▷ R) ≫ (tensorIsoTensorObj _ R).inv) := by
    unfold pullbackPairMul
    rw [tensorAssocIso_inv_eq, Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_assoc]
  rw [e]
  exact h

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.relativeProj

variable {X : AlgebraicGeometry.Scheme.{u}} (S : X.GradedQCAlgebra)

/-- Twist component of the associativity of `twistPullbackMul`, with the index transport spelled as in the target. -/
theorem twistPairMul_assoc_add_assoc (a b c : ℤ) :
    (AlgebraicGeometry.Scheme.relativeProj.twist S a ◁ twistPairMul S b c) ≫ twistPairMul S a (b + c) ≫
        CategoryTheory.eqToHom (congrArg (AlgebraicGeometry.Scheme.relativeProj.twist S) (add_assoc a b c).symm) =
      (α_ _ _ _).inv ≫ (twistPairMul S a b ▷ AlgebraicGeometry.Scheme.relativeProj.twist S c) ≫
        twistPairMul S (a + b) c := by
  have h := AlgebraicGeometry.Scheme.Modules.assoc_of_app_tensorSections (twistPairMul S b c) (𝟙 _)
    (twistPairMul S a (b + c))
    (CategoryTheory.eqToHom (congrArg (AlgebraicGeometry.Scheme.relativeProj.twist S) (add_assoc a b c).symm))
    (twistPairMul S a b) (𝟙 _) (twistPairMul S (a + b) c) (𝟙 _) (fun V x y z => by
      rw [Modules.Hom.id_app, Modules.Hom.id_app, Modules.Hom.id_app]
      show (CategoryTheory.eqToHom (congrArg (AlgebraicGeometry.Scheme.relativeProj.twist S) (add_assoc a b c).symm)).app V
        ((twistPairMul S a (b + c)).app V (Modules.tensorSections _ _ V x ((twistPairMul S b c).app V
          (Modules.tensorSections _ _ V y z)))) =
        (twistPairMul S (a + b) c).app V (Modules.tensorSections _ _ V ((twistPairMul S a b).app V
          (Modules.tensorSections _ _ V x y)) z)
      rw [twistPairMul_app_tensorSections, twistPairMul_app_tensorSections, twistPairMul_app_tensorSections,
        twistPairMul_app_tensorSections]
      exact (AlgebraicGeometry.Scheme.relativeProj.twistMul_app_assoc S a b c V x y z).symm)
  simpa only [Category.comp_id] using h


end AlgebraicGeometry.Scheme.relativeProj

end
