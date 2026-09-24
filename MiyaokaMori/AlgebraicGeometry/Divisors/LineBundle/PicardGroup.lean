import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.VarietyLineBundle
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.IdealSheafToModules
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModulesDual
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensor
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.SheafOfModulesMonoidal
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleOfModules
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.Stacks01ct
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorMonoidalIso
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.TensorRightInvertibleEquivalence

/-! # The Picard group

The Picard group `Pic(X)`: the abelian group of isomorphism classes of line bundles (invertible
sheaves) on `X` under tensor product.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open scoped CategoryTheory.MonoidalCategory

/-- The Picard group `Pic(X)`: isomorphism classes of line bundles on `X`. -/
def PicardGroup {k : Type u} [Field k] (X : Variety k) : Type (u + 1) :=
  Quotient (CategoryTheory.isIsomorphicSetoid (LineBundle X))

/-- `LineBundle X` is an `InducedCategory` over `X.carrier.Modules`, so an isomorphism of packaged line
bundles is the same as an isomorphism of the underlying module sheaves. -/
def LineBundle.isoOfModules {k : Type u} [Field k] {X : Variety k} {L M : LineBundle X}
    (e : L.toModules ≅ M.toModules) : L ≅ M :=
  (CategoryTheory.fullyFaithfulInducedFunctor
    (fun L : LineBundle X => L.toModules)).preimageIso e

/-- The converse direction. -/
def LineBundle.toModulesIso {k : Type u} [Field k] {X : Variety k} {L M : LineBundle X}
    (e : L ≅ M) : L.toModules ≅ M.toModules :=
  (CategoryTheory.inducedFunctor (fun L : LineBundle X => L.toModules)).mapIso e

/-- Functoriality of `Modules.tensor` in isomorphisms (through `tensorIsoTensorObj` to the monoidal `⊗`
and back). -/
noncomputable def AlgebraicGeometry.Scheme.Modules.tensorIsoCongr {X : AlgebraicGeometry.Scheme.{u}}
    {A A' B B' : X.Modules} (ea : A ≅ A') (eb : B ≅ B') :
    AlgebraicGeometry.Scheme.Modules.tensor A B ≅ AlgebraicGeometry.Scheme.Modules.tensor A' B' :=
  AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj A B ≪≫
    CategoryTheory.MonoidalCategory.tensorIso ea eb ≪≫
    (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj A' B').symm

/-- The tensor product of packaged line bundles (underlying module sheaf `Modules.tensor`; the line bundle
property is the instance of Stacks 01CT). -/
noncomputable def LineBundle.tensorPack {k : Type u} [Field k] {X : Variety k}
    (L M : LineBundle X) : LineBundle X :=
  letI : (AlgebraicGeometry.Scheme.Modules.tensor L.toModules M.toModules).IsLineBundle :=
    SheafOfModules.IsLineBundle.tensor L.toModules M.toModules
  LineBundle.ofModules (AlgebraicGeometry.Scheme.Modules.tensor L.toModules M.toModules)

/-- The dual of a packaged line bundle. -/
noncomputable def LineBundle.dualPack {k : Type u} [Field k] {X : Variety k}
    (L : LineBundle X) : LineBundle X :=
  letI : (AlgebraicGeometry.Scheme.Modules.dual L.toModules).IsLineBundle :=
    SheafOfModules.IsLineBundle.dual L.toModules
  LineBundle.ofModules (AlgebraicGeometry.Scheme.Modules.dual L.toModules)

/-- The group structure: `⟦L⟧ * ⟦M⟧ = ⟦L ⊗ M⟧`, `1 = ⟦O_X⟧`, `⟦L⟧⁻¹ = ⟦L^∨⟧`. Well-definedness uses
`tensorIsoCongr`; associativity, unit and commutativity use the symmetric monoidal structure of
`X.Modules` (associator, unitors, braiding); inverses use `nonempty_tensorObj_dual_iso_tensorUnit`
(`L ⊗ L^∨ ≅ 𝟙_`). -/

noncomputable instance {k : Type u} [Field k] (X : Variety k) : CommGroup (PicardGroup X) where
  mul := Quotient.map₂ LineBundle.tensorPack (by
    rintro L L' ⟨e⟩ M M' ⟨f⟩
    exact ⟨LineBundle.isoOfModules
      (AlgebraicGeometry.Scheme.Modules.tensorIsoCongr (LineBundle.toModulesIso e)
        (LineBundle.toModulesIso f))⟩)
  one := Quotient.mk _ (LineBundle.ofModules (SheafOfModules.unit X.toScheme.ringCatSheaf))
  -- well-definedness of the dual: inverses are unique in a monoidal category. If a ≅ a' (e), u : a ⊗ b ≅ 𝟙 and u' : a' ⊗ b' ≅ 𝟙, then
  -- b ≅ 𝟙 ⊗ b ≅ (a' ⊗ b') ⊗ b ≅ (a ⊗ b') ⊗ b ≅ (b' ⊗ a) ⊗ b ≅ b' ⊗ (a ⊗ b) ≅ b' ⊗ 𝟙 ≅ b'
  inv := Quotient.map LineBundle.dualPack (by
    rintro L L' ⟨e⟩
    obtain ⟨u⟩ :=
      AlgebraicGeometry.Scheme.Modules.nonempty_tensorObj_dual_iso_tensorUnit L.toModules
    obtain ⟨u'⟩ :=
      AlgebraicGeometry.Scheme.Modules.nonempty_tensorObj_dual_iso_tensorUnit L'.toModules
    have em := LineBundle.toModulesIso e
    exact ⟨LineBundle.isoOfModules
      ((λ_ (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).symm ≪≫
        CategoryTheory.MonoidalCategory.tensorIso u'.symm (CategoryTheory.Iso.refl _) ≪≫
        CategoryTheory.MonoidalCategory.tensorIso
          (CategoryTheory.MonoidalCategory.tensorIso em.symm (CategoryTheory.Iso.refl _))
          (CategoryTheory.Iso.refl _) ≪≫
        CategoryTheory.MonoidalCategory.tensorIso (β_ _ _) (CategoryTheory.Iso.refl _) ≪≫
        α_ _ _ _ ≪≫
        CategoryTheory.MonoidalCategory.tensorIso (CategoryTheory.Iso.refl _) u ≪≫
        ρ_ _)⟩)
  mul_assoc := by
    refine Quotient.ind fun L => Quotient.ind fun M => Quotient.ind fun N => ?_
    refine Quotient.sound ⟨LineBundle.isoOfModules ?_⟩
    exact AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _ ≪≫
      CategoryTheory.MonoidalCategory.tensorIso
        (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj L.toModules M.toModules)
        (CategoryTheory.Iso.refl N.toModules) ≪≫
      α_ _ _ _ ≪≫
      CategoryTheory.MonoidalCategory.tensorIso (CategoryTheory.Iso.refl L.toModules)
        (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj M.toModules N.toModules).symm ≪≫
      (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _).symm
  one_mul := by
    refine Quotient.ind fun L => ?_
    refine Quotient.sound ⟨LineBundle.isoOfModules ?_⟩
    exact AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _ ≪≫
      CategoryTheory.MonoidalCategory.tensorIso
        (CategoryTheory.eqToIso (AlgebraicGeometry.Scheme.Modules.unit_eq_tensorUnit X.toScheme))
        (CategoryTheory.Iso.refl L.toModules) ≪≫
      λ_ _
  mul_one := by
    refine Quotient.ind fun L => ?_
    refine Quotient.sound ⟨LineBundle.isoOfModules ?_⟩
    exact AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _ ≪≫
      CategoryTheory.MonoidalCategory.tensorIso (CategoryTheory.Iso.refl L.toModules)
        (CategoryTheory.eqToIso (AlgebraicGeometry.Scheme.Modules.unit_eq_tensorUnit X.toScheme)) ≪≫
      ρ_ _
  inv_mul_cancel := by
    refine Quotient.ind fun L => ?_
    obtain ⟨u⟩ :=
      AlgebraicGeometry.Scheme.Modules.nonempty_tensorObj_dual_iso_tensorUnit L.toModules
    exact Quotient.sound ⟨LineBundle.isoOfModules
      (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _ ≪≫ β_ _ _ ≪≫ u ≪≫
        (CategoryTheory.eqToIso
          (AlgebraicGeometry.Scheme.Modules.unit_eq_tensorUnit X.toScheme)).symm)⟩
  mul_comm := by
    refine Quotient.ind fun L => Quotient.ind fun M => ?_
    refine Quotient.sound ⟨LineBundle.isoOfModules ?_⟩
    exact AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _ ≪≫ β_ _ _ ≪≫
      (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _).symm

end
