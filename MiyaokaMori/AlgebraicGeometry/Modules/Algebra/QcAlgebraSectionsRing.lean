import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.PresheafModulesTensorLocalIso
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorSectionsCoherence
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedQcAlgebraSectionsRing
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensor
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.QuasicoherentAlgebra
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.SheafOfModulesMonoidal

/-! # The section ring of a quasi-coherent algebra

The section ring `A(U) = Γ(U, A)` of a quasi-coherent algebra `A` on an open `U` (multiplication from
`A.mul`); restriction gives ring homomorphisms, and the unit gives `Γ(X,U) → A(U)`. These are the rings
glued in the relative Spec.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry CategoryTheory.MonoidalCategory TensorProduct

noncomputable section

open scoped AlgebraicGeometry

/-- The multiplication at the presheaf level `A ⊗ₚ A → A`: `A.mul` is pulled back along
`L(A ⊗ₚ A) ≅ L A ⊗ L A` (the `μ` of the localized monoidal structure) and the sheafification counit
`L A ≅ A` to a morphism of sheaves `L(A ⊗ₚ A) → A`, then transposed along the sheafification
adjunction to a morphism of presheaves (the target is in the image of the right adjoint, whose
underlying presheaf is the sections of `A`). -/
noncomputable def AlgebraicGeometry.Scheme.QCAlgebra.presheafMul {X : AlgebraicGeometry.Scheme.{u}}
    (A : X.QCAlgebra) :
    (CategoryTheory.MonoidalCategoryStruct.tensorObj A.carrier.val A.carrier.val :
        _root_.PresheafOfModules.{u} X.ringCatSheaf.obj) ⟶
      (_root_.PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj A.carrier.val :=
  haveI := AlgebraicGeometry.Scheme.PresheafOfModules.sheafificationW_isMonoidal X
  haveI : (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).IsLocalization
      ((CategoryTheory.MorphismProperty.isomorphisms (SheafOfModules.{u} X.ringCatSheaf)).inverseImage
        (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))) :=
    (_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).isLocalization
  let adj := _root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  let e : ((_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj A.carrier.val : X.Modules) ≅
      A.carrier := (CategoryTheory.asIso adj.counit).app A.carrier
  let μ := CategoryTheory.Localization.Monoidal.μ
    (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))
    ((CategoryTheory.MorphismProperty.isomorphisms (SheafOfModules.{u} X.ringCatSheaf)).inverseImage
      (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)))
    (AlgebraicGeometry.Scheme.Modules.sheafificationUnitIso X) A.carrier.val A.carrier.val
  let t : CategoryTheory.MonoidalCategoryStruct.tensorObj (C := X.Modules)
      ((_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj A.carrier.val)
      ((_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj A.carrier.val) ⟶
      CategoryTheory.MonoidalCategoryStruct.tensorObj (C := X.Modules) A.carrier A.carrier :=
    CategoryTheory.MonoidalCategoryStruct.tensorHom (C := X.Modules) e.hom e.hom
  let m : ((_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
      (CategoryTheory.MonoidalCategoryStruct.tensorObj A.carrier.val A.carrier.val) : X.Modules) ⟶ A.carrier :=
    μ.inv ≫ t ≫ A.mul
  adj.homEquiv _ _ m

/-- The section ring: the underlying type is `Γ(A.carrier, U)`, with the `CommRing` structure given by
`A.mul` and `A.one` on sections. -/
noncomputable def AlgebraicGeometry.Scheme.QCAlgebra.sectionsRing {X : AlgebraicGeometry.Scheme.{u}}
    (A : X.QCAlgebra) (U : X.Opens) : Type u :=
  A.carrier.val.obj (Opposite.op U)

noncomputable instance {X : AlgebraicGeometry.Scheme.{u}} (A : X.QCAlgebra) (U : X.Opens) :
    AddCommGroup (A.sectionsRing U) :=
  inferInstanceAs (AddCommGroup (A.carrier.val.obj (Opposite.op U)))

/-- The multiplication of sections, `a · b := presheafMul(a ⊗ b)` (evaluated on the sectionwise tensor
product `A(U) ⊗_{O(U)} A(U)`). -/
noncomputable def AlgebraicGeometry.Scheme.QCAlgebra.sectionsMul {X : AlgebraicGeometry.Scheme.{u}}
    (A : X.QCAlgebra) (U : X.Opens) (a b : A.sectionsRing U) : A.sectionsRing U :=
  (A.presheafMul.app (Opposite.op U)).hom
    (@TensorProduct.tmul (X.presheaf.obj (Opposite.op U)) _ (A.carrier.val.obj (Opposite.op U))
      (A.carrier.val.obj (Opposite.op U)) _ _ (A.carrier.val.obj (Opposite.op U)).isModule
      (A.carrier.val.obj (Opposite.op U)).isModule a b)

/-- The unit section: `A.one` applied to the unit section `1 ∈ O(U)` of the structure sheaf. -/
noncomputable def AlgebraicGeometry.Scheme.QCAlgebra.sectionsOne {X : AlgebraicGeometry.Scheme.{u}}
    (A : X.QCAlgebra) (U : X.Opens) : A.sectionsRing U :=
  (A.one.val.app (Opposite.op U)).hom (1 : X.ringCatSheaf.obj.obj (Opposite.op U))

section SectionsRingAux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- The pointwise image of `A.one` and the multiplication of sections: `A.one.app U r * a = r • a` (the
axiom `QCAlgebra.one_mul` on sections, with `Modules.leftUnitor_app_tensorSections` and
`Modules.tensorHom_tensorSections`). -/
theorem AlgebraicGeometry.Scheme.QCAlgebra.sectionsOne_app_sectionsMul
    {X : AlgebraicGeometry.Scheme.{u}} (A : X.QCAlgebra) (U : X.Opens)
    (r : Γ(X, U)) (a : A.sectionsRing U) :
    A.sectionsMul U (A.one.app U r) a =
      @HSMul.hSMul Γ(X, U) Γ(A.carrier, U) Γ(A.carrier, U) _ r a := by
  have h := congrArg
    (fun (φ : CategoryTheory.MonoidalCategoryStruct.tensorObj (C := X.Modules)
        (𝟙_ X.Modules) A.carrier ⟶ A.carrier) =>
      φ.app U (AlgebraicGeometry.Scheme.Modules.tensorSections (𝟙_ X.Modules) A.carrier U r a))
    A.one_mul
  have hL := AlgebraicGeometry.Scheme.Modules.leftUnitor_app_tensorSections A.carrier U r a
  have hT := AlgebraicGeometry.Scheme.Modules.tensorHom_tensorSections
    A.one (𝟙 A.carrier) U r a
  rw [CategoryTheory.MonoidalCategory.tensorHom_id] at hT
  have hR : ((A.one ▷ A.carrier) ≫ A.mul).app U
      (AlgebraicGeometry.Scheme.Modules.tensorSections (𝟙_ X.Modules) A.carrier U r a)
      = A.sectionsMul U (A.one.app U r) a := by
    show A.mul.app U ((A.one ▷ A.carrier).val.app (Opposite.op U)
      (AlgebraicGeometry.Scheme.Modules.tensorSections (𝟙_ X.Modules) A.carrier U r a)) = _
    rw [hT]; rfl
  exact hR.symm.trans (h.symm.trans hL)

/-- The multiplication of sections is commutative (the axiom `QCAlgebra.mul_comm` +
`Modules.braiding_app_tensorSections`). -/
theorem AlgebraicGeometry.Scheme.QCAlgebra.sectionsMul_comm
    {X : AlgebraicGeometry.Scheme.{u}} (A : X.QCAlgebra) (U : X.Opens)
    (a b : A.sectionsRing U) : A.sectionsMul U a b = A.sectionsMul U b a := by
  have h := congrArg
    (fun (φ : CategoryTheory.MonoidalCategoryStruct.tensorObj (C := X.Modules)
        A.carrier A.carrier ⟶ A.carrier) =>
      φ.app U (AlgebraicGeometry.Scheme.Modules.tensorSections A.carrier A.carrier U a b))
    A.mul_comm
  have hb := AlgebraicGeometry.Scheme.Modules.braiding_app_tensorSections
    A.carrier A.carrier U a b
  exact h.symm.trans (congrArg (fun x => A.mul.app U x) hb)

/-- `sectionsOne` is a left unit for the multiplication of sections. -/
theorem AlgebraicGeometry.Scheme.QCAlgebra.sectionsOne_sectionsMul
    {X : AlgebraicGeometry.Scheme.{u}} (A : X.QCAlgebra) (U : X.Opens) (a : A.sectionsRing U) :
    A.sectionsMul U (A.sectionsOne U) a = a :=
  (A.sectionsOne_app_sectionsMul U 1 a).trans
    (one_smul Γ(X, U) (show Γ(A.carrier, U) from a))

/-- `sectionsOne` is a right unit for the multiplication of sections. -/
theorem AlgebraicGeometry.Scheme.QCAlgebra.sectionsMul_sectionsOne
    {X : AlgebraicGeometry.Scheme.{u}} (A : X.QCAlgebra) (U : X.Opens) (a : A.sectionsRing U) :
    A.sectionsMul U a (A.sectionsOne U) = a :=
  (A.sectionsMul_comm U a (A.sectionsOne U)).trans (A.sectionsOne_sectionsMul U a)

/-- The multiplication of sections is associative (the axiom `QCAlgebra.mul_assoc` +
`Modules.associator_app_tensorSections`). -/
theorem AlgebraicGeometry.Scheme.QCAlgebra.sectionsMul_assoc
    {X : AlgebraicGeometry.Scheme.{u}} (A : X.QCAlgebra) (U : X.Opens)
    (a b c : A.sectionsRing U) :
    A.sectionsMul U (A.sectionsMul U a b) c = A.sectionsMul U a (A.sectionsMul U b c) := by
  have h := congrArg
    (fun (φ : CategoryTheory.MonoidalCategoryStruct.tensorObj (C := X.Modules)
        (CategoryTheory.MonoidalCategoryStruct.tensorObj (C := X.Modules) A.carrier A.carrier)
        A.carrier ⟶ A.carrier) =>
      φ.app U (AlgebraicGeometry.Scheme.Modules.tensorSections
        (CategoryTheory.MonoidalCategoryStruct.tensorObj (C := X.Modules) A.carrier A.carrier)
        A.carrier U
        (AlgebraicGeometry.Scheme.Modules.tensorSections A.carrier A.carrier U a b) c))
    A.mul_assoc
  have hTR := AlgebraicGeometry.Scheme.Modules.tensorHom_tensorSections
    A.mul (𝟙 A.carrier) U
    (AlgebraicGeometry.Scheme.Modules.tensorSections A.carrier A.carrier U a b) c
  rw [CategoryTheory.MonoidalCategory.tensorHom_id] at hTR
  have hTL := AlgebraicGeometry.Scheme.Modules.tensorHom_tensorSections
    (𝟙 A.carrier) A.mul U a
    (AlgebraicGeometry.Scheme.Modules.tensorSections A.carrier A.carrier U b c)
  rw [CategoryTheory.MonoidalCategory.id_tensorHom] at hTL
  have ha := AlgebraicGeometry.Scheme.Modules.associator_app_tensorSections
    A.carrier A.carrier A.carrier U a b c
  have hR : ((A.mul ▷ A.carrier) ≫ A.mul).app U
      (AlgebraicGeometry.Scheme.Modules.tensorSections
        (CategoryTheory.MonoidalCategoryStruct.tensorObj (C := X.Modules) A.carrier A.carrier)
        A.carrier U
        (AlgebraicGeometry.Scheme.Modules.tensorSections A.carrier A.carrier U a b) c)
      = A.sectionsMul U (A.sectionsMul U a b) c := by
    show A.mul.app U ((A.mul ▷ A.carrier).val.app (Opposite.op U) _) = _
    rw [hTR]; rfl
  have hL : ((α_ A.carrier A.carrier A.carrier).hom ≫ (A.carrier ◁ A.mul) ≫ A.mul).app U
      (AlgebraicGeometry.Scheme.Modules.tensorSections
        (CategoryTheory.MonoidalCategoryStruct.tensorObj (C := X.Modules) A.carrier A.carrier)
        A.carrier U
        (AlgebraicGeometry.Scheme.Modules.tensorSections A.carrier A.carrier U a b) c)
      = A.sectionsMul U a (A.sectionsMul U b c) := by
    show A.mul.app U ((A.carrier ◁ A.mul).val.app (Opposite.op U)
      ((α_ A.carrier A.carrier A.carrier).hom.val.app (Opposite.op U) _)) = _
    rw [show (α_ A.carrier A.carrier A.carrier).hom.val.app (Opposite.op U) _ = _ from ha,
      hTL]; rfl
  exact hR.symm.trans (h.symm.trans hL)

/-- `A.one` preserves multiplication on `U`: `A.one` is `O_X`-linear, combined with
`sectionsOne_app_sectionsMul`. -/
theorem AlgebraicGeometry.Scheme.QCAlgebra.sectionsOne_app_mul
    {X : AlgebraicGeometry.Scheme.{u}} (A : X.QCAlgebra) (U : X.Opens) (r s : Γ(X, U)) :
    A.one.app U (r * s) = A.sectionsMul U (A.one.app U r) (A.one.app U s) := by
  refine Eq.trans ?_ (A.sectionsOne_app_sectionsMul U r (A.one.app U s)).symm
  exact AlgebraicGeometry.Scheme.Modules.Hom.app_smul A.one r (s : Γ(𝟙_ X.Modules, U))

end SectionsRingAux

noncomputable instance {X : AlgebraicGeometry.Scheme.{u}} (A : X.QCAlgebra) (U : X.Opens) :
    CommRing (A.sectionsRing U) :=
  { (inferInstance : AddCommGroup (A.sectionsRing U)) with
    mul := A.sectionsMul U
    one := A.sectionsOne U
    left_distrib := fun a b c =>
      (congrArg (A.presheafMul.app (Opposite.op U)).hom (TensorProduct.tmul_add _ _ _)).trans (map_add _ _ _)
    right_distrib := fun a b c =>
      (congrArg (A.presheafMul.app (Opposite.op U)).hom (TensorProduct.add_tmul _ _ _)).trans (map_add _ _ _)
    zero_mul := fun a =>
      (congrArg (A.presheafMul.app (Opposite.op U)).hom (TensorProduct.zero_tmul _ _)).trans (map_zero _)
    mul_zero := fun a =>
      (congrArg (A.presheafMul.app (Opposite.op U)).hom (TensorProduct.tmul_zero _ _)).trans (map_zero _)
    -- associativity, commutativity, unit laws: from `A.mul_assoc` / `mul_comm` / `one_mul` on sections
    mul_assoc := fun a b c => A.sectionsMul_assoc U a b c
    one_mul := fun a => A.sectionsOne_sectionsMul U a
    mul_one := fun a => A.sectionsMul_sectionsOne U a
    mul_comm := fun a b => A.sectionsMul_comm U a b }

/-- The restriction ring homomorphism `A(U') →+* A(U)` for `U ≤ U'`. -/
noncomputable def AlgebraicGeometry.Scheme.QCAlgebra.sectionsRestrict {X : AlgebraicGeometry.Scheme.{u}}
    (A : X.QCAlgebra) {U U' : X.Opens} (h : U ≤ U') : A.sectionsRing U' →+* A.sectionsRing U where
  toFun a := (A.carrier.val.map (CategoryTheory.homOfLE h).op).hom a
  map_zero' := map_zero _
  map_add' := map_add _
  -- restriction preserves multiplication and unit: naturality of `presheafMul` and `A.one`
  map_one' := by
    change (A.carrier.val.map (CategoryTheory.homOfLE h).op).hom
        (A.one.val.app (Opposite.op U')
          (1 : X.ringCatSheaf.obj.obj (Opposite.op U'))) =
      A.one.val.app (Opposite.op U)
        (1 : X.ringCatSheaf.obj.obj (Opposite.op U))
    have hn := PresheafOfModules.naturality_apply A.one.val
      (CategoryTheory.homOfLE h).op
      (1 : X.ringCatSheaf.obj.obj (Opposite.op U'))
    have h1 :
        ((𝟙_ X.Modules).val.map (CategoryTheory.homOfLE h).op).hom
            (1 : X.ringCatSheaf.obj.obj (Opposite.op U')) =
          (1 : X.ringCatSheaf.obj.obj (Opposite.op U)) := by
      change (X.presheaf.map (CategoryTheory.homOfLE h).op).hom 1 = 1
      exact map_one _
    rw [h1] at hn
    exact hn.symm
  map_mul' := by
    intro a b
    change (A.carrier.val.map (CategoryTheory.homOfLE h).op).hom
        ((A.presheafMul.app (Opposite.op U')).hom
          (@TensorProduct.tmul (X.presheaf.obj (Opposite.op U')) _
            (A.carrier.val.obj (Opposite.op U')) (A.carrier.val.obj (Opposite.op U')) _ _
            (A.carrier.val.obj (Opposite.op U')).isModule
            (A.carrier.val.obj (Opposite.op U')).isModule a b)) =
      (A.presheafMul.app (Opposite.op U)).hom
        (@TensorProduct.tmul (X.presheaf.obj (Opposite.op U)) _
          (A.carrier.val.obj (Opposite.op U)) (A.carrier.val.obj (Opposite.op U)) _ _
          (A.carrier.val.obj (Opposite.op U)).isModule
          (A.carrier.val.obj (Opposite.op U)).isModule
          ((A.carrier.val.map (CategoryTheory.homOfLE h).op).hom a)
          ((A.carrier.val.map (CategoryTheory.homOfLE h).op).hom b))
    have hn := PresheafOfModules.naturality_apply A.presheafMul
      (CategoryTheory.homOfLE h).op
      (@TensorProduct.tmul (X.presheaf.obj (Opposite.op U')) _
        (A.carrier.val.obj (Opposite.op U')) (A.carrier.val.obj (Opposite.op U')) _ _
        (A.carrier.val.obj (Opposite.op U')).isModule
        (A.carrier.val.obj (Opposite.op U')).isModule a b)
    change (A.presheafMul.app (Opposite.op U)).hom
        (((PresheafOfModules.Monoidal.tensorObj (R := X.presheaf)
            A.carrier.val A.carrier.val).map (CategoryTheory.homOfLE h).op).hom
          (a ⊗ₜ[X.presheaf.obj (Opposite.op U')] b)) = _ at hn
    erw [PresheafOfModules.Monoidal.tensorObj_map_tmul] at hn
    exact hn.symm

noncomputable def AlgebraicGeometry.Scheme.QCAlgebra.sectionsUnit {X : AlgebraicGeometry.Scheme.{u}}
    (A : X.QCAlgebra) (U : X.Opens) : Γ(X, U) →+* A.sectionsRing U where
  toFun r := (A.one.val.app (Opposite.op U)).hom (r : X.ringCatSheaf.obj.obj (Opposite.op U))
  map_zero' := map_zero _
  map_add' := map_add _
  map_one' := rfl
  -- `A.one` is `O_X`-linear, so `r ↦ r · 1_A` preserves multiplication
  map_mul' := fun r s => A.sectionsOne_app_mul U r s

/-- **Bridge lemma**: the multiplication of the section ring is `A.mul` applied to the section pairing
`tensorSections`. The body of `presheafMul` is `adj.homEquiv (sheafifyTensorTo ≫ A.mul)` and
`tensorSections = sheafifyTensorTo ∘ η`, so both sides are definitionally equal. -/
theorem AlgebraicGeometry.Scheme.QCAlgebra.sectionsMul_eq_mul_tensorSections
    {X : AlgebraicGeometry.Scheme.{u}} (A : X.QCAlgebra) (U : X.Opens) (a b : A.sectionsRing U) :
    a * b =
      A.mul.app U (AlgebraicGeometry.Scheme.Modules.tensorSections A.carrier A.carrier U a b) :=
  rfl

/-- `A.sectionsUnit U r * a = r • a`: the axiom `QCAlgebra.one_mul` on sections, with
`Modules.leftUnitor_app_tensorSections` (the left unitor on pure tensor sections is scalar multiplication)
and `Modules.tensorHom_tensorSections` (the section pairing is natural in `⊗ₘ`). -/
theorem AlgebraicGeometry.Scheme.QCAlgebra.smul_eq_sectionsUnit_mul
    {X : AlgebraicGeometry.Scheme.{u}} (A : X.QCAlgebra) (U : X.Opens)
    (r : Γ(X, U)) (a : A.sectionsRing U) :
    A.sectionsUnit U r * a =
      @HSMul.hSMul Γ(X, U) Γ(A.carrier, U) Γ(A.carrier, U) _ r a :=
  A.sectionsOne_app_sectionsMul U r a

end
