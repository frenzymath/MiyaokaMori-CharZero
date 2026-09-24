import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.PresheafModulesTensorLocalIso
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.QuasicoherentAlgebra
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.SheafOfModulesMonoidal
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.AffinePushforwardQuasicoherent
import MiyaokaMori.CategoryTheory.PushforwardQcAlgebraMonTransport

/-! # The pushforward algebra of an affine morphism

For an affine morphism `f : T → X`, `f_*O_T` as a quasi-coherent `O_X`-algebra (`X.QCAlgebra`): the carrier
is `f_*O_T`, the multiplication comes from the ring multiplication `Γ(T,f⁻¹U) ⊗ Γ(T,f⁻¹U) → Γ(T,f⁻¹U)` on
each open through the localized monoidal structure of sheafification, and the unit is `O_X → f_*O_T`
(the object part of "affine morphisms ↦ algebra sheaves", Stacks 01S5/01SA).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open scoped CategoryTheory.MonoidalCategory

/- `f_* O_T` as a quasi-coherent `O_X`-algebra on `X` (the object part of Stacks 01S5/01SA).
   `P := ` the underlying presheaf of modules of `f_* O_T` (the image under the right adjoint of the
   sheafification adjunction), `P(U) = Γ(T, f⁻¹U)`; the presheaf multiplication `m` is
   `P(U) ⊗_{O(U)} P(U) → P(U)`, `a ⊗ b ↦ a·b` on each open (`O(U)`-bilinear and natural); the sheaf
   multiplication uses that the tensor product of `X.Modules` is the localized monoidal structure of the
   sheafification `L`: with `Localization.Monoidal.μ : L(P) ⊗ L(P) ≅ L(P ⊗ P)` and the counit isomorphism
   `e : L(P) ≅ f_* O_T`, `mul := (e⁻¹ ⊗ e⁻¹) ≫ μ ≫ L(m) ≫ e`; the unit is `O_X → f_* O_T` (Mathlib
   `unitToPushforwardObjUnit`). The proof obligations (bilinearity, naturality of the presheaf
   multiplication, quasi-coherence, the three algebra axioms) are named theorems below. -/

/-- f_*O_T -/

noncomputable abbrev AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.obj {X T : AlgebraicGeometry.Scheme.{u}} (f : T ⟶ X) : X.Modules :=
  (AlgebraicGeometry.Scheme.Modules.pushforward f).obj (SheafOfModules.unit T.ringCatSheaf)

/-- The underlying presheaf of modules `P` of `f_*O_T`, `P(U) = Γ(T, f⁻¹U)`. -/

noncomputable abbrev AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.presheaf {X T : AlgebraicGeometry.Scheme.{u}} (f : T ⟶ X) :=
  (SheafOfModules.forget X.ringCatSheaf ⋙
    _root_.PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).obj (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.obj f)

/-- The multiplication `a, b ↦ a·b` on each open (the product in `Γ(T, f⁻¹U)`). -/

noncomputable def AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.mulFun {X T : AlgebraicGeometry.Scheme.{u}} (f : T ⟶ X) (U : (TopologicalSpace.Opens X)ᵒᵖ) :
    (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.presheaf f).obj U → (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.presheaf f).obj U → (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.presheaf f).obj U :=
  fun a b => ((show Γ(T, f ⁻¹ᵁ U.unop) from a) * (show Γ(T, f ⁻¹ᵁ U.unop) from b) :
    Γ(T, f ⁻¹ᵁ U.unop))

theorem AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.mulFun_add_left {X T : AlgebraicGeometry.Scheme.{u}} (f : T ⟶ X) (U : (TopologicalSpace.Opens X)ᵒᵖ)
    (m₁ m₂ n : (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.presheaf f).obj U) :
    AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.mulFun f U (m₁ + m₂) n = AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.mulFun f U m₁ n + AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.mulFun f U m₂ n :=
  add_mul (show Γ(T, f ⁻¹ᵁ U.unop) from m₁) (show Γ(T, f ⁻¹ᵁ U.unop) from m₂)
    (show Γ(T, f ⁻¹ᵁ U.unop) from n)

theorem AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.mulFun_add_right {X T : AlgebraicGeometry.Scheme.{u}} (f : T ⟶ X) (U : (TopologicalSpace.Opens X)ᵒᵖ)
    (m n₁ n₂ : (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.presheaf f).obj U) :
    AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.mulFun f U m (n₁ + n₂) = AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.mulFun f U m n₁ + AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.mulFun f U m n₂ :=
  mul_add (show Γ(T, f ⁻¹ᵁ U.unop) from m) (show Γ(T, f ⁻¹ᵁ U.unop) from n₁)
    (show Γ(T, f ⁻¹ᵁ U.unop) from n₂)

/-- The multiplication on each open is `O_X(U)`-linear in the left variable (a hypothesis of `tensorLift`).

This is the step "the multiplication of `f_*O_T` is `O_X`-bilinear" of Stacks 01S5; in ring theory it is the
associativity of `Γ(T, f⁻¹U)` as a `Γ(X,U)`-algebra. The `Γ(X,U)`-module structure on `P(U) = Γ(T, f⁻¹U)` is
restriction of scalars (`ModuleCat.restrictScalars.smul_def`): `a • m = (f.app U).hom a • m`, and the `•` on
the right is the action of the ring `Γ(T, f⁻¹U)` on itself, i.e. multiplication (`smul_eq_mul`); so
`mulFun (a • m) n = ((f.app U) a * m) * n = (f.app U) a * (m * n) = a • mulFun m n` by `mul_assoc`. -/
theorem AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.mulFun_smul_left {X T : AlgebraicGeometry.Scheme.{u}} (f : T ⟶ X) (U : (TopologicalSpace.Opens X)ᵒᵖ)
    (a : X.ringCatSheaf.obj.obj U)
    (m n : (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.presheaf f).obj U) :
    AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.mulFun f U (a • m) n = a • AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.mulFun f U m n := by
  show ((f.app U.unop).hom a * (show Γ(T, f ⁻¹ᵁ U.unop) from m)) * (show Γ(T, f ⁻¹ᵁ U.unop) from n) =
    (f.app U.unop).hom a * ((show Γ(T, f ⁻¹ᵁ U.unop) from m) * (show Γ(T, f ⁻¹ᵁ U.unop) from n))
  exact _root_.mul_assoc _ _ _

/-- The multiplication on each open is `O_X(U)`-linear in the right variable (a hypothesis of `tensorLift`).
As for `mulFun_smul_left`, rewrite `a • n` as `(f.app U) a * n`; then
`mulFun m (a • n) = m * ((f.app U) a * n) = (f.app U) a * (m * n) = a • mulFun m n` by `mul_left_comm` in a
commutative ring. -/
theorem AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.mulFun_smul_right {X T : AlgebraicGeometry.Scheme.{u}} (f : T ⟶ X) (U : (TopologicalSpace.Opens X)ᵒᵖ)
    (a : X.ringCatSheaf.obj.obj U)
    (m n : (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.presheaf f).obj U) :
    AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.mulFun f U m (a • n) = a • AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.mulFun f U m n := by
  show (show Γ(T, f ⁻¹ᵁ U.unop) from m) * ((f.app U.unop).hom a * (show Γ(T, f ⁻¹ᵁ U.unop) from n)) =
    (f.app U.unop).hom a * ((show Γ(T, f ⁻¹ᵁ U.unop) from m) * (show Γ(T, f ⁻¹ᵁ U.unop) from n))
  exact mul_left_comm _ _ _

noncomputable def AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.presheafMulApp {X T : AlgebraicGeometry.Scheme.{u}} (f : T ⟶ X) (U : (TopologicalSpace.Opens X)ᵒᵖ) :
    (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.presheaf f ⊗ AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.presheaf f).obj U ⟶ (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.presheaf f).obj U :=
  ModuleCat.MonoidalCategory.tensorLift
    (R := ((X.presheaf ⋙ CategoryTheory.forget₂ CommRingCat RingCat).obj U : RingCat))
    (M₃ := (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.presheaf f).obj U)
    (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.mulFun f U)
    (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.mulFun_add_left f U) (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.mulFun_smul_left f U)
    (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.mulFun_add_right f U) (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.mulFun_smul_right f U)

/-- Naturality of the presheaf multiplication (the field assembling the `presheafMulApp` on each open into
the morphism of presheaves of modules `presheafMul`). Sheaf-theoretically: the restriction maps are ring
homomorphisms (Stacks 01S5).

Proof: both sides are linear maps `(P ⊗ P)(U) ⟶ P(V)` (`U ⟶ V` in `Opensᵒᵖ`, i.e. an inclusion `V ⊆ U`).
Use `ModuleCat.MonoidalCategory.tensor_ext` to reduce to pure tensors `a ⊗ₜ b` (`a, b ∈ Γ(T, f⁻¹U)`).
* Left side: `(P ⊗ P).map g` sends `a ⊗ₜ b` to `a|_{f⁻¹V} ⊗ₜ b|_{f⁻¹V}` (the `map` of the presheaf tensor
  product acts factorwise), then multiply to get `a|_{f⁻¹V} · b|_{f⁻¹V}`.
* Right side: multiply to get `a·b`, then restrict to `(a·b)|_{f⁻¹V}`.
These agree because the restriction maps of `X.presheaf` and `T.presheaf` are ring homomorphisms
(morphisms in `CommRingCat`, `map_mul`), and `P.map g` on sections is the restriction of `T` along
`f⁻¹V ≤ f⁻¹U` (definition of the pushforward presheaf).

The `ModuleCat` instance spellings here make `rw [ModuleCat.hom_comp]` fail to match; reduce to elements
with `ModuleCat.MonoidalCategory.tensor_ext` first rather than rewriting at the level of morphisms. -/
theorem AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.presheafMulApp_naturality {X T : AlgebraicGeometry.Scheme.{u}} (f : T ⟶ X)
    {U V : (TopologicalSpace.Opens X)ᵒᵖ} (g : U ⟶ V) :
    (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.presheaf f ⊗ AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.presheaf f).map g ≫
        (ModuleCat.restrictScalars _).map (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.presheafMulApp f V) =
      AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.presheafMulApp f U ≫ (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.presheaf f).map g := by
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro a b
  -- first `show` both sides as composites at the level of elements (`rw [ModuleCat.hom_comp]` /
  -- `erw [tensorObj_map_tmul]` fail here because of instance spellings or time out in whnf; after the
  -- `show`, the defeq check of `exact` finishes)
  show ((ModuleCat.restrictScalars _).map (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.presheafMulApp f V)).hom
      (((AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.presheaf f ⊗
        AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.presheaf f).map g).hom (a ⊗ₜ b)) =
    ((AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.presheaf f).map g).hom
      ((AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.presheafMulApp f U).hom (a ⊗ₜ b))
  -- the two sides are `(a|_V)·(b|_V)` and `(a·b)|_V`; the restriction map `T.presheaf.map _` is a ring homomorphism
  exact ((T.presheaf.map ((Opens.map f.base).map g.unop).op).hom.map_mul a b).symm

noncomputable def AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.presheafMul {X T : AlgebraicGeometry.Scheme.{u}} (f : T ⟶ X) :
    AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.presheaf f ⊗ AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.presheaf f ⟶ AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.presheaf f where
  app := AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.presheafMulApp f
  naturality g := AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.presheafMulApp_naturality f g

/-- The counit isomorphism `e : L(P) ≅ f_*O_T`. -/

noncomputable def AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.counitIso {X T : AlgebraicGeometry.Scheme.{u}} (f : T ⟶ X) :
    (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.presheaf f) ≅ AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.obj f :=
  (CategoryTheory.asIso (_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit).app
    (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.obj f)

/-- The sheaf multiplication `mul := (e⁻¹ ⊗ e⁻¹) ≫ μ ≫ L(m) ≫ e`. -/

noncomputable def AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.mul {X T : AlgebraicGeometry.Scheme.{u}} (f : T ⟶ X) :
    AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.obj f ⊗ AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.obj f ⟶ AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.obj f :=
  haveI := AlgebraicGeometry.Scheme.PresheafOfModules.sheafificationW_isMonoidal X
  haveI : (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).IsLocalization
      ((CategoryTheory.MorphismProperty.isomorphisms (SheafOfModules.{u} X.ringCatSheaf)).inverseImage
        (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))) :=
    (_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).isLocalization
  ((AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.counitIso f).inv ⊗ₘ (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.counitIso f).inv) ≫
    (CategoryTheory.Localization.Monoidal.μ (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))
      ((CategoryTheory.MorphismProperty.isomorphisms (SheafOfModules.{u} X.ringCatSheaf)).inverseImage
        (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)))
      (AlgebraicGeometry.Scheme.Modules.sheafificationUnitIso X)
      (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.presheaf f) (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.presheaf f)).hom ≫
    (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.presheafMul f) ≫ (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.counitIso f).hom

/-- `f_*O_T` is quasi-coherent (`f` affine).

Reference: Stacks 01LC (pushforward along a quasi-compact quasi-separated morphism preserves
quasi-coherence); affine morphisms are quasi-compact and quasi-separated. This is
`AlgebraicGeometry.isQuasicoherent_pushforward_one_of_isAffineHom`
(`AffinePushforwardQuasicoherent.lean`), proved directly: on an affine open `V ⊆ X`, `f⁻¹V` is affine,
`(f_*O_T)(V) = Γ(T, f⁻¹V)`, and quasi-coherence amounts to compatibility with localization at basic opens,
`Γ(T, f⁻¹(D(g))) = Γ(T, f⁻¹V)_{f^♯ g}`, which is `IsAffineOpen.isLocalization_basicOpen` together with
`f⁻¹(D(g)) = D(f^♯ g)` (Mathlib `Scheme.preimage_basicOpen`). -/
theorem AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.obj_isQuasicoherent {X T : AlgebraicGeometry.Scheme.{u}} (f : T ⟶ X) [AlgebraicGeometry.IsAffineHom f] :
    (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.obj f).IsQuasicoherent :=
  AlgebraicGeometry.isQuasicoherent_pushforward_one_of_isAffineHom f

/-! ### Proof route for the three algebra axioms

`mul f = (e⁻¹ ⊗ e⁻¹) ≫ μ ≫ L(m) ≫ e`, where `L` is the sheafification functor, `μ` the comparison
isomorphism of the localized monoidal structure, `e` the counit isomorphism `counitIso f`, and
`m = presheafMul f`. The three axioms are proved in two steps:

1. **Presheaf level**: `presheaf f` with `presheafMul f`, `presheafOne f` (`= unitToPushforwardObjUnit` through
   `forget ⋙ restrictScalars (𝟙 _)`) is a **commutative monoid object** of `PresheafOfModules`
   (`presheafMonObj`, `presheafIsCommMonObj`): on each open, `PresheafOfModules.hom_ext` +
   `ModuleCat.MonoidalCategory.tensor_ext` reduce to pure tensors, where the axioms are the
   `one_mul` / `mul_one` / `mul_assoc` / `mul_comm` of `Γ(T, f⁻¹U)` (the unit `presheafOne` on `U` is `f.app U`,
   a ring homomorphism preserving `1`, so `1 • a = f(1)·a = a`).
2. **Transport**: `L` with `μ`, `ε` is a lax braided functor (Mathlib's `Functor.Braided` instance for
   `Localization.Monoidal`, assembled on the instances of `X.Modules`: `sheafificationLaxBraided`); the general
   lemmas `Functor.LaxMonoidal.transport_one_mul` / `transport_mul_assoc` / `Functor.LaxBraided.transport_mul_comm`
   (`PushforwardQcAlgebraMonTransport.lean`, a combination of Mathlib's `Functor.monObjObj` and `MonObj.ofIso`)
   transport the axioms from `presheaf f` to `obj f`; `transportMul` is by definition `mul f`, and the
   transported unit `ε ≫ L(presheafOne) ≫ e` equals `unitToPushforwardObjUnit` (`transportOne_eq`: naturality
   of the counit, and `sheafificationUnitIso` is the component of the counit at `O_X`).

Instance spellings: `Scheme.Modules` is a `def`, not an `abbrev`, so instance search finds
`Scheme.Modules.monoidalCategory` only when the type is **literally** `X.Modules`, and
`SiteModules.presheafSymmetricCategory` is not found through `ringCatSheaf`. Hence `L` is written as
`sheafificationToModules X : PresheafOfModules X.ringCatSheaf.obj ⥤ X.Modules`, and `presheafBraided`,
`sheafificationLaxBraided` are **local** instances of this file (`attribute [local instance]`, not exported). -/

namespace AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf

variable {X T : AlgebraicGeometry.Scheme.{u}} (f : T ⟶ X)

/-- The unit `O_X ⟶ P` at the presheaf level: `unitToPushforwardObjUnit` through the right adjoint
`forget ⋙ restrictScalars (𝟙 _)` (on `U` it is `f.app U : Γ(X, U) → Γ(T, f⁻¹U)`). -/
noncomputable def presheafOne :
    𝟙_ (_root_.PresheafOfModules.{u} X.ringCatSheaf.obj) ⟶ presheaf f :=
  (SheafOfModules.forget X.ringCatSheaf ⋙
    _root_.PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map
    (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)

/-- The left unit law at the presheaf level: `(1 ▷ P) ≫ m = λ_P`; on each open it is `1 • a = f(1)·a = a`
(definitionally). -/
theorem presheaf_one_mul :
    (presheafOne f ▷ presheaf f) ≫ presheafMul f = (λ_ (presheaf f)).hom := by
  apply _root_.PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro r a
  show mulFun f U ((f.app U.unop).hom r) a = (f.app U.unop).hom r * (show Γ(T, f ⁻¹ᵁ U.unop) from a)
  rfl

/-- The right unit law at the presheaf level: `(P ◁ 1) ≫ m = ρ_P`; on each open it is `a·f(r) = f(r)·a`
(commutative ring). -/
theorem presheaf_mul_one :
    (presheaf f ◁ presheafOne f) ≫ presheafMul f = (ρ_ (presheaf f)).hom := by
  apply _root_.PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro a r
  show mulFun f U a ((f.app U.unop).hom r) = (f.app U.unop).hom r * (show Γ(T, f ⁻¹ᵁ U.unop) from a)
  exact _root_.mul_comm (show Γ(T, f ⁻¹ᵁ U.unop) from a) ((f.app U.unop).hom r)

/-- Associativity at the presheaf level (in the form of Mathlib's `MonObj.mul_assoc`); on each open it is the
`mul_assoc` of `Γ(T, f⁻¹U)`. -/
theorem presheaf_mul_assoc :
    (presheafMul f ▷ presheaf f) ≫ presheafMul f =
      (α_ (presheaf f) (presheaf f) (presheaf f)).hom ≫ (presheaf f ◁ presheafMul f) ≫ presheafMul f := by
  apply _root_.PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext₃'
  intro a b c
  show mulFun f U (mulFun f U a b) c = mulFun f U a (mulFun f U b c)
  exact _root_.mul_assoc (show Γ(T, f ⁻¹ᵁ U.unop) from a) (show Γ(T, f ⁻¹ᵁ U.unop) from b)
    (show Γ(T, f ⁻¹ᵁ U.unop) from c)

/-- The braided structure on presheaves of modules over `X.ringCatSheaf.obj` (Mathlib's symmetric structure
via `SiteModules.presheafSymmetricCategory`; instance search does not find it through `ringCatSheaf`, so it
is given explicitly as a local instance of this file). -/
@[instance_reducible]
noncomputable def presheafBraided (X : AlgebraicGeometry.Scheme.{u}) :
    CategoryTheory.BraidedCategory (_root_.PresheafOfModules.{u} X.ringCatSheaf.obj) :=
  (SiteModules.presheafSymmetricCategory X.sheaf).toBraidedCategory

attribute [local instance] presheafBraided

/-- Commutativity at the presheaf level: `β ≫ m = m`; on each open it is the `mul_comm` of `Γ(T, f⁻¹U)`. -/
theorem presheaf_mul_comm :
    (β_ (presheaf f) (presheaf f)).hom ≫ presheafMul f = presheafMul f := by
  apply _root_.PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro a b
  show mulFun f U b a = mulFun f U a b
  exact _root_.mul_comm (show Γ(T, f ⁻¹ᵁ U.unop) from b) (show Γ(T, f ⁻¹ᵁ U.unop) from a)

/-- The underlying presheaf of modules `P` of `f_*O_T` is a monoid object of `PresheafOfModules`
(multiplication `presheafMul`, unit `presheafOne`). -/
@[instance_reducible]
noncomputable def presheafMonObj : CategoryTheory.MonObj (presheaf f) where
  one := presheafOne f
  mul := presheafMul f
  one_mul := presheaf_one_mul f
  mul_one := presheaf_mul_one f
  mul_assoc := presheaf_mul_assoc f

/-- And it is commutative. -/
theorem presheafIsCommMonObj :
    letI := presheafMonObj f
    CategoryTheory.IsCommMonObj (presheaf f) :=
  letI := presheafMonObj f
  ⟨presheaf_mul_comm f⟩

/-- The sheafification functor `L` with codomain spelled `X.Modules` (rather than
`SheafOfModules X.ringCatSheaf`), so that instance search finds the monoidal/symmetric structure of
`X.Modules`. By definition it is `PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)`. -/
noncomputable abbrev sheafificationToModules (X : AlgebraicGeometry.Scheme.{u}) :
    _root_.PresheafOfModules.{u} X.ringCatSheaf.obj ⥤ X.Modules :=
  _root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)

/-- The sheafification functor `L` with the comparison isomorphisms `μ`, `ε` of the localized monoidal
structure is a lax braided functor (Mathlib's `Functor.Braided` instance for `Localization.Monoidal`
transported to the instance spelling of `X.Modules`; a local instance of this file). Its `ε` is
`(sheafificationUnitIso X).inv` and `μ P Q` is `(Localization.Monoidal.μ … P Q).hom` (both `rfl`). -/
@[instance_reducible]
noncomputable def sheafificationLaxBraided (X : AlgebraicGeometry.Scheme.{u}) :
    (sheafificationToModules X).LaxBraided :=
  haveI := AlgebraicGeometry.Scheme.PresheafOfModules.sheafificationW_isMonoidal X
  haveI : (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).IsLocalization
      ((CategoryTheory.MorphismProperty.isomorphisms (SheafOfModules.{u} X.ringCatSheaf)).inverseImage
        (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))) :=
    (_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).isLocalization
  CategoryTheory.Functor.Braided.toLaxBraided
    (F := CategoryTheory.Localization.Monoidal.toMonoidalCategory
      (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj))
      ((CategoryTheory.MorphismProperty.isomorphisms (SheafOfModules.{u} X.ringCatSheaf)).inverseImage
        (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)))
      (AlgebraicGeometry.Scheme.Modules.sheafificationUnitIso X))

attribute [local instance] sheafificationLaxBraided

/-- The transported unit is `unitToPushforwardObjUnit`: `ε ≫ L(presheafOne f) ≫ e = 1`.
Proof: `ε = (sheafificationUnitIso X).inv`, and `sheafificationUnitIso X` is the component at `O_X` of the
counit of the sheafification adjunction; `presheafOne f = R(1)` (`R` the right adjoint), naturality of the
counit gives `L(R(1)) ≫ e = counit_{O_X} ≫ 1`, and `inv ≫ hom = 𝟙`. -/
theorem transportOne_eq :
    CategoryTheory.Functor.LaxMonoidal.ε (sheafificationToModules X) ≫
        (sheafificationToModules X).map (presheafOne f) ≫ (counitIso f).hom =
      SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom := by
  have hnat : (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
        ((SheafOfModules.forget X.ringCatSheaf ⋙
          _root_.PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map
          (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)) ≫
        (_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit.app (obj f) =
      (_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit.app
          (SheafOfModules.unit X.ringCatSheaf) ≫
        SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom :=
    (_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit.naturality
      (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)
  show (AlgebraicGeometry.Scheme.Modules.sheafificationUnitIso X).inv ≫
      (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
        ((SheafOfModules.forget X.ringCatSheaf ⋙
          _root_.PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map
          (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom)) ≫
      (_root_.PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).counit.app (obj f) = _
  -- `rw [hnat]` fails here because of implicit transparency issues between `TopCat.Sheaf` / `Sheaf`; use `congrArg`
  exact (congrArg (fun z => (AlgebraicGeometry.Scheme.Modules.sheafificationUnitIso X).inv ≫ z) hnat).trans
    ((AlgebraicGeometry.Scheme.Modules.sheafificationUnitIso X).inv_hom_id_assoc _)

end AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf

/-- Algebra axiom: the left unit law `λ = (1 ▷ id) ≫ mul`. The ring-theoretic content is the `one_mul` of
`Γ(T, f⁻¹U)` (Stacks 01S5).

Proof: `mul` is `(e⁻¹ ⊗ e⁻¹) ≫ μ ≫ L(m) ≫ e`, where `L` is the sheafification functor
`PresheafOfModules.sheafification (𝟙 …)`, `μ` the comparison isomorphism of the localized monoidal
structure (`CategoryTheory.Localization.Monoidal.μ`), `e` the counit isomorphism of the sheafification
adjunction on sheaves (`counitIso`), and `m = presheafMul` the presheaf multiplication.
1. **Transport to the presheaf level**: `L` with `μ`, `ε` is a lax monoidal functor and `e` a natural
   isomorphism, so the algebra structure on `X.Modules` with multiplication `mul` corresponds to the one on
   `PresheafOfModules` with multiplication `m` and unit `1 : unit ⟶ P` (the presheaf version of
   `unitToPushforwardObjUnit`); a monoidal functor sends left unit laws to left unit laws. This is the
   general lemma `CategoryTheory.Functor.LaxMonoidal.transport_one_mul`
   (`PushforwardQcAlgebraMonTransport.lean`, a combination of Mathlib's `Functor.monObjObj` and
   `MonObj.ofIso`; lax monoidal suffices), and the transported unit equals `unitToPushforwardObjUnit` by
   `transportOne_eq`.
2. **Verification on each open**: on `U`, the left side of `(λ_P)(1 ⊗ₜ m)` is `1 • m = m`, the right side is
   `mulFun f U 1 m = 1 * m = m` (`one_mul`; `1` is the unit of `Γ(T, f⁻¹U)`, which by
   `unitToPushforwardObjUnit_val_app_apply` is `f.app U` applied to the `1` of `O_X(U)`, a ring homomorphism
   preserving `1`). Reduce to pure tensors with `ModuleCat.MonoidalCategory.tensor_ext`; this is
   `presheafMonObj f` (`presheaf_one_mul`, `rfl` on each open). -/
theorem AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.one_mul {X T : AlgebraicGeometry.Scheme.{u}} (f : T ⟶ X) :
    (λ_ (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.obj f)).hom =
      CategoryTheory.MonoidalCategoryStruct.whiskerRight (C := X.Modules)
          (SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom) (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.obj f) ≫
        AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.mul f := by
  letI := AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.presheafBraided X
  letI := AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.sheafificationLaxBraided X
  letI := AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.presheafMonObj f
  have h := CategoryTheory.Functor.LaxMonoidal.transport_one_mul
    (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.sheafificationToModules X)
    (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.presheaf f)
    (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.counitIso f)
  refine h.trans ?_
  -- `transportMul` is by definition `mul f`; `transportOne` becomes `unitToPushforwardObjUnit` by `transportOne_eq`
  exact congrArg (fun z => CategoryTheory.MonoidalCategoryStruct.whiskerRight (C := X.Modules) z
      (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.obj f) ≫
      CategoryTheory.Functor.LaxMonoidal.transportMul
        (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.sheafificationToModules X)
        (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.presheaf f)
        (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.counitIso f))
    (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.transportOne_eq f)

/-- Algebra axiom: associativity (Stacks 01S5). Same two steps as `one_mul` (transport to the presheaf level
through `(L, μ, ε)` and `e`, then reduce to pure tensors with `tensor_ext` on each open); the presheaf-level
content is the `mul_assoc` of `Γ(T, f⁻¹U)`, `(a·b)·c = a·(b·c)`, and the transport uses the `associativity`
coherence of a monoidal functor: `Functor.LaxMonoidal.transport_mul_assoc` + `presheaf_mul_assoc` (on each open
`tensor_ext₃'` reduces to pure tensors, where it is `_root_.mul_assoc`). -/
theorem AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.mul_assoc {X T : AlgebraicGeometry.Scheme.{u}} (f : T ⟶ X) :
    (α_ (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.obj f) (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.obj f) (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.obj f)).hom ≫ (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.obj f ◁ AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.mul f) ≫ AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.mul f =
      (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.mul f ▷ AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.obj f) ≫ AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.mul f := by
  letI := AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.presheafBraided X
  letI := AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.sheafificationLaxBraided X
  letI := AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.presheafMonObj f
  exact CategoryTheory.Functor.LaxMonoidal.transport_mul_assoc
    (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.sheafificationToModules X)
    (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.presheaf f)
    (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.counitIso f)

/-- Algebra axiom: commutativity (`β ≫ mul = mul`), since `Γ(T, f⁻¹U)` is a commutative ring (Stacks 01S5).
As for `one_mul`, the transport uses the **braiding** compatibility of the sheafification functor
(`Functor.LaxBraided.braided`; the localized monoidal structure is braided, and the braiding of the presheaf
tensor product is `a ⊗ₜ b ↦ b ⊗ₜ a` on pure tensors), and the presheaf level is `mul_comm` on each open:
`Functor.LaxBraided.transport_mul_comm` (lax braided functor: Mathlib's `Localization.Monoidal` gives a
`Functor.Braided` instance for `toMonoidalCategory`, see `sheafificationLaxBraided`) + `presheaf_mul_comm`
(on each open `_root_.mul_comm`). -/
theorem AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.mul_comm {X T : AlgebraicGeometry.Scheme.{u}} (f : T ⟶ X) :
    (β_ (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.obj f) (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.obj f)).hom ≫ AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.mul f = AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.mul f := by
  letI := AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.presheafBraided X
  letI := AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.sheafificationLaxBraided X
  letI := AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.presheafMonObj f
  letI := AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.presheafIsCommMonObj f
  exact CategoryTheory.Functor.LaxBraided.transport_mul_comm
    (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.sheafificationToModules X)
    (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.presheaf f)
    (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.counitIso f)

noncomputable def AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf
    {X T : AlgebraicGeometry.Scheme.{u}} (f : T ⟶ X) [AlgebraicGeometry.IsAffineHom f] : X.QCAlgebra where
  carrier := AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.obj f
  quasicoherent := AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.obj_isQuasicoherent f
  mul := AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.mul f
  one := SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom
  one_mul := AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.one_mul f
  mul_assoc := AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.mul_assoc f
  mul_comm := AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.mul_comm f

end
