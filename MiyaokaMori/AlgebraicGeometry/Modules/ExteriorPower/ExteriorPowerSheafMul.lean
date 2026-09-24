import MiyaokaMori.Prelude
import MiyaokaMori.Algebra.ExteriorPowerMul
import MiyaokaMori.AlgebraicGeometry.Modules.ExteriorPower.ExteriorPowerSheaf
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensor
import MiyaokaMori.AlgebraicGeometry.Modules.ExteriorPower.ExteriorPowerRestriction
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModuleTensorAssociator

/-! # Wedge multiplication on exterior power sheaves

The **wedge multiplication** `Λ^a E ⊗_{O_X} Λ^b E ⟶ Λ^{a+b} E` on the exterior powers of an
`O_X`-module. The construction of `det F ⊗ det H ⟶ det G` for a short exact sequence
(`DetOfShortExact`) is locally "wedge together two families of sections"; this file provides the
underlying morphism of sheaves.

## Construction (why it goes through presheaves)

The exterior power sheaf is `AlgebraicGeometry.Scheme.Modules.moduleExteriorPower X E n`, the sheafification of
`moduleExteriorPresheaf X E.val n`, whose sections over an open `U` are the module exterior power
`⋀[Γ(X,U)]^n Γ(E,U)`; likewise the tensor sheaf is `AlgebraicGeometry.Scheme.Modules.moduleTensor A B`, the sheafification of
`A.val ⊗ᵖʳᵉ B.val`. After sheafification, sections are no longer pure wedges, so one **cannot** write a
formula directly on `Γ(Λ^a E, U) × Γ(Λ^b E, U)`. Instead:

1. on **presheaves**, use openwise the module wedge multiplication `Module.exteriorPowerMul`
   (`ExteriorPowerMul`), which is compatible with restriction (restriction acts termwise on pure
   wedges, wedge multiplication acts on indices by `Fin.append`, and the two commute), giving a
   morphism of presheaves `exteriorPresheafMul`;
2. use the fact that sheafification turns the tensor of the units into an isomorphism
   (`AlgebraicGeometry.Scheme.Modules.ModuleTensorAssociator.leftUnitIso` / `rightUnitIso`) to get the comparison isomorphism
   `sheafify(P ⊗ᵖʳᵉ Q) ≅ moduleTensor (sheafify P) (sheafify Q)`;
3. sheafify (1) and precompose with the inverse of (2) to obtain `Λ^a E ⊗ Λ^b E ⟶ Λ^{a+b} E`.

The multiplication is then completely characterized on **pure wedge sections** by
`exteriorSheafMul_wedge`: `(e_1∧…∧e_a) ⊗ (h_1∧…∧h_b) ↦ e_1∧…∧e_a∧h_1∧…∧h_b`.

Source: the multiplication used in the proof of Stacks 0FJB; Bourbaki, *Algèbre* III §7 (the graded
multiplication of the exterior algebra).
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry TensorProduct

noncomputable section

namespace MiyaokaMori.ExteriorPowerSheafMul

open AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false

variable {X : AlgebraicGeometry.Scheme.{u}}

local instance instCommRingSectionsForSheafMul (U : X.Opensᵒᵖ) :
    CommRing (X.ringCatSheaf.obj.obj U) :=
  inferInstanceAs (CommRing Γ(X, U.unop))

/-- The pure wedge generators in `ModuleCat` are Mathlib's `exteriorPower.ιMulti`. -/
theorem mk_eq_ιMulti {R : Type u} [CommRing R] {N : ModuleCat.{u} R} {n : ℕ} (v : Fin n → N) :
    (ModuleCat.exteriorPower.mk v : N.exteriorPower n) = exteriorPower.ιMulti R n v := rfl

/-- The value of the wedge multiplication on `ModuleCat` generators. -/
theorem exteriorPowerMul_mk {R : Type u} [CommRing R] {N : ModuleCat.{u} R} {a b : ℕ}
    (v : Fin a → N) (w : Fin b → N) :
    Module.exteriorPowerMul R N a b
        (ModuleCat.exteriorPower.mk v ⊗ₜ[R] ModuleCat.exteriorPower.mk w) =
      ModuleCat.exteriorPower.mk (Fin.append v w) :=
  Module.exteriorPowerMul_ιMulti v w

/-- A linear map out of `⋀^a N ⊗ ⋀^b N` is determined by its values on tensors of generators
(`ModuleCat` form). -/
theorem exteriorPowerMul_hom_ext_mk {R : Type u} [CommRing R] {N : ModuleCat.{u} R}
    {P : Type u} [AddCommGroup P] [Module R P] {a b : ℕ}
    {f g : ((⋀[R]^a N) ⊗[R] (⋀[R]^b N)) →ₗ[R] P}
    (h : ∀ (v : Fin a → N) (w : Fin b → N),
      f (ModuleCat.exteriorPower.mk v ⊗ₜ[R] ModuleCat.exteriorPower.mk w) =
        g (ModuleCat.exteriorPower.mk v ⊗ₜ[R] ModuleCat.exteriorPower.mk w)) :
    f = g :=
  Module.exteriorPowerMul_hom_ext h

/-- **Wedge multiplication on presheaves** `Λ^a_pre E ⊗ᵖʳᵉ Λ^b_pre E ⟶ Λ^{a+b}_pre E`.

Openwise it is the module wedge multiplication `Module.exteriorPowerMul`; compatibility with
restriction (naturality) follows from `exteriorRestriction_mk` (restriction acts termwise on wedge
generators) and `Module.exteriorPower_comp_finAppend` (composition commutes with `Fin.append`). -/
def exteriorPresheafMul (X : AlgebraicGeometry.Scheme.{u}) (M : X.PresheafOfModules) (a b : ℕ) :
    PresheafOfModules.Monoidal.tensorObj (R := X.presheaf)
        (moduleExteriorPresheaf X M a) (moduleExteriorPresheaf X M b) ⟶
      moduleExteriorPresheaf X M (a + b) where
  app U := ModuleCat.ofHom (Module.exteriorPowerMul _ (M.obj U) a b)
  naturality {U V} i := by
    refine ModuleCat.hom_ext (exteriorPowerMul_hom_ext_mk (fun v w => ?_))
    change Module.exteriorPowerMul _ (M.obj V) a b
        (exteriorRestriction X M a i (ModuleCat.exteriorPower.mk v) ⊗ₜ
          exteriorRestriction X M b i (ModuleCat.exteriorPower.mk w)) =
      exteriorRestriction X M (a + b) i
        (Module.exteriorPowerMul _ (M.obj U) a b
          (ModuleCat.exteriorPower.mk v ⊗ₜ ModuleCat.exteriorPower.mk w))
    rw [exteriorRestriction_mk, exteriorRestriction_mk, exteriorPowerMul_mk,
      exteriorPowerMul_mk, exteriorRestriction_mk, Module.exteriorPower_comp_finAppend]

/-- The comparison isomorphism between sheafification and tensor product:
`sheafify(P ⊗ᵖʳᵉ Q) ≅ (sheafify P) ⊗ (sheafify Q)`, the composite of `leftUnitIso` (replace the first
factor by its sheafification) and `rightUnitIso` (the second factor), both coming from the fact that
sheafification turns `η_P ⊗ 1` into an isomorphism. -/
def tensorSheafifyIso (P Q : X.PresheafOfModules) :
    moduleSheafification X (PresheafOfModules.Monoidal.tensorObj (R := X.presheaf) P Q) ≅
      moduleTensor (moduleSheafification X P) (moduleSheafification X Q) :=
  ModuleTensorAssociator.leftUnitIso P Q ≪≫
    ModuleTensorAssociator.rightUnitIso (moduleSheafification X P).val Q

/-- The comparison isomorphism sends the unit image of a presheaf tensor to the tensor section of the
two unit images. -/
theorem tensorSheafifyIso_hom_section (P Q : X.PresheafOfModules) (U : X.Opens)
    (p : P.obj (op U)) (q : Q.obj (op U)) :
    (tensorSheafifyIso P Q).hom.app U
        (moduleSheafificationUnit X
          (PresheafOfModules.Monoidal.tensorObj (R := X.presheaf) P Q) U (p ⊗ₜ[Γ(X, U)] q)) =
      moduleTensorSection (moduleSheafificationUnit X P U p)
        (moduleSheafificationUnit X Q U q) := by
  change (ModuleTensorAssociator.rightUnitIso (moduleSheafification X P).val Q).hom.app U
      ((ModuleTensorAssociator.leftUnitIso P Q).hom.app U _) = _
  rw [ModuleTensorAssociator.leftUnitIso_section,
    ModuleTensorAssociator.rightUnitIso_section]
  rfl

/-- The inverse comparison isomorphism sends a tensor section back to the unit image of the presheaf
tensor. -/
theorem tensorSheafifyIso_inv_section (P Q : X.PresheafOfModules) (U : X.Opens)
    (p : P.obj (op U)) (q : Q.obj (op U)) :
    (tensorSheafifyIso P Q).inv.app U
        (moduleTensorSection (moduleSheafificationUnit X P U p)
          (moduleSheafificationUnit X Q U q)) =
      moduleSheafificationUnit X
        (PresheafOfModules.Monoidal.tensorObj (R := X.presheaf) P Q) U (p ⊗ₜ[Γ(X, U)] q) := by
  have h := congrArg
    (fun f => f.app U
      (moduleSheafificationUnit X
        (PresheafOfModules.Monoidal.tensorObj (R := X.presheaf) P Q) U (p ⊗ₜ[Γ(X, U)] q)))
    (tensorSheafifyIso P Q).hom_inv_id
  change (tensorSheafifyIso P Q).inv.app U
      ((tensorSheafifyIso P Q).hom.app U
        (moduleSheafificationUnit X
          (PresheafOfModules.Monoidal.tensorObj (R := X.presheaf) P Q) U
          (p ⊗ₜ[Γ(X, U)] q))) = _ at h
  rw [tensorSheafifyIso_hom_section] at h
  exact h

/-- **Wedge multiplication on sheaves** `Λ^a E ⊗_{O_X} Λ^b E ⟶ Λ^{a+b} E`: the inverse of the
comparison isomorphism followed by the sheafification of the presheaf wedge multiplication (see the
module docstring). -/
def exteriorSheafMul (X : AlgebraicGeometry.Scheme.{u}) (E : X.Modules) (a b : ℕ) :
    moduleTensor (moduleExteriorPower X E a) (moduleExteriorPower X E b) ⟶
      moduleExteriorPower X E (a + b) :=
  (tensorSheafifyIso (moduleExteriorPresheaf X E.val a)
      (moduleExteriorPresheaf X E.val b)).inv ≫
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (exteriorPresheafMul X E.val a b)

/-- The value of the wedge multiplication on pure wedge sections: indices are concatenated by
`Fin.append`, i.e. `(e_1∧…∧e_a) ⊗ (h_1∧…∧h_b) ↦ e_1∧…∧e_a∧h_1∧…∧h_b`.

This formula **completely characterizes** `exteriorSheafMul` (the images of pure wedges locally
generate after sheafification). -/
theorem exteriorSheafMul_wedge (X : AlgebraicGeometry.Scheme.{u}) (E : X.Modules) (a b : ℕ)
    (U : X.Opens) (v : Fin a → Γ(E, U)) (w : Fin b → Γ(E, U)) :
    (exteriorSheafMul X E a b).app U
        (moduleTensorSection (moduleExteriorWedge X E a U v)
          (moduleExteriorWedge X E b U w)) =
      moduleExteriorWedge X E (a + b) U (Fin.append v w) := by
  change ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (exteriorPresheafMul X E.val a b)).val.app (op U)
      ((tensorSheafifyIso (moduleExteriorPresheaf X E.val a)
        (moduleExteriorPresheaf X E.val b)).inv.app U
        (moduleTensorSection
          (moduleSheafificationUnit X (moduleExteriorPresheaf X E.val a) U
            (ModuleCat.exteriorPower.mk v))
          (moduleSheafificationUnit X (moduleExteriorPresheaf X E.val b) U
            (ModuleCat.exteriorPower.mk w)))) = _
  rw [tensorSheafifyIso_inv_section, moduleSheafificationUnit_naturality]
  change moduleSheafificationUnit X (moduleExteriorPresheaf X E.val (a + b)) U
      (Module.exteriorPowerMul _ (E.val.obj (op U)) a b
        (ModuleCat.exteriorPower.mk v ⊗ₜ ModuleCat.exteriorPower.mk w)) = _
  rw [exteriorPowerMul_mk]
  rfl

end MiyaokaMori.ExteriorPowerSheafMul

/-- Functoriality of the exterior power in morphisms of sheaves of modules, `Λ^n(φ) : Λ^n E ⟶ Λ^n E'`
(an alias of `AlgebraicGeometry.Scheme.Modules.moduleExteriorMap`). -/
def AlgebraicGeometry.Scheme.Modules.exteriorMap {X : AlgebraicGeometry.Scheme.{u}}
    {E E' : X.Modules} (φ : E ⟶ E') (n : ℕ) :
    AlgebraicGeometry.Scheme.Modules.exteriorPower E n ⟶
      AlgebraicGeometry.Scheme.Modules.exteriorPower E' n :=
  AlgebraicGeometry.Scheme.Modules.moduleExteriorMap X n φ

/-- Functoriality of the tensor sheaf in two morphisms, `φ ⊗ ψ`: the presheaf `tensorHom`, sheafified. -/
def AlgebraicGeometry.Scheme.Modules.tensorMap {X : AlgebraicGeometry.Scheme.{u}}
    {A A' B B' : X.Modules} (φ : A ⟶ A') (ψ : B ⟶ B') :
    AlgebraicGeometry.Scheme.Modules.tensor A B ⟶
      AlgebraicGeometry.Scheme.Modules.tensor A' B' :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
    (PresheafOfModules.Monoidal.tensorHom (R := X.presheaf) φ.val ψ.val)

/-- Alias: `Λ^a E ⊗_{O_X} Λ^b E ⟶ Λ^{a+b} E` (see `MiyaokaMori.ExteriorPowerSheafMul.exteriorSheafMul`). -/
def AlgebraicGeometry.Scheme.Modules.exteriorPowerMul {X : AlgebraicGeometry.Scheme.{u}}
    (E : X.Modules) (a b : ℕ) :
    AlgebraicGeometry.Scheme.Modules.tensor
        (AlgebraicGeometry.Scheme.Modules.exteriorPower E a)
        (AlgebraicGeometry.Scheme.Modules.exteriorPower E b) ⟶
      AlgebraicGeometry.Scheme.Modules.exteriorPower E (a + b) :=
  MiyaokaMori.ExteriorPowerSheafMul.exteriorSheafMul X E a b

end
