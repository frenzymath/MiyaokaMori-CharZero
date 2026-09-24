import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModuleGenericFiber
import Mathlib.Algebra.Category.ModuleCat.Stalk
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Relative flatness of the original module stalks

For an actual scheme map `π : Y ⟶ S`, a module on `Y` is flat over `S` when
each of its stalks is flat over the corresponding local ring of `S`. Scalars
act through the actual `π.stalkMap`; the stalk and its local-ring action are
Mathlib's original constructions. The germ formula records this action on
local representatives.

Sources: Stacks Project, Tags 08KT and 01U3. The composition result is the
usual transitivity of flat modules. The consumer is the flat-family Euler
characteristic argument of the paper. This file makes no finiteness,
quasi-coherence, smoothness or nonemptiness assumption and asserts no Euler
constancy. Comparisons for the structure module and locally free modules
are separate obligations.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules.ModuleRelativeFlatness

variable {Y S : Scheme.{u}}

/-- Restrict the canonical stalk action along the actual scheme stalk map. -/
abbrev relativeStalkModule (π : Y ⟶ S) (M : Y.Modules) (y : Y) :
    Module (S.presheaf.stalk (π y)) (M.presheaf.stalk y) :=
  Module.compHom (M.presheaf.stalk y) (π.stalkMap y).hom

/-- Relative flatness at a point, with the specified restriction of scalars. -/
def FlatAt (π : Y ⟶ S) (M : Y.Modules) (y : Y) : Prop :=
  letI := relativeStalkModule π M y
  Module.Flat (S.presheaf.stalk (π y)) (M.presheaf.stalk y)

/-- Relative flatness means flatness of every original stalk over the target local ring. -/
def FlatOver (π : Y ⟶ S) (M : Y.Modules) : Prop :=
  ∀ y : Y, FlatAt π M y

/-- On local representatives, relative scalars act by pulling back the local function. -/
theorem relativeStalkModule_germ_smul (π : Y ⟶ S) (M : Y.Modules) (y : Y)
    (V : S.Opens) (hy : π y ∈ V) (r : Γ(S, V)) (m : Γ(M, π ⁻¹ᵁ V)) :
    letI := relativeStalkModule π M y
    S.presheaf.germ V (π y) hy r • M.presheaf.germ (π ⁻¹ᵁ V) y hy m =
      M.presheaf.germ (π ⁻¹ᵁ V) y hy (π.app V r • m) := by
  change π.stalkMap y (S.presheaf.germ V (π y) hy r) •
      M.presheaf.germ (π ⁻¹ᵁ V) y hy m = _
  rw [Scheme.Hom.germ_stalkMap_apply]
  exact (PresheafOfModules.germ_smul M.val y (π ⁻¹ᵁ V) hy (π.app V r) m).symm

/-- A stalk flat over its source local ring is relatively flat along a flat scheme map. -/
theorem flatAt_of_flat_stalk (π : Y ⟶ S) [AlgebraicGeometry.Flat π]
    (M : Y.Modules) (y : Y) (h : Module.Flat (Y.presheaf.stalk y) (M.presheaf.stalk y)) :
    FlatAt π M y := by
  letI := (π.stalkMap y).hom.toAlgebra
  letI := relativeStalkModule π M y
  letI : IsScalarTower (S.presheaf.stalk (π y)) (Y.presheaf.stalk y) (M.presheaf.stalk y) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  letI : Module.Flat (S.presheaf.stalk (π y)) (Y.presheaf.stalk y) :=
    AlgebraicGeometry.Flat.stalkMap π y
  letI := h
  exact Module.Flat.trans (S.presheaf.stalk (π y)) (Y.presheaf.stalk y) (M.presheaf.stalk y)

/-- Stalkwise flatness over the source implies relative flatness along a flat scheme map. -/
theorem flatOver_of_flat_stalks (π : Y ⟶ S) [AlgebraicGeometry.Flat π]
    (M : Y.Modules) (h : ∀ y : Y, Module.Flat (Y.presheaf.stalk y) (M.presheaf.stalk y)) :
    FlatOver π M :=
  fun y ↦ flatAt_of_flat_stalk π M y (h y)

end AlgebraicGeometry.Scheme.Modules.ModuleRelativeFlatness
