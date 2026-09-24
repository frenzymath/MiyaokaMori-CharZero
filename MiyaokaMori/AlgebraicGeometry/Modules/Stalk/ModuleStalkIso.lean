import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModuleGenericFiber
import Mathlib.Topology.Sheaves.Stalks

/-!
# Detecting module-sheaf isomorphisms on the actual stalks

The same linear stalk maps used for generic fibers detect isomorphisms of module
sheaves. The converse uses the sheaf condition on the underlying abelian-group
sheaves and then reflects isomorphisms through the module forgetful functor.
It requires neither local freeness nor a nonempty scheme.

The consumers are the stalk comparisons for exterior-power pullback in the
degree computation and the tensor
sheafification comparison. The stalkwise bijectivity remains a separate proof
obligation for each particular comparison map.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

universe u

variable {X : Scheme.{u}} {M N : X.Modules}

/-- A morphism of module sheaves is invertible precisely when its actual linear stalk maps
are bijective at every point. -/
theorem moduleHom_isIso_iff_stalk_bijective (φ : M ⟶ N) :
    IsIso φ ↔ ∀ x : X, Function.Bijective (moduleStalkMap X x φ) := by
  constructor
  · intro h x
    let : IsIso φ := h
    exact (ConcreteCategory.isIso_iff_bijective ((moduleStalkFunctor X x).map φ)).mp
      inferInstance
  · intro h
    apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
    intro U
    apply (ConcreteCategory.isIso_iff_bijective (φ.app U)).mpr
    exact TopCat.Presheaf.app_bijective_of_stalkFunctor_map_bijective
      ((SheafOfModules.toSheaf X.ringCatSheaf).map φ) U (fun x _ ↦ h x)

end AlgebraicGeometry.Scheme.Modules
