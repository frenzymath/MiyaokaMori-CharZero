import MiyaokaMori.Prelude
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-! # Stalk isomorphisms along flat preimmersions

A flat preimmersion of schemes induces isomorphisms on all stalks. (Used for the local model
`Bl_𝔪 Spec O_{W,x} = Bl_x W ×_W Spec O_{W,x} → Bl_x W` in the proof of Stacks 0AHH (blowing up improves the length sum):
`Spec O_{W,x} → W` is a flat preimmersion, and both properties are stable under base change.)

Source: Stacks 00HR (a flat local homomorphism of local rings is faithfully flat, hence injective);
Stacks 01S4 (preimmersions have surjective stalk maps).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- A flat preimmersion induces isomorphisms on stalks: the stalk map `O_{Y,f x} → O_{X,x}` is
surjective (preimmersion), and it is a flat local homomorphism of local rings, hence faithfully
flat (`Module.FaithfullyFlat.of_flat_of_isLocalHom`), hence injective. -/
theorem AlgebraicGeometry.Scheme.Hom.isIso_stalkMap_of_flat_of_isPreimmersion
    {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) [AlgebraicGeometry.Flat f]
    [AlgebraicGeometry.IsPreimmersion f] (x : X) : IsIso (f.stalkMap x) := by
  have hsurj : Function.Surjective (f.stalkMap x) := f.stalkMap_surjective x
  have hflat : (f.stalkMap x).hom.Flat := AlgebraicGeometry.Flat.stalkMap f x
  let _ : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := (f.stalkMap x).hom.toAlgebra
  have : Module.Flat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := hflat
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
    inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
  have : Module.FaithfullyFlat (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hinj : Function.Injective (f.stalkMap x) :=
    FaithfulSMul.algebraMap_injective (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)
  exact (ConcreteCategory.isIso_iff_bijective _).mpr ⟨hinj, hsurj⟩

end
