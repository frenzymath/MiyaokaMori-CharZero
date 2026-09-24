import MiyaokaMori.Prelude

/-! # The structure map of a stalk over the base field

The `k`-algebra structure map `k → O_{X,x}` on the stalk of a `k`-scheme `X` (given by
`Spec O_{X,x} → X → Spec k`), and its compatibility with specialization maps and with the stalk
maps of `k`-morphisms.

Sources: Hartshorne II.2 (schemes over `k`); Stacks 01J5.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open AlgebraicGeometry

/-- The structure map `k → O_{X,x}`: the ring map corresponding to `Spec O_{X,x} → X → Spec k`. -/
def AlgebraicGeometry.Scheme.stalkStructureHom (k : Type u) [Field k] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))] (x : X) : k →+* X.presheaf.stalk x :=
  (Spec.preimage (X.fromSpecStalk x ≫ (X ↘ Spec (CommRingCat.of k)))).hom

theorem AlgebraicGeometry.Scheme.SpecMap_stalkStructureHom (k : Type u) [Field k] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))] (x : X) :
    Spec.map (CommRingCat.ofHom (X.stalkStructureHom k x)) =
      X.fromSpecStalk x ≫ (X ↘ Spec (CommRingCat.of k)) :=
  Spec.map_preimage _

theorem AlgebraicGeometry.Scheme.stalkSpecializes_comp_stalkStructureHom (k : Type u) [Field k]
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of k))] {x y : X} (h : x ⤳ y) :
    (X.presheaf.stalkSpecializes h).hom.comp (X.stalkStructureHom k y) = X.stalkStructureHom k x := by
  have key : CommRingCat.ofHom (X.stalkStructureHom k y) ≫ X.presheaf.stalkSpecializes h =
      CommRingCat.ofHom (X.stalkStructureHom k x) := by
    apply Spec.map_injective
    rw [Spec.map_comp, X.SpecMap_stalkStructureHom k y, X.SpecMap_stalkStructureHom k x,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk_assoc]
  exact congrArg CommRingCat.Hom.hom key

theorem AlgebraicGeometry.Scheme.Hom.stalkMap_comp_stalkStructureHom (k : Type u) [Field k]
    {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))] [Y.Over (Spec (CommRingCat.of k))]
    (f : X ⟶ Y) [f.IsOver (Spec (CommRingCat.of k))] (x : X) :
    (f.stalkMap x).hom.comp (Y.stalkStructureHom k (f x)) = X.stalkStructureHom k x := by
  have key : CommRingCat.ofHom (Y.stalkStructureHom k (f x)) ≫ f.stalkMap x =
      CommRingCat.ofHom (X.stalkStructureHom k x) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Y.SpecMap_stalkStructureHom k (f x), X.SpecMap_stalkStructureHom k x,
      Scheme.SpecMap_stalkMap_fromSpecStalk_assoc, CategoryTheory.comp_over]
  exact congrArg CommRingCat.Hom.hom key

end
