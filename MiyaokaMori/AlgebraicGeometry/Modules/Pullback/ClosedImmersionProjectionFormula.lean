import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesProjectionFormulaHom
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorMonoidalIso

/-! # The projection formula for a closed immersion

The projection formula for a closed immersion: `i_*(G ⊗ i^*L) ≅ i_*G ⊗ L` for `L` a line bundle
(in particular for invertible sheaves and their tensor powers).

This file gives the **explicit** isomorphism `AlgebraicGeometry.Scheme.Modules.pushforwardTensorPullbackIso`,
built from the canonical comparison morphism `projectionFormulaHom` (the unit of `i^* ⊣ i_*`
followed by the monoidal structure morphism of `f^*` and the counit), the canonical isomorphism
`Modules.tensor ≅ ⊗` (monoidal) and the braiding of the symmetric structure;
`pushforwardTensorPullbackIso_inv` records this as an equation, and
`projectionFormulaHom_eq_unit_comp` unfolds `projectionFormulaHom` as "adjunction unit ≫ i_*(…)",
which is the compatibility with the adjunction unit. The bare existence statement
`pushforward_tensor_pullback_iso` is kept as a corollary.

Reference: Stacks 01E8.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
open scoped CategoryTheory.MonoidalCategory

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {Z X : AlgebraicGeometry.Scheme.{u}}

/-- The canonical comparison morphism is "adjunction unit ≫ i_*(monoidal structure morphism of `f^*`
≫ counit)", i.e. it is compatible with the adjunction unit (the unfolding of `projectionFormulaHom`:
the unit form of `Adjunction.homEquiv`). -/
theorem projectionFormulaHom_eq_unit_comp (i : Z ⟶ X) (L : X.Modules) (G : Z.Modules) :
    AlgebraicGeometry.Scheme.Modules.projectionFormulaHom i L G
      = (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
          (L ⊗ (AlgebraicGeometry.Scheme.Modules.pushforward i).obj G) ≫
        (AlgebraicGeometry.Scheme.Modules.pushforward i).map
          (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom i L
              ((AlgebraicGeometry.Scheme.Modules.pushforward i).obj G) ≫
            ((AlgebraicGeometry.Scheme.Modules.pullback i).obj L ◁
              (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction i).counit.app G)) :=
  (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction i).homEquiv_apply _ _ _

/-- **Projection formula for a closed immersion (any morphism of schemes suffices): the explicit
isomorphism** `i_*(G ⊗ i^*L) ≅ i_*G ⊗ L`. Both `⊗` are `Modules.tensor`; the isomorphism is
assembled from the canonical comparison morphism `projectionFormulaHom` (invertible for `L` a
line bundle), `Modules.tensor ≅ ⊗` (monoidal), and the braiding of the symmetric structure. -/
def pushforwardTensorPullbackIso (i : Z ⟶ X) (G : Z.Modules) (L : X.Modules) [L.IsLineBundle] :
    (AlgebraicGeometry.Scheme.Modules.pushforward i).obj
        (G.tensor ((AlgebraicGeometry.Scheme.Modules.pullback i).obj L)) ≅
      ((AlgebraicGeometry.Scheme.Modules.pushforward i).obj G).tensor L :=
  (AlgebraicGeometry.Scheme.Modules.pushforward i).mapIso
      (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj G
          ((AlgebraicGeometry.Scheme.Modules.pullback i).obj L) ≪≫
        β_ G ((AlgebraicGeometry.Scheme.Modules.pullback i).obj L)) ≪≫
    (AlgebraicGeometry.Scheme.Modules.projectionFormulaIso i L G).symm ≪≫
    β_ L ((AlgebraicGeometry.Scheme.Modules.pushforward i).obj G) ≪≫
    (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj
      ((AlgebraicGeometry.Scheme.Modules.pushforward i).obj G) L).symm

/-- The inverse of the isomorphism is the canonical comparison morphism (transported on both sides by
`Modules.tensor ≅ ⊗` and the braiding); together with `projectionFormulaHom_eq_unit_comp` this
says that the isomorphism is compatible with the adjunction unit. -/
theorem pushforwardTensorPullbackIso_inv (i : Z ⟶ X) (G : Z.Modules) (L : X.Modules)
    [L.IsLineBundle] :
    (pushforwardTensorPullbackIso i G L).inv
      = (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj
            ((AlgebraicGeometry.Scheme.Modules.pushforward i).obj G) L).hom ≫
        (β_ ((AlgebraicGeometry.Scheme.Modules.pushforward i).obj G) L).hom ≫
        AlgebraicGeometry.Scheme.Modules.projectionFormulaHom i L G ≫
        (AlgebraicGeometry.Scheme.Modules.pushforward i).map
          ((β_ G ((AlgebraicGeometry.Scheme.Modules.pullback i).obj L)).inv ≫
            (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj G
              ((AlgebraicGeometry.Scheme.Modules.pullback i).obj L)).inv) := by
  simp [pushforwardTensorPullbackIso, AlgebraicGeometry.Scheme.Modules.projectionFormulaIso,
    Functor.map_comp, SymmetricCategory.braiding_swap_eq_inv_braiding]

end AlgebraicGeometry.Scheme.Modules

/-- The bare existence statement, a corollary of the explicit isomorphism above. -/
theorem AlgebraicGeometry.Scheme.Modules.pushforward_tensor_pullback_iso
    {Z X : AlgebraicGeometry.Scheme.{u}}
    (i : Z ⟶ X) (G : Z.Modules) (L : X.Modules) [L.IsLineBundle] :
    Nonempty ((AlgebraicGeometry.Scheme.Modules.pushforward i).obj
        (G.tensor ((AlgebraicGeometry.Scheme.Modules.pullback i).obj L)) ≅
      ((AlgebraicGeometry.Scheme.Modules.pushforward i).obj G).tensor L) :=
  ⟨AlgebraicGeometry.Scheme.Modules.pushforwardTensorPullbackIso i G L⟩

end
