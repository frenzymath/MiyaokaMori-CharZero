import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.FreeSheaf
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.PullbackUnit

/-! # Pullback of free sheaves of modules on schemes

The pullback of sheaves of modules on schemes sends free sheaves to free sheaves:
`g^*O_Y^{(I)} ≅ O_X^{(I)}`, naturally in `I`, matching `g^*(ιFree i)` with `ιFree i` (the
instantiation on schemes of Mathlib's `SheafOfModules.pullbackObjFreeIso`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The instance `(Opens.map g.base).Final` is `AlgebraicGeometry.Scheme.Modules.opensMap_final`
(`PullbackUnit.lean`). The isomorphism `g^*O_Y^{(I)} ≅ O_X^{(I)}`. -/
noncomputable def AlgebraicGeometry.Scheme.Modules.pullbackObjFreeIso {X Y : AlgebraicGeometry.Scheme.{u}}
    (g : X ⟶ Y) (I : Type u) :
    (AlgebraicGeometry.Scheme.Modules.pullback g).obj (SheafOfModules.free (R := Y.ringCatSheaf) I) ≅
      (SheafOfModules.free (R := X.ringCatSheaf) I : X.Modules) :=
  haveI : (SheafOfModules.pushforward.{u} g.toRingCatSheafHom).IsRightAdjoint :=
    (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction g).isRightAdjoint
  SheafOfModules.pullbackObjFreeIso g.toRingCatSheafHom I

theorem AlgebraicGeometry.Scheme.Modules.pullbackObjFreeIso_hom_naturality {X Y : AlgebraicGeometry.Scheme.{u}}
    (g : X ⟶ Y) {I J : Type u} (φ : I → J) :
    (AlgebraicGeometry.Scheme.Modules.pullback g).map (SheafOfModules.freeMap (R := Y.ringCatSheaf) φ) ≫
        (AlgebraicGeometry.Scheme.Modules.pullbackObjFreeIso g J).hom =
      (AlgebraicGeometry.Scheme.Modules.pullbackObjFreeIso g I).hom ≫
        (SheafOfModules.freeMap (R := X.ringCatSheaf) φ : (SheafOfModules.free I : X.Modules) ⟶ SheafOfModules.free J) :=
  haveI : (SheafOfModules.pushforward.{u} g.toRingCatSheafHom).IsRightAdjoint :=
    (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction g).isRightAdjoint
  SheafOfModules.pullbackObjFreeIso_hom_naturality g.toRingCatSheafHom φ

end
