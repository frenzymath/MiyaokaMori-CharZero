import MiyaokaMori.Prelude

/-! # Pullback of rational functions

The pullback of rational functions `f^* : K(Y) → K(X)` (the stalk map at the generic point)
induced by a morphism `f : X → Y` of integral schemes sending the generic point to the generic
point; for a non-dominant morphism it is the zero function by convention. The paper's `η^*ψ`,
`η_1^*ψ` are instances.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- For a dominant `f` the pullback is a ring map (a map of fields, hence injective):
`AlgebraicGeometry.Scheme.dominantFunctionFieldMap` (the stalk map at the generic point, aligned with `stalkCongr`);
`h` gives `IsDominant` (the generic point is in the image, whose closure is everything). -/

noncomputable def pullbackFunctionHom {X Y : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsIntegral X]
    [AlgebraicGeometry.IsIntegral Y] (f : X ⟶ Y) (h : f.base (genericPoint X) = genericPoint Y) :
    Y.functionField →+* X.functionField :=
  haveI : AlgebraicGeometry.IsDominant f :=
    ⟨((dense_iff_closure_eq.mpr (genericPoint_closure Y)).mono
      (Set.singleton_subset_iff.mpr ⟨genericPoint X, h⟩))⟩
  (AlgebraicGeometry.Scheme.dominantFunctionFieldMap f).hom

/-- The pullback without a proof obligation: `pullbackFunctionHom` when `f` is dominant, the zero
function otherwise. -/

noncomputable def pullbackFunction {X Y : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsIntegral X]
    [AlgebraicGeometry.IsIntegral Y] (f : X ⟶ Y) : Y.functionField → X.functionField := by
  classical
  exact if h : f.base (genericPoint X) = genericPoint Y then pullbackFunctionHom f h else fun _ => 0

theorem pullbackFunctionHom_apply {X Y : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsIntegral X]
    [AlgebraicGeometry.IsIntegral Y] (f : X ⟶ Y) (h : f.base (genericPoint X) = genericPoint Y)
    (ψ : Y.functionField) : pullbackFunctionHom f h ψ = pullbackFunction f ψ := by
  simp [pullbackFunction, h]

theorem pullbackFunction_ne_zero {X Y : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsIntegral X]
    [AlgebraicGeometry.IsIntegral Y] (f : X ⟶ Y) (h : f.base (genericPoint X) = genericPoint Y)
    {ψ : Y.functionField} (hψ : ψ ≠ 0) : pullbackFunction f ψ ≠ 0 := by
  rw [← pullbackFunctionHom_apply f h ψ]
  intro hz
  apply hψ
  apply (pullbackFunctionHom f h).injective
  simpa using hz

end
