import MiyaokaMori.AlgebraicGeometry.Modules.ExteriorPower.ExteriorPowerStalkConjugacy

/-!
# The stalk conjugacy on arbitrary scalar-extension sections

The preceding file proves the comparison on pure scalar/wedge generators.  This
file records its linear extension to every element of the actual tensor product
`X_stalk ⊗[Y_stalk] (⋀^n M_stalk)`.  The extension uses the public
`TensorProduct.induction_on` and `exteriorPower.linearMap_ext` APIs; no
bijectivity or `IsIso` assertion is introduced.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Modules
open MiyaokaMori.Algebra

universe u

set_option backward.isDefEq.respectTransparency false

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) (n : ℕ) (x : X)

local instance (U : Y.Opensᵒᵖ) : CommRing (Y.ringCatSheaf.obj.obj U) :=
  inferInstanceAs (CommRing Γ(Y, U.unop))

local instance : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
  modulePullbackStalkAlgebra f x

-- `⋀[R]^n` binds tighter than function application, so `⋀[R]^n M.presheaf.stalk (f x)` parses as
-- `(⋀[R]^n M.presheaf.stalk) (f x)` (error: `↥Y → Ab` used as `Type u`); hence the parentheses.
/--
The stalk conjugacy for the canonical exterior pullback comparison holds on
every element of the actual scalar-extension tensor product.  The preceding
pure scalar/wedge identity is extended by `TensorProduct.induction_on` and the
public exterior-power spanning/extensionality API.  The statement includes
degree zero and makes no claim that either comparison map is an isomorphism.
-/
theorem moduleExteriorPullbackComparison_stalk_conjugacy_all
    (z : X.presheaf.stalk x ⊗[Y.presheaf.stalk (f x)]
      (⋀[Y.presheaf.stalk (f x)]^n (M.presheaf.stalk (f x)))) :
    moduleExteriorPowerStalkEquiv X ((Scheme.Modules.pullback f).obj M) x n
        (moduleStalkMap X x (moduleExteriorPullbackComparison f M n)
          (modulePullbackStalkTensorMap f (moduleExteriorPower Y M n) x
            (((moduleExteriorPowerStalkEquiv Y M (f x) n).symm.toLinearMap.baseChange
              (X.presheaf.stalk x)) z))) =
      exteriorPower.map n (modulePullbackStalkTensorMap f M x)
        (exteriorPowerBaseChangeMap
          (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)
          (M.presheaf.stalk (f x)) n z) := by
  let A :
      (X.presheaf.stalk x ⊗[Y.presheaf.stalk (f x)]
          (⋀[Y.presheaf.stalk (f x)]^n (M.presheaf.stalk (f x)))) →ₗ[X.presheaf.stalk x]
        (⋀[X.presheaf.stalk x]^n
          (((Scheme.Modules.pullback f).obj M).presheaf.stalk x)) :=
    (moduleExteriorPowerStalkEquiv X ((Scheme.Modules.pullback f).obj M) x n).toLinearMap.comp
      ((moduleStalkMap X x (moduleExteriorPullbackComparison f M n)).comp
        ((modulePullbackStalkTensorMap f (moduleExteriorPower Y M n) x).comp
          ((moduleExteriorPowerStalkEquiv Y M (f x) n).symm.toLinearMap.baseChange
            (X.presheaf.stalk x))))
  let B :
      (X.presheaf.stalk x ⊗[Y.presheaf.stalk (f x)]
          (⋀[Y.presheaf.stalk (f x)]^n (M.presheaf.stalk (f x)))) →ₗ[X.presheaf.stalk x]
        (⋀[X.presheaf.stalk x]^n
          (((Scheme.Modules.pullback f).obj M).presheaf.stalk x)) :=
    (exteriorPower.map n (modulePullbackStalkTensorMap f M x)).comp
      (exteriorPowerBaseChangeMap
        (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)
        (M.presheaf.stalk (f x)) n)
  change A z = B z
  induction z using TensorProduct.induction_on with
  | zero =>
      simp only [map_zero]
  | add z₁ z₂ hz₁ hz₂ =>
      simpa only [map_add] using congrArg₂ (· + ·) hz₁ hz₂
  | tmul s m =>
      letI : Module (Y.presheaf.stalk (f x))
          (⋀[X.presheaf.stalk x]^n
            (((Scheme.Modules.pullback f).obj M).presheaf.stalk x)) :=
        Module.compHom _ (f.stalkMap x).hom
      letI : IsScalarTower (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)
          (⋀[X.presheaf.stalk x]^n
            (((Scheme.Modules.pullback f).obj M).presheaf.stalk x)) :=
        IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
      let A_s :
          (⋀[Y.presheaf.stalk (f x)]^n (M.presheaf.stalk (f x))) →ₗ[Y.presheaf.stalk (f x)]
            (⋀[X.presheaf.stalk x]^n
              (((Scheme.Modules.pullback f).obj M).presheaf.stalk x)) :=
        (A.restrictScalars (Y.presheaf.stalk (f x))).comp
          (TensorProduct.mk (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)
            (⋀[Y.presheaf.stalk (f x)]^n (M.presheaf.stalk (f x))) s)
      let B_s :
          (⋀[Y.presheaf.stalk (f x)]^n (M.presheaf.stalk (f x))) →ₗ[Y.presheaf.stalk (f x)]
            (⋀[X.presheaf.stalk x]^n
              (((Scheme.Modules.pullback f).obj M).presheaf.stalk x)) :=
        (B.restrictScalars (Y.presheaf.stalk (f x))).comp
          (TensorProduct.mk (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)
            (⋀[Y.presheaf.stalk (f x)]^n (M.presheaf.stalk (f x))) s)
      have hAB : A_s = B_s := by
        apply exteriorPower.linearMap_ext
        apply AlternatingMap.ext
        intro v
        change moduleExteriorPowerStalkEquiv X ((Scheme.Modules.pullback f).obj M) x n
          (moduleStalkMap X x (moduleExteriorPullbackComparison f M n)
            (modulePullbackStalkTensorMap f (moduleExteriorPower Y M n) x
              (((moduleExteriorPowerStalkEquiv Y M (f x) n).symm.toLinearMap.baseChange
                (X.presheaf.stalk x))
                (s ⊗ₜ[Y.presheaf.stalk (f x)]
                  exteriorPower.ιMulti (Y.presheaf.stalk (f x)) n v)))) = _
        rw [LinearMap.baseChange_tmul]
        exact moduleExteriorPullbackComparison_stalk_conjugacy f M n x s v
      exact congrArg (fun q ↦ q m) hAB

end AlgebraicGeometry.Scheme.Modules
