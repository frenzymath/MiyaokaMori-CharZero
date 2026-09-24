import MiyaokaMori.Algebra.ExteriorPowerBaseChange
import MiyaokaMori.AlgebraicGeometry.Modules.ExteriorPower.ExteriorPowerPullbackComparison
import MiyaokaMori.AlgebraicGeometry.Modules.ExteriorPower.ExteriorPowerStalk
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModulePullbackStalkTensor

/-!
# The stalk formula for the exterior pullback comparison

This file records the actual comparison on pure scalar/wedge generators.  The
source stalk of the pulled-back exterior power is mapped by the genuine
pullback unit, while the right hand side first applies the scalar-extension
map for exterior powers and then wedges the genuine pullback unit on each
entry.  No inverse or isomorphism assertion is used here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Modules
open MiyaokaMori.Algebra

universe u

set_option backward.isDefEq.respectTransparency false

attribute [local instance] modulePullbackStalkAlgebra

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) (n : ℕ) (x : X)

local instance (U : Y.Opensᵒᵖ) : CommRing (Y.ringCatSheaf.obj.obj U) :=
  inferInstanceAs (CommRing Γ(Y, U.unop))

-- `whnf` times out at the default 200000 heartbeats; raising the limit suffices (elaboration cost, not
-- a kernel problem).
set_option maxHeartbeats 1000000 in
/--
On every scalar and finite tuple of source stalk elements, the stalk of the
canonical exterior pullback comparison agrees with scalar extension followed
by the exterior power of the genuine module pullback stalk map.

The statement is deliberately on the pure scalar/wedge generators.  It uses
the actual `modulePullbackStalkTensorMap` for both `M` and
`moduleExteriorPower Y M n`; no bijectivity or `IsIso` hypothesis is hidden in
the declaration.  The empty tuple is covered by `Fin 0`.
-/
theorem moduleExteriorPullbackComparison_stalk_conjugacy
    (s : X.presheaf.stalk x)
    (v : Fin n → M.presheaf.stalk (f x)) :
    moduleExteriorPowerStalkEquiv X ((Scheme.Modules.pullback f).obj M) x n
        (moduleStalkMap X x (moduleExteriorPullbackComparison f M n)
          (modulePullbackStalkTensorMap f (moduleExteriorPower Y M n) x
            (s ⊗ₜ[Y.presheaf.stalk (f x)]
              ((moduleExteriorPowerStalkEquiv Y M (f x) n).symm
                (exteriorPower.ιMulti (Y.presheaf.stalk (f x)) n v))))) =
      exteriorPower.map n (modulePullbackStalkTensorMap f M x)
        (exteriorPowerBaseChangeMap
          (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)
          (M.presheaf.stalk (f x)) n
          (s ⊗ₜ[Y.presheaf.stalk (f x)]
            exteriorPower.ιMulti (Y.presheaf.stalk (f x)) n v)) := by
  obtain ⟨U, hxU, a, ha⟩ :=
    modulePresheafStalk_exists_fin Y M.val (f x) n v
  have hv : v = fun i ↦ M.presheaf.germ U (f x) hxU (a i) :=
    funext fun i ↦ (ha i).symm
  subst v
  let w : Fin n → Γ(M, U) := a
  have hstalk :
      (moduleExteriorPowerStalkEquiv Y M (f x) n).symm
          (exteriorPower.ιMulti (Y.presheaf.stalk (f x)) n
            (fun i ↦ M.presheaf.germ U (f x) hxU (w i))) =
        (moduleExteriorPower Y M n).presheaf.germ U (f x) hxU
          (moduleExteriorWedge Y M n U w) := by
    apply (moduleExteriorPowerStalkEquiv Y M (f x) n).injective
    rw [LinearEquiv.apply_symm_apply]
    exact (moduleExteriorPowerStalkEquiv_wedge_germ Y M (f x) n U hxU w).symm
  rw [hstalk]
  rw [modulePullbackStalkTensorMap_tmul_germ]
  rw [_root_.map_smul]
  rw [moduleStalkMap_germ]
  rw [moduleExteriorPullbackComparison_wedge]
  rw [_root_.map_smul]
  rw [moduleExteriorPowerStalkEquiv_wedge_germ]
  rw [exteriorPowerBaseChangeMap_tmul_ιMulti]
  rw [_root_.map_smul, exteriorPower.map_apply_ιMulti]
  apply congrArg (fun w : Fin n → modulePullbackStalk f M x ↦
    s • exteriorPower.ιMulti (X.presheaf.stalk x) n w)
  funext i
  simp only [Function.comp_apply, modulePullbackStalkTensorMap_tmul_germ, one_smul]
  -- what remains is to rewrite `w i` back to `a i` (`w` is `let w := a`).
  rfl

end AlgebraicGeometry.Scheme.Modules
