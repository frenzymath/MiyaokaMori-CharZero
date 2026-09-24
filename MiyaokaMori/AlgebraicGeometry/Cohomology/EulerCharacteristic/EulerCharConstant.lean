import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedQcAlgebraPullback
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.CoherentSheaf
import MiyaokaMori.AlgebraicGeometry.Cohomology.EulerCharacteristic.EulerCharacteristic
import MiyaokaMori.AlgebraicGeometry.Cohomology.EulerCharacteristic.EulerCharLocallyConstant
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProjectiveMorphism
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModuleSheafStalkStmt
import MiyaokaMori.AlgebraicGeometry.Morphisms.Stacks01wc

/-! # Constancy of the Euler characteristic in a flat projective family

The Euler characteristic is constant in a flat projective family: if the base is locally Noetherian and
connected, `f` projective, and `M` coherent and flat over the base, then `χ_{κ(t)}(Y_t, M|_{Y_t})` does not
depend on `t` (the paper cites Hartshorne III.12.8; proved here along the Grothendieck complex route of
Hartshorne III.12.2 / Stacks 07VK–07VL).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem eulerCharacteristic_constant_in_flat_family
    {Y T : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsLocallyNoetherian T]
    [ConnectedSpace T]
    (f : Y ⟶ T) [AlgebraicGeometry.IsProjectiveMorphism f]
    (M : Y.Modules) [M.IsCoherent]
    (hM : AlgebraicGeometry.Scheme.Modules.ModuleRelativeFlatness.FlatOver f M) (t₁ t₂ : T) :
    -- the fibre as a `κ(t)`-scheme: Mathlib's `fiberOverSpecResidueField` is a `@[reducible] def`, not an
    -- instance, hence the explicit `letI`
    letI := f.fiberOverSpecResidueField t₁
    letI := f.fiberOverSpecResidueField t₂
    AlgebraicGeometry.sheafEulerCharacteristic (k := T.residueField t₁) (f.fiber t₁)
        ((AlgebraicGeometry.Scheme.Modules.pullback (f.fiberι t₁)).obj M)
      = AlgebraicGeometry.sheafEulerCharacteristic (k := T.residueField t₂) (f.fiber t₂)
        ((AlgebraicGeometry.Scheme.Modules.pullback (f.fiberι t₂)).obj M) := by
  -- `f` projective ⇒ proper (01WC); `χ` is locally constant; the base is connected ⇒ constant
  have : AlgebraicGeometry.IsProper f := AlgebraicGeometry.IsProjectiveMorphism.isProper f
  exact (eulerCharacteristic_isLocallyConstant_in_flat_family f M hM).apply_eq_of_preconnectedSpace
    t₁ t₂

end
