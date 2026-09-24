import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.VarietyLineBundle
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleOfModules

/-! # The trivial line bundle

The trivial line bundle `O_X` on a variety `X`: the underlying module is the structure sheaf
`SheafOfModules.unit X.ringCatSheaf` (a line bundle by `IsLineBundle.unit`), bundled with
`LineBundle.ofModules`; `LineBundle.trivial` is an alias for the same object.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/- The trivial line bundle `O_X` (underlying module the structure sheaf `SheafOfModules.unit`);
   `LineBundle.trivial` is an alias for the same object. -/

noncomputable def LineBundle.one {k : Type u} [Field k] (X : Variety k) : LineBundle X :=
  LineBundle.ofModules (SheafOfModules.unit X.toScheme.ringCatSheaf)

noncomputable abbrev LineBundle.trivial {k : Type u} [Field k] (X : Variety k) : LineBundle X :=
  LineBundle.one X

theorem LineBundle.one_toModules {k : Type u} [Field k] (X : Variety k) :
    (LineBundle.one X).toModules = SheafOfModules.unit X.toScheme.ringCatSheaf :=
  LineBundle.ofModules_toModules _

end
