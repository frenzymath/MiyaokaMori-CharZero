import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.VarietyLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.RankAtStalkLocalIso
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundle
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModulesDual
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensor
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorPower
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.SheafOfModulesMonoidal
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.Stacks01ct
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleOfModules

/-! # Integer tensor powers of a bundled line bundle

Integer tensor powers `L^{⊗q}` of a line bundle (using the dual for `q < 0`), and `L^0 ≅ O_X`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The tensor power `moduleTensorPower L n` is an (unbundled) line bundle: for `n = 0` it is by definition
the structure sheaf (`AlgebraicGeometry.Scheme.Modules.IsLineBundle.unit`), for `n + 1` it is by definition
`moduleTensor L (moduleTensorPower L n) = Modules.tensor L (moduleTensorPower L n)`
(`SheafOfModules.IsLineBundle.tensor`). -/
instance AlgebraicGeometry.Scheme.Modules.moduleTensorPower_isLineBundle {X : AlgebraicGeometry.Scheme.{u}}
    (L : X.Modules) [L.IsLineBundle] (n : ℕ) : (AlgebraicGeometry.Scheme.Modules.moduleTensorPower L n).IsLineBundle := by
  induction n with
  | zero => exact inferInstanceAs (SheafOfModules.unit X.ringCatSheaf).IsLineBundle
  | succ n ih =>
      have := ih
      exact inferInstanceAs
        (AlgebraicGeometry.Scheme.Modules.tensor L (AlgebraicGeometry.Scheme.Modules.moduleTensorPower L n)).IsLineBundle

/-- The negative power `moduleNegativePower L n = moduleTensorPower (moduleSheafDual L) n` is a line bundle
(the dual is a line bundle, `SheafOfModules.IsLineBundle.dual`, then the tensor power above). -/
instance AlgebraicGeometry.Scheme.Modules.moduleNegativePower_isLineBundle {X : AlgebraicGeometry.Scheme.{u}}
    (L : X.Modules) [L.IsLineBundle] (n : ℕ) : (AlgebraicGeometry.Scheme.Modules.moduleNegativePower L n).IsLineBundle :=
  inferInstanceAs
    (AlgebraicGeometry.Scheme.Modules.moduleTensorPower (AlgebraicGeometry.Scheme.Modules.dual L) n).IsLineBundle

/- `L^{⊗q}`: for `q ≥ 0` use `moduleTensorPower L q` (the `0`-th power is by definition `O_X`), for `q < 0` use
   `moduleNegativePower L |q| = (L^∨)^{⊗|q|}` (`L^∨` is `moduleSheafDual`); in both cases these are unbundled
   line bundles (the two instances above), bundled with `LineBundle.ofModules` (`toModules` unchanged,
   `rank := 1`, local freeness and finite type from the line bundle instance, rank 1 at every stalk from
   `rankAtStalk_eq_one_of_isLineBundle`). -/

noncomputable def LineBundle.zpow {k : Type u} [Field k] {X : Variety k}
    (L : LineBundle X) : ℤ → LineBundle X
  | (n : ℕ) => LineBundle.ofModules (AlgebraicGeometry.Scheme.Modules.moduleTensorPower L.toModules n)
  | Int.negSucc n => LineBundle.ofModules (AlgebraicGeometry.Scheme.Modules.moduleNegativePower L.toModules (n + 1))

theorem LineBundle.zpow_zero {k : Type u} [Field k] {X : Variety k} (L : LineBundle X) :
    Nonempty ((L.zpow 0).toModules ≅ SheafOfModules.unit X.toScheme.ringCatSheaf) :=
  ⟨CategoryTheory.Iso.refl _⟩

end
