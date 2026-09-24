import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleStalkFree
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModuleSheafStalkStmt
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.IsLineBundleZpow

/-! # Powers of a line bundle are flat over the base

If `f : Y ⟶ X` is flat and `L` is a line bundle on `Y`, then every power `L ^ p` (`p : ℤ`)
is flat over `X`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- If `f` is flat and `L` is a line bundle, then `L ^ p` is flat over `X` along `f`:
the stalk `(L^p)_y` is a free `O_{Y,y}`-module and `O_{X,f y} → O_{Y,y}` is flat, so
transitivity of flatness applies. -/
theorem twistPow_isFlatOver {Y X : AlgebraicGeometry.Scheme.{u}} (f : Y ⟶ X)
    [AlgebraicGeometry.Flat f] (L : Y.Modules) [L.IsLineBundle] (p : ℤ) :
    AlgebraicGeometry.Scheme.Modules.ModuleRelativeFlatness.FlatOver f (L ^ p) := by
  -- `FlatOver` is defined stalkwise: for each `y`, the stalk `(L^p)_y`, viewed over `O_{X, f y}`
  -- via `f.stalkMap y`, is flat.
  intro y
  -- the tower `O_{X, f y} → O_{Y, y} → (L^p)_y`
  let _ : Algebra (X.presheaf.stalk (f.base y)) (Y.presheaf.stalk y) :=
    (AlgebraicGeometry.Scheme.Hom.stalkMap f y).hom.toAlgebra
  let _ : Module (X.presheaf.stalk (f.base y)) ((L ^ p).presheaf.stalk y) :=
    AlgebraicGeometry.Scheme.Modules.ModuleRelativeFlatness.relativeStalkModule f (L ^ p) y
  -- `f` flat ⇒ the stalk maps are flat (`AlgebraicGeometry.Flat.stalkMap`)
  have : Module.Flat (X.presheaf.stalk (f.base y)) (Y.presheaf.stalk y) :=
    AlgebraicGeometry.Flat.stalkMap f y
  -- `L^p` is again a line bundle, and the stalk of a line bundle is a free `O_{Y,y}`-module
  have : Module.Free (Y.presheaf.stalk y) ((L ^ p).presheaf.stalk y) :=
    AlgebraicGeometry.Scheme.Modules.free_stalk_of_isLineBundle (L ^ p) y
  have : IsScalarTower (X.presheaf.stalk (f.base y)) (Y.presheaf.stalk y)
      ((L ^ p).presheaf.stalk y) := ⟨fun a b c => mul_smul _ _ _⟩
  -- free ⇒ flat; flatness is transitive along the tower (`Module.Flat.trans`)
  exact Module.Flat.trans (X.presheaf.stalk (f.base y)) (Y.presheaf.stalk y)
    ((L ^ p).presheaf.stalk y)

end
