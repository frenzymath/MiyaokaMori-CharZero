import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierDivisor
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierDivisorLocalData
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.VarietyLineBundle
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.QuotientSheafAsCokernel
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.QuotientSheafLocal
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.QuotientSheafStalk
import MiyaokaMori.AlgebraicGeometry.Divisors.Meromorphic.RationalFunctionsSheaf
import MiyaokaMori.AlgebraicGeometry.Divisors.Meromorphic.RationalFunctionsSheafSheafify
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.SheafOfUnits
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundle
import MiyaokaMori.AlgebraicGeometry.Divisors.LineBundle.DivisorLineBundleSections
import MiyaokaMori.AlgebraicGeometry.Divisors.LineBundle.DivisorLineBundleFrame
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.RankAtStalkOfIsLineBundle

/-! # The line bundle of a Cartier divisor

The line bundle `O_X(D)` associated with a Cartier divisor `D`, packaged as a `LineBundle`. The data
(`lineBundleSections`, `lineBundleRestrict`, `lineBundlePresheaf`, `lineBundleModules`) are in
`DivisorLineBundleSections`; the three propositional fields follow from Hartshorne II.6.13 (the inverse
`t^{-1}` of a local equation `t` is a frame of `O_X(D)` on `U`, so `O_X(D)` is a line bundle;
`DivisorLineBundleFrame`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- `O_X(D)` is locally free. -/
theorem CartierDivisor.lineBundleModules_isLocallyFree {k : Type u} [Field k] {X : Variety k}
    (D : CartierDivisor X) : (CartierDivisor.lineBundleModules D).IsLocallyFree :=
  inferInstance

/-- `O_X(D)` is of finite type. -/
theorem CartierDivisor.lineBundleModules_isFiniteType {k : Type u} [Field k] {X : Variety k}
    (D : CartierDivisor X) : (CartierDivisor.lineBundleModules D).IsFiniteType :=
  inferInstance

/-- `O_X(D)` has rank `1` at every point. -/
theorem CartierDivisor.lineBundleModules_rankAtStalk {k : Type u} [Field k] {X : Variety k}
    (D : CartierDivisor X) (x : X.carrier) :
    AlgebraicGeometry.Scheme.Modules.rankAtStalk (CartierDivisor.lineBundleModules D) x = 1 :=
  AlgebraicGeometry.Scheme.Modules.rankAtStalk_eq_one_of_isLineBundle _ x

/-- The line bundle `O_X(D)` of a Cartier divisor `D`, packaged as a `LineBundle`. -/
noncomputable def CartierDivisor.lineBundle {k : Type u} [Field k] {X : Variety k}
    (D : CartierDivisor X) : LineBundle X where
  toModules := CartierDivisor.lineBundleModules D
  rank := 1
  locallyFree := CartierDivisor.lineBundleModules_isLocallyFree D
  isFiniteType := CartierDivisor.lineBundleModules_isFiniteType D
  rankAtStalk_eq := CartierDivisor.lineBundleModules_rankAtStalk D
  rank_eq_one := rfl

end
