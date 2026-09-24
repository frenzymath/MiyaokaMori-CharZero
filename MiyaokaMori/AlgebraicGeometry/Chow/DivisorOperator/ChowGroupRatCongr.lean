import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.RationalEquivalence.ChowGroupRational

/-! # Transport of the dimension index of the rational Chow group

Transport of the dimension index of the Chow group with ℚ-coefficients: for `p = q`, the map
`CH_p(X)_ℚ → CH_q(X)_ℚ` is the identity transported along `h` (ℚ-linear). Used in `capProd` and
`capPow_add_smul` for indices such as `d + card ι` versus `d + (toList.map D).length`, or `d + n`
versus `(d + (n − s)) + s`, which are propositionally but not definitionally equal. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Transport of the dimension index of the rational Chow group: `h : p = q` gives
`CH_p(X)_ℚ → CH_q(X)_ℚ` (the identity transported along `h`). -/

noncomputable def AlgebraicGeometry.ChowGroupRat.congr (X : AlgebraicGeometry.Scheme.{u}) {p q : ℕ}
    (h : p = q) :
    AlgebraicGeometry.ChowGroupRat X p →ₗ[ℚ] AlgebraicGeometry.ChowGroupRat X q := by
  subst h
  exact LinearMap.id

end
