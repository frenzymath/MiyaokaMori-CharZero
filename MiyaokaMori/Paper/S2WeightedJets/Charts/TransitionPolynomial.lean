import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModulesSupport

/-! # The transition polynomials

The transition polynomial `P_{αα',q}` of eq. (2.7) of the paper: its coefficients are
regular on the overlap, each of its monomials has weight exactly `q` and ordinary degree `≥ 2`, and
it involves only the coordinates of order `< q`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- `P` is a jet transition polynomial of order `q`: every monomial has weight `q` (the variable
`x_{i,q'}` having weight `q' + 1`), ordinary degree `≥ 2`, and only involves variables of order
`< q`. -/
structure IsJetTransitionPolynomial {R : Type*} [CommRing R] (n k q : ℕ)
    (P : MvPolynomial (Fin (n + 1) × Fin k) R) : Prop where
  weighted_homogeneous :
    MvPolynomial.IsWeightedHomogeneous (fun iq : Fin (n + 1) × Fin k => ((iq.2 : ℕ) + 1)) P q
  degree_ge_two : ∀ m ∈ P.support, 2 ≤ m.sum (fun _ e => e)
  lower_order : ∀ m ∈ P.support, ∀ iq ∈ m.support, ((iq.2 : ℕ) + 1) < q

end
