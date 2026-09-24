import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModuleSheafStalk
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.Paper.S2WeightedJets.Charts.TransitionPolynomial

/-! # Jet coordinates related by a jet transition

Two tuples of jet coordinates `a, a' ∈ K(C̃)` (`i ≤ n`, `1 ≤ q ≤ κ`) are related at a point `z` by a jet transition
if `a'_{i,q} = Σ_j (g_q)_{ij} a_{j,q} + P_{i,q}(a_{·,1},…,a_{·,q−1})`, where each `g_q` is an invertible matrix with
entries in `O_{C̃,z}` and `P_{i,q}` has coefficients in `O_{C̃,z}` with every monomial of weight exactly `q`
(`IsJetTransitionPolynomial`); the reverse direction (the inverse transition) has the same shape. This formalizes
the hypothesis "change of jet chart" of `weightedOrder_chart_independent` (§3 of the paper: "a change of chart
cannot decrease the minimum … reverse inequality").

The linear part `g` depends on the weight `q` (`g : Fin κ → Matrix …`, each `g q` invertible): the lemma producing a
`JetTransitionStep` (`affineJetCoord_jetTransitionRelated`) compares the coordinates of one affine jet in two
arbitrary *honest* charts (`HonestJetChart`), which differ by an arbitrary graded automorphism of `Γ(V)[x_{i,q}]`;
its weight-`(q+1)` linear part is a matrix `g_q` that may depend on `q` (e.g. `x'_{i,q} = λ_q x_{i,q}`), and with a
single `g` the statement would be false (`n = 0`, `κ = 2`, `b = (t, 1)`, `t` a uniformizer). The paper's
equation (2.7) (§2, `g` = the Jacobian of a coordinate change on `X`) is the special case of a
constant family; the consumer `weightedOrder_chart_independent` only uses that the coefficients of weight `q`
are regular at `z`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/- A one-way jet transition: `a'` is obtained from `a` by the jet transition formula
   `a'_{i,q} = Σ_j (g_q)_{ij} a_{j,q} + P_{i,q}(a)`, where the linear part `g_q` of each weight `q` and the
   coefficients of the transition polynomials `P` are regular at `z` (they take values in the stalk `O_{C̃,z}`),
   each `g_q` is invertible, and `P_{i,q}` is a transition polynomial of weight `q` (every monomial of weight exactly
   `q`, involving only coordinates of order `< q`; the index `q` runs over `Fin κ` starting from `0`, the weight
   being `q + 1`). -/

def JetTransitionStep {k : Type u} [Field k] {Ct : SmoothProjectiveCurve k} {n κ : ℕ}
    (a a' : Fin (n + 1) → Fin κ → Ct.toScheme.functionField) (z : Ct.toScheme) : Prop :=
  ∃ (g : Fin κ → Matrix (Fin (n + 1)) (Fin (n + 1)) (Ct.toScheme.presheaf.stalk z))
    (P : Fin (n + 1) → Fin κ → MvPolynomial (Fin (n + 1) × Fin κ) (Ct.toScheme.presheaf.stalk z)),
    (∀ q, IsUnit (g q)) ∧
    (∀ i (q : Fin κ), IsJetTransitionPolynomial n κ ((q : ℕ) + 1) (P i q)) ∧
    ∀ i (q : Fin κ), a' i q =
      (∑ j, algebraMap (Ct.toScheme.presheaf.stalk z) Ct.toScheme.functionField (g q i j) * a j q)
        + MvPolynomial.aeval (fun p : Fin (n + 1) × Fin κ => a p.1 p.2) (P i q)

/- Two tuples of jet coordinates are related at `z` by a jet transition and its inverse: both directions have the shape above. -/

def JetTransitionRelated {k : Type u} [Field k] {Ct : SmoothProjectiveCurve k} {n κ : ℕ}
    (a a' : Fin (n + 1) → Fin κ → Ct.toScheme.functionField) (z : Ct.toScheme) : Prop :=
  JetTransitionStep a a' z ∧ JetTransitionStep a' a z

end
