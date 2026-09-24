import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafCohomologyModule

/-! # Definition of the Euler characteristic

The definition of the Euler characteristic `χ(X, M) = Σᶠ (−1)^i dim_k H^i(X, M)`.

Why a separate module: `EulerCharacteristic.lean` proves finiteness/vanishing of cohomology and therefore
imports `Stacks02o6`; the cohomology infrastructure (`SheafCohomologyLinearMap`, `SheafCohomologyZeroEquiv`,
`SheafCohomologyLinearLongExact`, `SheafCohomologyFiniteTwoOutOfThree`) only needs the *definition* of `χ`,
and the proofs of 02O5/02O6 need that infrastructure — importing `χ` from `EulerCharacteristic.lean` would
close an import cycle. This module imports nothing beyond `sheafCohomology`.
-/

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The Euler characteristic of a coherent sheaf, `χ(X, M) := Σᶠ_i (−1)^i · dim_k H^i(X, M)`
(Hartshorne III Ex. 5.1; Stacks 08A9).

**The domain is wider than in the literature, through two `0` fallbacks**: `Module.finrank` is `0` in
infinite dimension and `finsum` is `0` on infinite support, so the expression has a value for every
`X.Over (Spec k)` and every `M : X.Modules` (a convention of the same kind as `x / 0 = 0`). When `X` is
proper over `k` and `M` coherent, neither fallback is triggered (`sheafCohomology_finite_and_vanishing`),
and `χ` is the `χ` of the literature.

**Discipline**: every lemma **assigning a value to `χ`** (additivity 08AA, Snapper polynomials 0BEM/0BEN,
zero-dimensional degrees, Riemann–Roch, `χ(L^p) = P(p)` and the like) must
1. assume `hX : IsProperOver k X` and `[M.IsCoherent]`;
2. first rewrite the `finsum` into a finite sum over `Finset.range (X.dimension + 1)` via
   `sheafEulerCharacteristic_eq_sum`, then use `sheafCohomology_finiteDimensional_of_isProperOver` to treat
   `finrank` as the true dimension.
Lemmas that only say "`χ` is invariant under isomorphism" (`sheafEulerCharacteristic_eq_of_iso` etc.) hold
in both branches and are exempt. Deriving a nontrivial value from the fallback branch (infinite dimension ⇒
`finrank = 0`) is **not allowed**. -/
noncomputable def AlgebraicGeometry.sheafEulerCharacteristic {k : Type u} [Field k]
    (X : AlgebraicGeometry.Scheme.{u})
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (M : X.Modules) : ℤ :=
  ∑ᶠ i : ℕ, (-1 : ℤ) ^ i *
    (Module.finrank k (AlgebraicGeometry.sheafCohomology X M i) : ℤ)

end
