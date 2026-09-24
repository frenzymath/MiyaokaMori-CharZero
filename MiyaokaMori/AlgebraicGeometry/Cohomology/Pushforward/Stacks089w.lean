import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.Pushforward.PushforwardCohomologyLerayDegeneration
import MiyaokaMori.AlgebraicGeometry.Cohomology.Vanishing.Stacks01xb

/-! # Cohomology along an affine morphism (Stacks 089W)

Stacks 089W: `f : X → S` affine, `M` quasi-coherent ⇒ `H^i(X, M) ≅ H^i(S, f_*M)` for all `i` (from
`R^i f_*M = 0`, Stacks 01XC, and the degenerate Leray spectral sequence).

Source: Stacks 089W (coherent-lemma-relative-affine-cohomology), 01XC (coherent-lemma-relative-affine-
vanishing); Hartshorne III Ex. 8.2, Ex. 4.1.

## Proof
* For every affine open `V ⊆ S`, `f⁻¹V` is affine (definition of an affine morphism, Mathlib
  `IsAffineOpen.preimage`), so `H^q(f⁻¹V, M) = 0` for `q > 0` by Serre vanishing on affine opens
  (Stacks 01XB, `sheafCohomology'_affineOpen_vanishing`). This is the statement `R^q f_* M = 0` of
  Stacks 01XC in the form the next step consumes.
* Leray degeneration in affine-basis form (Stacks 01F4(1), proved by dimension shifting in
  `PushforwardCohomologyLerayDegeneration.lean`) then gives `H^i(X, M) ≃+ H^i(S, f_*M)` for every `i`.

The closed-immersion case is Stacks 02UV (Ext-adjunction route).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Stacks 089W: `f` affine, `M` quasi-coherent ⇒ `H^i(X, M) ≅ H^i(S, f_*M)` (from `R^i f_*M = 0`,
Stacks 01XC, and Leray). -/

theorem AlgebraicGeometry.sheafCohomology_pushforward_equiv_of_isAffineHom
    {X S : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ S) [AlgebraicGeometry.IsAffineHom f]
    (M : X.Modules) [M.IsQuasicoherent] (i : ℕ) :
    Nonempty (CategoryTheory.Sheaf.H M.toAddCommGrpSheaf i ≃+
      CategoryTheory.Sheaf.H ((AlgebraicGeometry.Scheme.Modules.pushforward f).obj M).toAddCommGrpSheaf i) :=
  AlgebraicGeometry.Scheme.Modules.sheafCohomology_pushforward_addEquiv_of_hPrime_vanishing f i M
    (fun V q hq => sheafCohomology'_affineOpen_vanishing M (V.2.preimage f) q hq)

end
