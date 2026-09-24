import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.Pushforward.Stacks01xkMayerVietorisStep
import MiyaokaMori.AlgebraicGeometry.Cohomology.Pushforward.Stacks01xkDegreeZero

/-! # Affine base case of the Mayer–Vietoris induction for Stacks 01XJ/01XK

**Base case of the Mayer–Vietoris induction in Stacks 01XJ/01XK (condition (i) of 08DR):** for a
quasi-coherent `M` on `X`, `r ∈ Γ(X, O_X)` and an affine open `U`, the restriction maps
`H'^q(U, M) → H'^q(U ∩ D(r), M)` are localizations of `Γ(X, ⊤)`-modules at the powers of `r`, for
every `q` (`LocProp M (powers r) (X.basicOpen r) U`).

**Proof.** `U ∩ D(r) = X.basicOpen (r|_U)` (`Scheme.basicOpen_res`), which is an affine open
(`IsAffineOpen.basicOpen`).
* `q = 0`: degree-0 cohomology is sections and sections of a quasi-coherent module over an affine
  localize along a basic open — `Stacks01xkDegreeZero.lean`.
* `q ≥ 1`: both `H'^q(U, M)` and `H'^q(U ∩ D(r), M)` vanish (Serre vanishing on affine opens,
  Stacks 01XB, `subsingleton_E_of_isAffineOpen`), and a linear map between subsingleton modules is a
  localization (`IsLocalizedModule.of_subsingleton`).

Source: Stacks 01XJ proof paragraph 1 (affine case), 01XB. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

open CategoryTheory.Abelian CategoryTheory.Abelian.Ext

variable {X : AlgebraicGeometry.Scheme.{u}} (M : X.Modules)

attribute [local instance] smulEndAction ExtAction.module

/-- **Affine base case**: `LocProp` holds for every affine open. -/
theorem locProp_of_isAffineOpen [M.IsQuasicoherent] (r : Γ(X, ⊤)) {U : X.Opens}
    (hU : IsAffineOpen U) : LocProp M (Submonoid.powers r) (X.basicOpen r) U := by
  intro W' hle hW' q
  have hW'' : W' = X.basicOpen (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op r) := by
    rw [hW', AlgebraicGeometry.Scheme.basicOpen_res]
  cases q with
  | zero => exact isLocalizedModule_precompLinear_zero_of_isAffineOpen M r hU hW'' hle
  | succ p =>
    have h1 : Subsingleton (E M U (p + 1)) := subsingleton_E_of_isAffineOpen M hU (p + 1) p.succ_pos
    have h2 : Subsingleton (E M W' (p + 1)) :=
      subsingleton_E_of_isAffineOpen M (hW'' ▸ hU.basicOpen _) (p + 1) p.succ_pos
    exact IsLocalizedModule.of_subsingleton _ _

end AlgebraicGeometry.Scheme.Modules

end
