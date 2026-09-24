import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.ModulesMulBy
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafCohomologyModule
import MiyaokaMori.AlgebraicGeometry.Cohomology.EulerCharacteristic.EulerCharacteristic
import MiyaokaMori.AlgebraicGeometry.Cohomology.Pushforward.Stacks02uv
import MiyaokaMori.AlgebraicGeometry.Cohomology.Pushforward.SheafCohomologyClosedImmersionFiniteOver

/-! # Cohomology along a closed immersion, `K`-linearly: corollaries

Let `K` be a commutative ring, `i : Z → X` a closed immersion of `K`-schemes (a `K`-morphism) and `M` a
module on `Z`. Then for every `p`, `H^p(Z, M)` and `H^p(X, i_*M)` are `K`-linearly isomorphic; hence for
`K` a field the `h^p` agree, the Euler characteristics agree, and one side vanishes iff the other does.

Proof sketch:
1. `i_*` is exact on abelian sheaves (stalks of a closed immersion: `(i_*F)_x = F_x` for `x ∈ Z`, `0` for
   `x ∉ Z`; the proof of Stacks 02UV) and preserves injectives (`i_*` has the exact left adjoint `i^{-1}`),
   so it sends an injective resolution of `M` to one of `i_*M`; taking global sections
   `Γ(X, i_*I^•) = Γ(Z, I^•)` gives the additive isomorphism `H^p(Z, M) ≅ H^p(X, i_*M)` (Stacks 02UV).
2. `K`-linearity: `c ∈ K` acts on `H^p(Z, M)` through the endomorphism `μ_{c_Z}` of `M` by functoriality,
   where `c_Z` is the image of `c` in `Γ(Z, O_Z)`; on `H^p(X, i_*M)` it acts through `μ_{c_X}`. Since `i`
   is a `K`-morphism, `i^♯(c_X) = c_Z`, and the `O_X`-action on `i_*M` is given via `i^♯`, so
   `i_*(μ_{c_Z}) = μ_{c_X}` (checked on each open). The isomorphism of step 1 is natural in endomorphisms of
   `M`, hence commutes with the action of `c`.

Source: Stacks 02UV (the additive isomorphism).

The `K`-linear isomorphism `sheafCohomologyClosedImmersionLinearEquiv` (and `appTop_structureMap`) is
constructed in `SheafCohomologyClosedImmersionFiniteOver.lean` (namespace `AlgebraicGeometry`); this
module imports it and provides the corollaries (`Nonempty` form, `finrank_eq`, `subsingleton_iff`, Euler
characteristic).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry

theorem sheafCohomology_closedImmersion_linearEquiv {K : Type u} [CommRing K]
    {Z X : Scheme.{u}} [Z.Over (Spec (CommRingCat.of K))] [X.Over (Spec (CommRingCat.of K))]
    (i : Z ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (CommRingCat.of K))]
    (M : Z.Modules) (p : ℕ) :
    Nonempty (sheafCohomology Z M p ≃ₗ[K]
      sheafCohomology X ((Scheme.Modules.pushforward i).obj M) p) :=
  ⟨sheafCohomologyClosedImmersionLinearEquiv i M p⟩

theorem sheafCohomology_closedImmersion_finrank_eq {K : Type u} [Field K]
    {Z X : Scheme.{u}} [Z.Over (Spec (CommRingCat.of K))] [X.Over (Spec (CommRingCat.of K))]
    (i : Z ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (CommRingCat.of K))]
    (M : Z.Modules) (p : ℕ) :
    Module.finrank K (sheafCohomology Z M p) =
      Module.finrank K (sheafCohomology X ((Scheme.Modules.pushforward i).obj M) p) :=
  (sheafCohomologyClosedImmersionLinearEquiv i M p).finrank_eq

theorem sheafCohomology_closedImmersion_subsingleton_iff {K : Type u} [CommRing K]
    {Z X : Scheme.{u}} [Z.Over (Spec (CommRingCat.of K))] [X.Over (Spec (CommRingCat.of K))]
    (i : Z ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (CommRingCat.of K))]
    (M : Z.Modules) (p : ℕ) :
    Subsingleton (sheafCohomology Z M p) ↔
      Subsingleton (sheafCohomology X ((Scheme.Modules.pushforward i).obj M) p) :=
  (sheafCohomologyClosedImmersionLinearEquiv (K := K) i M p).toEquiv.subsingleton_congr

theorem sheafEulerCharacteristic_closedImmersion {K : Type u} [Field K]
    {Z X : Scheme.{u}} [Z.Over (Spec (CommRingCat.of K))] [X.Over (Spec (CommRingCat.of K))]
    (i : Z ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (CommRingCat.of K))]
    (M : Z.Modules) :
    sheafEulerCharacteristic (k := K) Z M =
      sheafEulerCharacteristic (k := K) X ((Scheme.Modules.pushforward i).obj M) := by
  unfold sheafEulerCharacteristic
  exact finsum_congr fun p => by rw [sheafCohomology_closedImmersion_finrank_eq i M p]

end AlgebraicGeometry

end
