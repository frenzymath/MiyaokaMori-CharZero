import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.ModulesMulBy
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafCohomologyModule
import MiyaokaMori.AlgebraicGeometry.Cohomology.Pushforward.Stacks02uv

/-! # Cohomology along a closed immersion: `K`-linearity and `K`-finiteness

`K`-linearity and `K`-finiteness transfer for the cohomology isomorphism along a closed immersion
(Stacks 02UV), for schemes over `Spec K`.

For `i : Z → X` a closed immersion of `K`-schemes (`K` a commutative ring) and `M : Z.Modules`,
Stacks 02UV (`Stacks02uv.lean`) gives the concrete additive isomorphism
`sheafCohomologyClosedImmersionAddEquiv i M p : H^p(Z, M) ≃+ H^p(X, i_* M)` together with its
naturality in `M`. Here we record

* `sheafCohomologyClosedImmersionAddEquivOver` — the same isomorphism, typed with the module carriers
  `sheafCohomology Z M p`, `sheafCohomology X (i_* M) p` (this retyping is what keeps the kernel
  checks below cheap: building a `LinearEquiv` directly from the `Sheaf.H`-typed `AddEquiv` costs
  tens of seconds of kernel time);
* `sheafCohomologyClosedImmersionAddEquivOver_smul` — it is `K`-linear for the `K`-module structures
  `sheafCohomology.moduleOver` (scalars through `K ≅ Γ(Spec K, ⊤) → Γ(−, ⊤)`): by naturality applied
  to the endomorphism "multiply by the image of `c`" (`mulBy`), as in
  `sheafCohomologyClosedImmersionLinearEquiv`;
* `AlgebraicGeometry.sheafCohomologyClosedImmersionLinearEquiv` — the resulting `K`-linear
  isomorphism `H^p(Z, M) ≃ₗ[K] H^p(X, i_* M)`;
* `finite_sheafCohomology_pushforward_of_isClosedImmersion` — hence `Module.Finite K H^p(Z, M)` implies
  `Module.Finite K H^p(X, i_* M)`.

`SheafCohomologyClosedImmersionLinear.lean` (whose import closure contains `Stacks02o6` and therefore
cannot be used inside the proof of the dévissage generator) imports this module and derives the
`finrank` / `Subsingleton` / Euler-characteristic corollaries.

Source: Stacks 02UV (cohomology and closed immersions); Hartshorne III Lemma 2.10.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry

/-- A `K`-morphism `i : Z → X` sends the image of `c ∈ K` in `Γ(X, ⊤)` to its image in `Γ(Z, ⊤)`:
`i^♯(c_X) = c_Z`. -/
theorem appTop_structureMap {K : Type u} [CommRing K]
    {Z X : Scheme.{u}} [Z.Over (Spec (CommRingCat.of K))] [X.Over (Spec (CommRingCat.of K))]
    (i : Z ⟶ X) [i.IsOver (Spec (CommRingCat.of K))] (c : K) :
    (((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
        (Z ↘ Spec (CommRingCat.of K)).appTop).hom) c
      = i.appTop ((((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
        (X ↘ Spec (CommRingCat.of K)).appTop).hom) c) := by
  have key : (Z ↘ Spec (CommRingCat.of K)).appTop
      = (X ↘ Spec (CommRingCat.of K)).appTop ≫ i.appTop := by
    rw [← Scheme.Hom.comp_appTop, CategoryTheory.comp_over]
  rw [key]
  rfl

end AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

/-- The scalar action of `sheafCohomology.moduleOver` unfolded: `c • α = H.map (smulEnd c_X) α`. -/
theorem moduleOver_smul_eq_H_map {K : Type u} [CommRing K]
    (X : Scheme.{u}) [X.Over (Spec (CommRingCat.of K))] (M : X.Modules) (p : ℕ)
    (c : K) (α : sheafCohomology X M p) :
    c • α = CategoryTheory.Sheaf.H.map (M.smulEnd ((((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
      (X ↘ Spec (CommRingCat.of K)).appTop).hom) c)) p α := rfl

/-- The 02UV isomorphism `H^p(Z, M) ≃+ H^p(X, i_* M)`, typed with the module carriers. -/
def sheafCohomologyClosedImmersionAddEquivOver
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (M : Z.Modules) (p : ℕ) :
    sheafCohomology Z M p ≃+ sheafCohomology X ((Scheme.Modules.pushforward i).obj M) p :=
  sheafCohomologyClosedImmersionAddEquiv i M p

/-- Naturality of `sheafCohomologyClosedImmersionAddEquivOver` in `M` (restatement of
`sheafCohomologyClosedImmersionAddEquiv_naturality`). -/
theorem sheafCohomologyClosedImmersionAddEquivOver_naturality
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] {M N : Z.Modules} (f : M ⟶ N) (p : ℕ)
    (α : sheafCohomology Z M p) :
    sheafCohomologyClosedImmersionAddEquivOver i N p
        (CategoryTheory.Sheaf.H.map ((SheafOfModules.toSheaf Z.ringCatSheaf).map f) p α)
      = CategoryTheory.Sheaf.H.map
          ((SheafOfModules.toSheaf X.ringCatSheaf).map
            ((AlgebraicGeometry.Scheme.Modules.pushforward i).map f)) p
          (sheafCohomologyClosedImmersionAddEquivOver i M p α) :=
  sheafCohomologyClosedImmersionAddEquiv_naturality i f p α

/-- `K`-linearity of the 02UV isomorphism: naturality applied to `mulBy (i^♯ c_X) = mulBy c_Z`. -/
theorem sheafCohomologyClosedImmersionAddEquivOver_smul {K : Type u} [CommRing K]
    {Z X : Scheme.{u}} [Z.Over (Spec (CommRingCat.of K))] [X.Over (Spec (CommRingCat.of K))]
    (i : Z ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (CommRingCat.of K))]
    (M : Z.Modules) (p : ℕ) (c : K) (α : sheafCohomology Z M p) :
    sheafCohomologyClosedImmersionAddEquivOver i M p (c • α)
      = c • sheafCohomologyClosedImmersionAddEquivOver i M p α := by
  have h := sheafCohomologyClosedImmersionAddEquivOver_naturality
    i (M.mulBy (i.appTop ((((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
      (X ↘ Spec (CommRingCat.of K)).appTop).hom) c))) p α
  rw [pushforward_map_mulBy, toSheaf_map_mulBy, toSheaf_map_mulBy,
    ← appTop_structureMap (K := K) i c] at h
  rw [moduleOver_smul_eq_H_map, moduleOver_smul_eq_H_map]
  exact h

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

open AlgebraicGeometry.Scheme.Modules in
/-- **`K`-linear cohomology isomorphism along a closed immersion** (Stacks 02UV + `K`-linearity):
`H^p(Z, M) ≃ₗ[K] H^p(X, i_* M)`. The underlying additive equivalence is the concrete 02UV
isomorphism (`sheafCohomologyClosedImmersionAddEquivOver`), `K`-linearity is
`sheafCohomologyClosedImmersionAddEquivOver_smul` (naturality applied to `mulBy c`). -/
def sheafCohomologyClosedImmersionLinearEquiv {K : Type u} [CommRing K]
    {Z X : Scheme.{u}} [Z.Over (Spec (CommRingCat.of K))] [X.Over (Spec (CommRingCat.of K))]
    (i : Z ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (CommRingCat.of K))]
    (M : Z.Modules) (p : ℕ) :
    sheafCohomology Z M p ≃ₗ[K]
      sheafCohomology X ((Scheme.Modules.pushforward i).obj M) p :=
  { sheafCohomologyClosedImmersionAddEquivOver i M p with
    map_smul' := sheafCohomologyClosedImmersionAddEquivOver_smul i M p }

end AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

/-- `K`-finiteness of cohomology descends along a closed immersion of `K`-schemes:
`H^p(Z, M)` a finite `K`-module ⇒ `H^p(X, i_* M)` a finite `K`-module (Stacks 02UV). -/
theorem finite_sheafCohomology_pushforward_of_isClosedImmersion {K : Type u} [CommRing K]
    {Z X : Scheme.{u}} [Z.Over (Spec (CommRingCat.of K))] [X.Over (Spec (CommRingCat.of K))]
    (i : Z ⟶ X) [IsClosedImmersion i] [i.IsOver (Spec (CommRingCat.of K))]
    (M : Z.Modules) (p : ℕ) [Module.Finite K (sheafCohomology Z M p)] :
    Module.Finite K (sheafCohomology X ((Scheme.Modules.pushforward i).obj M) p) :=
  Module.Finite.equiv (sheafCohomologyClosedImmersionLinearEquiv i M p)

end AlgebraicGeometry.Scheme.Modules

end
