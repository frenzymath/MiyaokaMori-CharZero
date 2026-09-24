import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModuleSheafStalk
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModulesSupport
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.CoherentSheaf
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafCohomologyModule
import MiyaokaMori.AlgebraicGeometry.Varieties.Points.PointClosureSubscheme
import MiyaokaMori.AlgebraicGeometry.Varieties.Points.ReducedInducedSubschemeIntegral
import MiyaokaMori.AlgebraicGeometry.Varieties.Points.PointClosureTransport
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModulesSupportBasics
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.ModuleSupportGenericPoints
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.Stacks01y6
import MiyaokaMori.AlgebraicGeometry.Cohomology.Pushforward.SheafCohomologyClosedImmersionFiniteOver
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.SupportPushforwardClosedImmersion
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.PushforwardClosedImmersionGenericStalk
import MiyaokaMori.AlgebraicGeometry.Cohomology.Coherent.IntegralProperGeneratorSheaf

/-! # The dévissage generator for proper morphisms over a Noetherian ring

The dévissage generator of Stacks 02O5 / 02O6 (proof of 02O5, condition (2) of the dévissage
Lemma 01YI), stated for cohomology over an affine Noetherian base: for `f : X → Spec A` proper, `A`
Noetherian, and every point `ξ ∈ X`, there is a coherent `G` on `X` with support `closure {ξ}`, stalk
`G_ξ ≅ κ(ξ)` (killed by `m_ξ`, length 1) and all `H^i(X, G)` finite `A`-modules.

Source: Stacks 02O5 (coherent-lemma-proper-pushforward-coherent), proof, second paragraph
(the Chow's lemma step); EGA III 3.2.1. This is the hard core of Stacks 02O6; the rest of 02O6 is the
dévissage 01YI + the two-out-of-three lemma (`SheafCohomologyFiniteTwoOutOfThree.lean`).

The proof is assembled from
* `exists_coherent_generic_finite_sheafCohomology_of_isProper_isIntegral` (the Chow's-lemma step on the
  integral scheme `Z = closure {ξ}`);
* `pushforward_stalk_genericPoint_of_isClosedImmersion` (`m_ξ`-annihilation and length `1` of
  `(i_* G')_ξ`);
* `support_pushforward_of_isClosedImmersion`;
* `finite_sheafCohomology_pushforward_of_isClosedImmersion` (Stacks 02UV);
* Stacks 01Y6 (coherence of the pushforward along a finite morphism), `isClosed_support_of_isCoherent`
  (Stacks 01B4), and the integrality of the reduced induced subscheme.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- **The dévissage generator** (Stacks 02O5, proof, step (2) of the dévissage; EGA III 3.2.1). `A` Noetherian, `f : X → Spec A` proper, `ξ : X`. Then there is a coherent
`G : X.Modules` with `Supp G = closure {ξ}`, `m_ξ · G_ξ = 0`, `length_{O_{X,ξ}} G_ξ = 1`, and
`H^i(X, G)` a finite `A`-module for every `i` (A-module structure via `letI : X.Over (Spec A) := ⟨f⟩`
and `sheafCohomology.moduleOver`). This is exactly hypothesis `hgen` of
`AlgebraicGeometry.Scheme.Modules.coherent_devissage` (Stacks 01YI) for
`P F := ∀ i, Module.Finite A (H^i(X, F))`, and it is used only there (Stacks 02O6).

**Proof (Stacks 02O5, second paragraph of the proof).** `X` is locally Noetherian
(`LocallyOfFiniteType.isLocallyNoetherian f`).
1. *The integral closed subscheme.* `Z := X.pointClosure ξ` is `closure {ξ}` with its reduced induced
   structure (Mathlib `IdealSheafData.vanishingIdeal`, `subscheme`), `i := X.pointClosureι ξ : Z → X` is
   a closed immersion (`IsClosedImmersion.instSubschemeι`), `Z` is integral
   (`Scheme.isIntegral_pointClosure`) with generic point `η` and `i η = ξ` (`pointClosureι_genericPoint`).
   `g := i ≫ f : Z → Spec A` is proper (closed immersions are finite, hence proper; compositions).
2. *The generator on `Z`* (`exists_coherent_generic_finite_sheafCohomology_of_isProper_isIntegral`,
   Stacks 02O5's Chow's-lemma step:
   `Z' → Z` projective birational, `L` relatively ample, `G' := π_* L^{⊗n}` for `n ≫ 0`, degenerate Leray,
   projective case 02O4): a coherent `G' : Z.Modules` with `length_{O_{Z,η}} G'_η = 1` and all
   `H^i(Z, G')` finite over `A` (`A` acting through `⟨i ≫ f⟩`).
3. *`G := i_* G'`.*
   * Coherent: Stacks 01Y6 (`isCoherent_pushforward_of_isFinite`; a closed immersion is finite, Mathlib
     `IsClosedImmersion.iff_isFinite_and_mono`).
   * Support: `Supp G = i(Supp G')` (Stacks 00AE, `support_pushforward_of_isClosedImmersion`), and
     `Supp G' = Z`: it is closed (Stacks 01B4, `isClosed_support_of_isCoherent`) and contains the generic
     point `η` (`G'_η ≠ 0` because a module of length `1` is simple, hence nontrivial), so it contains
     `closure {η} = Z`. Finally `i(Z) = closure {i η} = closure {ξ}` (`range_eq_closure_of_isClosedImmersion`).
   * Stalk: `pushforward_stalk_genericPoint_of_isClosedImmersion` at `i η`, rewritten with `i η = ξ`:
     `(i_* G')_ξ ≅ G'_η` `O_{X,ξ}`-linearly through the surjective local map `O_{X,ξ} → O_{Z,η} = κ(η)`,
     so `m_ξ` acts by `0` and the length over `O_{X,ξ}` is the length over `O_{Z,η}`, i.e. `1`.
   * Cohomology: `H^i(X, i_* G') ≃ₗ[A] H^i(Z, G')` (Stacks 02UV made `A`-linear,
     `finite_sheafCohomology_pushforward_of_isClosedImmersion`; `i` is a morphism over `Spec A` by
     construction of the `Over` structures), hence finite over `A`.

**Edge cases.** `X = ∅`: no `ξ`, vacuous. `A` a field: `Spec A` a point, fine. `ξ` a closed point:
`Z = {ξ}` (`Spec` of a field finite over `A`), Chow's lemma is trivial (`Z' = Z`, `N = 0`),
`G = i_* O_Z` works directly. `A` the zero ring: `Spec A = ∅`, so `X = ∅`, vacuous.

**Why this form.** The Stacks proof of 02O5 proves `R^p f_* F` coherent for all `p`; over the affine
base `Spec A` and by 01XK, `R^p f_* F` coherent is equivalent to `H^p(X, F)` finite over `A`, so the
dévissage property `P` is taken to be `∀ i, Module.Finite A (H^i(X, F))` and the generator statement
is the `H^p`-version of Stacks' `R^p g_* G` computation. The signature was written to match
`coherent_devissage`'s `hgen` verbatim; the mathematics is Stacks 02O5. -/
theorem AlgebraicGeometry.exists_coherent_generic_finite_sheafCohomology_of_isProper
    {A : CommRingCat.{u}} [IsNoetherianRing A]
    {X : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ AlgebraicGeometry.Spec A) [AlgebraicGeometry.IsProper f]
    (ξ : X) :
    letI : X.Over (AlgebraicGeometry.Spec A) := ⟨f⟩
    ∃ G : X.Modules, G.IsCoherent ∧ G.support = closure {ξ} ∧
      IsLocalRing.maximalIdeal (X.presheaf.stalk ξ) ≤
        Module.annihilator (X.presheaf.stalk ξ) (G.stalk ξ) ∧
      Module.length (X.presheaf.stalk ξ) (G.stalk ξ) = 1 ∧
      ∀ i : ℕ, Module.Finite A (AlgebraicGeometry.sheafCohomology X G i) := by
  letI : X.Over (AlgebraicGeometry.Spec A) := ⟨f⟩
  have : AlgebraicGeometry.IsLocallyNoetherian X :=
    AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian f
  have : AlgebraicGeometry.IsClosedImmersion (X.pointClosureι ξ) := by
    unfold AlgebraicGeometry.Scheme.pointClosureι
    exact AlgebraicGeometry.IsClosedImmersion.instSubschemeι _
  have : AlgebraicGeometry.IsIntegral (X.pointClosure ξ) :=
    AlgebraicGeometry.Scheme.isIntegral_pointClosure ξ
  letI : (X.pointClosure ξ).Over (AlgebraicGeometry.Spec A) := ⟨X.pointClosureι ξ ≫ f⟩
  have : (X.pointClosureι ξ).IsOver (AlgebraicGeometry.Spec A) := ⟨rfl⟩
  obtain ⟨G', hcoh, hlen, hfin⟩ :=
    AlgebraicGeometry.exists_coherent_generic_finite_sheafCohomology_of_isProper_isIntegral
      (X.pointClosureι ξ ≫ f)
  have := hcoh
  have hη : genericPoint (X.pointClosure ξ) ∈ G'.support := by
    rw [AlgebraicGeometry.Scheme.Modules.mem_support_iff]
    have : IsSimpleModule ((X.pointClosure ξ).presheaf.stalk (genericPoint (X.pointClosure ξ)))
        (G'.stalk (genericPoint (X.pointClosure ξ))) :=
      Module.length_eq_one_iff.mp hlen
    exact IsSimpleModule.nontrivial ((X.pointClosure ξ).presheaf.stalk (genericPoint (X.pointClosure ξ)))
      (G'.stalk (genericPoint (X.pointClosure ξ)))
  have hsupp : G'.support = Set.univ := by
    apply Set.eq_univ_of_univ_subset
    have h1 : closure ({genericPoint (X.pointClosure ξ)} : Set (X.pointClosure ξ)) = Set.univ :=
      (genericPoint_spec _).def
    rw [← h1]
    exact (AlgebraicGeometry.Scheme.Modules.isClosed_support_of_isCoherent G').closure_subset_iff.mpr
      (Set.singleton_subset_iff.mpr hη)
  have hstalk := AlgebraicGeometry.Scheme.Modules.pushforward_stalk_genericPoint_of_isClosedImmersion
    (X.pointClosureι ξ) G' hlen
  rw [AlgebraicGeometry.Scheme.pointClosureι_genericPoint] at hstalk
  refine ⟨(AlgebraicGeometry.Scheme.Modules.pushforward (X.pointClosureι ξ)).obj G', ?_, ?_,
    hstalk.1, hstalk.2, ?_⟩
  · exact AlgebraicGeometry.Scheme.Modules.isCoherent_pushforward_of_isFinite (X.pointClosureι ξ) G'
  · rw [AlgebraicGeometry.Scheme.Modules.support_pushforward_of_isClosedImmersion, hsupp,
      Set.image_univ, MiyaokaMori.PointClosureTransport.range_eq_closure_of_isClosedImmersion,
      AlgebraicGeometry.Scheme.pointClosureι_genericPoint]
  · intro j
    have := hfin j
    exact AlgebraicGeometry.Scheme.Modules.finite_sheafCohomology_pushforward_of_isClosedImmersion
      (K := A) (X.pointClosureι ξ) G' j

end
