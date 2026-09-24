import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.QuasicoherentAffineLocal
import MiyaokaMori.AlgebraicGeometry.Cohomology.Pushforward.Stacks01xk
import MiyaokaMori.AlgebraicGeometry.Cohomology.Coherent.Stacks02o5
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.Stacks01pb
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.CoherentSheaf
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafCohomologyModule
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.Stacks01yi
import MiyaokaMori.AlgebraicGeometry.Cohomology.Coherent.SheafCohomologyFiniteTwoOutOfThree
import MiyaokaMori.AlgebraicGeometry.Cohomology.Coherent.ProperOverNoetherianDevissageGenerator

/-! # Finiteness of coherent cohomology for proper schemes over a Noetherian ring (Stacks 02O6)

Cohomology of coherent sheaves on a scheme proper over a Noetherian affine scheme is finite
(Stacks 02O6): `A` Noetherian, `f : X → Spec A` proper, `F` coherent ⇒ every `H^i(X, F)` is a finite
`A`-module.

Source: Stacks 02O6.

The proof follows the dévissage structure of the original proof of Stacks 02O5: `X` is Noetherian
(Mathlib) → dévissage of coherent sheaves, Stacks 01YI → two-out-of-three
(`SheafCohomologyFiniteTwoOutOfThree.lean`) → generators (`ProperOverNoetherianDevissageGenerator.lean`,
the Chow's-lemma step).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- **Stacks 02O6** (coherent-lemma-proper-over-affine-cohomology-finite): `A` a Noetherian ring,
`f : X → Spec A` proper, `M` coherent ⇒ every `H^i(X, M)` is a finite `A`-module. The `A`-module
structure is `sheafCohomology.moduleOver` after `letI : X.Over (Spec A) := ⟨f⟩` (restriction of scalars
along `A ≅ Γ(Spec A, ⊤) → Γ(X, ⊤)`).

This is the lemma that rules out the infinite-dimensional fallback of `finrank` in the Euler
characteristic (via `sheafCohomology_finiteDimensional_of_isProperOver` with `A = k` a field), and it
is used for the local constancy of `χ` in flat proper families, where `A` is a general Noetherian ring.

**Proof (Stacks 02O6 = the affine case of 02O5; the original proof of 02O5 is the dévissage of
EGA III 3.2.1, done here directly on cohomology):**
0. `X` is Noetherian: `f` locally of finite type and `Spec A` locally Noetherian ⇒ `X` locally Noetherian
   (Mathlib `LocallyOfFiniteType.isLocallyNoetherian`); `f` quasi-compact (proper ⇒ universally closed ⇒
   quasi-compact) and `Spec A` quasi-compact ⇒ `X` quasi-compact
   (`QuasiCompact.compactSpace_of_compactSpace`).
1. Apply the dévissage of Stacks 01YI (`Scheme.Modules.coherent_devissage`) to the property
   `P(F) :⟺ ∀ i, H^i(X, F)` is a finite `A`-module. Three things are to be checked:
   (0) zero objects satisfy `P`: the cohomology of a zero module is a singleton
       (`sheafCohomology.finite_of_isZero`);
   (1) in a short exact sequence `0 → F₁ → F₂ → F₃ → 0` of coherent modules, if two terms satisfy `P`
       so does the third: by the `A`-linear long exact sequence
       `H^{i−1}(F₃) → H^i(F₁) → H^i(F₂) → H^i(F₃) → H^{i+1}(F₁)` and "over a Noetherian ring, the middle
       term of an exact sequence `N₁ → N₂ → N₃` with `N₁`, `N₃` finite is finite" (for `i = 0`,
       `H^0(F₁) → H^0(F₂)` is injective since `H^0 = Γ(−, ⊤)` and a mono of modules is injective on
       sections): `sheafCohomology.finite_X₃_of_finite_X₁_X₂` / `finite_X₂_of_finite_X₁_X₃` /
       `finite_X₁_of_finite_X₂_X₃`;
   (2) for every point `ξ` there is a coherent `G` with `Supp G = closure{ξ}`, `G_ξ` killed by `m_ξ`,
       `length G_ξ = 1` and `P(G)`: this is the Chow's-lemma step of the original proof of Stacks 02O5
       (`Z = closure{ξ}` with its reduced structure, Chow's lemma gives a projective `Z′ → Z` with a
       relatively ample `L`, and `G := i_*π_*L^{⊗n}` for `n ≫ 0`),
       `exists_coherent_generic_finite_sheafCohomology_of_isProper`.
2. By dévissage, `P(M)` holds; take the component `i`.

Edge cases: for `X` empty all `H^i = 0`, finite; for `i > dim X`, `H^i = 0` (02UZ); for `A` a field,
"finite module" means finite-dimensional (the case used for `χ`). -/
theorem AlgebraicGeometry.finite_sheafCohomology_of_isProper {A : CommRingCat.{u}} [IsNoetherianRing A]
    {X : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ AlgebraicGeometry.Spec A) [AlgebraicGeometry.IsProper f]
    (M : X.Modules) [M.IsCoherent] (i : ℕ) :
    letI : X.Over (AlgebraicGeometry.Spec A) := ⟨f⟩
    Module.Finite A (AlgebraicGeometry.sheafCohomology X M i) := by
  letI : X.Over (AlgebraicGeometry.Spec A) := ⟨f⟩
  have : AlgebraicGeometry.IsLocallyNoetherian X :=
    AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace f
  have : AlgebraicGeometry.IsNoetherian X := {}
  have key : ∀ j, Module.Finite A (AlgebraicGeometry.sheafCohomology X M j) :=
    AlgebraicGeometry.Scheme.Modules.coherent_devissage
      (fun F => ∀ j, Module.Finite A (AlgebraicGeometry.sheafCohomology X F j))
      (fun F hF j => AlgebraicGeometry.sheafCohomology.finite_of_isZero A F hF j)
      (fun S hS _ _ _ =>
        ⟨fun h₁ h₂ => AlgebraicGeometry.sheafCohomology.finite_X₃_of_finite_X₁_X₂ A hS h₁ h₂,
         fun h₁ h₃ => AlgebraicGeometry.sheafCohomology.finite_X₂_of_finite_X₁_X₃ A hS h₁ h₃,
         fun h₂ h₃ => AlgebraicGeometry.sheafCohomology.finite_X₁_of_finite_X₂_X₃ A hS h₂ h₃⟩)
      (fun ξ => AlgebraicGeometry.exists_coherent_generic_finite_sheafCohomology_of_isProper f ξ)
      M
  exact key i

end
