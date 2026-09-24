import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Morphisms.ClosedSubschemeProperOver
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPullbackRank
import MiyaokaMori.AlgebraicGeometry.Cohomology.Pushforward.SheafCohomologyClosedImmersionLinear
import MiyaokaMori.AlgebraicGeometry.Cohomology.EulerCharacteristic.EulerCharArtinianTensor
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ProjectionFormulaClosedImmersion
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.CoherentSchemeTheoreticSupport
import MiyaokaMori.AlgebraicGeometry.Chow.Snapper.SnapperFullSupportStep
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModulesSupportBasics

/-! # Coherent sheaves with zero-dimensional support (Stacks 0AYT)

Coherent sheaves with zero-dimensional support (Stacks 0AYT): for a proper scheme `X` over a field and a
coherent sheaf `F` with `dim Supp F ≤ 0`, `χ(F ⊗ E) = n·χ(F)` for every locally free sheaf `E` of rank `n`
(in particular tensoring with an invertible sheaf does not change `χ`).

Source: Stacks 0AYT.

The proof follows Stacks 0AYT:
1. Scheme-theoretic support: `F ≅ i_* G` for the closed immersion `i : Z → X` of the scheme-theoretic
   support, `G` coherent, `Supp G = Z`.
2. `Z` is proper over `k` (`isProperOver_of_closedImmersion`), `dim Z ≤ dim Supp F ≤ 0`
   (`topologicalKrullDim_le_support_pushforward`), hence Artinian (Mathlib
   `IsLocallyArtinian.of_topologicalKrullDim_le_zero`, quasi-compact ⇒ `IsArtinianScheme`).
3. Projection formula for the closed immersion: `(i_* G) ⊗ E ≅ i_* (G ⊗ i^* E)`; `i^* E` is locally free of
   rank `n` (`isLocallyFree_pullback`).
4. Closed immersions preserve `χ` (`sheafEulerCharacteristic_closedImmersion`, Stacks 02UV, `k`-linear).
5. The Artinian case (`EulerCharArtinianTensor.lean`): `χ(Z, G ⊗ i^*E) = n χ(Z, G)` — via
   `i^*E ≅ O_Z^{⊕ n}`, `G ⊗ O_Z^{⊕ n} ≅ G^{⊕ n}`, `χ(G^{⊕ n}) = n χ(G)` (from Stacks 08AA), and a separate
   degenerate case for `n = 0` (`EulerCharArtinianRankZero.lean`).

The identity `χ(X, F) = dim_k H^0(X, F)` of Stacks 0AYT is not part of the Lean statement and is not used.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- **Stacks 0AYT.** `X` proper over `k`, `F` coherent with `dim Supp F ≤ 0`, `E` locally free of rank `n`
(`rankAtStalk E x = n` for all `x`). Then `χ(X, F ⊗ E) = n · χ(X, F)`. Route: see the module docstring. -/
theorem AlgebraicGeometry.sheafEulerCharacteristic_tensor_of_dim_support_le_zero {k : Type u} [Field k]
    (X : AlgebraicGeometry.Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (hX : IsProperOver k X)
    (F : X.Modules) [F.IsCoherent] (hF : topologicalKrullDim F.support ≤ 0)
    (E : X.Modules) [E.IsLocallyFree] (n : ℕ)
    (hE : ∀ x, AlgebraicGeometry.Scheme.Modules.rankAtStalk E x = n) :
    AlgebraicGeometry.sheafEulerCharacteristic (k := k) X (F.tensor E) =
      n * AlgebraicGeometry.sheafEulerCharacteristic (k := k) X F := by
  have hloc : AlgebraicGeometry.IsLocallyNoetherian X :=
    AlgebraicGeometry.isLocallyNoetherian_of_isProperOver X hX
  -- Step 1: scheme-theoretic support `F ≅ i_* G`.
  obtain ⟨I, G, hGcoh, hGsupp, ⟨eG⟩⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_pushforward_subschemeι_iso_of_isCoherent F
  let _ : I.subscheme.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨I.subschemeι ≫ (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  have : I.subschemeι.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) := ⟨rfl⟩
  -- Step 2: `Z` is a proper Artinian `k`-scheme.
  have hZ : IsProperOver k I.subscheme := isProperOver_of_closedImmersion hX I.subschemeι
  have hdimZ : topologicalKrullDim I.subscheme ≤ 0 := by
    refine le_trans
      (AlgebraicGeometry.Scheme.Modules.topologicalKrullDim_le_support_pushforward I.subschemeι G hGsupp) ?_
    rw [AlgebraicGeometry.Scheme.Modules.support_eq_of_iso eG]
    exact hF
  have : AlgebraicGeometry.IsLocallyNoetherian I.subscheme :=
    AlgebraicGeometry.isLocallyNoetherian_of_isProperOver I.subscheme hZ
  have : AlgebraicGeometry.IsLocallyArtinian I.subscheme :=
    AlgebraicGeometry.IsLocallyArtinian.of_topologicalKrullDim_le_zero hdimZ
  have : AlgebraicGeometry.IsProper (I.subscheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := hZ
  have : CompactSpace I.subscheme :=
    AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace
      (I.subscheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
  have : AlgebraicGeometry.IsArtinianScheme I.subscheme := ⟨⟩
  -- Step 3: the pulled-back bundle is locally free of rank `n`.
  obtain ⟨hE'free, hE'rank⟩ := AlgebraicGeometry.Scheme.Modules.isLocallyFree_pullback I.subschemeι E
  have := hE'free
  have hrank : ∀ z, AlgebraicGeometry.Scheme.Modules.rankAtStalk
      ((AlgebraicGeometry.Scheme.Modules.pullback I.subschemeι).obj E) z = n :=
    fun z => (hE'rank z).trans (hE _)
  obtain ⟨ePF⟩ :=
    AlgebraicGeometry.Scheme.Modules.nonempty_pushforward_tensor_pullback_iso_of_isClosedImmersion
      I.subschemeι G E
  -- Steps 4–5: transfer `χ` to `Z` and apply the Artinian case.
  calc AlgebraicGeometry.sheafEulerCharacteristic (k := k) X (F.tensor E)
      = AlgebraicGeometry.sheafEulerCharacteristic (k := k) X
          (((AlgebraicGeometry.Scheme.Modules.pushforward I.subschemeι).obj G).tensor E) :=
        AlgebraicGeometry.sheafEulerCharacteristic_eq_of_iso
          (AlgebraicGeometry.Scheme.Modules.tensorIsoLeft eG.symm E)
    _ = AlgebraicGeometry.sheafEulerCharacteristic (k := k) X
          ((AlgebraicGeometry.Scheme.Modules.pushforward I.subschemeι).obj
            (G.tensor ((AlgebraicGeometry.Scheme.Modules.pullback I.subschemeι).obj E))) :=
        AlgebraicGeometry.sheafEulerCharacteristic_eq_of_iso ePF.symm
    _ = AlgebraicGeometry.sheafEulerCharacteristic (k := k) I.subscheme
          (G.tensor ((AlgebraicGeometry.Scheme.Modules.pullback I.subschemeι).obj E)) :=
        (AlgebraicGeometry.sheafEulerCharacteristic_closedImmersion I.subschemeι _).symm
    _ = n * AlgebraicGeometry.sheafEulerCharacteristic (k := k) I.subscheme G :=
        AlgebraicGeometry.sheafEulerCharacteristic_tensor_of_isArtinianScheme I.subscheme hZ G _ n hrank
    _ = n * AlgebraicGeometry.sheafEulerCharacteristic (k := k) X
          ((AlgebraicGeometry.Scheme.Modules.pushforward I.subschemeι).obj G) := by
        rw [AlgebraicGeometry.sheafEulerCharacteristic_closedImmersion I.subschemeι G]
    _ = n * AlgebraicGeometry.sheafEulerCharacteristic (k := k) X F := by
        rw [AlgebraicGeometry.sheafEulerCharacteristic_eq_of_iso eG]

end
