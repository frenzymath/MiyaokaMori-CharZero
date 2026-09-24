import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPullbackMonoidal
import MiyaokaMori.AlgebraicGeometry.Morphisms.ClosedSubschemeProperOver
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.RankAtStalkOfIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Cohomology.Pushforward.SheafCohomologyClosedImmersionLinear
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.Stacks02ol
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.Stacks02om
import MiyaokaMori.AlgebraicGeometry.Cohomology.EulerCharacteristic.Stacks0ayt
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.NowhereDenseDimensionDrop
import MiyaokaMori.AlgebraicGeometry.Chow.Snapper.SnapperFullSupportStep
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModulesSupportBasics
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.TwistByLineBundleList

/-! # The induction of Snapper's theorem

The induction of Snapper's theorem (Stacks 0BEM), run for an abstract family of
exponent line bundles: `X` proper over `k`, `F` coherent with `dim Supp F ≤ e`, `L₁, …, L_r` invertible,
`𝓜 i : ℤ → X.Modules` line bundles with `𝓜 i (n+1) ≅ 𝓜 i n ⊗ L i`; then `n ↦ χ(F ⊗ 𝓜₁(n₁) ⊗ ⋯ ⊗ 𝓜_r(n_r))`
is given by a polynomial in `ℚ[n₁, …, n_r]` of total degree `≤ e`. (0BEM is the case `𝓜 i n = L i ^ n`.)
The family `𝓜` is abstract so that the statement can be pulled back along a
closed immersion `i : Z → X` (`𝓜' i n := i^* (𝓜 i n)`, `i^*(A ⊗ B) ≅ i^*A ⊗ i^*B`) without identifying
`i^*(L^n)` with `(i^*L)^n`.

Proof: induction on `e`, for all `X, F` at once (the statement is universally quantified over the scheme
so that the induction hypothesis applies to the closed subscheme `Z`).

* `e = 0`: `dim Supp F ≤ 0`; `E := O_X ⊗ 𝓜₁(n₁) ⊗ ⋯` is a line bundle (rank 1 everywhere), so by Stacks 0AYT
  `χ(F ⊗ E) = χ(F)`; and `F ⊗ 𝓜₁(n₁) ⊗ ⋯ ≅ F ⊗ E`. The constant polynomial `χ(F)`
  has total degree `0`.
* `e → e + 1`: Stacks 02OL gives `0 → K → F → F' → 0` with `K` coherent, `Supp K`
  nowhere dense in `Supp F` (so `dim Supp K ≤ e`), `Supp F' = Supp F`,
  `F'` without embedded associated points. Twisting is exact and `χ` additive (08AA), so
  `χ(F ⊗ 𝓜(n)) = χ(K ⊗ 𝓜(n)) + χ(F' ⊗ 𝓜(n))`, and the first term is a polynomial of degree `≤ e` by
  induction. Stacks 02OM writes `F' ≅ i_* G` for the closed subscheme `i : Z → X` cut
  out by the annihilator, with `Z` without embedded points, `G` coherent without embedded associated points
  and `Supp G = Z`. `Z` is proper over `k` (closed immersions are proper), `dim Z ≤ dim Supp (i_* G)
  = dim Supp F ≤ e + 1`, and by the projection formula and Stacks 02UV
  `χ_X(F' ⊗ 𝓜(n)) = χ_X(i_*(G ⊗ i^*𝓜(n))) = χ_Z(G ⊗ i^*𝓜(n))`. The induction hypothesis on `Z` and
  the full-support step (`SnapperFullSupportStep.lean`) give a polynomial of total degree `≤ e + 1` for the latter.

Source: Stacks 0BEM.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry

/-- **Snapper's theorem for an abstract family of exponent line bundles**, by induction on the dimension
bound `e` (see the module docstring). -/
theorem exists_snapper_mvPolynomial_aux {k : Type u} [Field k] (e : ℕ) :
    ∀ (X : AlgebraicGeometry.Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))],
      IsProperOver k X →
    ∀ (F : X.Modules) [F.IsCoherent], topologicalKrullDim F.support ≤ (e : WithBot ℕ∞) →
    ∀ {r : ℕ} (L : Fin r → X.Modules) [∀ i, (L i).IsLineBundle]
      (𝓜 : Fin r → ℤ → X.Modules) [∀ i n, (𝓜 i n).IsLineBundle],
      (∀ i n, Nonempty (𝓜 i (n + 1) ≅ (𝓜 i n).tensor (L i))) →
      ∃ P : MvPolynomial (Fin r) ℚ, P.totalDegree ≤ e ∧ ∀ n : Fin r → ℤ,
        (AlgebraicGeometry.sheafEulerCharacteristic (k := k) X
            (Scheme.Modules.twistList (fun i => 𝓜 i (n i)) (List.finRange r) F) : ℚ)
          = MvPolynomial.eval (fun i => (n i : ℚ)) P := by
  induction e with
  | zero =>
    intro X _ hX F _ he r L _ 𝓜 _ h𝓜
    refine ⟨MvPolynomial.C (AlgebraicGeometry.sheafEulerCharacteristic (k := k) X F : ℚ),
      by rw [MvPolynomial.totalDegree_C], fun n => ?_⟩
    rw [MvPolynomial.eval_C]
    have he0 : topologicalKrullDim F.support ≤ 0 := by simpa using he
    have hE : (Scheme.Modules.twistList (fun i => 𝓜 i (n i)) (List.finRange r)
        (SheafOfModules.unit X.ringCatSheaf)).IsLineBundle :=
      Scheme.Modules.twistList_isLineBundle _ _ _
    have h0 := AlgebraicGeometry.sheafEulerCharacteristic_tensor_of_dim_support_le_zero X hX F he0
      (Scheme.Modules.twistList (fun i => 𝓜 i (n i)) (List.finRange r) (SheafOfModules.unit X.ringCatSheaf))
      1 (fun x => Scheme.Modules.rankAtStalk_eq_one_of_isLineBundle _ x)
    rw [AlgebraicGeometry.sheafEulerCharacteristic_eq_of_iso
      (Scheme.Modules.twistList_iso_tensor_unit (fun i => 𝓜 i (n i)) (List.finRange r) F), h0]
    push_cast
    ring
  | succ e ih =>
    intro X _ hX F _ he r L _ 𝓜 _ h𝓜
    have hloc : AlgebraicGeometry.IsLocallyNoetherian X := isLocallyNoetherian_of_isProperOver X hX
    have hnoeth : TopologicalSpace.NoetherianSpace X := noetherianSpace_of_isProperOver X hX
    -- Stacks 02OL: remove embedded points
    obtain ⟨K, ι, hι, hKcoh, hnd, hsupp', hnoemb⟩ := Scheme.Modules.exists_remove_embedded_points F
    have hF' : (CategoryTheory.Limits.cokernel ι).IsCoherent := Scheme.Modules.isCoherent_cokernel ι
    have hdimK : topologicalKrullDim K.support ≤ (e : WithBot ℕ∞) :=
      TopologicalSpace.topologicalKrullDim_le_of_isNowhereDense_preimage
        (Scheme.Modules.support_subset_of_mono ι) hnd he
    obtain ⟨PK, hPKdeg, hPK⟩ := ih X hX K hdimK L 𝓜 h𝓜
    have hadd : ∀ n : Fin r → ℤ,
        AlgebraicGeometry.sheafEulerCharacteristic (k := k) X
            (Scheme.Modules.twistList (fun i => 𝓜 i (n i)) (List.finRange r) F)
          = AlgebraicGeometry.sheafEulerCharacteristic (k := k) X
              (Scheme.Modules.twistList (fun i => 𝓜 i (n i)) (List.finRange r) K)
            + AlgebraicGeometry.sheafEulerCharacteristic (k := k) X
              (Scheme.Modules.twistList (fun i => 𝓜 i (n i)) (List.finRange r)
                (CategoryTheory.Limits.cokernel ι)) := fun n => by
      have : (CategoryTheory.ShortComplex.cokernelSequence ι).X₁.IsCoherent := hKcoh
      have : (CategoryTheory.ShortComplex.cokernelSequence ι).X₂.IsCoherent := ‹F.IsCoherent›
      have : (CategoryTheory.ShortComplex.cokernelSequence ι).X₃.IsCoherent := hF'
      have h := Scheme.Modules.sheafEulerCharacteristic_twistList_shortExact hX (fun i => 𝓜 i (n i))
        (List.finRange r) (CategoryTheory.ShortComplex.cokernelSequence ι)
        (Scheme.Modules.cokernelSequence_shortExact ι)
      simpa only [CategoryTheory.ShortComplex.cokernelSequence_X₁,
        CategoryTheory.ShortComplex.cokernelSequence_X₂,
        CategoryTheory.ShortComplex.cokernelSequence_X₃] using h
    -- Stacks 02OM: `F' ≅ i_* G` on the closed subscheme `Z`
    obtain ⟨I, G, hGcoh, hGnoemb, hGsupp, hZnoemb, ⟨eG⟩⟩ :=
      Scheme.Modules.eq_pushforward_of_noEmbeddedPoints (CategoryTheory.Limits.cokernel ι) hnoemb
    let _ : I.subscheme.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨I.subschemeι ≫ (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    have : I.subschemeι.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) := ⟨rfl⟩
    have hZ : IsProperOver k I.subscheme := isProperOver_of_closedImmersion hX I.subschemeι
    have hdimZ : topologicalKrullDim I.subscheme ≤ ((e + 1 : ℕ) : WithBot ℕ∞) := by
      refine le_trans (Scheme.Modules.topologicalKrullDim_le_support_pushforward I.subschemeι G hGsupp) ?_
      rw [Scheme.Modules.support_eq_of_iso eG, hsupp']
      exact he
    -- the pulled-back families
    have hL' : ∀ i, ((Scheme.Modules.pullback I.subschemeι).obj (L i)).IsLineBundle := fun i => inferInstance
    have h𝓜'' : ∀ i m, ((Scheme.Modules.pullback I.subschemeι).obj (𝓜 i m)).IsLineBundle :=
      fun i m => inferInstance
    have h𝓜' : ∀ i m, Nonempty ((Scheme.Modules.pullback I.subschemeι).obj (𝓜 i (m + 1)) ≅
        ((Scheme.Modules.pullback I.subschemeι).obj (𝓜 i m)).tensor
          ((Scheme.Modules.pullback I.subschemeι).obj (L i))) := fun i m =>
      ⟨(Scheme.Modules.pullback I.subschemeι).mapIso (h𝓜 i m).some ≪≫
        Scheme.Modules.pullbackTensorIso I.subschemeι _ _⟩
    have IH' : ∀ (Q : I.subscheme.Modules) [Q.IsCoherent],
        topologicalKrullDim Q.support ≤ (e : WithBot ℕ∞) →
        ∃ P : MvPolynomial (Fin r) ℚ, P.totalDegree ≤ e ∧ ∀ n : Fin r → ℤ,
          (AlgebraicGeometry.sheafEulerCharacteristic (k := k) I.subscheme
              (Scheme.Modules.twistList (fun i => (Scheme.Modules.pullback I.subschemeι).obj (𝓜 i (n i)))
                (List.finRange r) Q) : ℚ)
            = MvPolynomial.eval (fun i => (n i : ℚ)) P := fun Q _ hQ =>
      ih I.subscheme hZ Q hQ (fun i => (Scheme.Modules.pullback I.subschemeι).obj (L i))
        (fun i m => (Scheme.Modules.pullback I.subschemeι).obj (𝓜 i m)) h𝓜'
    obtain ⟨R, hRdeg, hR⟩ := exists_snapper_of_full_support e I.subscheme hZ hZnoemb hdimZ G hGnoemb hGsupp
      (fun i => (Scheme.Modules.pullback I.subschemeι).obj (L i))
      (fun i m => (Scheme.Modules.pullback I.subschemeι).obj (𝓜 i m)) h𝓜' IH'
    -- transfer `χ` from `Z` to `X`
    have htrans : ∀ n : Fin r → ℤ,
        AlgebraicGeometry.sheafEulerCharacteristic (k := k) X
            (Scheme.Modules.twistList (fun i => 𝓜 i (n i)) (List.finRange r)
              (CategoryTheory.Limits.cokernel ι))
          = AlgebraicGeometry.sheafEulerCharacteristic (k := k) I.subscheme
              (Scheme.Modules.twistList (fun i => (Scheme.Modules.pullback I.subschemeι).obj (𝓜 i (n i)))
                (List.finRange r) G) := fun n => by
      rw [AlgebraicGeometry.sheafEulerCharacteristic_eq_of_iso
          (Scheme.Modules.twistList_mapIso (fun i => 𝓜 i (n i)) (List.finRange r) eG.symm),
        AlgebraicGeometry.sheafEulerCharacteristic_eq_of_iso
          (Scheme.Modules.twistList_pushforward_iso I.subschemeι (fun i => 𝓜 i (n i)) (List.finRange r) G),
        ← AlgebraicGeometry.sheafEulerCharacteristic_closedImmersion I.subschemeι]
    refine ⟨PK + R, ?_, fun n => ?_⟩
    · exact (MvPolynomial.totalDegree_add _ _).trans (max_le (hPKdeg.trans (Nat.le_succ e)) hRdeg)
    · rw [MvPolynomial.eval_add, ← hPK n, ← hR n, ← htrans n, hadd n]
      push_cast
      ring

end AlgebraicGeometry

end
