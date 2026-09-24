import MiyaokaMori.Prelude
import MiyaokaMori.RingTheory.Polynomial.NumericalPolynomialOfDifferences
import MiyaokaMori.AlgebraicGeometry.Cohomology.EulerCharacteristic.EulerCharacteristic
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.Stacks01y1
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.Stacks01ic
import MiyaokaMori.AlgebraicGeometry.Chow.Snapper.SnapperDenominatorMapsCoherent
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.NowhereDenseDimensionDrop
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.TwistByLineBundleList

/-! # The full-support step of Snapper's theorem

The inductive step of Snapper's theorem (Stacks 0BEM) in the case already reduced
to `Supp G = Z`, `Z` and `G` without embedded points (paragraph 4 of the Stacks proof + the "simple
arithmetic argument"):

Let `Z` be proper over `k` with no embedded points and `dim Z ≤ e + 1`, `G` coherent with no embedded
associated points and `Supp G = Z`, `L₁, …, L_r` invertible, and `𝓜 i : ℤ → Z.Modules` line bundles with
`𝓜 i (n+1) ≅ 𝓜 i n ⊗ L i`. Assume (induction hypothesis) that for every coherent `Q` with `dim Supp Q ≤ e`
the function `n ↦ χ(Q ⊗ 𝓜₁(n₁) ⊗ ⋯ ⊗ 𝓜_r(n_r))` is a polynomial of total degree `≤ e`. Then
`P(n) := χ(G ⊗ 𝓜₁(n₁) ⊗ ⋯)` is a polynomial of total degree `≤ e + 1`.

Proof. Fix `j`. The denominator-ideal lemma (`exists_denominator_maps_isCoherent`, Stacks
02OZ + 02P2) applied to `L_j` gives a coherent `IF` and monomorphisms `a : IF → G`, `b : IF → G ⊗ L_j`
whose cokernels `Q, Q'` are supported in a closed `T` with empty interior. Since `Z` is Noetherian,
`dim Supp Q, dim Supp Q' ≤ e`, so by the induction hypothesis
`n ↦ χ(Q ⊗ 𝓜(n))`, `n ↦ χ(Q' ⊗ 𝓜(n))` are polynomials `P_Q, P_{Q'}` of total degree `≤ e`. Tensoring the
two short exact sequences with the line bundle `𝓜(n)` keeps them exact and `χ` is additive (Stacks 08AA),
so `χ(G ⊗ 𝓜(n)) = χ(IF ⊗ 𝓜(n)) + P_Q(n)` and `χ(G ⊗ L_j ⊗ 𝓜(n)) = χ(IF ⊗ 𝓜(n)) + P_{Q'}(n)`. Finally
`G ⊗ L_j ⊗ 𝓜(n) ≅ G ⊗ 𝓜(n + e_j)` (`𝓜 j (n_j + 1) ≅ 𝓜 j n_j ⊗ L_j`, commutativity), hence
`P(n + e_j) − P(n) = P_{Q'}(n) − P_Q(n)` has total degree `< e + 1`, and the difference criterion
(`MvPolynomial.exists_eval_eq_of_forall_sub_eval_eq`) gives the polynomial of total degree `≤ e + 1`.

Source: Stacks 0BEM.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry

/-- A scheme proper over a field is locally Noetherian. -/
theorem isLocallyNoetherian_of_isProperOver {k : Type u} [Field k] (X : AlgebraicGeometry.Scheme.{u})
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (hX : IsProperOver k X) :
    AlgebraicGeometry.IsLocallyNoetherian X := by
  have : AlgebraicGeometry.IsProper (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := hX
  exact AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian
    (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))

/-- A scheme proper over a field is Noetherian; its underlying space is a Noetherian space. -/
theorem noetherianSpace_of_isProperOver {k : Type u} [Field k] (X : AlgebraicGeometry.Scheme.{u})
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (hX : IsProperOver k X) :
    TopologicalSpace.NoetherianSpace X := by
  have : AlgebraicGeometry.IsProper (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := hX
  have : AlgebraicGeometry.IsLocallyNoetherian X := isLocallyNoetherian_of_isProperOver X hX
  have : CompactSpace X :=
    AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace
      (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
  have : AlgebraicGeometry.IsNoetherian X := ⟨⟩
  infer_instance

/-- Cokernels of maps of coherent sheaves on a locally Noetherian scheme are coherent
(quasi-coherent by Stacks 01IC, then Stacks 01Y1). -/
theorem Scheme.Modules.isCoherent_cokernel {X : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsLocallyNoetherian X] {M N : X.Modules} (φ : M ⟶ N) [hM : M.IsCoherent]
    [hN : N.IsCoherent] : (CategoryTheory.Limits.cokernel φ).IsCoherent := by
  have := hM.quasicoherent
  have := hN.quasicoherent
  have : (CategoryTheory.Limits.cokernel φ).IsQuasicoherent :=
    (AlgebraicGeometry.Scheme.Modules.isQuasicoherent_kernel φ).2
  exact AlgebraicGeometry.Scheme.Modules.isCoherent_of_epi (CategoryTheory.Limits.cokernel.π φ)

/-- `0 → M → N → coker φ → 0` is short exact for a monomorphism `φ`. -/
theorem Scheme.Modules.cokernelSequence_shortExact {X : AlgebraicGeometry.Scheme.{u}}
    {M N : X.Modules} (φ : M ⟶ N) [CategoryTheory.Mono φ] :
    (CategoryTheory.ShortComplex.cokernelSequence φ).ShortExact := by
  refine CategoryTheory.ShortComplex.ShortExact.mk' (CategoryTheory.ShortComplex.cokernelSequence_exact φ)
    ?_ inferInstance
  show CategoryTheory.Mono φ
  infer_instance

/-- **Inductive step of 0BEM on a scheme equal to the support** (see the module docstring). -/
theorem exists_snapper_of_full_support {k : Type u} [Field k] (e : ℕ)
    (Z : AlgebraicGeometry.Scheme.{u}) [Z.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (hZ : IsProperOver k Z) (hZemb : Z.HasNoEmbeddedPoints)
    (hdim : topologicalKrullDim Z ≤ ((e + 1 : ℕ) : WithBot ℕ∞))
    (G : Z.Modules) [G.IsCoherent] (hG : G.HasNoEmbeddedAssociatedPoints) (hGsupp : G.support = Set.univ)
    {r : ℕ} (L : Fin r → Z.Modules) [∀ i, (L i).IsLineBundle]
    (𝓜 : Fin r → ℤ → Z.Modules) [∀ i n, (𝓜 i n).IsLineBundle]
    (h𝓜 : ∀ i n, Nonempty (𝓜 i (n + 1) ≅ (𝓜 i n).tensor (L i)))
    (IH : ∀ (Q : Z.Modules) [Q.IsCoherent], topologicalKrullDim Q.support ≤ (e : WithBot ℕ∞) →
      ∃ P : MvPolynomial (Fin r) ℚ, P.totalDegree ≤ e ∧ ∀ n : Fin r → ℤ,
        (AlgebraicGeometry.sheafEulerCharacteristic (k := k) Z
            (Scheme.Modules.twistList (fun i => 𝓜 i (n i)) (List.finRange r) Q) : ℚ)
          = MvPolynomial.eval (fun i => (n i : ℚ)) P) :
    ∃ P : MvPolynomial (Fin r) ℚ, P.totalDegree ≤ e + 1 ∧ ∀ n : Fin r → ℤ,
      (AlgebraicGeometry.sheafEulerCharacteristic (k := k) Z
          (Scheme.Modules.twistList (fun i => 𝓜 i (n i)) (List.finRange r) G) : ℚ)
        = MvPolynomial.eval (fun i => (n i : ℚ)) P := by
  have hloc : AlgebraicGeometry.IsLocallyNoetherian Z := isLocallyNoetherian_of_isProperOver Z hZ
  have hnoeth : TopologicalSpace.NoetherianSpace Z := noetherianSpace_of_isProperOver Z hZ
  refine MvPolynomial.exists_eval_eq_of_forall_sub_eval_eq (e := e + 1)
    (fun n : Fin r → ℤ => (AlgebraicGeometry.sheafEulerCharacteristic (k := k) Z
      (Scheme.Modules.twistList (fun i => 𝓜 i (n i)) (List.finRange r) G) : ℚ)) (fun j => ?_)
  obtain ⟨IF, a, b, T, hIF, ha, hb, hTc, hTi, hQa, hQb⟩ :=
    Scheme.Modules.exists_denominator_maps_isCoherent hZemb G hG hGsupp (L j)
  have hGL : (G.tensor (L j)).IsCoherent := Scheme.Modules.isCoherent_tensor_of_isLineBundle G (L j)
  have hQa' : (CategoryTheory.Limits.cokernel a).IsCoherent := Scheme.Modules.isCoherent_cokernel a
  have hQb' : (CategoryTheory.Limits.cokernel b).IsCoherent := Scheme.Modules.isCoherent_cokernel b
  have hTnd : IsNowhereDense T := by
    unfold IsNowhereDense
    rw [hTc.closure_eq]
    exact hTi
  have hdima : topologicalKrullDim (CategoryTheory.Limits.cokernel a).support ≤ (e : WithBot ℕ∞) :=
    TopologicalSpace.topologicalKrullDim_le_of_isNowhereDense (hTnd.mono hQa) hdim
  have hdimb : topologicalKrullDim (CategoryTheory.Limits.cokernel b).support ≤ (e : WithBot ℕ∞) :=
    TopologicalSpace.topologicalKrullDim_le_of_isNowhereDense (hTnd.mono hQb) hdim
  obtain ⟨Pa, hPa, hPa'⟩ := IH (CategoryTheory.Limits.cokernel a) hdima
  obtain ⟨Pb, hPb, hPb'⟩ := IH (CategoryTheory.Limits.cokernel b) hdimb
  refine ⟨Pb - Pa, Or.inr ?_, fun n => ?_⟩
  · refine lt_of_le_of_lt (MvPolynomial.totalDegree_sub Pb Pa) ?_
    exact Nat.lt_succ_of_le (max_le hPb hPa)
  · -- additivity on the two twisted short exact sequences
    have : (CategoryTheory.ShortComplex.cokernelSequence a).X₁.IsCoherent := hIF
    have : (CategoryTheory.ShortComplex.cokernelSequence a).X₂.IsCoherent := ‹G.IsCoherent›
    have : (CategoryTheory.ShortComplex.cokernelSequence a).X₃.IsCoherent := hQa'
    have : (CategoryTheory.ShortComplex.cokernelSequence b).X₁.IsCoherent := hIF
    have : (CategoryTheory.ShortComplex.cokernelSequence b).X₂.IsCoherent := hGL
    have : (CategoryTheory.ShortComplex.cokernelSequence b).X₃.IsCoherent := hQb'
    have hSa := Scheme.Modules.sheafEulerCharacteristic_twistList_shortExact hZ (fun i => 𝓜 i (n i))
      (List.finRange r) (CategoryTheory.ShortComplex.cokernelSequence a)
      (Scheme.Modules.cokernelSequence_shortExact a)
    have hSb := Scheme.Modules.sheafEulerCharacteristic_twistList_shortExact hZ (fun i => 𝓜 i (n i))
      (List.finRange r) (CategoryTheory.ShortComplex.cokernelSequence b)
      (Scheme.Modules.cokernelSequence_shortExact b)
    simp only [CategoryTheory.ShortComplex.cokernelSequence_X₁,
      CategoryTheory.ShortComplex.cokernelSequence_X₂,
      CategoryTheory.ShortComplex.cokernelSequence_X₃] at hSa hSb
    -- `G ⊗ L_j ⊗ 𝓜(n) ≅ G ⊗ 𝓜(n + e_j)`
    have hj : Function.update n j (n j + 1) j = n j + 1 := Function.update_self ..
    obtain ⟨e₁⟩ := Scheme.Modules.twistList_finRange_update_iso
      (𝓜 := fun i => 𝓜 i (n i)) (𝓝 := fun i => 𝓜 i (Function.update n j (n j + 1) i)) (j := j)
      (M := L j) (fun i hij => by simp only [Function.update_of_ne hij])
      (CategoryTheory.eqToIso (congrArg (𝓜 j) hj) ≪≫ (h𝓜 j (n j)).some) G
    have e₂ := Scheme.Modules.twistList_tensor_right_iso (fun i => 𝓜 i (n i)) (List.finRange r) G (L j)
    have hχ : AlgebraicGeometry.sheafEulerCharacteristic (k := k) Z
        (Scheme.Modules.twistList (fun i => 𝓜 i (Function.update n j (n j + 1) i)) (List.finRange r) G)
          = AlgebraicGeometry.sheafEulerCharacteristic (k := k) Z
            (Scheme.Modules.twistList (fun i => 𝓜 i (n i)) (List.finRange r) (G.tensor (L j))) := by
      rw [AlgebraicGeometry.sheafEulerCharacteristic_eq_of_iso e₁,
        AlgebraicGeometry.sheafEulerCharacteristic_eq_of_iso e₂]
    show (AlgebraicGeometry.sheafEulerCharacteristic (k := k) Z
        (Scheme.Modules.twistList (fun i => 𝓜 i (Function.update n j (n j + 1) i)) (List.finRange r) G) : ℚ)
      - (AlgebraicGeometry.sheafEulerCharacteristic (k := k) Z
        (Scheme.Modules.twistList (fun i => 𝓜 i (n i)) (List.finRange r) G) : ℚ) = _
    rw [map_sub, ← hPa' n, ← hPb' n, hχ, hSb, hSa]
    push_cast
    ring

end AlgebraicGeometry

end
