import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.CoherentSheaf
import MiyaokaMori.AlgebraicGeometry.Cohomology.EulerCharacteristic.EulerCharacteristic
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProperOverField
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.SchemeDimension
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafCohomologyLinearMap
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.SchemeDimensionFinite
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.Stacks01xz
import MiyaokaMori.AlgebraicGeometry.Chow.Snapper.Stacks0bem
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModuleTensorUnit

/-! # The Snapper polynomial

`p ↦ χ(X, L^{⊗p})` agrees with a polynomial of degree `≤ dim X` at all integers `p` (the Snapper
polynomial). The general form is Stacks 0BEM.

Proof: specialize Stacks 0BEM (`AlgebraicGeometry.exists_snapper_mvPolynomial`: for a proper scheme `X`,
a coherent sheaf `F` and invertible sheaves `L_1..L_r`, `(n_i) ↦ χ(F ⊗ ⨂ L_i^{n_i})` is a polynomial of
total degree `≤ dim Supp F`) to `F = O_X`, `r = 1`, `L_1 = L`:
1. `X` proper over the field `k` ⇒ locally Noetherian (`LocallyOfFiniteType.isLocallyNoetherian`); `O_X`
   is locally free of finite type, hence coherent (`isCoherent_of_isLocallyFree`, Stacks 01XZ).
2. `Supp O_X ⊆ X`, and the topological Krull dimension of a subspace is at most that of the whole space
   (`topologicalKrullDim_subspace_le`); `X` proper ⇒ `topologicalKrullDim X ≠ ⊤`
   (`topologicalKrullDim_ne_top_of_isProperOver`), so `topologicalKrullDim X ≤ X.dimension`
   (`X.dimension` is the `toNat` truncation sending `⊥` to `0`).
3. For `r = 1` the fold of 0BEM is `foldl … O_X = O_X ⊗ L^p`; the left unitor `moduleTensorLeftUnitIso`
   gives `O_X ⊗ L^p ≅ L^p`, and `χ` is invariant under isomorphism (`sheafEulerCharacteristic_eq_of_iso`).
4. `MvPolynomial.uniqueAlgEquiv ℚ (Fin 1)` turns the multivariate polynomial `Q` of 0BEM into
   `P : Polynomial ℚ`: `coeff_uniqueAlgEquiv` + `coeff_eq_zero_of_totalDegree_lt` give
   `natDegree P ≤ totalDegree Q ≤ dim X`, and `eval₂_uniqueAlgEquiv` gives `P.eval p = Q.eval (fun _ => p)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The topological Krull dimension of a proper `k`-scheme is `≤ X.dimension` (the latter sends `⊥` to `0`;
`⊤` does not occur). -/
theorem AlgebraicGeometry.topologicalKrullDim_le_dimension_of_isProperOver {k : Type u} [Field k]
    (X : AlgebraicGeometry.Scheme.{u})
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (hX : IsProperOver k X) :
    topologicalKrullDim X ≤ (X.dimension : WithBot ℕ∞) := by
  have hne : topologicalKrullDim X ≠ ⊤ :=
    AlgebraicGeometry.topologicalKrullDim_ne_top_of_isProperOver X hX
  unfold AlgebraicGeometry.Scheme.dimension
  cases hd : topologicalKrullDim X with
  | bot => exact bot_le
  | coe d =>
    cases d with
    | top => exact (hne hd).elim
    | coe n => simp

theorem exists_snapper_polynomial {k : Type u} [Field k]
    (X : AlgebraicGeometry.Scheme.{u})
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (hX : IsProperOver k X)
    (L : X.Modules) [L.IsLineBundle] :
    ∃ P : Polynomial ℚ, P.natDegree ≤ X.dimension ∧
      ∀ p : ℤ, (AlgebraicGeometry.sheafEulerCharacteristic (k := k) X (L ^ p) : ℚ) = P.eval (p : ℚ) := by
  -- 1. `O_X` is coherent
  have : AlgebraicGeometry.IsProper (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := hX
  have : AlgebraicGeometry.IsLocallyNoetherian X :=
    AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian
      (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  have hO : O.IsCoherent := AlgebraicGeometry.Scheme.Modules.isCoherent_of_isLocallyFree O
  -- 2. `dim Supp O_X ≤ dim X`
  have hsupp : topologicalKrullDim O.support ≤ ((X.dimension : ℕ) : WithBot ℕ∞) :=
    (topologicalKrullDim_subspace_le X O.support).trans
      (AlgebraicGeometry.topologicalKrullDim_le_dimension_of_isProperOver X hX)
  -- 3. 0BEM with `r = 1`
  obtain ⟨Q, hQdeg, hQ⟩ :=
    AlgebraicGeometry.exists_snapper_mvPolynomial X hX O (r := 1) (fun _ => L) X.dimension hsupp
  refine ⟨MvPolynomial.uniqueAlgEquiv ℚ (Fin 1) Q, ?_, ?_⟩
  · -- natDegree ≤ totalDegree ≤ dim X
    refine (Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun N hN => ?_).trans hQdeg
    rw [MvPolynomial.coeff_uniqueAlgEquiv]
    apply MvPolynomial.coeff_eq_zero_of_totalDegree_lt
    refine lt_of_lt_of_le hN (le_of_eq ?_)
    have hN0 : N ≠ 0 := by omega
    simp [Finsupp.support_single, hN0]
  · intro p
    have h := hQ (fun _ => p)
    have hfold : (List.finRange 1).foldl (fun (G : X.Modules) (i : Fin 1) => G.tensor (L ^ p)) O
        = O.tensor (L ^ p) := by
      simp only [List.finRange_succ, List.finRange_zero, List.map_nil, List.foldl_cons,
        List.foldl_nil]
    rw [hfold] at h
    have e : O.tensor (L ^ p) ≅ L ^ p := AlgebraicGeometry.Scheme.Modules.moduleTensorLeftUnitIso (L ^ p)
    rw [AlgebraicGeometry.sheafEulerCharacteristic_eq_of_iso e] at h
    rw [h]
    have := @MvPolynomial.eval₂_uniqueAlgEquiv (Fin 1) ℚ ℚ _ _ _ Q (RingHom.id ℚ) (fun _ => (p : ℚ))
    exact this.symm


end
