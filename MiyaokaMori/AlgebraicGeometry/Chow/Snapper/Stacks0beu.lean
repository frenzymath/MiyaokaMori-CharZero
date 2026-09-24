import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ClosedImmersionProjectionFormula
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedQcAlgebraPullback
import MiyaokaMori.AlgebraicGeometry.Morphisms.ClosedSubschemeProperOver
import MiyaokaMori.RingTheory.Polynomial.NumericalPolynomialOfDifferences
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.TensorLineBundleExact
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierDivisorPullback
import MiyaokaMori.AlgebraicGeometry.Divisors.LineBundle.DivisorLineBundle
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundlePullback
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.AlgebraicGeometry.Cohomology.EulerCharacteristic.EulerCharacteristic
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.IdealSheafToModules
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.ModulesLineBundleZpow
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensor
import MiyaokaMori.RingTheory.NumericalPolynomialDiagonalCoeff
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProperOverField
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.SchemeDimension
import MiyaokaMori.AlgebraicGeometry.Cohomology.SnapperPolynomial
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.VarietyDimension
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundlePullback
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SectionRestrictionSequence
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafCohomologyLinearMap
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.NefPullback
import MiyaokaMori.AlgebraicGeometry.Cohomology.Pushforward.Stacks02uv
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.Stacks01xz
import MiyaokaMori.AlgebraicGeometry.Cohomology.EulerCharacteristic.Stacks08aa
import MiyaokaMori.AlgebraicGeometry.Chow.Snapper.Stacks0bem
import MiyaokaMori.AlgebraicGeometry.Chow.Snapper.Stacks0bep
import MiyaokaMori.AlgebraicGeometry.Chow.Snapper.EulerCharEffectiveCartierRestriction
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.FoldlTensorIso
import MiyaokaMori.RingTheory.Polynomial.MvPolynomialMixedDifference

/-! # Restriction of the Snapper intersection number to an effective Cartier divisor (Stacks 0BEU)

Stacks 0BEU: if `L_1 ≅ O_X(D)` with `D` an effective Cartier divisor, then
`(L_1⋯L_d·X) = (L_2|_D⋯L_d|_D·D)`.

Source: Stacks 0BEU; Lazarsfeld, Positivity in Algebraic Geometry I, §1.1.C, footnote 7; used in the proof
that the Snapper intersection number equals the Chow one.

## Proof (directly from the finite-difference definition of `snapperIntersection`, without comparing
coefficients of numerical polynomials)

Write `ι : D → X`, `L'_i := ι^*L_i`, `e_S := 1_S` (`S ⊆ {0,…,d}`), `F_X(n) := ⊗_i L_i^{n_i}` (the `List.foldl`
spelling of `Stacks0bep`), and `G(n) := ⊗_i L'_i^{n_i}` (on `D`).

1. **Split according to `0 ∈ S`** (`Finset.sum_finset_fin_succ_split`):
   `(L_0⋯L_d·X) = ∑_{T ⊆ {1..d}} (−1)^{d−|T|} [χ(X, F_X(1, e_T)) − χ(X, F_X(0, e_T))]`.
2. **Restriction sequence** (`EffectiveCartierDivisor.sheafEulerCharacteristic_sub_tensor_dual`, i.e.
   `0 → M ⊗ O(D)^∨ → M → ι_*ι^*M → 0`, additivity of `χ`, and invariance of cohomology under closed
   immersions): for `M := F_X(1, e_T)`, `χ(X, M) − χ(X, M ⊗ O(D)^∨) = χ(D, ι^*M)`; and
   `M ⊗ O(D)^∨ ≅ F_X(0, e_T)` (`L_0 ≅ O(D)`, `O(D) ⊗ O(D)^∨ ≅ O_X`, the tensor factor moved to the start of
   the fold: `nonempty_foldl_tensor_tensor_iso`).
3. **Pullback commutes with tensor products** (`nonempty_pullback_foldl_tensor_iso`): `ι^*F_X(n) ≅ G(n)`. Hence
   `(L_0⋯L_d·X) = ∑_T (−1)^{d−|T|} χ(D, G(1, e_T))`.
4. The right side is by definition `∑_T (−1)^{d−|T|} χ(D, ⊗_{i≥1} L'_i^{e_T}) = ∑_T (−1)^{d−|T|} χ(D, G(0, e_T))`
   (starting point `O_D ⊗ L'_0^0 = O_D ⊗ O_D ≅ O_D`).
5. **Vanishing of the leading term**: the difference of the two sides is
   `∑_{S ⊆ {0..d}} (−1)^{d+1−|S|} χ(D, G(e_S))`, the `(d+1)`-fold mixed difference of `n ↦ χ(D, G(n))`; by 0BEM
   (on `D`, `dim D = d`) this is a numerical polynomial of total degree `≤ d`, whose `(d+1)`-fold mixed
   difference is `0` (`MvPolynomial.mixed_difference_eq_zero_of_totalDegree_le`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry

section Aux

variable {k : Type u} [Field k]

/-- Sign bookkeeping for each pair of terms after the split:
`(-1)^{d+1-|T|} a + (-1)^{d+1-(|T|+1)} b = (-1)^{d-|T|} (b - a)`. -/
theorem snapper_pair_sign {d : ℕ} (T : Finset (Fin d)) (a b : ℚ) :
    (-1 : ℚ) ^ (d + 1 - (T.map (Fin.succEmb d)).card) * a
        + (-1 : ℚ) ^ (d + 1 - (insert 0 (T.map (Fin.succEmb d))).card) * b
      = (-1 : ℚ) ^ (d - T.card) * (b - a) := by
  have h0 : (0 : Fin (d + 1)) ∉ T.map (Fin.succEmb d) := by
    simp [Finset.mem_map, Fin.succ_ne_zero]
  rw [Finset.card_insert_of_notMem h0, Finset.card_map]
  have hT : T.card ≤ d := Finset.card_le_of_fin T
  have h1 : d + 1 - T.card = (d - T.card) + 1 := by omega
  have h2 : d + 1 - (T.card + 1) = d - T.card := by omega
  rw [h1, h2, pow_succ]
  ring

/-- Splitting the indicator function through `Fin.cons`: `1_{insert 0 (T.map succ)} = Fin.cons 1 1_T`. -/
theorem indicator_insert_zero_map_succ {d : ℕ} (T : Finset (Fin d)) :
    (fun i : Fin (d + 1) => if i ∈ insert 0 (T.map (Fin.succEmb d)) then (1 : ℤ) else 0)
      = Fin.cons 1 (fun i : Fin d => if i ∈ T then (1 : ℤ) else 0) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp
  · simp [Fin.succ_ne_zero]

/-- Splitting the indicator function through `Fin.cons`: `1_{T.map succ} = Fin.cons 0 1_T`. -/
theorem indicator_map_succ {d : ℕ} (T : Finset (Fin d)) :
    (fun i : Fin (d + 1) => if i ∈ T.map (Fin.succEmb d) then (1 : ℤ) else 0)
      = Fin.cons 0 (fun i : Fin d => if i ∈ T then (1 : ℤ) else 0) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [Fin.succ_ne_zero]
  · simp

/-- The fold along `map succ` rewritten as a fold over `Fin d` (`Fin.cons_succ` holds by definition; direct
structural recursion). -/
theorem foldl_map_succ_aux {Y : AlgebraicGeometry.Scheme.{u}} {d : ℕ}
    (L : Fin (d + 1) → Y.Modules) (a : ℤ) (m : Fin d → ℤ) :
    ∀ (l : List (Fin d)) (A : Y.Modules),
      List.foldl
        (fun (G : Y.Modules) (i : Fin (d + 1)) => G.tensor (L i ^ (Fin.cons a m : Fin (d + 1) → ℤ) i))
        A (l.map Fin.succ)
      = List.foldl (fun (G : Y.Modules) (i : Fin d) => G.tensor (L i.succ ^ m i)) A l
  | [], _ => rfl
  | i :: l, A => foldl_map_succ_aux L a m l (A.tensor (L i.succ ^ m i))

/-- The fold split along `finRange (d+1) = 0 :: map succ (finRange d)`. -/
theorem foldl_finRange_succ_cons {Y : AlgebraicGeometry.Scheme.{u}} {d : ℕ}
    (L : Fin (d + 1) → Y.Modules) (a : ℤ) (m : Fin d → ℤ) :
    (List.finRange (d + 1)).foldl
        (fun (G : Y.Modules) (i : Fin (d + 1)) => G.tensor (L i ^ (Fin.cons a m : Fin (d + 1) → ℤ) i))
        (SheafOfModules.unit Y.ringCatSheaf)
      = (List.finRange d).foldl
        (fun (G : Y.Modules) (i : Fin d) => G.tensor (L i.succ ^ m i))
        (AlgebraicGeometry.Scheme.Modules.tensor (SheafOfModules.unit Y.ringCatSheaf) (L 0 ^ a)) := by
  rw [List.finRange_succ]
  exact foldl_map_succ_aux L a m (List.finRange d) _

end Aux

/-- **Stacks 0BEU**: if `L 0 ≅ O_X(D)` for an effective Cartier divisor `D` of dimension `d`, then
`(L_0⋯L_d·X) = (L_1|_D⋯L_d|_D·D)`. -/
theorem snapperIntersection_effectiveCartier {k : Type u} [Field k]
    (X : AlgebraicGeometry.Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (hX : IsProperOver k X) {d : ℕ} (hd : X.dimension = d + 1)
    (L : Fin (d + 1) → X.Modules) [∀ i, (L i).IsLineBundle]
    (D : AlgebraicGeometry.EffectiveCartierDivisor X) (hL : Nonempty (L 0 ≅ D.lineBundle))
    (hdD : D.toScheme.dimension = d) :
    letI : D.toScheme.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨D.idealSheaf.subschemeι ≫ (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    AlgebraicGeometry.snapperIntersection X hX hd L
      = AlgebraicGeometry.snapperIntersection D.toScheme
          (isProperOver_of_closedImmersion hX D.idealSheaf.subschemeι) hdD
          (fun i => (AlgebraicGeometry.Scheme.Modules.pullback D.idealSheaf.subschemeι).obj (L i.succ)) := by
  classical
  letI : D.toScheme.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨D.idealSheaf.subschemeι ≫ (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  obtain ⟨eL⟩ := hL
  have hD : IsProperOver k D.toScheme := isProperOver_of_closedImmersion hX D.idealSheaf.subschemeι
  have : AlgebraicGeometry.IsProper (D.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := hD
  have : AlgebraicGeometry.IsLocallyNoetherian D.toScheme :=
    AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian
      (D.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
  -- notation
  set ι := D.idealSheaf.subschemeι with hι
  let L' : Fin (d + 1) → D.toScheme.Modules := fun i => (AlgebraicGeometry.Scheme.Modules.pullback ι).obj (L i)
  haveI hL' : ∀ i, (L' i).IsLineBundle := fun i => inferInstance
  let OX : X.Modules := SheafOfModules.unit X.ringCatSheaf
  let OD : D.toScheme.Modules := SheafOfModules.unit D.toScheme.ringCatSheaf
  let FX : (Fin (d + 1) → ℤ) → X.Modules := fun n =>
    (List.finRange (d + 1)).foldl (fun (G : X.Modules) (i : Fin (d + 1)) => G.tensor (L i ^ n i)) OX
  let GD : (Fin (d + 1) → ℤ) → D.toScheme.Modules := fun n =>
    (List.finRange (d + 1)).foldl (fun (G : D.toScheme.Modules) (i : Fin (d + 1)) => G.tensor (L' i ^ n i)) OD
  let FD : Finset (Fin d) → D.toScheme.Modules := fun T =>
    (List.finRange d).foldl
      (fun (G : D.toScheme.Modules) (i : Fin d) => G.tensor (L' i.succ ^ (if i ∈ T then (1 : ℤ) else 0))) OD
  let ind : Finset (Fin (d + 1)) → Fin (d + 1) → ℤ := fun S i => if i ∈ S then 1 else 0
  let m : Finset (Fin d) → Fin d → ℤ := fun T i => if i ∈ T then 1 else 0
  let χX : X.Modules → ℤ := AlgebraicGeometry.sheafEulerCharacteristic (k := k) X
  let χD : D.toScheme.Modules → ℤ := AlgebraicGeometry.sheafEulerCharacteristic (k := k) D.toScheme
  have hind1 : ∀ T : Finset (Fin d), ind (insert 0 (T.map (Fin.succEmb d))) = Fin.cons 1 (m T) :=
    fun T => indicator_insert_zero_map_succ T
  have hind0 : ∀ T : Finset (Fin d), ind (T.map (Fin.succEmb d)) = Fin.cons 0 (m T) :=
    fun T => indicator_map_succ T
  -- step 3: `ι^* F_X(n) ≅ G(n)`
  have hpull : ∀ S : Finset (Fin (d + 1)),
      χD ((AlgebraicGeometry.Scheme.Modules.pullback ι).obj (FX (ind S))) = χD (GD (ind S)) := by
    intro S
    obtain ⟨e₁⟩ := AlgebraicGeometry.Scheme.Modules.nonempty_pullback_foldl_tensor_iso ι
      (fun i => L i ^ ind S i) (fun i => L' i ^ ind S i)
      (fun i => AlgebraicGeometry.Scheme.Modules.nonempty_pullback_zpow_indicator_iso ι (L i) (i ∈ S))
      (List.finRange (d + 1)) OX
    obtain ⟨e₂⟩ := AlgebraicGeometry.Scheme.Modules.nonempty_foldl_tensor_iso_of_iso
      (fun i => L' i ^ ind S i) (List.finRange (d + 1))
      (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso ι)
    exact AlgebraicGeometry.sheafEulerCharacteristic_eq_of_iso (k := k) (e₁ ≪≫ e₂)
  -- step 5: the `(d+1)`-fold mixed difference on `D` vanishes
  have hvanish : (∑ S : Finset (Fin (d + 1)), (-1 : ℚ) ^ (d + 1 - S.card) * (χD (GD (ind S)) : ℚ)) = 0 := by
    have hOD : OD.IsCoherent := AlgebraicGeometry.Scheme.Modules.isCoherent_of_isLocallyFree OD
    have hsupp : topologicalKrullDim OD.support ≤ ((d : ℕ) : WithBot ℕ∞) := by
      rw [← hdD]
      exact (topologicalKrullDim_subspace_le D.toScheme OD.support).trans
        (AlgebraicGeometry.topologicalKrullDim_le_dimension_of_isProperOver D.toScheme hD)
    obtain ⟨P, hPdeg, hP⟩ :=
      AlgebraicGeometry.exists_snapper_mvPolynomial D.toScheme hD OD (r := d + 1) L' d hsupp
    rw [← MvPolynomial.mixed_difference_eq_zero_of_totalDegree_le P hPdeg]
    refine Finset.sum_congr rfl fun S _ => ?_
    congr 1
    rw [hP (ind S)]
    congr 2
    funext i
    simp only [ind]
    split <;> norm_num
  -- step 2: the restriction sequence
  have hres : ∀ T : Finset (Fin d),
      (χX (FX (Fin.cons 1 (m T))) : ℤ) - χX (FX (Fin.cons 0 (m T)))
        = χD ((AlgebraicGeometry.Scheme.Modules.pullback ι).obj (FX (Fin.cons 1 (m T)))) := by
    intro T
    haveI hlb : ∀ i : Fin (d + 1), (L i ^ (Fin.cons 1 (m T) : Fin (d + 1) → ℤ) i).IsLineBundle := by
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · rw [Fin.cons_zero]
        exact SheafOfModules.IsLineBundle.tensor (L 0) (SheafOfModules.unit X.ringCatSheaf)
      · rw [Fin.cons_succ]
        exact AlgebraicGeometry.Scheme.Modules.isLineBundle_zpow_indicator (L j.succ) (j ∈ T)
    haveI hM : (FX (Fin.cons 1 (m T))).IsLineBundle :=
      AlgebraicGeometry.Scheme.Modules.isLineBundle_foldl_tensor
        (fun i => L i ^ (Fin.cons 1 (m T) : Fin (d + 1) → ℤ) i) (List.finRange (d + 1)) OX
    have h := D.sheafEulerCharacteristic_sub_tensor_dual (k := k) X hX (FX (Fin.cons 1 (m T)))
    -- M ⊗ O(D)^∨ ≅ F_X(0, e_T)
    have hiso : Nonempty ((FX (Fin.cons 1 (m T))).tensor (AlgebraicGeometry.Scheme.Modules.dual D.lineBundle)
        ≅ FX (Fin.cons 0 (m T))) := by
      have hF1 : FX (Fin.cons 1 (m T)) = (List.finRange d).foldl
          (fun (G : X.Modules) (i : Fin d) => G.tensor (L i.succ ^ m T i))
          (AlgebraicGeometry.Scheme.Modules.tensor OX (L 0 ^ (1 : ℤ))) :=
        foldl_finRange_succ_cons L 1 (m T)
      have hF0 : FX (Fin.cons 0 (m T)) = (List.finRange d).foldl
          (fun (G : X.Modules) (i : Fin d) => G.tensor (L i.succ ^ m T i))
          (AlgebraicGeometry.Scheme.Modules.tensor OX (L 0 ^ (0 : ℤ))) :=
        foldl_finRange_succ_cons L 0 (m T)
      rw [hF1, hF0]
      obtain ⟨e₁⟩ := AlgebraicGeometry.Scheme.Modules.nonempty_foldl_tensor_tensor_iso
        (fun i : Fin d => L i.succ ^ m T i) (List.finRange d) (OX.tensor (L 0 ^ (1 : ℤ)))
        (AlgebraicGeometry.Scheme.Modules.dual D.lineBundle)
      obtain ⟨eDD⟩ := SheafOfModules.IsLineBundle.tensor_dual_iso D.lineBundle
      have e₀ : (OX.tensor (L 0 ^ (1 : ℤ))).tensor (AlgebraicGeometry.Scheme.Modules.dual D.lineBundle)
          ≅ OX.tensor (L 0 ^ (0 : ℤ)) :=
        AlgebraicGeometry.Scheme.Modules.tensorIsoLeft
            (AlgebraicGeometry.Scheme.Modules.tensorIsoRight OX
                (show L 0 ^ (1 : ℤ) ≅ D.lineBundle from
                  (AlgebraicGeometry.Scheme.Modules.moduleTensorRightUnitIso (L 0) : (L 0).tensor OX ≅ L 0) ≪≫ eL) ≪≫
              (AlgebraicGeometry.Scheme.Modules.moduleTensorLeftUnitIso D.lineBundle : OX.tensor D.lineBundle ≅ D.lineBundle))
            (AlgebraicGeometry.Scheme.Modules.dual D.lineBundle) ≪≫
          eDD ≪≫
          (AlgebraicGeometry.Scheme.Modules.moduleTensorLeftUnitIso OX : OX.tensor OX ≅ OX).symm
      obtain ⟨e₂⟩ := AlgebraicGeometry.Scheme.Modules.nonempty_foldl_tensor_iso_of_iso
        (fun i : Fin d => L i.succ ^ m T i) (List.finRange d) e₀
      exact ⟨e₁.symm ≪≫ e₂⟩
    obtain ⟨e⟩ := hiso
    rw [AlgebraicGeometry.sheafEulerCharacteristic_eq_of_iso (k := k) e] at h
    exact h
  -- step 4: `G(0, e_T) ≅ F_D(T)`
  have hGD0 : ∀ T : Finset (Fin d), χD (GD (Fin.cons 0 (m T))) = χD (FD T) := by
    intro T
    have hG0 : GD (Fin.cons 0 (m T)) = (List.finRange d).foldl
        (fun (G : D.toScheme.Modules) (i : Fin d) => G.tensor (L' i.succ ^ m T i))
        (AlgebraicGeometry.Scheme.Modules.tensor OD (L' 0 ^ (0 : ℤ))) :=
      foldl_finRange_succ_cons L' 0 (m T)
    rw [hG0]
    obtain ⟨e⟩ := AlgebraicGeometry.Scheme.Modules.nonempty_foldl_tensor_iso_of_iso
      (fun i : Fin d => L' i.succ ^ m T i) (List.finRange d)
      (AlgebraicGeometry.Scheme.Modules.moduleTensorLeftUnitIso OD : OD.tensor OD ≅ OD)
    exact AlgebraicGeometry.sheafEulerCharacteristic_eq_of_iso (k := k) e
  -- assembly
  have hLHS : AlgebraicGeometry.snapperIntersection X hX hd L
      = ∑ T : Finset (Fin d), (-1 : ℚ) ^ (d - T.card) *
          ((χX (FX (Fin.cons 1 (m T))) : ℚ) - χX (FX (Fin.cons 0 (m T)))) := by
    unfold AlgebraicGeometry.snapperIntersection
    rw [Finset.sum_finset_fin_succ_split]
    refine Finset.sum_congr rfl fun T _ => ?_
    show (-1 : ℚ) ^ (d + 1 - (T.map (Fin.succEmb d)).card) * (χX (FX (ind (T.map (Fin.succEmb d)))) : ℚ)
        + (-1 : ℚ) ^ (d + 1 - (insert 0 (T.map (Fin.succEmb d))).card) *
            (χX (FX (ind (insert 0 (T.map (Fin.succEmb d))))) : ℚ)
      = (-1 : ℚ) ^ (d - T.card) * ((χX (FX (Fin.cons 1 (m T))) : ℚ) - χX (FX (Fin.cons 0 (m T))))
    rw [snapper_pair_sign, hind1 T, hind0 T]
  have hRHS : AlgebraicGeometry.snapperIntersection D.toScheme hD hdD (fun i => L' i.succ)
      = ∑ T : Finset (Fin d), (-1 : ℚ) ^ (d - T.card) * (χD (FD T) : ℚ) := by
    unfold AlgebraicGeometry.snapperIntersection
    rfl
  have hvanish' : (∑ T : Finset (Fin d), (-1 : ℚ) ^ (d - T.card) *
      ((χD (GD (Fin.cons 1 (m T))) : ℚ) - χD (GD (Fin.cons 0 (m T))))) = 0 := by
    rw [← hvanish, Finset.sum_finset_fin_succ_split]
    refine Finset.sum_congr rfl fun T _ => ?_
    show (-1 : ℚ) ^ (d - T.card) * ((χD (GD (Fin.cons 1 (m T))) : ℚ) - χD (GD (Fin.cons 0 (m T))))
      = (-1 : ℚ) ^ (d + 1 - (T.map (Fin.succEmb d)).card) * (χD (GD (ind (T.map (Fin.succEmb d)))) : ℚ)
        + (-1 : ℚ) ^ (d + 1 - (insert 0 (T.map (Fin.succEmb d))).card) *
            (χD (GD (ind (insert 0 (T.map (Fin.succEmb d))))) : ℚ)
    rw [snapper_pair_sign, hind1 T, hind0 T]
  show AlgebraicGeometry.snapperIntersection X hX hd L
      = AlgebraicGeometry.snapperIntersection D.toScheme hD hdD (fun i => L' i.succ)
  rw [hLHS, hRHS, ← sub_eq_zero, ← Finset.sum_sub_distrib, ← hvanish']
  refine Finset.sum_congr rfl fun T _ => ?_
  have hres' := hres T
  have hpull' : χD ((AlgebraicGeometry.Scheme.Modules.pullback ι).obj (FX (Fin.cons 1 (m T))))
      = χD (GD (Fin.cons 1 (m T))) := by
    have := hpull (insert 0 (T.map (Fin.succEmb d)))
    rw [hind1 T] at this
    exact this
  rw [hpull'] at hres'
  rw [hGD0 T]
  have : ((χX (FX (Fin.cons 1 (m T))) : ℚ) - χX (FX (Fin.cons 0 (m T)))) = χD (GD (Fin.cons 1 (m T))) := by
    exact_mod_cast hres'
  rw [this]
  ring

end AlgebraicGeometry

end
