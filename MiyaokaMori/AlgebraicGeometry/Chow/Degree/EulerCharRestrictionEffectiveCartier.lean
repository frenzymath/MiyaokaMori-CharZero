import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.Snapper.Stacks0bem
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.EulerCharZeroDimDegree
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDimensionAndFrame
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ChowDegreeRatPushforward

/-! # Euler characteristic of the restriction of a line bundle to an effective Cartier divisor

Let `X` be a proper, integral, one-dimensional scheme over a field `k`, `D` an effective Cartier divisor
with `i : D → X`, and `M` a line bundle on `X`. Then `i_*i^*M` is coherent and
`χ(X, i_*i^*M) = deg_k D := deg [D]_0` (the `k`-degree `Σ_x length(O_{D,x})·[κ(x):k]` of
`D.idealSheaf.cycle 0`).

Proof:
1. `i^*M` is a line bundle on `D` (pullback of a line bundle) and `D` is locally Noetherian, so it is
   coherent; `i` is a closed immersion, hence finite, so `i_*i^*M` is coherent (Stacks 01Y6).
2. `dim D = 0`: if `D = ∅` then `D.dimension = 0` (`Scheme.dimension` truncates `⊥` to `0`); if `D ≠ ∅`
   use `EffectiveCartierDivisor.toScheme_dimension_eq` (Stacks 0BCN + 0A21: a nonempty effective
   Cartier divisor on an integral proper `k`-scheme drops the dimension by `1`), with `X.dimension = 1`
   from `topologicalKrullDim X = 1`.
3. Pushforward along a closed immersion does not change `χ` (`sheafEulerCharacteristic_closedImmersion`,
   the `k`-linear form of Stacks 089W): `χ(X, i_*i^*M) = χ(D, i^*M)`.
4. `χ(D, i^*M) = χ(D, O_D)`: instead of Stacks 02M9 (triviality of `Pic` of a zero-dimensional semilocal
   ring) use the Snapper polynomial (Stacks 0BEM, `exists_snapper_mvPolynomial`): `supp O_D = D` has
   topological Krull dimension `≤ 0`, so `n ↦ χ(D, O_D ⊗ L^n)` is a polynomial of total degree `≤ 0`,
   i.e. constant; take `n = 1, 0` and use `O_D ⊗ L^1 ≅ L`, `O_D ⊗ L^0 ≅ O_D`.
5. `χ(D, O_D) = deg [D]_0` (`sheafEulerCharacteristic_eq_degree_fundamentalCycle`, Stacks 02M0).
6. `D.idealSheaf.cycle 0 = i_*[D]_0` (`IdealSheafData.cycle_eq_properPushforward`), the pushforward along
   a closed immersion descends (`pushforwardDescends_subschemeι`), and the pushforward along a proper
   `k`-morphism preserves the degree of zero-cycles (`degree_properPushforward`, the zero-dimensional
   case of Stacks 02R6).

Source: the proof of Stacks 0AYY (varieties-lemma-degree-effective-Cartier-divisor) + 0AYT + 02M0;
step 4 goes through 0BEM.
-/

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry

/-- `deg_k D := deg [D]_0 = Σ_{x ∈ D} length(O_{D,x})·[κ(x):k]`; when `X` is proper over `k` and `D` is
zero-dimensional the fallback of the `finsum` is not triggered. -/
def EffectiveCartierDivisor.degreeOver (k : Type u) [Field k] {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k))] [IsLocallyNoetherian X] (D : EffectiveCartierDivisor X) : ℤ :=
  AlgebraicCycle.degree (k := k) (D.idealSheaf.cycle 0)

/-- **χ of a line bundle on a zero-dimensional proper `k`-scheme equals χ(O_Z)** (Stacks 0BEM applied
with `r = 1`, `e = 0`). Proof: `supp O_Z = Z` has topological Krull dimension `≤ 0`, so by
`exists_snapper_mvPolynomial` the function `n ↦ χ(Z, O_Z ⊗ L^n)` is given by a polynomial `P ∈ ℚ[t]`
of total degree `≤ 0`, i.e. a constant (`MvPolynomial.totalDegree_eq_zero_iff_eq_C`); evaluate at
`n = 1` and `n = 0` and use `O_Z ⊗ L^1 ≅ L`, `O_Z ⊗ L^0 ≅ O_Z`. This replaces the Pic-triviality of
semilocal rings (Stacks 02M9) in the original route. Edge cases: `Z = ∅` gives `0 = 0`. -/
theorem sheafEulerCharacteristic_lineBundle_eq_unit_of_dimension_eq_zero {k : Type u} [Field k]
    {Z : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k))] (hZ : IsProperOver k Z)
    (hd : Z.dimension = 0) (L : Z.Modules) [L.IsLineBundle] :
    sheafEulerCharacteristic (k := k) Z L =
      sheafEulerCharacteristic (k := k) Z (SheafOfModules.unit Z.ringCatSheaf) := by
  classical
  set OZ : Z.Modules := SheafOfModules.unit Z.ringCatSheaf with hOZ
  have hprop : IsProper (Z ↘ Spec (CommRingCat.of k)) := hZ
  have : IsLocallyNoetherian Z :=
    LocallyOfFiniteType.isLocallyNoetherian (Z ↘ Spec (CommRingCat.of k))
  have : OZ.IsCoherent := Scheme.Modules.isCoherent_of_isLocallyFree OZ
  have hsupp : topologicalKrullDim OZ.support ≤ ((0 : ℕ) : WithBot ℕ∞) :=
    (topologicalKrullDim_subspace_le Z OZ.support).trans
      (topologicalKrullDim_le_zero_of_dimension_eq_zero Z hZ hd)
  obtain ⟨P, hPdeg, hP⟩ :=
    exists_snapper_mvPolynomial Z hZ OZ (r := 1) (fun _ => L) 0 hsupp
  have hconst : ∀ n m : Fin 1 → ℤ,
      MvPolynomial.eval (fun i => (n i : ℚ)) P = MvPolynomial.eval (fun i => (m i : ℚ)) P := by
    intro n m
    have hc := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp (Nat.le_zero.mp hPdeg)
    rw [hc]
    simp
  have h1 := hP (fun _ => 1)
  have h0 := hP (fun _ => 0)
  have hf1 : (List.finRange 1).foldl
      (fun (G : Z.Modules) (i : Fin 1) => G.tensor ((fun _ => L) i ^ (fun _ : Fin 1 => (1 : ℤ)) i)) OZ
      = OZ.tensor (L ^ (1 : ℤ)) := rfl
  have hf0 : (List.finRange 1).foldl
      (fun (G : Z.Modules) (i : Fin 1) => G.tensor ((fun _ => L) i ^ (fun _ : Fin 1 => (0 : ℤ)) i)) OZ
      = OZ.tensor (L ^ (0 : ℤ)) := rfl
  rw [hf1] at h1
  rw [hf0] at h0
  have e1 : OZ.tensor (L ^ (1 : ℤ)) ≅ L :=
    Scheme.Modules.tensorIsoRight OZ
        (show L ^ (1 : ℤ) ≅ L from (AlgebraicGeometry.Scheme.Modules.moduleTensorRightUnitIso L : L.tensor OZ ≅ L)) ≪≫
      (AlgebraicGeometry.Scheme.Modules.moduleTensorLeftUnitIso L : OZ.tensor L ≅ L)
  have e0 : OZ.tensor (L ^ (0 : ℤ)) ≅ OZ := (AlgebraicGeometry.Scheme.Modules.moduleTensorLeftUnitIso OZ : OZ.tensor OZ ≅ OZ)
  have hQ : (sheafEulerCharacteristic (k := k) Z L : ℚ) = sheafEulerCharacteristic (k := k) Z OZ := by
    rw [← sheafEulerCharacteristic_eq_of_iso (k := k) e1, ← sheafEulerCharacteristic_eq_of_iso (k := k) e0,
      h1, h0]
    exact hconst _ _
  exact_mod_cast hQ

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]
  [IsIntegral X] [IsLocallyNoetherian X]

/-- **An effective Cartier divisor on a one-dimensional integral proper `k`-scheme is
zero-dimensional** (`Scheme.dimension`, which sends `⊥` to `0`). If `D = ∅` (`D.idealSheaf = ⊤`),
`D.toScheme` is empty, its Krull dimension is `⊥` and `dimension = 0`. Otherwise
`EffectiveCartierDivisor.toScheme_dimension_eq` (Stacks 0BCN + 0A21) gives `dim D = dim X - 1 = 0`,
where `X.dimension = 1` follows from `topologicalKrullDim X = 1` via `Scheme.dimension_spec`. -/
theorem EffectiveCartierDivisor.toScheme_dimension_eq_zero (hX : IsProperOver k X)
    (hdim : SchemeIsOneDimensional X) (D : EffectiveCartierDivisor X) :
    D.toScheme.dimension = 0 := by
  by_cases hT : D.idealSheaf = ⊤
  · have hE : IsEmpty D.toScheme :=
      (D.idealSheaf.subschemeι.ker_eq_top_iff_isEmpty).mp
        (by rw [Scheme.IdealSheafData.ker_subschemeι]; exact hT)
    have : IsEmpty (IrreducibleCloseds D.toScheme) :=
      ⟨fun W => W.isIrreducible'.nonempty.elim fun x _ => isEmptyElim x⟩
    unfold Scheme.dimension topologicalKrullDim
    rw [Order.krullDim_eq_bot]
    rfl
  · have hkd : topologicalKrullDim X = 1 := hdim
    have hne_bot : topologicalKrullDim X ≠ ⊥ := by rw [hkd]; exact WithBot.coe_ne_bot
    have hne_top : topologicalKrullDim X ≠ ⊤ := by
      rw [hkd]
      exact fun h => ENat.one_ne_top (WithBot.coe_injective h)
    have hspec := X.dimension_spec hne_bot hne_top
    rw [hkd] at hspec
    have hd1 : X.dimension = 0 + 1 := by
      have : ((1 : ℕ) : WithBot ℕ∞) = (X.dimension : WithBot ℕ∞) := by exact_mod_cast hspec
      exact_mod_cast this.symm
    exact D.toScheme_dimension_eq hX hd1 hT

omit [IsIntegral X] in
theorem EffectiveCartierDivisor.isCoherent_pushforward_pullback
    (D : EffectiveCartierDivisor X) (M : X.Modules) [M.IsLineBundle] :
    ((Scheme.Modules.pushforward D.idealSheaf.subschemeι).obj
      ((Scheme.Modules.pullback D.idealSheaf.subschemeι).obj M)).IsCoherent := by
  have : IsLocallyNoetherian D.idealSheaf.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian D.idealSheaf.subschemeι
  have : ((Scheme.Modules.pullback D.idealSheaf.subschemeι).obj M).IsCoherent :=
    Scheme.Modules.isCoherent_of_isLocallyFree _
  exact Scheme.Modules.isCoherent_pushforward_of_isFinite D.idealSheaf.subschemeι _

/-- **χ(X, i_*i^*M) = deg_k D** for a line bundle `M` on a one-dimensional integral proper `k`-scheme
`X` and an effective Cartier divisor `D` with closed immersion `i : D → X` (Stacks 0AYY, proof).
Route (module docstring, steps 2–6): χ is invariant under closed-immersion pushforward; on the
zero-dimensional `D` every line bundle has the same χ as `O_D` (Snapper polynomial of degree ≤ 0);
χ(D, O_D) = deg [D]_0; and `D.idealSheaf.cycle 0 = i_*[D]_0` has the same degree. -/
theorem EffectiveCartierDivisor.sheafEulerCharacteristic_pushforward_pullback
    (hX : IsProperOver k X) (hdim : SchemeIsOneDimensional X)
    (D : EffectiveCartierDivisor X) (M : X.Modules) [M.IsLineBundle] :
    sheafEulerCharacteristic (k := k) X
        ((Scheme.Modules.pushforward D.idealSheaf.subschemeι).obj
          ((Scheme.Modules.pullback D.idealSheaf.subschemeι).obj M)) = D.degreeOver k := by
  classical
  let _ : D.toScheme.Over (Spec (CommRingCat.of k)) :=
    ⟨D.idealSheaf.subschemeι ≫ (X ↘ Spec (CommRingCat.of k))⟩
  have hιo : D.idealSheaf.subschemeι.IsOver (Spec (CommRingCat.of k)) := ⟨rfl⟩
  have hD : IsProperOver k D.toScheme := isProperOver_of_closedImmersion hX D.idealSheaf.subschemeι
  have hpropX : IsProper (X ↘ Spec (CommRingCat.of k)) := hX
  have hftX : LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k)) := hpropX.toLocallyOfFiniteType
  have hd0 : D.toScheme.dimension = 0 := D.toScheme_dimension_eq_zero hX hdim
  -- Step 3: closed immersion pushforward preserves χ
  have hA : sheafEulerCharacteristic (k := k) X
      ((Scheme.Modules.pushforward D.idealSheaf.subschemeι).obj
        ((Scheme.Modules.pullback D.idealSheaf.subschemeι).obj M))
      = sheafEulerCharacteristic (k := k) D.toScheme
          ((Scheme.Modules.pullback D.idealSheaf.subschemeι).obj M) :=
    (sheafEulerCharacteristic_closedImmersion D.idealSheaf.subschemeι _).symm
  -- Step 4: χ(D, i^*M) = χ(D, O_D)
  have hB := sheafEulerCharacteristic_lineBundle_eq_unit_of_dimension_eq_zero hD hd0
    ((Scheme.Modules.pullback D.idealSheaf.subschemeι).obj M)
  -- Step 5: χ(D, O_D) = deg [D]_0
  have hC := sheafEulerCharacteristic_eq_degree_fundamentalCycle D.toScheme hD hd0
  -- Step 6: deg (D.idealSheaf.cycle 0) = deg [D]_0
  have hdesc : PushforwardDescends D.idealSheaf.subschemeι 0 :=
    D.idealSheaf.pushforwardDescends_subschemeι (k := k) 0
  have hmemZ : D.toScheme.fundamentalCycle 0 ∈ cycleSubgroup D.toScheme 0 :=
    (mem_cycleSubgroup_iff_pointClosureDimension _).mpr fun x hx => by
      by_contra h
      exact hx (if_neg h)
  have hZ' := properPushforward_mem_cycleSubgroup D.idealSheaf.subschemeι 0 hdesc ⟨_, hmemZ⟩
  have hdeg := MiyaokaMori.ChowDegreeRatPushforward.degree_properPushforward hD hX
    D.idealSheaf.subschemeι ⟨_, hmemZ⟩ hZ'
  unfold EffectiveCartierDivisor.degreeOver
  rw [hA, hB, hC, D.idealSheaf.cycle_eq_properPushforward 0]
  exact hdeg.symm

end AlgebraicGeometry

end
