import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ChowDegreeRat
import MiyaokaMori.AlgebraicGeometry.Chow.RationalEquivalence.ChowGroupRational
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.EulerCharZeroDimDegree
import MiyaokaMori.AlgebraicGeometry.Chow.FirstChernClass
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProjectiveOverField
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProperOverField
import MiyaokaMori.AlgebraicGeometry.Chow.DivisorOperator.RatDivisorOperator
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.SchemeDimension
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.SchemeFundamentalCycle
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ZeroCycleDegreeScheme
import MiyaokaMori.AlgebraicGeometry.Chow.Snapper.Stacks0bep

/-! # Snapper = Chow in dimension zero

Let `P(k, d)` be the statement "for every `d`-dimensional locally Noetherian scheme `X` proper over the
field `k` and any `d` invertible sheaves `L_1, …, L_d` on `X`, the intersection number `(L_1⋯L_d·X)`
defined by `χ` (Stacks 0BEP) equals `deg(c_1(L_1) ∩ ⋯ ∩ c_1(L_d) ∩ [X]_d)`" (in Lean:
`AlgebraicGeometry.SnapperEqChowInDim k d`). This file proves `P(k, 0)`.

Proof:
1. For `d = 0` the index set `Fin 0` is empty: the sum on the left has only the term `S = ∅`, with sign
   `(−1)^0 = 1`, and the empty tensor product is `O_X`, so the left side is `χ(X, O_X)` (unfold the
   definition of `snapperIntersection`).
2. Right side: `Finset.univ.toList = []` and `capProd` is the identity, so the right side is
   `deg(1 ⊗ [X]_0) = deg [X]_0` (`degree_tmul`; `ChowGroup.degreeOver` on `ChowGroup.mk` is by definition
   `AlgebraicCycle.degree`).
3. `χ(X, O_X) = deg [X]_0` (`EulerCharZeroDimDegree.lean`).

Source: the first paragraph of the proof of Stacks 0BFI (`d = 0` uses 0AYT).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The equality at a single `(X, L)`: the intersection number defined by `χ` equals the Chow intersection
number. -/
def AlgebraicGeometry.SnapperEqChowFor {k : Type u} [Field k]
    (X : AlgebraicGeometry.Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (hX : IsProperOver k X) [AlgebraicGeometry.IsLocallyNoetherian X]
    {d : ℕ} (hd : X.dimension = d) (L : Fin d → X.Modules) [∀ i, (L i).IsLineBundle] : Prop :=
  AlgebraicGeometry.snapperIntersection X hX hd L
    = AlgebraicGeometry.ChowGroupRat.degree X hX
        (AlgebraicGeometry.RatDivisorOp.capProd
          (fun i => AlgebraicGeometry.ratDivisorOpOfLineBundle (L i)) 0
          ((by simp : d = 0 + Fintype.card (Fin d)) ▸
            ((1 : ℚ) ⊗ₜ[ℤ] X.fundamentalChowClass d)))

/-- `P(k, d)`: the Snapper intersection number equals the Chow intersection number in dimension `d`, stated
simultaneously for all locally Noetherian schemes **projective** over `k` and all families of invertible
sheaves (in the induction `X` is replaced by `d`-dimensional integral closed subschemes and effective
Cartier divisors, so one must quantify over all `X`; both are closed subschemes of `X`, and projectivity
passes down by `IsProjectiveOver.of_isClosedImmersion`). The quantifier is "projective over `k`" rather
than "proper over `k`": this avoids Chow's lemma (Stacks 0200) and 0BET, and the schemes to which 0BFI is
applied in the paper are all projective. -/
def AlgebraicGeometry.SnapperEqChowInDim (k : Type u) [Field k] (d : ℕ) : Prop :=
  ∀ (X : AlgebraicGeometry.Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (hX : IsProperOver k X) (_ : IsProjectiveOver k X)
    [AlgebraicGeometry.IsLocallyNoetherian X]
    (hd : X.dimension = d) (L : Fin d → X.Modules) [∀ i, (L i).IsLineBundle],
    AlgebraicGeometry.SnapperEqChowFor X hX hd L

private theorem capList_of_eq_nil {X : AlgebraicGeometry.Scheme.{u}}
    (l : List (AlgebraicGeometry.RatDivisorOp X)) (hl : l = []) {b : ℕ} (h1 : 0 = b)
    (h2 : b = 0 + l.length) (z : AlgebraicGeometry.ChowGroupRat X 0) :
    AlgebraicGeometry.RatDivisorOp.capList l 0 (AlgebraicGeometry.ChowGroupRat.congr X h2 (h1 ▸ z)) = z := by
  subst hl; subst h1; rfl

/-- `P(k, 0)`: in dimension zero both intersection numbers equal `χ(X, O_X) = deg [X]_0`. -/
theorem AlgebraicGeometry.snapperEqChowInDim_zero (k : Type u) [Field k] :
    AlgebraicGeometry.SnapperEqChowInDim k 0 := by
  intro X _ hX _ _ hd L _
  unfold AlgebraicGeometry.SnapperEqChowFor
  have hR : AlgebraicGeometry.RatDivisorOp.capProd
      (fun i => AlgebraicGeometry.ratDivisorOpOfLineBundle (L i)) 0
      ((by simp : (0 : ℕ) = 0 + Fintype.card (Fin 0)) ▸
        (((1 : ℚ) ⊗ₜ[ℤ] X.fundamentalChowClass 0 : TensorProduct ℤ ℚ _) :
          AlgebraicGeometry.ChowGroupRat X 0))
      = ((1 : ℚ) ⊗ₜ[ℤ] X.fundamentalChowClass 0 : TensorProduct ℤ ℚ _) := by
    unfold AlgebraicGeometry.RatDivisorOp.capProd
    rw [LinearMap.comp_apply]
    exact capList_of_eq_nil _ (by simp) (by simp) _ _
  rw [hR, AlgebraicGeometry.ChowGroupRat.degree_tmul, one_mul]
  have hL : AlgebraicGeometry.snapperIntersection X hX hd L
      = (AlgebraicGeometry.sheafEulerCharacteristic (k := k) X
          (SheafOfModules.unit X.ringCatSheaf) : ℚ) := by
    unfold AlgebraicGeometry.snapperIntersection
    rw [Fintype.sum_unique]
    simp
    rfl
  rw [hL, AlgebraicGeometry.sheafEulerCharacteristic_eq_degree_fundamentalCycle X hX hd]
  rfl

end
