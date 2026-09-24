import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorMonoidalIso
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensor
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProperOverField
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.SchemeDimension
import MiyaokaMori.AlgebraicGeometry.Chow.Snapper.Stacks0ber

/-! # The Snapper intersection number vanishes when a factor is trivial

Let `X` be proper over a field `k` with `dim X = d`, and `L_1, …, L_d` invertible sheaves. If some factor
`L_i ≅ O_X`, then `(L_1⋯L_d·X) = 0`. This bypasses Stacks 0BEU (which assumes `dim D = d−1`) in the
case `D = ∅` (`O(D) ≅ O_X`).

Proof:
1. For any family `L` and index `i`: `L_i ≅ L_i ⊗ O_X` (inverse of the right unitor, transported to
   `Modules.tensor`). Additivity (Stacks 0BER) gives `(L) = (L[i ↦ L_i]) + (L[i ↦ O_X])`, and
   `L[i ↦ L_i] = L` (`Function.update_eq_self`), hence `(L[i ↦ O_X]) = 0`.
2. If `L_i ≅ O_X`, then `L_i ≅ O_X ⊗ O_X`, and additivity again gives
   `(L) = (L[i ↦ O_X]) + (L[i ↦ O_X]) = 0 + 0`.

Source: a consequence of Stacks 0BER; the case `D = ∅` in the proof of Stacks 0BFI.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- `M ≅ M ⊗ O_X` (spelled with `Modules.tensor`). -/
noncomputable def AlgebraicGeometry.Scheme.Modules.isoTensorUnit {X : AlgebraicGeometry.Scheme.{u}}
    (M : X.Modules) :
    M ≅ AlgebraicGeometry.Scheme.Modules.tensor M (SheafOfModules.unit X.ringCatSheaf : X.Modules) :=
  (CategoryTheory.MonoidalCategoryStruct.rightUnitor (C := X.Modules) M).symm ≪≫
    (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj M
      (SheafOfModules.unit X.ringCatSheaf : X.Modules)).symm

private theorem isLineBundle_update {X : AlgebraicGeometry.Scheme.{u}} {d : ℕ}
    (L : Fin d → X.Modules) [∀ i, (L i).IsLineBundle] (i : Fin d) (M : X.Modules)
    [M.IsLineBundle] : ∀ j, (Function.update L i M j).IsLineBundle := by
  intro j
  by_cases h : j = i
  · subst h; simpa using (inferInstance : M.IsLineBundle)
  · simpa [Function.update_of_ne h] using (inferInstance : (L j).IsLineBundle)

/-- Replacing the `i`-th factor by `O_X` gives intersection number `0`. -/
theorem AlgebraicGeometry.snapperIntersection_update_unit {k : Type u} [Field k]
    (X : AlgebraicGeometry.Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (hX : IsProperOver k X) {d : ℕ} (hd : X.dimension = d) (L : Fin d → X.Modules)
    [∀ i, (L i).IsLineBundle] (i : Fin d)
    [∀ j, (Function.update L i (SheafOfModules.unit X.ringCatSheaf : X.Modules) j).IsLineBundle] :
    AlgebraicGeometry.snapperIntersection X hX hd
      (Function.update L i (SheafOfModules.unit X.ringCatSheaf : X.Modules)) = 0 := by
  have hself : ∀ j, (Function.update L i (L i) j).IsLineBundle := isLineBundle_update L i (L i)
  have h := AlgebraicGeometry.snapperIntersection_tensor X hX hd L i (L i)
    (SheafOfModules.unit X.ringCatSheaf : X.Modules)
    (AlgebraicGeometry.Scheme.Modules.isoTensorUnit (L i))
  have hL : AlgebraicGeometry.snapperIntersection X hX hd (Function.update L i (L i))
      = AlgebraicGeometry.snapperIntersection X hX hd L := by
    congr 1
    · exact Function.update_eq_self i L
  rw [hL] at h
  linarith

/-- The intersection number vanishes when some factor `L_i ≅ O_X` (the bypass of 0BEU for `D = ∅`). -/
theorem AlgebraicGeometry.snapperIntersection_eq_zero_of_iso_unit {k : Type u} [Field k]
    (X : AlgebraicGeometry.Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (hX : IsProperOver k X) {d : ℕ} (hd : X.dimension = d) (L : Fin d → X.Modules)
    [∀ i, (L i).IsLineBundle] (i : Fin d)
    (e : L i ≅ (SheafOfModules.unit X.ringCatSheaf : X.Modules)) :
    AlgebraicGeometry.snapperIntersection X hX hd L = 0 := by
  have hO : ∀ j, (Function.update L i (SheafOfModules.unit X.ringCatSheaf : X.Modules) j).IsLineBundle :=
    isLineBundle_update L i _
  have h := AlgebraicGeometry.snapperIntersection_tensor X hX hd L i
    (SheafOfModules.unit X.ringCatSheaf : X.Modules) (SheafOfModules.unit X.ringCatSheaf : X.Modules)
    (e ≪≫ AlgebraicGeometry.Scheme.Modules.isoTensorUnit _)
  rw [AlgebraicGeometry.snapperIntersection_update_unit X hX hd L i] at h
  simpa using h

end
