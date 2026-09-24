import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.ModulesPow
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpaceTwistTensor
import MiyaokaMori.AlgebraicGeometry.Cohomology.Coherent.Stacks01xt
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.Stacks02uzExactAux

/-! # Cohomology of twisted finite direct sums of twisting sheaves

Cohomology of a twisted finite direct sum of twisting sheaves on `P^N_k` (the "free part" of the
descending induction in Stacks 0B5T(4) / 01YS): for `d : Fin r → ℤ` and `p > 0` there is `n₀` with

  `H^p(P^N, (⨁_j O(d_j)) ⊗ O(n)) = 0` for all `n ≥ n₀`.

Proof.
1. `(⨁_j O(d_j)) ⊗ O(n) ≅ ⨁_j (O(d_j) ⊗ O(n)) ≅ ⨁_j O(d_j + n)`: `− ⊗ O(n)` is an autoequivalence of
   `P^N.Modules` (`isEquivalence_tensorRight_of_isLineBundle`), hence preserves coproducts, and finite
   biproducts are coproducts; then `O(a) ⊗ O(b) ≅ O(a + b)` (`projectiveSpaceTwist_tensor`).
2. `H^p` of a finite biproduct of abelian sheaves is the biproduct of the `H^p` (`Sheaf.functorH` is additive,
   hence preserves finite biproducts; the forgetful functor `SheafOfModules.toSheaf` preserves finite
   limits, hence finite biproducts), and a finite biproduct of zero objects is zero (`biproduct.total`).
3. Take `n₀ := max_j (−N − d_j)⁺`. For `n ≥ n₀` and every `j` we have `d_j + n ≥ −N > −(N + 1)`, so
   `H^p(P^N, O(d_j + n)) = 0` for `p > 0` by the explicit computation of Stacks 01XT
   (`subsingleton_sheafCohomology_projectiveSpaceTwist`): the only non-zero groups
   are `H^0(O(m))` for `m ≥ 0` and `H^N(O(m))` for `m ≤ −N − 1`.

Source: Stacks 01XT, 01YS (proof), 0B5T (proof of (4)).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w w'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry CategoryTheory.MonoidalCategory

noncomputable section

/-- `H^p` of a finite biproduct of `O_X`-modules vanishes if each `H^p (g i)` does. Proof: apply the
additive functor `Φ := toSheaf ⋙ functorH p` to `𝟙 = ∑ π_j ≫ ι_j` (`biproduct.total`); each summand
factors through the zero object `Φ.obj (g j)`, so `𝟙 (Φ.obj (⨁ g)) = 0`. -/
theorem AlgebraicGeometry.Scheme.Modules.subsingleton_H_biproduct {X : AlgebraicGeometry.Scheme.{u}}
    {ι : Type} [Fintype ι] (g : ι → X.Modules) (p : ℕ)
    [∀ i, Subsingleton (CategoryTheory.Sheaf.H (g i).toAddCommGrpSheaf p)] :
    Subsingleton (CategoryTheory.Sheaf.H (⨁ g).toAddCommGrpSheaf p) := by
  haveI hT : (SheafOfModules.toSheaf X.ringCatSheaf : X.Modules ⥤ _).Additive :=
    inferInstanceAs (SheafOfModules.toSheaf X.ringCatSheaf).Additive
  haveI hΦ : ((SheafOfModules.toSheaf X.ringCatSheaf : X.Modules ⥤ _) ⋙
      CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) p).Additive := inferInstance
  let Φ : X.Modules ⥤ AddCommGrpCat.{u} :=
    (SheafOfModules.toSheaf X.ringCatSheaf : X.Modules ⥤ _) ⋙
      CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) p
  haveI : Φ.Additive := hΦ
  haveI : ∀ i, Subsingleton ((Φ.obj (g i) : AddCommGrpCat.{u}) : Type u) := fun i =>
    inferInstanceAs (Subsingleton (CategoryTheory.Sheaf.H (g i).toAddCommGrpSheaf p))
  have hz : ∀ i, IsZero (Φ.obj (g i)) := fun i => AddCommGrpCat.isZero_of_subsingleton _
  have htot : (∑ j, biproduct.π g j ≫ biproduct.ι g j) = 𝟙 (⨁ g) := biproduct.total
  have h1 : 𝟙 (Φ.obj (⨁ g)) = 0 := by
    rw [← Φ.map_id, ← htot, Φ.map_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [Φ.map_comp, (hz j).eq_zero_of_tgt (Φ.map (biproduct.π g j)), zero_comp]
  exact AddCommGrpCat.subsingleton_of_isZero ((IsZero.iff_id_eq_zero _).mpr h1)

/-- `(⨁_j O(d_j)) ⊗ O(n) ≅ ⨁_j O(d_j + n)` on `P^N_k`. -/
theorem biproduct_projectiveSpaceTwist_tensor_twist_iso {k : Type u} [Field k] (N : ℕ) {r : ℕ}
    (d : Fin r → ℤ) (n : ℤ) :
    Nonempty ((CategoryTheory.Limits.biproduct (fun j => projectiveSpaceTwist k N (d j))).tensor
        (projectiveSpaceTwist k N n) ≅
      CategoryTheory.Limits.biproduct (fun j => projectiveSpaceTwist k N (d j + n))) := by
  let B := projectiveSpaceTwist k N n
  let f : Fin r → (ProjectiveSpace N k).Modules := fun j => projectiveSpaceTwist k N (d j)
  haveI : (CategoryTheory.MonoidalCategory.tensorRight B).IsEquivalence :=
    AlgebraicGeometry.Scheme.Modules.isEquivalence_tensorRight_of_isLineBundle B
  have e₁ : (⨁ f) ⊗ B ≅ ⨁ fun j => f j ⊗ B :=
    (CategoryTheory.MonoidalCategory.tensorRight B).mapIso (biproduct.isoCoproduct f) ≪≫
      PreservesCoproduct.iso (CategoryTheory.MonoidalCategory.tensorRight B) f ≪≫
      (biproduct.isoCoproduct (fun j => f j ⊗ B)).symm
  have e₂ : ∀ j, f j ⊗ B ≅ projectiveSpaceTwist k N (d j + n) := fun j =>
    (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj (f j) B).symm ≪≫
      (projectiveSpaceTwist_tensor N (d j) n).some
  exact ⟨AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj (⨁ f) B ≪≫ e₁ ≪≫
    biproduct.mapIso e₂⟩

/-- **Vanishing of the free part** (Stacks 01XT + 01YS): for `d : Fin r → ℤ` and `p > 0`,
`H^p(P^N, (⨁_j O(d_j)) ⊗ O(n)) = 0` for all `n ≥ max_j (−N − d_j)⁺`. -/
theorem AlgebraicGeometry.subsingleton_H_biproduct_twists_tensor_twist {k : Type u} [Field k] (N : ℕ)
    {r : ℕ} (d : Fin r → ℤ) (p : ℕ) (hp : 0 < p) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, Subsingleton (CategoryTheory.Sheaf.H
      ((CategoryTheory.Limits.biproduct (fun j => projectiveSpaceTwist k N (d j))).tensor
        (projectiveSpaceTwist k N n)).toAddCommGrpSheaf p) := by
  refine ⟨Finset.univ.sup (fun j => Int.toNat (-(N : ℤ) - d j)), fun n hn => ?_⟩
  obtain ⟨e⟩ := biproduct_projectiveSpaceTwist_tensor_twist_iso (k := k) N d n
  haveI hz : ∀ j, Subsingleton (CategoryTheory.Sheaf.H
      (projectiveSpaceTwist k N (d j + n)).toAddCommGrpSheaf p) := by
    intro j
    have h₁ : Int.toNat (-(N : ℤ) - d j) ≤ n :=
      (Finset.le_sup (f := fun j => Int.toNat (-(N : ℤ) - d j)) (Finset.mem_univ j)).trans hn
    have h₂ : -(N : ℤ) - d j ≤ n := Int.toNat_le.mp h₁
    exact subsingleton_sheafCohomology_projectiveSpaceTwist N (d j + n) p
      (fun h => by omega) (fun h => by omega)
  haveI : Subsingleton (CategoryTheory.Sheaf.H
      (⨁ fun j => projectiveSpaceTwist k N (d j + n)).toAddCommGrpSheaf p) :=
    AlgebraicGeometry.Scheme.Modules.subsingleton_H_biproduct
      (fun j => projectiveSpaceTwist k N (d j + n)) p
  exact CategoryTheory.Sheaf.subsingleton_H_of_iso
    ((SheafOfModules.toSheaf.{u} (ProjectiveSpace N k).ringCatSheaf).mapIso e).symm p

end
