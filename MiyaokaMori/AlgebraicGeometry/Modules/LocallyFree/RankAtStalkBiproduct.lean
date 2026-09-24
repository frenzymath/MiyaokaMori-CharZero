import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.ModulesBiproductLocallyFree
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.LocalTrivializationPullback
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.RankAtStalkLocalIso
import MiyaokaMori.AlgebraicGeometry.Modules.FiniteTypeRestrictFreeIndexFinite

/-! # The rank of a biproduct at a stalk

The biproduct of a finite family `G : ι → X.Modules` of locally free sheaves of finite type has, at
every point, rank equal to the sum of the ranks: `rankAtStalk (⨁ G) x = Σ_i rankAtStalk (G i) x`.

Proof sketch:
1. Each `G i` has a trivialization `(G i)|_U ≅ O_U^{(I_i)}` near `x` (`LocalTrivializationPullback`);
   `exists_common_open` shrinks the finitely many neighbourhoods to a common `V ∋ x`
   (`pullback_iso_free_of_le`).
2. Finite type gives `I_i` finite (`finite_index_of_restrict_iso_free`).
3. Pullback preserves finite biproducts (`Functor.mapBiproduct`), and a finite biproduct of free
   sheaves is the free sheaf on the disjoint union of the index types (`biproduct_iso_free`), so
   `(⨁ G)|_V ≅ O_V^{(Σ_i I_i)}`.
4. `rankAtStalk_of_restrict_iso_free` gives
   `rankAtStalk (⨁ G) x = #(Σ_i I_i) = Σ_i #I_i = Σ_i rankAtStalk (G i) x`.

Reference: Stacks 01C9 (the rank of locally free sheaves is additive), biproduct case. Used for the
rank `r` of the split weighted bundle `⊕_i Q_i` (§2 of the paper).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem AlgebraicGeometry.Scheme.Modules.rankAtStalk_biproduct {X : AlgebraicGeometry.Scheme.{u}}
    {ι : Type} [Fintype ι] (G : ι → X.Modules) [∀ i, (G i).IsLocallyFree]
    [∀ i, (G i).IsFiniteType] (x : X) :
    AlgebraicGeometry.Scheme.Modules.rankAtStalk (CategoryTheory.Limits.biproduct G) x =
      ∑ i, AlgebraicGeometry.Scheme.Modules.rankAtStalk (G i) x := by
  classical
  obtain ⟨V, hxV, hV⟩ := AlgebraicGeometry.Scheme.Modules.exists_common_open (ι := ι) x
    (fun i U => ∃ I : Type u, Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback U.ι).obj (G i) ≅
      SheafOfModules.free (R := U.toScheme.ringCatSheaf) I))
    (fun i V U hVU ⟨I, ⟨e⟩⟩ => ⟨I, AlgebraicGeometry.Scheme.Modules.pullback_iso_free_of_le (G i) hVU I e⟩)
    (fun i => by
      obtain ⟨U, I, hx, he⟩ :=
        AlgebraicGeometry.Scheme.Modules.exists_pullback_iso_free_of_isLocallyFree (G i) x
      exact ⟨U, hx, I, he⟩)
  choose I e using hV
  have hfin : ∀ i, Finite (I i) := fun i =>
    AlgebraicGeometry.Scheme.Modules.finite_index_of_restrict_iso_free (G i) V (I i) (e i).some x hxV
  let _ : ∀ i, Fintype (I i) := fun i => Fintype.ofFinite (I i)
  obtain ⟨ebig⟩ := AlgebraicGeometry.Scheme.Modules.biproduct_iso_free
    (fun i => (AlgebraicGeometry.Scheme.Modules.pullback V.ι).obj (G i)) I (fun i => (e i).some)
  have hiso : (AlgebraicGeometry.Scheme.Modules.pullback V.ι).obj (CategoryTheory.Limits.biproduct G) ≅
      SheafOfModules.free (R := V.toScheme.ringCatSheaf) (Σ i, I i) :=
    (AlgebraicGeometry.Scheme.Modules.pullback V.ι).mapBiproduct G ≪≫ ebig
  rw [AlgebraicGeometry.Scheme.Modules.rankAtStalk_of_restrict_iso_free
    (CategoryTheory.Limits.biproduct G) V (Σ i, I i) hiso x hxV, Fintype.card_sigma]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [AlgebraicGeometry.Scheme.Modules.rankAtStalk_of_restrict_iso_free (G i) V (I i) (e i).some x hxV]

end
