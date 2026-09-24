import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.PointIdealSheaf
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.PointIdealSheafSupport
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.PointIdealSheafStalk
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.IdealSheafStalkIdealBasic

/-! # Ideal sheaves with prescribed finite cosupport and stalks

The ideal sheaf `∏_{x∈T} pointIdealSheaf x q_x` determined by a finite set of closed points `T`
and `𝔪_x`-primary ideals `q_x`: its cosupport is contained in `T`, and its stalk ideal at `x ∈ T`
is `q_x`.

References: input to Stacks 0AHH (ideal sheaves with finite cosupport); Hartshorne II
Example 7.17.3 (base ideals).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open AlgebraicGeometry AlgebraicGeometry.Scheme

theorem AlgebraicGeometry.Scheme.finitePointsIdealSheaf_support_subset
    (X : AlgebraicGeometry.Scheme.{u}) (T : Finset X)
    (q : ∀ x : X, Ideal (X.presheaf.stalk x))
    (hT : ∀ x ∈ T, IsClosed ({x} : Set X))
    (hq : ∀ x ∈ T, ∃ n : ℕ, IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ n ≤ q x) :
    ((X.finitePointsIdealSheaf T q).support : Set X) ⊆ (T : Set X) := by
  classical
  unfold AlgebraicGeometry.Scheme.finitePointsIdealSheaf
  induction T using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty]
    intro y hy
    have h : ((1 : X.IdealSheafData).support : Set X) = ∅ := by
      change ((⊤ : X.IdealSheafData).support : Set X) = ∅
      rw [IdealSheafData.support_top]; rfl
    rw [h] at hy
    exact hy.elim
  | insert i T hi ih =>
    rw [Finset.prod_insert hi, IdealSheafData.support_mul]
    intro y hy
    rcases hy with hy | hy
    · obtain ⟨n, hn⟩ := hq i (Finset.mem_insert_self i T)
      have := X.pointIdealSheaf_support_subset i (hT i (Finset.mem_insert_self i T)) (q i) n hn hy
      rw [Set.mem_singleton_iff] at this
      rw [this]; exact Finset.mem_insert_self i T
    · exact Finset.mem_insert_of_mem
        (ih (fun x hx => hT x (Finset.mem_insert_of_mem hx))
          (fun x hx => hq x (Finset.mem_insert_of_mem hx)) hy)

theorem AlgebraicGeometry.Scheme.finitePointsIdealSheaf_stalkIdeal
    (X : AlgebraicGeometry.Scheme.{u}) (T : Finset X)
    (q : ∀ x : X, Ideal (X.presheaf.stalk x))
    (hT : ∀ x ∈ T, IsClosed ({x} : Set X))
    (hq : ∀ x ∈ T, ∃ n : ℕ, IsLocalRing.maximalIdeal (X.presheaf.stalk x) ^ n ≤ q x)
    (x : X) (hx : x ∈ T) :
    (X.finitePointsIdealSheaf T q).stalkIdeal x = q x := by
  classical
  unfold AlgebraicGeometry.Scheme.finitePointsIdealSheaf
  rw [IdealSheafData.stalkIdeal_finset_prod, Finset.prod_eq_single x]
  · obtain ⟨n, hn⟩ := hq x hx
    exact X.pointIdealSheaf_stalkIdeal x (q x) n hn
  · intro y hy hyx
    rw [Ideal.one_eq_top]
    apply IdealSheafData.stalkIdeal_eq_top_of_notMem_support
    intro hmem
    obtain ⟨n, hn⟩ := hq y hy
    have := X.pointIdealSheaf_support_subset y (hT y hy) (q y) n hn hmem
    exact hyx (Set.mem_singleton_iff.mp this).symm
  · intro h; exact (h hx).elim

end
