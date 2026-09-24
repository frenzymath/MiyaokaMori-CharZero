import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.IdealSheafStalkIdeal
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.IdealSheafStalkIdealEqMapGerm

/-! # Basic properties of the stalk ideal

The stalk ideal of a product is the product of the stalk ideals (also for finite products), and
outside the support the stalk ideal is the unit ideal.

References: Stacks 01QZ; Atiyah–Macdonald Prop 3.11(v) (extension of ideals commutes with
products).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open AlgebraicGeometry AlgebraicGeometry.Scheme

theorem AlgebraicGeometry.Scheme.exists_affineOpens_mem (X : AlgebraicGeometry.Scheme.{u}) (x : X) :
    ∃ U : X.affineOpens, x ∈ U.1 := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  exact ⟨⟨U, hU⟩, hxU⟩

theorem AlgebraicGeometry.Scheme.IdealSheafData.stalkIdeal_mul
    {X : AlgebraicGeometry.Scheme.{u}} (I J : X.IdealSheafData) (x : X) :
    (I * J).stalkIdeal x = I.stalkIdeal x * J.stalkIdeal x := by
  obtain ⟨U, hx⟩ := X.exists_affineOpens_mem x
  rw [stalkIdeal_eq_map_germ _ x U hx, stalkIdeal_eq_map_germ I x U hx,
    stalkIdeal_eq_map_germ J x U hx, IdealSheafData.ideal_mul, Pi.mul_apply, Ideal.map_mul]

theorem AlgebraicGeometry.Scheme.IdealSheafData.stalkIdeal_top
    {X : AlgebraicGeometry.Scheme.{u}} (x : X) :
    (⊤ : X.IdealSheafData).stalkIdeal x = ⊤ := by
  obtain ⟨U, hx⟩ := X.exists_affineOpens_mem x
  rw [stalkIdeal_eq_map_germ _ x U hx, IdealSheafData.ideal_top, Pi.top_apply, Ideal.map_top]

theorem AlgebraicGeometry.Scheme.IdealSheafData.stalkIdeal_finset_prod
    {X : AlgebraicGeometry.Scheme.{u}} {ι : Type*} (T : Finset ι) (I : ι → X.IdealSheafData) (x : X) :
    (∏ i ∈ T, I i).stalkIdeal x = ∏ i ∈ T, (I i).stalkIdeal x := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    rw [Ideal.one_eq_top]
    exact stalkIdeal_top x
  | insert i T hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, stalkIdeal_mul, ih]

/-- Outside the support of `I` the stalk ideal is the unit ideal. -/
theorem AlgebraicGeometry.Scheme.IdealSheafData.stalkIdeal_eq_top_of_notMem_support
    {X : AlgebraicGeometry.Scheme.{u}} (I : X.IdealSheafData) (x : X)
    (hx : x ∉ I.support) : I.stalkIdeal x = ⊤ := by
  obtain ⟨U, hxU⟩ := X.exists_affineOpens_mem x
  rw [stalkIdeal_eq_map_germ I x U hxU]
  rw [IdealSheafData.mem_support_iff_of_mem hxU, AlgebraicGeometry.Scheme.mem_zeroLocus_iff] at hx
  simp only [not_forall] at hx
  obtain ⟨s, hs, hxs⟩ := hx
  rw [not_not] at hxs
  have hunit : IsUnit ((X.presheaf.germ U.1 x hxU).hom s) :=
    (AlgebraicGeometry.Scheme.mem_basicOpen X s x hxU).mp hxs
  exact Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hs) hunit

end
