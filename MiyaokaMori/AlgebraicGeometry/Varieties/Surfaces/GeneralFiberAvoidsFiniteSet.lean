import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Points.ClosedPoint
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.CurveDimensionOne
import MiyaokaMori.AlgebraicGeometry.Morphisms.MorphismImageAsRange
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.AlgebraicGeometry.Varieties.Surfaces.SmoothProjectiveSurface

/-! # General fibres avoid a finite set

Given finitely many closed points of a surface, there is a nonempty open `V` of the base curve
such that the fibres over `V` avoid all of them (`V` is `C` minus the images of these points; the
image of a closed point is a closed point). A nonempty open contains a closed point (a scheme of
finite type over a field is a Jacobson space). The paper's "general fibre" is always expressed as
"there is a nonempty open `V` such that the fibre over every closed point of `V` …".
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Finitely many closed points of the surface are avoided by the fibres over a nonempty open of the
base curve. -/
theorem exists_open_avoiding {k : Type u} [Field k]
    {S : SmoothProjectiveSurface k} {C : SmoothProjectiveCurve k}
    (π : S.toScheme ⟶ C.toScheme) [π.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (Z : Finset S.toScheme) (hZ : ∀ z ∈ Z, IsClosed ({z} : Set S.toScheme)) :
    ∃ V : Set C.toScheme, IsOpen V ∧ V.Nonempty ∧
      ∀ y ∈ V, ∀ z ∈ Z, π.base z ≠ y := by
  letI : JacobsonSpace C.toScheme :=
    AlgebraicGeometry.LocallyOfFiniteType.jacobsonSpace
      (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
  have hcomp : AlgebraicGeometry.LocallyOfFiniteType
      (π ≫ (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) := by
    rw [(inferInstance : π.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))).1]
    infer_instance
  letI : AlgebraicGeometry.LocallyOfFiniteType π :=
    AlgebraicGeometry.locallyOfFiniteType_of_comp π
      (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
  let T : Set C.toScheme := π.base '' (Z : Set S.toScheme)
  have hTfin : T.Finite := by
    exact (Finset.finite_toSet Z).image π.base
  have hTclosed : IsClosed T := by
    rw [← Set.biUnion_of_singleton T]
    exact hTfin.isClosed_biUnion (fun y hy => by
      change y ∈ closedPoints C.toScheme
      obtain ⟨z, hzZ, rfl⟩ := hy
      have hzclosed : z ∈ closedPoints S.toScheme := by
        change IsClosed ({z} : Set S.toScheme)
        exact hZ z hzZ
      exact (AlgebraicGeometry.Scheme.Hom.closePoints_subset_preimage_closedPoints π) hzclosed)
  let V : Set C.toScheme := Tᶜ
  have hVopen : IsOpen V := hTclosed.isOpen_compl
  have hnontr : Nontrivial C.toScheme := by
    by_contra hnt
    letI : Subsingleton C.toScheme := not_nontrivial_iff_subsingleton.mp hnt
    haveI : DiscreteTopology C.toScheme := by infer_instance
    have hle : topologicalKrullDim C.toScheme ≤ 0 :=
      topologicalKrullDim_zero_of_discreteTopology C.toScheme
    have hdim : topologicalKrullDim C.toScheme = 1 := C.dim_one
    rw [hdim] at hle
    norm_num at hle
  have hgenclosed : ¬ IsClosed ({genericPoint C.toScheme} : Set C.toScheme) := by
    intro hgen
    have hcl : closure ({genericPoint C.toScheme} : Set C.toScheme) =
        {genericPoint C.toScheme} := closure_eq_iff_isClosed.mpr hgen
    have huniv : closure ({genericPoint C.toScheme} : Set C.toScheme) = Set.univ :=
      genericPoint_closure C.toScheme
    have heq : (Set.univ : Set C.toScheme) = {genericPoint C.toScheme} :=
      huniv.symm.trans hcl
    have hsub : Subsingleton C.toScheme := by
      constructor
      intro a b
      have ha : a ∈ ({genericPoint C.toScheme} : Set C.toScheme) := by
        rw [← heq]
        trivial
      have hb : b ∈ ({genericPoint C.toScheme} : Set C.toScheme) := by
        rw [← heq]
        trivial
      simpa only [Set.mem_singleton_iff] using ha.trans hb.symm
    exact (not_nontrivial_iff_subsingleton.mpr hsub) hnontr
  have hgenV : genericPoint C.toScheme ∈ V := by
    change genericPoint C.toScheme ∉ T
    intro hgenT
    have hgenTclosed : IsClosed ({genericPoint C.toScheme} : Set C.toScheme) := by
      change genericPoint C.toScheme ∈ closedPoints C.toScheme
      obtain ⟨z, hzZ, hz_eq⟩ := hgenT
      rw [← hz_eq]
      have hzclosed : z ∈ closedPoints S.toScheme := by
        change IsClosed ({z} : Set S.toScheme)
        exact hZ z hzZ
      exact (AlgebraicGeometry.Scheme.Hom.closePoints_subset_preimage_closedPoints π) hzclosed
    exact hgenclosed hgenTclosed
  refine ⟨V, hVopen, ⟨genericPoint C.toScheme, hgenV⟩, ?_⟩
  intro y hyV z hzZ heq
  apply hyV
  exact ⟨z, hzZ, heq⟩

/-- A nonempty open of a smooth projective curve contains a closed point. -/
theorem exists_closedPoint_mem_open {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    {V : Set C.toScheme} (hV : IsOpen V) (hne : V.Nonempty) :
    ∃ y ∈ V, IsClosed ({y} : Set C.toScheme) := by
  letI : AlgebraicGeometry.LocallyOfFiniteType
      (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    C.isOfFiniteType.toLocallyOfFiniteType
  letI : JacobsonSpace C.toScheme :=
    AlgebraicGeometry.LocallyOfFiniteType.jacobsonSpace
      (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
  obtain ⟨y, hyV, hyclosed⟩ := nonempty_inter_closedPoints
    (Z := V) hne hV.isLocallyClosed
  exact ⟨y, hyV, hyclosed⟩

end
