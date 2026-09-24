import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProjectiveOverField
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.AlgebraicGeometry.Blowup.BlowupIsoAwayFromCenter
import MiyaokaMori.AlgebraicGeometry.Varieties.Surfaces.PointBlowupSurface
import MiyaokaMori.AlgebraicGeometry.Varieties.Surfaces.SmoothProjectiveSurface
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.IntegralCurve
import MiyaokaMori.AlgebraicGeometry.Blowup.StrictTransform

/-! # The fibre of a surface after a point blowup

If the centre `p` of a point blowup lies on the fibre of `π : S → C` over `y`, the reduced support of the
new fibre is the union of the strict transforms of the components of the old fibre and the exceptional
curve, and the exceptional curve meets the rest of the fibre (proof of Lemma 5.1 of the
paper, §5: "under a point blowup the strict transforms remain smooth rational curves and the new exceptional
curve is a `P¹` meeting the remaining fiber").
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- If the fibre `π⁻¹(y)` is covered by the curves `Γ i` and `p ∈ π⁻¹(y)`, the fibre of
`pointBlowup.π S p ≫ π` over `y` is covered by the strict transforms of the `Γ i` together with the
exceptional curve. -/
theorem blowup_fiber_support {k : Type u} [Field k] [PerfectField k] {S : SmoothProjectiveSurface k}
    {C : SmoothProjectiveCurve k} (π : S.toScheme ⟶ C.toScheme) (hπ : AlgebraicGeometry.Surjective π)
    (p : S.toScheme) (hpc : IsClosed ({p} : Set S.toScheme)) (y : C.toScheme) (hp : π.base p = y)
    {ι : Type} [Fintype ι] {Γ : ι → IntegralCurve k S.toScheme}
    (hcov : (⋃ i, Set.range (Γ i).ι.base) = π.base ⁻¹' {y}) :
    ((pointBlowup.π S p hpc ≫ π).base ⁻¹' {y}
       = Set.range (pointBlowup.exceptional S p hpc).ι.base
         ∪ ⋃ i, Set.range (strictTransform p hpc (Γ i)).ι.base)
    ∧ (∃ i, (Set.range (pointBlowup.exceptional S p hpc).ι.base
              ∩ Set.range (strictTransform p hpc (Γ i)).ι.base).Nonempty) := by
  let b := pointBlowup.π S p hpc
  have hproperSource : AlgebraicGeometry.IsProper
      ((pointBlowup S p hpc).toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ((isProjectiveOver_iff_isProper_and_isAmple k _).mp
      (pointBlowup S p hpc).toSmoothProjectiveVariety.projective).1
  letI : AlgebraicGeometry.IsProper
      ((pointBlowup S p hpc).toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    hproperSource
  have hcomp : b ≫ (S.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      ((pointBlowup S p hpc).toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := rfl
  have hproperComp : AlgebraicGeometry.IsProper
      (b ≫ (S.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) := by
    rw [hcomp]
    exact hproperSource
  letI : AlgebraicGeometry.IsProper
      (b ≫ (S.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) := hproperComp
  haveI : AlgebraicGeometry.IsProper b := by
    exact AlgebraicGeometry.IsProper.of_comp b
      (S.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
  haveI : AlgebraicGeometry.Surjective b := inferInstance
  constructor
  · apply Set.Subset.antisymm
    · intro x hx
      have hx' : π.base (b.base x) = y := by
        simpa only [AlgebraicGeometry.Scheme.Hom.comp_base, TopCat.coe_comp,
          Function.comp_apply, Set.mem_preimage, Set.mem_singleton_iff] using hx
      have hbx : b.base x ∈ ⋃ i, Set.range (Γ i).ι.base := by
        rw [hcov]
        simpa using hx'
      simp only [Set.mem_iUnion] at hbx
      obtain ⟨i, hxi⟩ := hbx
      by_cases hxp : b.base x = p
      · left
        rw [pointBlowup.range_exceptional S p hpc]
        simpa using hxp
      · right
        rw [Set.mem_iUnion]
        refine ⟨i, ?_⟩
        rw [strictTransform_range]
        exact subset_closure ⟨hxi, by simpa using hxp⟩
    · intro x hx
      rcases hx with hxE | hxT
      · have hxp : b.base x = p := by
          rw [pointBlowup.range_exceptional S p hpc] at hxE
          simpa using hxE
        change π.base (b.base x) = y
        rw [hxp, hp]
      · simp only [Set.mem_iUnion] at hxT
        obtain ⟨i, hxi⟩ := hxT
        rw [strictTransform_range] at hxi
        have hsub :
            closure (b.base ⁻¹' (Set.range (Γ i).ι.base \ {p})) ⊆
              b.base ⁻¹' Set.range (Γ i).ι.base := by
          apply closure_minimal
          · exact Set.preimage_mono Set.diff_subset
          · exact (Γ i).ι.isClosedEmbedding.isClosed_range.preimage b.continuous
        have hbxΓ : b.base x ∈ Set.range (Γ i).ι.base := hsub hxi
        have hbx : b.base x ∈ π.base ⁻¹' {y} := by
          rw [← hcov]
          exact Set.mem_iUnion.mpr ⟨i, hbxΓ⟩
        simpa only [AlgebraicGeometry.Scheme.Hom.comp_base, TopCat.coe_comp,
          Function.comp_apply, Set.mem_preimage, Set.mem_singleton_iff] using hbx
  · have hpFiber : p ∈ π.base ⁻¹' {y} := by simpa using hp
    have hpUnion : p ∈ ⋃ i, Set.range (Γ i).ι.base := by
      rw [hcov]
      exact hpFiber
    simp only [Set.mem_iUnion] at hpUnion
    obtain ⟨i, hpi⟩ := hpUnion
    obtain ⟨z, hz⟩ := hpi
    have hnontr : Nontrivial (Γ i).carrier := by
      by_contra hnt
      letI : Subsingleton (Γ i).carrier := not_nontrivial_iff_subsingleton.mp hnt
      haveI : DiscreteTopology (Γ i).carrier := by infer_instance
      have hle : topologicalKrullDim (Γ i).carrier ≤ 0 :=
        topologicalKrullDim_zero_of_discreteTopology (Γ i).carrier
      rw [(Γ i).dim_eq_one] at hle
      norm_num at hle
    letI : Nontrivial (Γ i).carrier := hnontr
    obtain ⟨z', hz'⟩ := exists_ne z
    have hz'image : (Γ i).ι.base z' ≠ p := by
      intro hz'p
      apply hz'
      apply (Γ i).ι.isClosedEmbedding.injective
      exact hz'p.trans hz.symm
    have hdiffne : (Set.range (Γ i).ι.base \ {p}).Nonempty :=
      ⟨(Γ i).ι.base z', ⟨z', rfl⟩, by simpa using hz'image⟩
    have hirr : IsPreirreducible (Set.range (Γ i).ι.base) := by
      rw [← Set.image_univ]
      exact PreirreducibleSpace.isPreirreducible_univ.image
        (Γ i).ι.base (Γ i).ι.continuous.continuousOn
    have hdense : Set.range (Γ i).ι.base ⊆
        closure (Set.range (Γ i).ι.base \ {p}) := by
      simpa [Set.diff_eq] using
        (subset_closure_inter_of_isPreirreducible_of_isOpen hirr hpc.isOpen_compl
          (by simpa [Set.diff_eq] using hdiffne))
    have hpclosure : p ∈ closure (Set.range (Γ i).ι.base \ {p}) := hdense ⟨z, hz⟩
    let T := Set.range (strictTransform p hpc (Γ i)).ι.base
    have hTclosed : IsClosed T :=
      (strictTransform p hpc (Γ i)).ι.isClosedEmbedding.isClosed_range
    have himageClosed : IsClosed (b.base '' T) := b.isClosedMap T hTclosed
    have hdiffsub : Set.range (Γ i).ι.base \ {p} ⊆ b.base '' T := by
      intro q hq
      obtain ⟨x, hx⟩ := b.surjective q
      refine ⟨x, ?_, hx⟩
      dsimp [T]
      rw [strictTransform_range]
      apply subset_closure
      change b.base x ∈ Set.range (Γ i).ι.base \ {p}
      rwa [hx]
    have hpimage : p ∈ b.base '' T :=
      (closure_minimal hdiffsub himageClosed) hpclosure
    obtain ⟨x, hxT, hxp⟩ := hpimage
    refine ⟨i, x, ?_, hxT⟩
    rw [pointBlowup.range_exceptional S p hpc]
    simpa using hxp

end
