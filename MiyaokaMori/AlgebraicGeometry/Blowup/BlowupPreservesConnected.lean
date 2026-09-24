import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Blowup.BlowupIsoAwayFromCenter
import MiyaokaMori.AlgebraicGeometry.Blowup.BlowupTowerSurjective
import MiyaokaMori.AlgebraicGeometry.Varieties.Surfaces.PointBlowupSurface
import MiyaokaMori.AlgebraicGeometry.Varieties.Surfaces.SmoothProjectiveSurface
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.IntegralCurve

/-! # Point blowups preserve connected fibres

A point blowup preserves the connectedness of the reduced support of a fibre: the exceptional curve is
connected and meets the rest of the fibre (proof of Lemma 5.1 of the paper, §5).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Every fibre of the point blowup `b = pointBlowup.π S p hp` is connected.
For `q = p` the fibre is the support of the exceptional curve (`pointBlowup.range_exceptional`),
which is integral hence irreducible hence connected; for `q ≠ p` the fibre is a single point,
because `b` restricted over `{p}ᶜ` is an isomorphism (`pointBlowup_isIso_away`). -/
theorem pointBlowup.isConnected_fiber {k : Type u} [Field k] [PerfectField k]
    (S : SmoothProjectiveSurface k) (p : S.toScheme) (hp : IsClosed ({p} : Set S.toScheme))
    (q : S.toScheme) : _root_.IsConnected ((pointBlowup.π S p hp).base ⁻¹' {q}) := by
  by_cases hq : q = p
  · subst hq
    rw [← pointBlowup.range_exceptional S q hp]
    have : AlgebraicGeometry.IsIntegral (pointBlowup.exceptional S q hp).carrier :=
      (pointBlowup.exceptional S q hp).isIntegral
    exact isConnected_range (pointBlowup.exceptional S q hp).ι.base.hom.continuous
  · obtain ⟨x, hx⟩ := (pointBlowup.π_surjective S p hp).surj q
    let U : S.toScheme.Opens := ⟨{p}ᶜ, hp.isOpen_compl⟩
    have hqU : q ∈ (U : Set S.toScheme) := hq
    have : IsIso ((pointBlowup.π S p hp) ∣_ U) :=
      pointBlowup_isIso_away S p hp U (fun h => h rfl)
    have hinj := ((pointBlowup.π S p hp) ∣_ U).isOpenEmbedding.injective
    have hsing : (pointBlowup.π S p hp).base ⁻¹' {q} = {x} := by
      ext x'
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      constructor
      · intro hx'
        have hx'U : x' ∈ (pointBlowup.π S p hp) ⁻¹ᵁ U := by
          show (pointBlowup.π S p hp).base x' ∈ (U : Set S.toScheme)
          rw [hx']; exact hqU
        have hxU : x ∈ (pointBlowup.π S p hp) ⁻¹ᵁ U := by
          show (pointBlowup.π S p hp).base x ∈ (U : Set S.toScheme)
          rw [hx]; exact hqU
        have heq : ((pointBlowup.π S p hp) ∣_ U) ⟨x', hx'U⟩ = ((pointBlowup.π S p hp) ∣_ U) ⟨x, hxU⟩ := by
          apply Subtype.ext
          exact (AlgebraicGeometry.morphismRestrict_base_coe (pointBlowup.π S p hp) U ⟨x', hx'U⟩).trans
            ((hx'.trans hx.symm).trans
              (AlgebraicGeometry.morphismRestrict_base_coe (pointBlowup.π S p hp) U ⟨x, hxU⟩).symm)
        exact congrArg Subtype.val (hinj heq)
      · rintro rfl; exact hx
    rw [hsing]
    exact isConnected_singleton

/-- If the fibre of `π : S → C` over a closed point `y` is connected, so is the fibre of
`pointBlowup.π S p hp ≫ π`: the blowup is a closed surjection with connected fibres. -/
theorem blowup_fiber_connected {k : Type u} [Field k] [PerfectField k] {S : SmoothProjectiveSurface k}
    {C : SmoothProjectiveCurve k} (π : S.toScheme ⟶ C.toScheme)
    (p : S.toScheme) (hp : IsClosed ({p} : Set S.toScheme))
    (y : C.toScheme) (hy : IsClosed ({y} : Set C.toScheme))
    (h : _root_.IsConnected (π.base ⁻¹' {y})) :
    _root_.IsConnected ((pointBlowup.π S p hp ≫ π).base ⁻¹' {y}) := by
  have hpre : (pointBlowup.π S p hp ≫ π).base ⁻¹' {y} =
      (pointBlowup.π S p hp).base ⁻¹' (π.base ⁻¹' {y}) := by
    rw [AlgebraicGeometry.Scheme.Hom.comp_base]; rfl
  rw [hpre]
  -- b is proper (Bl_p S projective over k, S separated over k), hence a closed map.
  have hproperSource : AlgebraicGeometry.IsProper
      ((pointBlowup S p hp).toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ((isProjectiveOver_iff_isProper_and_isAmple k _).mp
      (pointBlowup S p hp).toSmoothProjectiveVariety.projective).1
  have hcomp : pointBlowup.π S p hp ≫ (S.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      ((pointBlowup S p hp).toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := rfl
  have hproperComp : AlgebraicGeometry.IsProper
      (pointBlowup.π S p hp ≫ (S.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) := by
    rw [hcomp]
    exact hproperSource
  have : AlgebraicGeometry.IsProper (pointBlowup.π S p hp) :=
    AlgebraicGeometry.IsProper.of_comp (pointBlowup.π S p hp)
      (S.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
  have hcl : IsClosedMap (pointBlowup.π S p hp).base := (pointBlowup.π S p hp).isClosedMap
  have hsurj : Function.Surjective (pointBlowup.π S p hp).base :=
    (pointBlowup.π_surjective S p hp).surj
  have hquot : Topology.IsQuotientMap (pointBlowup.π S p hp).base :=
    hcl.isQuotientMap (pointBlowup.π S p hp).base.hom.continuous hsurj
  exact Topology.IsCoinducing.isConnected_preimage_of_isClosed
    (pointBlowup.isConnected_fiber S p hp) hquot.isCoinducing
    (hy.preimage π.base.hom.continuous) h

end
