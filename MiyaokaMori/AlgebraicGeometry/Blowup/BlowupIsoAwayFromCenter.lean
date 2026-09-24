import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.VarietyDimension
import MiyaokaMori.AlgebraicGeometry.Blowup.BlowupIsoAwayFromCenterAffineLeaf
import MiyaokaMori.AlgebraicGeometry.Varieties.Surfaces.PointBlowupSurface

/-! # The point blowup is an isomorphism away from the centre

The blowup of a smooth surface at a closed point is an isomorphism over the complement of the centre
(Stacks 02OS(1)), and is therefore a dominant (birational) morphism. Used for the resolution
`β : S → W` of Corollary 4.3 of the paper (§4), which is an isomorphism over the
zero section.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry

/-- If the chart `S.projToOpen U : Proj S(U) → U` is an isomorphism, so is the restriction of the
structure morphism of the relative Proj to `U` (`projChart_isPullback`). -/
theorem Scheme.GradedAffineAlgebra.isIso_relativeProj_hom_restrict {X : Scheme.{u}}
    (S : X.GradedAffineAlgebra) (U : X.AffineZariskiSite) [IsIso (S.projToOpen U)] :
    IsIso (S.relativeProj.hom ∣_ U.toOpens) := by
  have h₁ := S.projChart_isPullback U
  have h₂ := isPullback_morphismRestrict S.relativeProj.hom U.toOpens
  have he : (h₁.isoIsPullback _ _ h₂).inv ≫ S.projToOpen U = S.relativeProj.hom ∣_ U.toOpens :=
    h₁.isoIsPullback_inv_fst _ _ h₂
  rw [← he]
  infer_instance

/-- Stacks 02OS(1): the blowup morphism is an isomorphism over any open set `U` disjoint from the support
of the centre `I` (Zariski-locally on `U`, `I(V) = ⊤` and the chart is an isomorphism). -/
theorem Scheme.isIso_blowup_hom_restrict_of_disjoint_support {X : Scheme.{u}}
    (I : X.IdealSheafData) (U : X.Opens) (hU : Disjoint (U : Set X) (I.support : Set X)) :
    IsIso ((Scheme.blowup I).hom ∣_ U) := by
  rw [← MorphismProperty.isomorphisms.iff]
  refine IsZariskiLocalAtTarget.of_iSup_eq_top (P := MorphismProperty.isomorphisms Scheme)
    (fun V : U.toScheme.affineOpens => (V : U.toScheme.Opens)) (iSup_affineOpens_eq_top _) ?_
  intro V
  rw [(MorphismProperty.isomorphisms Scheme).arrow_mk_iso_iff
    (morphismRestrictRestrict (Scheme.blowup I).hom U V.1), MorphismProperty.isomorphisms.iff]
  have hV : IsAffineOpen (U.ι ''ᵁ V.1) := V.2.image_of_isOpenImmersion U.ι
  have hle : U.ι ''ᵁ V.1 ≤ U :=
    (U.ι.image_le_opensRange V.1).trans (le_of_eq (Scheme.Opens.opensRange_ι U))
  have htop : I.ideal ⟨U.ι ''ᵁ V.1, hV⟩ = ⊤ :=
    I.ideal_eq_top_of_disjoint_support ⟨_, hV⟩ (hU.mono_left (fun _ h => hle h))
  have := I.isIso_reesAlgebra_projToOpen_of_ideal_eq_top ⟨U.ι ''ᵁ V.1, hV⟩ htop
  exact I.reesAlgebra.toGradedAffineAlgebra.isIso_relativeProj_hom_restrict ⟨U.ι ''ᵁ V.1, hV⟩

end AlgebraicGeometry

/-- The point blowup `π : Bl_p S → S` is an isomorphism over every open set `U` not containing `p`. -/
theorem pointBlowup_isIso_away {k : Type u} [Field k] [PerfectField k] (S : SmoothProjectiveSurface k)
    (p : S.toScheme) (hp : IsClosed ({p} : Set S.toScheme))
    (U : S.toScheme.Opens) (hU : p ∉ (U : Set S.toScheme)) :
    CategoryTheory.IsIso ((pointBlowup.π S p hp) ∣_ U) := by
  have hsupp : (((AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal
      (⟨{p}, hp⟩ : TopologicalSpace.Closeds S.toScheme)).support :
        TopologicalSpace.Closeds S.toScheme) : Set S.toScheme) = {p} :=
    AlgebraicGeometry.Scheme.IdealSheafData.coe_support_vanishingIdeal _
  have hdisj : Disjoint (U : Set S.toScheme)
      (((AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal
        (⟨{p}, hp⟩ : TopologicalSpace.Closeds S.toScheme)).support :
          TopologicalSpace.Closeds S.toScheme) : Set S.toScheme) := by
    rw [hsupp]
    exact Set.disjoint_singleton_right.mpr hU
  exact AlgebraicGeometry.Scheme.isIso_blowup_hom_restrict_of_disjoint_support _ U hdisj

/-- The point blowup is dominant: it is an isomorphism over the dense open `S ∖ {p}`. -/
instance {k : Type u} [Field k] [PerfectField k] (S : SmoothProjectiveSurface k) (p : S.toScheme)
    (hp : IsClosed ({p} : Set S.toScheme)) :
    AlgebraicGeometry.IsDominant (pointBlowup.π S p hp) := by
  have : AlgebraicGeometry.IsIntegral S.toScheme := inferInstance
  have : IrreducibleSpace S.toScheme := AlgebraicGeometry.irreducibleSpace_of_isIntegral S.toScheme
  let U : S.toScheme.Opens := ⟨{p}ᶜ, hp.isOpen_compl⟩
  have := pointBlowup_isIso_away S p hp U (fun h => h rfl)
  have hsub : (U : Set S.toScheme) ⊆ Set.range (pointBlowup.π S p hp) := by
    intro y hy
    obtain ⟨z, hz⟩ := (pointBlowup.π S p hp ∣_ U).surjective ⟨y, hy⟩
    refine ⟨((pointBlowup.π S p hp) ⁻¹ᵁ U).ι z, ?_⟩
    have h1 := AlgebraicGeometry.morphismRestrict_base_coe (pointBlowup.π S p hp) U z
    rw [hz] at h1
    exact h1.symm
  have hne : (U : Set S.toScheme).Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    have hss : Subsingleton S.toScheme := ⟨fun a b => by
      have ha : a ∈ ({p} : Set S.toScheme) := by
        by_contra h
        have : a ∈ (U : Set S.toScheme) := h
        rw [hemp] at this
        exact this
      have hb : b ∈ ({p} : Set S.toScheme) := by
        by_contra h
        have : b ∈ (U : Set S.toScheme) := h
        rw [hemp] at this
        exact this
      exact ha.trans hb.symm⟩
    have hsub' : Subsingleton (TopologicalSpace.IrreducibleCloseds S.toScheme) := ⟨fun a b => by
      apply TopologicalSpace.IrreducibleCloseds.ext
      exact a.2.nonempty.eq_univ.trans b.2.nonempty.eq_univ.symm⟩
    have h0 : topologicalKrullDim S.toScheme ≤ 0 := Order.krullDim_nonpos_of_subsingleton
    rw [Variety.dim_spec S.toVariety, S.dim_eq_two] at h0
    norm_num at h0
  exact ⟨(U.isOpen.dense hne).mono hsub⟩

end
