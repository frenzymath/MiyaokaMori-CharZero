import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProjectiveQuasiProjectiveProper
import MiyaokaMori.AlgebraicGeometry.Morphisms.QuasiProjectiveMorphism
import MiyaokaMori.AlgebraicGeometry.Morphisms.QuasiProjectiveProperProjective
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProjectiveOverField
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProjectiveMorphism
import MiyaokaMori.AlgebraicGeometry.Modules.Ample.Stacks01pu

/-! # Two notions of projectivity over a field agree

Over a field `k`, `X` admits a closed immersion into some `P^N_k` (`IsProjectiveOver`) if and only if
its structure morphism is a projective morphism in the sense of EGA (a closed subscheme of the relative
Proj of a graded algebra generated in degree one with degree-one part of finite type).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem isProjectiveOver_iff_isProjectiveMorphism (k : Type u) [Field k]
    (X : AlgebraicGeometry.Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] :
    IsProjectiveOver k X ↔
      AlgebraicGeometry.IsProjectiveMorphism (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := by
  rw [isProjectiveOver_iff_isProper_and_isAmple]
  constructor
  · rintro ⟨hproper, L, hL, hLamp⟩
    have : AlgebraicGeometry.IsProper (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := hproper
    have : L.IsLineBundle := hL
    have : AlgebraicGeometry.IsQuasiProjectiveMorphism
        (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := by
      refine ⟨inferInstance, inferInstance, ⟨L, hL, fun V => ?_⟩⟩
      have : AlgebraicGeometry.IsClosedImmersion
          ((X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) ⁻¹ᵁ V.1).ι := by
        refine AlgebraicGeometry.IsClosedImmersion.iff_isPreimmersion.mpr ⟨inferInstance, ?_⟩
        rw [AlgebraicGeometry.Scheme.Opens.range_ι, AlgebraicGeometry.Scheme.Hom.coe_preimage]
        exact (isClosed_discrete (V.1 : Set (AlgebraicGeometry.Spec (CommRingCat.of k)))).preimage
          (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)).continuous
      exact AlgebraicGeometry.IsAmple.pullback_of_isClosedImmersion _ L hLamp
    exact AlgebraicGeometry.IsProjectiveMorphism.of_isQuasiProjective_isProper _
  · intro h
    obtain ⟨hqp, hproper⟩ :=
      AlgebraicGeometry.IsProjectiveMorphism.isQuasiProjective_isProper
        (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
    refine ⟨hproper, ?_⟩
    obtain ⟨L, hL, hamp⟩ := hqp.exists_relativelyAmple
    have : L.IsLineBundle := hL
    have hamp_top := hamp ⟨⊤, AlgebraicGeometry.isAffineOpen_top _⟩
    have : IsIso ((X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) ⁻¹ᵁ
        (⊤ : (AlgebraicGeometry.Spec (CommRingCat.of k)).Opens)).ι := by
      rw [AlgebraicGeometry.Scheme.Hom.preimage_top]
      exact ⟨⟨X.topIso.inv, X.ι_toIso_inv, X.toIso_inv_ι⟩⟩
    exact ⟨(AlgebraicGeometry.Scheme.Modules.pullback
        (inv ((X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) ⁻¹ᵁ
          (⊤ : (AlgebraicGeometry.Spec (CommRingCat.of k)).Opens)).ι)).obj
        ((AlgebraicGeometry.Scheme.Modules.pullback
          ((X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) ⁻¹ᵁ
            (⊤ : (AlgebraicGeometry.Spec (CommRingCat.of k)).Opens)).ι).obj L),
      inferInstance, AlgebraicGeometry.IsAmple.pullback_of_isClosedImmersion _ _ hamp_top⟩

end
