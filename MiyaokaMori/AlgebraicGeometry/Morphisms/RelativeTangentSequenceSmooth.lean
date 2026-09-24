import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.OmegaFiniteType
import MiyaokaMori.AlgebraicGeometry.Modules.Differentials.RelativeDifferentialsLocallyFree
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.DualPullbackCommute
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.DualShortExactLocallyFree
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPullbackRank
import MiyaokaMori.AlgebraicGeometry.Modules.Differentials.RelativeTangentSheaf
import MiyaokaMori.CategoryTheory.ShortExactTransport
import MiyaokaMori.AlgebraicGeometry.Morphisms.Stacks02k4

/-! # The relative tangent sequence of a composition of smooth morphisms

For smooth morphisms `Z --g--> W --h--> S`, the relative tangent sheaves form the short exact
sequence `0 → T_{Z/W} → T_{Z/S} → g^*T_{W/S} → 0` (the dual of the first fundamental exact
sequence; §2.1 of the paper, (2.2)).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem AlgebraicGeometry.relativeTangent_shortExact {Z W S : AlgebraicGeometry.Scheme.{u}}
    (g : Z ⟶ W) (h : W ⟶ S) [AlgebraicGeometry.Smooth g] [AlgebraicGeometry.Smooth h] :
    ∃ (i : AlgebraicGeometry.relativeTangent g ⟶ AlgebraicGeometry.relativeTangent (g ≫ h))
      (π : AlgebraicGeometry.relativeTangent (g ≫ h) ⟶
        (AlgebraicGeometry.Scheme.Modules.pullback g).obj (AlgebraicGeometry.relativeTangent h))
      (hz : i ≫ π = 0),
      (CategoryTheory.ShortComplex.mk i π hz).ShortExact := by
  -- Step 1–2 (01UX + 02K4): `0 → g^*Ω_{W/S} → Ω_{Z/S} → Ω_{Z/W} → 0` is short exact since `g` is smooth.
  obtain ⟨α, β, hz₀, hS₀⟩ := AlgebraicGeometry.Omega_shortExact_of_smooth g h
  -- Step 3: all three terms are finite locally free (02G1 + pullback), and finite type.
  have : (AlgebraicGeometry.Omega h).IsLocallyFree := AlgebraicGeometry.isLocallyFree_omega_of_smooth h
  have : (AlgebraicGeometry.Omega h).IsFiniteType := AlgebraicGeometry.Omega_isFiniteType h
  have : (CategoryTheory.ShortComplex.mk α β hz₀).X₁.IsLocallyFree :=
    (AlgebraicGeometry.Scheme.Modules.isLocallyFree_pullback g (AlgebraicGeometry.Omega h)).1
  have : (CategoryTheory.ShortComplex.mk α β hz₀).X₂.IsLocallyFree :=
    AlgebraicGeometry.isLocallyFree_omega_of_smooth (g ≫ h)
  have : (CategoryTheory.ShortComplex.mk α β hz₀).X₃.IsLocallyFree :=
    AlgebraicGeometry.isLocallyFree_omega_of_smooth g
  have : (CategoryTheory.ShortComplex.mk α β hz₀).X₃.IsFiniteType :=
    AlgebraicGeometry.Omega_isFiniteType g
  -- Step 4: dualise the short exact sequence of finite locally free sheaves.
  obtain ⟨i, π, hz₁, hS₁⟩ := AlgebraicGeometry.Scheme.Modules.dual_shortExact hS₀
  -- Step 5: `(g^*Ω_{W/S})^∨ ≅ g^*(Ω_{W/S}^∨) = g^*T_{W/S}`.
  obtain ⟨e⟩ := AlgebraicGeometry.Scheme.Modules.dual_pullback g (AlgebraicGeometry.Omega h)
  refine ⟨i, π ≫ e.hom, ?_, ?_⟩
  · show i ≫ π ≫ e.hom = 0
    rw [← Category.assoc, hz₁, zero_comp]
  · refine shortExact_transport_of_iso (S := CategoryTheory.ShortComplex.mk i π hz₁)
      (T := CategoryTheory.ShortComplex.mk i (π ≫ e.hom) _) (Iso.refl _) (Iso.refl _) e ?_ ?_ hS₁
    · show 𝟙 _ ≫ i = i ≫ 𝟙 _
      rw [Category.id_comp, Category.comp_id]
    · show 𝟙 _ ≫ (π ≫ e.hom) = π ≫ e.hom
      rw [Category.id_comp]

end
