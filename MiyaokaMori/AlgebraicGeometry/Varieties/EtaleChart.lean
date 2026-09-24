import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Smooth.EtaleChartAffineSpaceSmooth
import MiyaokaMori.Paper.S2WeightedJets.Charts.EtaleChartConormalBasis
import MiyaokaMori.Paper.S2WeightedJets.Charts.EtaleChartOmegaVanishing
import MiyaokaMori.AlgebraicGeometry.Morphisms.EtaleChartSmoothResLE
import MiyaokaMori.AlgebraicGeometry.Morphisms.EtaleCriterionDifferentials

/-! # Étale chart around a section

On an affine open `U` over which `E` is trivial, the `n+1` functions obtained by lifting a basis of
`I/I²` define a `U`-morphism `φ : V → A^{n+1}_U` (`V` an open neighbourhood of `s(U)`) which sends
`s(U)` to the zero section and is étale (§2 of the paper).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- **Étale chart around the seed section** (§2 of the paper).
On an affine open `U ⊆ C` where `E = s^*T_{Z/C}` is trivial, there is an affine open `V` of `Z` with
`s(U) ⊆ V ⊆ Zx ∩ p⁻¹U` and a `U`-morphism `φ : V ⟶ 𝔸^{n+1}_U` which is étale and sends `s(U)` to
the zero section.

Assembly:
1. `exists_etaleChart_conormal_basis`: functions
   `h : Fin (n+1) → Γ(p⁻¹U)` vanishing along `s(U)` whose classes form a basis of `I/I²`.
2. `exists_etaleChart_omega_isZero_of_mem`: an open
   `V₀ ⊆ Zx ∩ p⁻¹U` containing `s(U)` (i.e. `∀ c ∈ U, s c ∈ V₀`) on which `Ω` of
   `φ₀ := homOfLE ≫ homOfVector (p ∣_ U) h` vanishes.
3. `IsAffineOpen.exists_basicOpen_le_of_isClosed_inter_subset` (proved in
   `EtaleChartOmegaVanishing`): with `W := p⁻¹U` affine and the closed set `T := s(C)`, one has
   `T ∩ W ⊆ V₀` (a point `s c ∈ p⁻¹U` has `c = p (s c) ∈ U`, so `s c ∈ V₀`); hence there is
   `f ∈ Γ(W)` with `T ∩ W ⊆ D(f) ⊆ V₀`. Take `V := D(f)`, affine by `IsAffineOpen.basicOpen`;
   `s(U) ⊆ V` because `s(U) ⊆ T ∩ W`.
4. `smoothOfRelativeDimension_resLE_of_le` and `AffineSpace.smoothOfRelativeDimension_over`:
   `V₀ ⟶ U` and `𝔸^{n+1}_U ⟶ U` are smooth of relative dimension `n+1`; with step 2 the étale
   criterion `etale_of_omega_isZero` makes `φ₀` étale, and
   `φ := homOfLE ≫ φ₀` is étale as an open immersion followed by an étale map.
5. `φ ≫ (𝔸 ↘ U) = p.resLE U V` is `homOfVector_over`; `s|_U ≫ φ = homOfVector 𝟙 0` follows from
   `comp_homOfVector`, `s|_U ≫ p|_U = 𝟙` and `h i ∈ ker σ`. -/
theorem exists_etale_chart {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    {Z : AlgebraicGeometry.Scheme.{u}} (p : Z ⟶ C.toScheme) (s : C.toScheme ⟶ Z)
    (hs : s ≫ p = CategoryTheory.CategoryStruct.id C.toScheme)
    [AlgebraicGeometry.IsClosedImmersion s] [AlgebraicGeometry.IsAffineHom p]
    (Zx : Z.Opens) (hsZx : ∀ c, s.base c ∈ Zx) (n : ℕ)
    [AlgebraicGeometry.SmoothOfRelativeDimension (n + 1) (Zx.ι ≫ p)]
    (U : C.toScheme.affineOpens)
    (htriv : Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback U.1.ι).obj (coneTangentBundle p s hs) ≅
      SheafOfModules.free (R := U.1.toScheme.ringCatSheaf) (ULift.{u} (Fin (n + 1))))) :
    ∃ (V : Z.Opens) (_ : AlgebraicGeometry.IsAffineOpen V) (hsV : U.1 ≤ s ⁻¹ᵁ V) (hVU : V ≤ p ⁻¹ᵁ U.1) (_ : V ≤ Zx)
      (φ : V.toScheme ⟶
        AlgebraicGeometry.AffineSpace (ULift.{u} (Fin (n + 1))) U.1.toScheme),
      AlgebraicGeometry.Etale φ ∧
      φ ≫ (AlgebraicGeometry.AffineSpace (ULift.{u} (Fin (n + 1))) U.1.toScheme ↘ U.1.toScheme) = p.resLE U.1 V hVU ∧
      s.resLE V U.1 hsV ≫ φ =
        AlgebraicGeometry.AffineSpace.homOfVector (CategoryTheory.CategoryStruct.id U.1.toScheme) 0 := by
  obtain ⟨h, hmem, b, hb⟩ := exists_etaleChart_conormal_basis p s hs Zx hsZx n U htriv
  obtain ⟨V₀, hV₀, hV₀Zx, hsV₀, hΩ⟩ :=
    exists_etaleChart_omega_isZero_of_mem p s hs Zx hsZx n U h hmem b hb
  have hW : AlgebraicGeometry.IsAffineOpen (p ⁻¹ᵁ U.1) := U.2.preimage p
  have hT : IsClosed (Set.range s.base) :=
    (AlgebraicGeometry.IsClosedImmersion.isClosedEmbedding s).isClosed_range
  -- `s ⁻¹ᵁ p ⁻¹ᵁ U = U`: a point `s c` lies over `U` iff `c ∈ U`.
  have hpre : s ⁻¹ᵁ p ⁻¹ᵁ U.1 = U.1 := by
    rw [← AlgebraicGeometry.Scheme.Hom.comp_preimage, hs, AlgebraicGeometry.Scheme.Hom.id_preimage]
  obtain ⟨f, hfV₀, hTf⟩ := hW.exists_basicOpen_le_of_isClosed_inter_subset (V := V₀) hT
    (by
      rintro _ ⟨c, rfl⟩ hcW
      have hc : c ∈ s ⁻¹ᵁ p ⁻¹ᵁ U.1 := hcW
      rw [hpre] at hc
      exact hsV₀ c hc)
  set V : Z.Opens := Z.basicOpen f with hVdef
  have hVaff : AlgebraicGeometry.IsAffineOpen V := hW.basicOpen f
  have hVV₀ : V ≤ V₀ := hfV₀
  have hVU : V ≤ p ⁻¹ᵁ U.1 := hVV₀.trans hV₀
  have hsV : U.1 ≤ s ⁻¹ᵁ V := fun c hc => hTf _ ⟨c, rfl⟩ (etaleChart_le_preimage p s hs U.1 hc)
  set φ₀ := Z.homOfLE hV₀ ≫ AlgebraicGeometry.AffineSpace.homOfVector (p ∣_ U.1) h with hφ₀
  have hφ₀over : φ₀ ≫ (AlgebraicGeometry.AffineSpace (ULift.{u} (Fin (n + 1))) U.1.toScheme ↘ U.1.toScheme) =
      p.resLE U.1 V₀ hV₀ := by
    simp only [hφ₀, Category.assoc, AlgebraicGeometry.AffineSpace.homOfVector_over]
    rfl
  have : AlgebraicGeometry.SmoothOfRelativeDimension (n + 1)
      (φ₀ ≫ (AlgebraicGeometry.AffineSpace (ULift.{u} (Fin (n + 1))) U.1.toScheme ↘ U.1.toScheme)) := by
    rw [hφ₀over]
    exact AlgebraicGeometry.smoothOfRelativeDimension_resLE_of_le p Zx (n + 1) U.1 V₀ hV₀Zx hV₀
  have : AlgebraicGeometry.SmoothOfRelativeDimension (n + 1)
      (AlgebraicGeometry.AffineSpace (ULift.{u} (Fin (n + 1))) U.1.toScheme ↘ U.1.toScheme) :=
    AlgebraicGeometry.AffineSpace.smoothOfRelativeDimension_over (n + 1) U.1.toScheme
  have hφ₀et : AlgebraicGeometry.Etale φ₀ := AlgebraicGeometry.etale_of_omega_isZero φ₀
    (AlgebraicGeometry.AffineSpace (ULift.{u} (Fin (n + 1))) U.1.toScheme ↘ U.1.toScheme) (n + 1) hΩ
  refine ⟨V, hVaff, hsV, hVU, hVV₀.trans hV₀Zx, Z.homOfLE hVV₀ ≫ φ₀, inferInstance, ?_, ?_⟩
  · rw [Category.assoc, hφ₀over, AlgebraicGeometry.Scheme.Hom.map_resLE]
  · have e1 : s.resLE (p ⁻¹ᵁ U.1) U.1 (etaleChart_le_preimage p s hs U.1) ≫ p ∣_ U.1 =
        CategoryTheory.CategoryStruct.id U.1.toScheme := by
      rw [← cancel_mono U.1.ι, Category.assoc, AlgebraicGeometry.morphismRestrict_ι,
        AlgebraicGeometry.Scheme.Hom.resLE_comp_ι_assoc, hs, Category.comp_id, Category.id_comp]
    have e2 : (s.resLE (p ⁻¹ᵁ U.1) U.1 (etaleChart_le_preimage p s hs U.1)).appTop ∘ h = 0 := by
      funext i
      exact RingHom.mem_ker.mp (hmem i)
    rw [hφ₀, AlgebraicGeometry.Scheme.Hom.resLE_map_assoc, AlgebraicGeometry.Scheme.Hom.resLE_map_assoc,
      AlgebraicGeometry.AffineSpace.comp_homOfVector, e1, e2]

end
