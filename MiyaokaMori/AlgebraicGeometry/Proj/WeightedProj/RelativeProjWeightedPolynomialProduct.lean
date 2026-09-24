import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjIsoOfAlgebraIso
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.RelativeProjWeightedPolynomialProductAffine
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedPolynomialAlgebraPullback
import MiyaokaMori.AlgebraicGeometry.Morphisms.Stacks01o3

/-! # Relative Proj of the weighted polynomial algebra over a `k`-scheme

The relative Proj of the weighted polynomial algebra over a `k`-scheme `U` is `U ×_k P_k(w)`
(compatibly with the projection to `U`), and `O(m)` corresponds to `pr_2^* O_{P(w)}(m)`.

Proof: (1) `weightedPolynomialQCAlgebra_pullback` (the algebra isomorphism `pU^* S_{Spec k} ≅ S_U`)
and `relativeProj.exists_iso_of_algebra_iso`; (2) base change of the relative Proj,
`relativeProj_baseChange` (Stacks 01O3); (3) the affine base case
`relativeProj_weightedPolynomialQCAlgebra_spec_iso`; (4) `pullback.map` (replacing
`U ×_k Proj_{Spec k} 𝒜` by `U ×_k P_k(w)`) together with Mathlib's
`Scheme.Modules.pullbackComp` / `pullbackCongr`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- `Proj_U (weighted polynomial algebra) ≅ U ×_k P_k(w)` over `U`, with `O(m) ≅ pr_2^* O_{P(w)}(m)`. -/
theorem relativeProj_weightedPolynomialAlgebra_iso {k : Type u} [Field k]
    {U : AlgebraicGeometry.Scheme.{u}} (pU : U ⟶ AlgebraicGeometry.Spec (CommRingCat.of k))
    {σ : Type u} [Fintype σ] (w : σ → ℕ) (hw : ∀ i, 0 < w i) :
    ∃ φ : (AlgebraicGeometry.Scheme.relativeProj
            (AlgebraicGeometry.Scheme.weightedPolynomialQCAlgebra U w hw)).left ≅
        CategoryTheory.Limits.pullback pU
          (weightedProjectiveSpace k w hw ↘ AlgebraicGeometry.Spec (CommRingCat.of k)),
      φ.hom ≫ CategoryTheory.Limits.pullback.fst _ _ =
          (AlgebraicGeometry.Scheme.relativeProj
            (AlgebraicGeometry.Scheme.weightedPolynomialQCAlgebra U w hw)).hom ∧
        ∀ m : ℤ, Nonempty (AlgebraicGeometry.Scheme.relativeProj.twist
            (AlgebraicGeometry.Scheme.weightedPolynomialQCAlgebra U w hw) m ≅
          (AlgebraicGeometry.Scheme.Modules.pullback
            (φ.hom ≫ CategoryTheory.Limits.pullback.snd _ _)).obj (weightedProjTwist k w hw m)) := by
  -- notation
  set 𝒜 := AlgebraicGeometry.Scheme.weightedPolynomialQCAlgebra
    (AlgebraicGeometry.Spec (CommRingCat.of k)) w hw with h𝒜
  set S := AlgebraicGeometry.Scheme.weightedPolynomialQCAlgebra U w hw with hS
  set P := weightedProjectiveSpace k w hw with hP
  set pP : P ⟶ AlgebraicGeometry.Spec (CommRingCat.of k) :=
    weightedProjectiveSpace k w hw ↘ AlgebraicGeometry.Spec (CommRingCat.of k) with hpP
  -- Step 1: `S ≅ pU^* 𝒜`, hence `Proj_U S ≅ Proj_U (pU^* 𝒜)`
  obtain ⟨α⟩ := AlgebraicGeometry.Scheme.weightedPolynomialQCAlgebra_pullback pU w hw
  obtain ⟨e₁, he₁, htw₁⟩ :=
    AlgebraicGeometry.Scheme.relativeProj.exists_iso_of_algebra_iso α.symm
  -- Step 2: Stacks 01O3
  obtain ⟨e₂, he₂, htw₂⟩ := AlgebraicGeometry.Scheme.relativeProj_baseChange pU 𝒜
  -- Step 3: the affine base
  obtain ⟨ψ, hψ, htwψ⟩ := relativeProj_weightedPolynomialQCAlgebra_spec_iso k w hw
  -- Step 4: `U ×_k Proj 𝒜 ≅ U ×_k P`
  have hψ' : (AlgebraicGeometry.Scheme.relativeProj 𝒜).hom ≫ 𝟙 _ = ψ.hom ≫ pP := by
    rw [Category.comp_id, hψ]
  let e₃ : CategoryTheory.Limits.pullback pU (AlgebraicGeometry.Scheme.relativeProj 𝒜).hom ≅
      CategoryTheory.Limits.pullback pU pP :=
    asIso (CategoryTheory.Limits.pullback.map pU (AlgebraicGeometry.Scheme.relativeProj 𝒜).hom
      pU pP (𝟙 U) ψ.hom (𝟙 _) (by simp) hψ')
  have he₃_fst : e₃.hom ≫ CategoryTheory.Limits.pullback.fst pU pP =
      CategoryTheory.Limits.pullback.fst pU (AlgebraicGeometry.Scheme.relativeProj 𝒜).hom := by
    simp only [e₃, asIso_hom]
    exact (CategoryTheory.Limits.pullback.lift_fst _ _ _).trans (Category.comp_id _)
  have he₃_snd : e₃.hom ≫ CategoryTheory.Limits.pullback.snd pU pP =
      CategoryTheory.Limits.pullback.snd pU (AlgebraicGeometry.Scheme.relativeProj 𝒜).hom ≫ ψ.hom := by
    simp only [e₃, asIso_hom]
    exact CategoryTheory.Limits.pullback.lift_snd _ _ _
  refine ⟨e₁ ≪≫ e₂ ≪≫ e₃, ?_, ?_⟩
  · simp only [Iso.trans_hom, Category.assoc]
    rw [he₃_fst, he₂, he₁]
  · intro m
    obtain ⟨i₁⟩ := htw₁ m
    obtain ⟨i₂⟩ := htw₂ m
    obtain ⟨i₃⟩ := htwψ m
    have hcomp : e₁.hom ≫ (e₂.hom ≫ CategoryTheory.Limits.pullback.snd pU
        (AlgebraicGeometry.Scheme.relativeProj 𝒜).hom) ≫ ψ.hom =
        (e₁ ≪≫ e₂ ≪≫ e₃).hom ≫ CategoryTheory.Limits.pullback.snd pU pP := by
      simp only [Iso.trans_hom, Category.assoc]
      rw [he₃_snd]
    refine ⟨i₁ ≪≫ (AlgebraicGeometry.Scheme.Modules.pullback e₁.hom).mapIso
      (i₂.symm ≪≫ (AlgebraicGeometry.Scheme.Modules.pullback
        (e₂.hom ≫ CategoryTheory.Limits.pullback.snd pU
          (AlgebraicGeometry.Scheme.relativeProj 𝒜).hom)).mapIso i₃ ≪≫
        (AlgebraicGeometry.Scheme.Modules.pullbackComp
          (e₂.hom ≫ CategoryTheory.Limits.pullback.snd pU
            (AlgebraicGeometry.Scheme.relativeProj 𝒜).hom) ψ.hom).app
          (weightedProjTwist k w hw m)) ≪≫
      (AlgebraicGeometry.Scheme.Modules.pullbackComp e₁.hom _).app (weightedProjTwist k w hw m) ≪≫
      (AlgebraicGeometry.Scheme.Modules.pullbackCongr hcomp).app (weightedProjTwist k w hw m)⟩

end
