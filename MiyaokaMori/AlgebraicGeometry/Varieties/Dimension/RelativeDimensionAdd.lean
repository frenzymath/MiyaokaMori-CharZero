import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedQcAlgebraPullback
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierDivisorPullback
import MiyaokaMori.Paper.S1Intro.TangentBundlePullback
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundlePullback
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.DimensionOpenCoverSup
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedPolynomialAlgebraPullback
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundlePullback
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.NefPullback
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.Stacks0b7i
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.Stacks0b2m

/-! # Dimension of a scheme which is locally a product

If `π : X → C` is, over an open cover of `C`, isomorphic to the product with a fixed fibre `F`
(`C` and `F` locally of finite type over `k`), then `dim X = dim C + dim F`. The paper uses this
to add the dimension `1` of `C` to the fibre dimension `(n+1)k − 1`, obtaining `s_k`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

private lemma withBot_iSup_add_const
    {ι : Type*} [Nonempty ι] (f : ι → WithBot ℕ∞)
    (a : WithBot ℕ∞) :
    (⨆ i, f i) + a = ⨆ i, f i + a := by
  cases a with
  | bot => simp
  | coe a =>
      by_cases hs : (⨆ i, f i) = ⊥
      · have hfbot : ∀ i, f i = ⊥ := by
          intro i
          exact le_bot_iff.mp ((le_iSup f i).trans_eq hs)
        simp [hfbot]
      · obtain ⟨s, hs'⟩ := WithBot.ne_bot_iff_exists.mp hs
        have hS : (⨆ i, f i) = (s : WithBot ℕ∞) := hs'.symm
        have hex : ∃ j, f j ≠ ⊥ := by
          by_contra h
          push Not at h
          exact hs (by simp [h])
        obtain ⟨j, hj⟩ := hex
        let g : ι → ℕ∞ := fun i => (f i).unbotD 0
        have hfg : ∀ i, f i ≤ (g i : WithBot ℕ∞) := by
          intro i
          exact WithBot.le_coe_unbotD (f i) 0
        have hgs : ∀ i, (g i : WithBot ℕ∞) ≤ ⨆ i, f i := by
          intro i
          by_cases hi : f i = ⊥
          · simp [g, hi, hS]
          · obtain ⟨x, hx⟩ := WithBot.ne_bot_iff_exists.mp hi
            have hi' : (g i : WithBot ℕ∞) = f i := by
              simp [g, ← hx]
            rw [hi']
            exact le_iSup f i
        have hSg : (⨆ i, f i) = (⨆ i, g i : ℕ∞) := by
          apply le_antisymm
          · rw [WithBot.coe_iSup (OrderTop.bddAbove _)]
            exact iSup_mono hfg
          · rw [WithBot.coe_iSup (OrderTop.bddAbove _)]
            exact iSup_le hgs
        have hqa : ∀ i, f i + (a : WithBot ℕ∞) ≤ ((g i + a : ℕ∞) : WithBot ℕ∞) := by
          intro i
          have := add_le_add_right (hfg i) (a : WithBot ℕ∞)
          simpa only [WithBot.coe_add, add_comm] using this
        have hqb : ∀ i, ((g i + a : ℕ∞) : WithBot ℕ∞) ≤ ⨆ i, f i + (a : WithBot ℕ∞) := by
          intro i
          by_cases hi : f i = ⊥
          · have hja : ((0 + a : ℕ∞) : WithBot ℕ∞) ≤
                f j + (a : WithBot ℕ∞) := by
              obtain ⟨x, hx⟩ := WithBot.ne_bot_iff_exists.mp hj
              have hxa : ((0 + a : ℕ∞) : WithBot ℕ∞) ≤ ((x + a : ℕ∞) : WithBot ℕ∞) := by
                exact WithBot.coe_le_coe.mpr (add_le_add_left (bot_le : (0 : ℕ∞) ≤ x) a)
              simpa only [← hx, WithBot.coe_add] using hxa
            simpa [g, hi] using hja.trans (le_iSup (fun k => f k + (a : WithBot ℕ∞)) j)
          · obtain ⟨x, hx⟩ := WithBot.ne_bot_iff_exists.mp hi
            have hi' : ((g i + a : ℕ∞) : WithBot ℕ∞) =
                f i + (a : WithBot ℕ∞) := by
              simp [g, ← hx]
            rw [hi']
            exact le_iSup (fun k => f k + (a : WithBot ℕ∞)) i
        have hq : (⨆ i, f i + (a : WithBot ℕ∞)) =
            (⨆ i, g i + a : ℕ∞) := by
          rw [WithBot.coe_iSup (OrderTop.bddAbove _)]
          apply le_antisymm
          · exact iSup_mono hqa
          · exact iSup_le hqb
        calc
          (⨆ i, f i) + (a : WithBot ℕ∞) =
              (((⨆ i, g i : ℕ∞) + a : ℕ∞) : WithBot ℕ∞) := by rw [hSg, WithBot.coe_add]
          _ = (((⨆ i, g i + a : ℕ∞) : ℕ∞) : WithBot ℕ∞) := by rw [ENat.iSup_add]
          _ = ⨆ i, f i + (a : WithBot ℕ∞) := hq.symm

/-- `dim X = dim C + dim F` when `π : X → C` is locally over `C` the projection from `C × F`. -/
theorem dimension_eq_of_locally_product {k : Type u} [Field k]
    {X C F : AlgebraicGeometry.Scheme.{u}}
    (pC : C ⟶ AlgebraicGeometry.Spec (CommRingCat.of k))
    (pF : F ⟶ AlgebraicGeometry.Spec (CommRingCat.of k))
    [AlgebraicGeometry.LocallyOfFiniteType pC] [AlgebraicGeometry.LocallyOfFiniteType pF]
    (π : X ⟶ C) (𝒰 : C.OpenCover)
    (e : ∀ i, ∃ φ : CategoryTheory.Limits.pullback π (𝒰.f i) ≅
        CategoryTheory.Limits.pullback (𝒰.f i ≫ pC) pF,
        φ.hom ≫ CategoryTheory.Limits.pullback.fst (𝒰.f i ≫ pC) pF =
          CategoryTheory.Limits.pullback.snd π (𝒰.f i)) :
    topologicalKrullDim X = topologicalKrullDim C + topologicalKrullDim F := by
  let 𝒱 : X.OpenCover :=
    { I₀ := 𝒰.I₀
      X := fun i => CategoryTheory.Limits.pullback π (𝒰.f i)
      f := fun i => CategoryTheory.Limits.pullback.fst π (𝒰.f i)
      mem₀ := by
        rw [AlgebraicGeometry.Scheme.presieve₀_mem_precoverage_iff]
        constructor
        · intro x
          obtain ⟨i, y, hy⟩ := AlgebraicGeometry.Scheme.Cover.exists_eq
            (𝒰.pullback₁ π) x
          exact ⟨i, y, hy⟩
        · intro i
          infer_instance }
  have hblock : ∀ i : 𝒰.I₀, topologicalKrullDim (𝒱.X i) =
      topologicalKrullDim (𝒰.X i) + topologicalKrullDim F := by
    intro i
    obtain ⟨φ, _⟩ := e i
    change topologicalKrullDim
        (CategoryTheory.Limits.pullback (π : X ⟶ C) (𝒰.f i) : AlgebraicGeometry.Scheme) =
      topologicalKrullDim (𝒰.X i) + topologicalKrullDim F
    rw [IsHomeomorph.topologicalKrullDim_eq _
      (AlgebraicGeometry.Scheme.homeoOfIso φ).isHomeomorph]
    exact stacks_0B2M (𝒰.f i ≫ pC) pF
  rw [topologicalKrullDim_eq_iSup_openCover 𝒱,
    topologicalKrullDim_eq_iSup_openCover 𝒰]
  change (⨆ i : 𝒰.I₀, topologicalKrullDim (𝒱.X i)) =
    (⨆ i : 𝒰.I₀, topologicalKrullDim (𝒰.X i)) + topologicalKrullDim F
  cases isEmpty_or_nonempty 𝒰.I₀ with
  | inl h =>
      letI := h
      simp
  | inr h =>
      letI := h
      simp_rw [hblock]
      exact (withBot_iSup_add_const _ _).symm

end
