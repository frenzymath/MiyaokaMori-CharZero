import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProjectiveOverField
import MiyaokaMori.AlgebraicGeometry.Morphisms.AffineLineOver
import MiyaokaMori.Paper.S2WeightedJets.Ygg.JetWeightLcm
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.LocallyWeightedPartFiniteType
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.LocallyWeightedPolynomialAlgebra
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.ProjVeroneseIso
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProjectiveBaseChange
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProjectiveMorphism
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProjectiveMorphismComp
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProjectiveOverIffProjectiveMorphism
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.VeroneseGeneration

/-! # Relative Proj of a locally weighted polynomial algebra is projective over the line

General form of the projectivity statement for the deformation family `𝒴 → C × A¹ → A¹` of
Lemma 2.3 of the paper:

Let `X` be a scheme over a field `k` which is projective over `k` (`IsProjectiveOver k X`), and let
`S` be a graded quasi-coherent algebra on `X × A¹` which is locally a weighted polynomial algebra in a
non-empty finite set `σ` of variables with weights `w i ∈ [1, κ]`. Then
`Proj_{X×A¹} S → X × A¹ → A¹_k` is a projective morphism.

Proof (each step is a named lemma below):
1. `IsProjectiveMorphism.of_isIso_comp`: precomposing a projective morphism with an isomorphism keeps
   it projective (compose the closed immersion into the relative Proj with the isomorphism).
2. `affineLineOver.toLine_isProjectiveMorphism`: `X × A¹ → A¹_k` is projective. The square
   `X × A¹ → A¹_k`, `X × A¹ → X`, `A¹_k → Spec k`, `X → Spec k` is a pullback
   (Mathlib `AffineSpace.isPullback_map`), so `toLine` is, up to the isomorphism
   `X × A¹ ≅ X ×_{Spec k} A¹_k`, the base change `pullback.snd` of `X → Spec k` along `A¹_k → Spec k`;
   `X → Spec k` is projective (`isProjectiveOver_iff_isProjectiveMorphism`), base change is projective
   (Stacks 02V6), and step 1 removes the isomorphism.
3. `relativeProj_isProjectiveMorphism_of_locallyWeighted`: `Proj_Y S → Y` is projective for `S`
   locally weighted polynomial. With `m = |σ|·lcm(1,…,κ)`, the Veronese algebra `S^{(m)}` is generated in degree one
   (`VeroneseGeneration`), `S^{(m)}_1 = S_m` is of finite type, and the Veronese isomorphism gives
   `Proj S ≅ Proj S^{(m)}` over `Y`; the inverse isomorphism is the required closed immersion.
4. `relativeProj_locallyWeighted_isProjective_over_line`: `A¹_k = Spec k[λ]` is affine, hence
   quasi-compact and quasi-separated, so the composition of projective morphisms composes steps 2 and 3.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Precomposing a projective morphism with an isomorphism keeps it projective:
the closed immersion `i : X ⟶ Proj S` becomes `e ≫ i`. -/
theorem AlgebraicGeometry.IsProjectiveMorphism.of_isIso_comp {X' X Y : AlgebraicGeometry.Scheme.{u}}
    (e : X' ⟶ X) [IsIso e] (f : X ⟶ Y) [AlgebraicGeometry.IsProjectiveMorphism f] :
    AlgebraicGeometry.IsProjectiveMorphism (e ≫ f) := by
  obtain ⟨S, i, hgen, hft, hi, hfac⟩ :=
    AlgebraicGeometry.IsProjectiveMorphism.exists_closed_immersion (f := f)
  refine ⟨S, e ≫ i, hgen, hft, ?_, by rw [Category.assoc, hfac]⟩
  letI := hi
  infer_instance

/-- `X × A¹ → A¹_k` is projective when `X` is projective over `k`: it is the base change of
`X → Spec k` along `A¹_k → Spec k` (Mathlib `AffineSpace.isPullback_map`), Stacks 02V6. -/
theorem AlgebraicGeometry.Scheme.affineLineOver.toLine_isProjectiveMorphism {k : Type u} [Field k]
    (X : AlgebraicGeometry.Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (hX : IsProjectiveOver k X) :
    AlgebraicGeometry.IsProjectiveMorphism
      (AlgebraicGeometry.Scheme.affineLineOver.toLine (k := k) X) := by
  have : AlgebraicGeometry.IsProjectiveMorphism (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    (isProjectiveOver_iff_isProjectiveMorphism k X).mp hX
  let f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of k) := X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)
  let g : AlgebraicGeometry.AffineSpace (ULift.{u} (Fin 1)) (AlgebraicGeometry.Spec (CommRingCat.of k)) ⟶
      AlgebraicGeometry.Spec (CommRingCat.of k) :=
    AlgebraicGeometry.AffineSpace (ULift.{u} (Fin 1)) (AlgebraicGeometry.Spec (CommRingCat.of k)) ↘
      AlgebraicGeometry.Spec (CommRingCat.of k)
  have hP := (AlgebraicGeometry.AffineSpace.isPullback_map (n := ULift.{u} (Fin 1)) f).flip
  have h := hP.isoPullback_hom_snd
  have := AlgebraicGeometry.IsProjectiveMorphism.baseChange f g
  have hproj : AlgebraicGeometry.IsProjectiveMorphism
      (hP.isoPullback.hom ≫ CategoryTheory.Limits.pullback.snd f g) :=
    AlgebraicGeometry.IsProjectiveMorphism.of_isIso_comp _ _
  rw [h] at hproj
  exact hproj

/-- `Proj_Y S → Y` is projective when `S` is locally a weighted polynomial algebra in a non-empty
finite set of variables with weights in `[1, κ]`: with `m = |σ|·lcm(1,…,κ)` the Veronese algebra
`S^{(m)}` is generated in degree one, its degree-one piece `S_m` is of
finite type, and `Proj S ≅ Proj S^{(m)}` over `Y`. -/
theorem relativeProj_isProjectiveMorphism_of_locallyWeighted {Y : AlgebraicGeometry.Scheme.{u}}
    (S : Y.GradedQCAlgebra) {σ : Type u} [Fintype σ] [Nonempty σ] {κ : ℕ} (w : σ → ℕ)
    (hw : ∀ i, w i ∈ Finset.Icc 1 κ)
    (hS : S.IsLocallyWeightedPolynomial w (fun i => (Finset.mem_Icc.mp (hw i)).1)) :
    AlgebraicGeometry.IsProjectiveMorphism (AlgebraicGeometry.Scheme.relativeProj S).hom := by
  have hSD := veronese_generation S w hw hS
  set m := Fintype.card σ * jetWeight κ with hm
  have hmpos : 0 < m := hSD.1
  have hgen : (S.veronese m).GeneratedInDegreeOne := hSD.2
  have hft1 : (S.part (1 * m)).IsFiniteType := by
    rw [Nat.one_mul]
    exact locallyWeighted_part_isFiniteType S w (fun i => (Finset.mem_Icc.mp (hw i)).1) hS m
  have hft : ((S.veronese m).part 1).IsFiniteType := hft1
  let e := AlgebraicGeometry.Scheme.relativeProj.veroneseIso S m hmpos
  have hi : AlgebraicGeometry.IsClosedImmersion e.inv.left := by
    have hleft : e.inv.left ≫ e.hom.left = 𝟙 _ :=
      congrArg CategoryTheory.Over.Hom.left e.inv_hom_id
    have hcomp : AlgebraicGeometry.IsClosedImmersion (e.inv.left ≫ e.hom.left) := by
      rw [hleft]
      infer_instance
    exact AlgebraicGeometry.IsClosedImmersion.of_comp e.inv.left e.hom.left
  have hover : e.inv.left ≫ (AlgebraicGeometry.Scheme.relativeProj (S.veronese m)).hom =
      (AlgebraicGeometry.Scheme.relativeProj S).hom :=
    CategoryTheory.Over.w e.inv
  exact ⟨S.veronese m, e.inv.left, hgen, hft, hi, hover⟩

/-- Projectivity of the deformation family over the line, in general form:
`Proj_{X×A¹} S → X × A¹ → A¹_k` is projective for `X` projective over `k` and `S` locally weighted
polynomial (non-empty finite variable set, weights in `[1, κ]`). `A¹_k` is affine, hence
quasi-compact and quasi-separated, and composition of projective morphisms applies. -/
theorem relativeProj_locallyWeighted_isProjective_over_line {k : Type u} [Field k]
    {X : AlgebraicGeometry.Scheme.{u}} [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (hX : IsProjectiveOver k X)
    (S : (AlgebraicGeometry.Scheme.affineLineOver X).GradedQCAlgebra)
    {σ : Type u} [Fintype σ] [Nonempty σ] {κ : ℕ} (w : σ → ℕ) (hw : ∀ i, w i ∈ Finset.Icc 1 κ)
    (hS : S.IsLocallyWeightedPolynomial w (fun i => (Finset.mem_Icc.mp (hw i)).1)) :
    AlgebraicGeometry.IsProjectiveMorphism ((AlgebraicGeometry.Scheme.relativeProj S).hom ≫
      AlgebraicGeometry.Scheme.affineLineOver.toLine (k := k) X) := by
  have := relativeProj_isProjectiveMorphism_of_locallyWeighted S w hw hS
  have := AlgebraicGeometry.Scheme.affineLineOver.toLine_isProjectiveMorphism X hX
  have : AlgebraicGeometry.IsAffine
      (AlgebraicGeometry.Scheme.affineLineOver (AlgebraicGeometry.Spec (CommRingCat.of k))) :=
    inferInstanceAs (AlgebraicGeometry.IsAffine
      (AlgebraicGeometry.AffineSpace (ULift.{u} (Fin 1)) (AlgebraicGeometry.Spec (CommRingCat.of k))))
  exact IsProjectiveMorphism.comp _ _

end
