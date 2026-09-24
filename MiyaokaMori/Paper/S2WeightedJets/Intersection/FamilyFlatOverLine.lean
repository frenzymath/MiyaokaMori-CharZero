import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S2WeightedJets.Intersection.DeformationFamilyProj
import MiyaokaMori.Paper.S2WeightedJets.Intersection.DeformedJetAlgebra
import MiyaokaMori.AlgebraicGeometry.Morphisms.LocallyProductFlat
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.LocallyWeightedProjLocalProduct

/-! # The deformation family is flat over the line

`𝒴` is flat over `𝔸¹` (locally it is a product with the fixed weighted projective fiber; Lemma 2.3
of the paper).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem deformationFamily_flat {k : Type u} [Field k] [CharZero k] {C : SmoothProjectiveCurve k}
    (Z : CategoryTheory.Over C.toScheme) [AlgebraicGeometry.IsAffineHom Z.hom] (sec : C.toScheme ⟶ Z.left)
    (hs : sec ≫ Z.hom = CategoryTheory.CategoryStruct.id _) (n r : ℕ)
    (E : AlgebraicGeometry.VectorBundle C.toVariety) (hE : E.rank = n + 1)
    (hEZ : Nonempty (E.toModules ≅ coneTangentBundle Z.hom sec hs))
    (hloc : ((jetGradedAlgebra (k := k) Z sec hs r).1).IsLocallyWeightedPolynomial
      (fun iq : ULift.{u} (Fin (n + 1) × Fin r) => ((iq.down.2 : ℕ) + 1)) (fun _ => Nat.succ_pos _)) :
    AlgebraicGeometry.Flat ((deformationFamily Z sec hs r).hom ≫
        AlgebraicGeometry.Scheme.affineLineOver.toLine (k := k) C.toScheme) := by
  -- Step 1: the deformed algebra is locally a weighted polynomial algebra (deformedJetAlgebra_spec).
  have hS := deformedJetAlgebra_isLocallyWeightedPolynomial Z sec hs n r hloc
  -- Step 2: 𝒴 → C × A¹ is flat, being locally the projection U_i ×_k P(w) → U_i.
  have h1 : AlgebraicGeometry.Flat (deformationFamily Z sec hs r).hom := by
    obtain ⟨𝒰, h𝒰⟩ := relativeProj_locallyWeighted_localProduct.{u, u}
      (AlgebraicGeometry.Scheme.affineLineOver.toBase C.toScheme ≫
        (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))
      (deformedJetAlgebra Z sec hs r) _ _ hS
    refine flat_of_locally_product (deformationFamily Z sec hs r).hom
      (AlgebraicGeometry.Scheme.affineLineOver.toBase C.toScheme ≫
        (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))
      (weightedProjectiveSpace k (fun iq : ULift.{u} (Fin (n + 1) × Fin r) => ((iq.down.2 : ℕ) + 1))
        (fun _ => Nat.succ_pos _) ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) 𝒰 fun i => ?_
    obtain ⟨φ, hφ, -⟩ := h𝒰 i
    exact ⟨φ, hφ⟩
  -- Step 3: C × A¹ → A¹_k is the base change of C → Spec k, hence flat; compose.
  have h2 : AlgebraicGeometry.Flat
      (AlgebraicGeometry.Scheme.affineLineOver.toLine (k := k) C.toScheme) :=
    AlgebraicGeometry.Flat.isStableUnderBaseChange.of_isPullback
      (AlgebraicGeometry.AffineSpace.isPullback_map (n := ULift.{u} (Fin 1))
        (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))).flip inferInstance
  exact AlgebraicGeometry.Flat.comp _ _


end
