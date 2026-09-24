import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundle
import MiyaokaMori.AlgebraicGeometry.Morphisms.AffineLineOver
import MiyaokaMori.Paper.S2WeightedJets.Cone.ConeTangentBundle
import MiyaokaMori.Paper.S2WeightedJets.Intersection.DeformationFamilyProj
import MiyaokaMori.Paper.S2WeightedJets.Intersection.DeformedJetAlgebra
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.FamilyFiberAtZeroFiberOverLine
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetGrading
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.LocallyWeightedPolynomialAlgebra
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjIsoOfAlgebraIso
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.RelativeProjTwistQC
import MiyaokaMori.Paper.S2WeightedJets.Ygg.WeightedProjectivization

/-! # The fiber of the deformation family at `λ = 1`

The fiber of `𝒴` at `λ = 1` is `Y_k^GG` (Lemma 2.3 of the paper).

Proof: the general statement "the fiber of `Proj_{C×A¹} S → A¹_k` at the `k`-rational point `λ = t` is
`Proj_C (S|_{λ=t})`, over `C`, with `O(m)` corresponding" is `AlgebraicGeometry.Scheme.relativeProj_fiber_over_line`
(`AffineSpace.isPullback_map`, pasting of pullback squares, `κ(point k t) = k`, and Stacks 01O3
`relativeProj_baseChange`). Here `S = deformedJetAlgebra` and `S|_{λ=1} ≅ jetGradedAlgebra` is the second clause of
`deformedJetAlgebra_spec`; transporting `Proj_C` and `O(m)` along that isomorphism is
`relativeProj.exists_iso_of_algebra_iso`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem deformationFamily_fiber_one {k : Type u} [Field k] [CharZero k] {C : SmoothProjectiveCurve k}
    (Z : CategoryTheory.Over C.toScheme) [AlgebraicGeometry.IsAffineHom Z.hom] (sec : C.toScheme ⟶ Z.left)
    (hs : sec ≫ Z.hom = CategoryTheory.CategoryStruct.id _) (n r : ℕ)
    (E : AlgebraicGeometry.VectorBundle C.toVariety) (hE : E.rank = n + 1)
    (hEZ : Nonempty (E.toModules ≅ coneTangentBundle Z.hom sec hs))
    (hloc : ((jetGradedAlgebra (k := k) Z sec hs r).1).IsLocallyWeightedPolynomial
      (fun iq : ULift.{u} (Fin (n + 1) × Fin r) => ((iq.down.2 : ℕ) + 1)) (fun _ => Nat.succ_pos _)) :
    ∃ e : (((deformationFamily Z sec hs r).hom ≫
        AlgebraicGeometry.Scheme.affineLineOver.toLine (k := k) C.toScheme).fiber (AlgebraicGeometry.Scheme.affineLineOver.point k 1) ≅ (weightedJetProjectivization (k := k) Z sec hs r).left),
      e.hom ≫ (weightedJetProjectivization (k := k) Z sec hs r).hom =
          ((deformationFamily Z sec hs r).hom ≫
        AlgebraicGeometry.Scheme.affineLineOver.toLine (k := k) C.toScheme).fiberι (AlgebraicGeometry.Scheme.affineLineOver.point k 1) ≫ (deformationFamily Z sec hs r).hom ≫
          AlgebraicGeometry.Scheme.affineLineOver.toBase C.toScheme ∧
      ∀ m : ℤ, Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback (((deformationFamily Z sec hs r).hom ≫
        AlgebraicGeometry.Scheme.affineLineOver.toLine (k := k) C.toScheme).fiberι (AlgebraicGeometry.Scheme.affineLineOver.point k 1))).obj
          (AlgebraicGeometry.Scheme.relativeProj.twist (deformedJetAlgebra Z sec hs r) m) ≅
        (AlgebraicGeometry.Scheme.Modules.pullback e.hom).obj
          (AlgebraicGeometry.Scheme.relativeProj.twist (jetGradedAlgebra (k := k) Z sec hs r).1 m)) := by
  -- `deformationFamily` is by definition `relativeProj (deformedJetAlgebra …)`
  unfold deformationFamily
  -- the general fiber statement for S = deformedJetAlgebra at λ = 1
  obtain ⟨e, he, htw⟩ := AlgebraicGeometry.Scheme.relativeProj_fiber_over_line (k := k)
    (deformedJetAlgebra Z sec hs r) (1 : k)
  -- S|_{λ=1} ≅ jet graded algebra
  obtain ⟨φ⟩ := deformedJetAlgebra_restrictToLambda_one (k := k) Z sec hs r
  -- Proj_C is functorial in the algebra, with O(m) corresponding
  obtain ⟨e₂, he₂, htw₂⟩ := AlgebraicGeometry.Scheme.relativeProj.exists_iso_of_algebra_iso φ
  have he₂' : e₂.hom ≫ (weightedJetProjectivization (k := k) Z sec hs r).hom =
      (AlgebraicGeometry.Scheme.relativeProj
        ((deformedJetAlgebra Z sec hs r).restrictToLambda (1 : k))).hom := he₂
  refine ⟨e ≪≫ e₂, ?_, ?_⟩
  · rw [Iso.trans_hom, Category.assoc, he₂']
    exact he
  · intro m
    obtain ⟨ψ⟩ := htw m
    obtain ⟨χ⟩ := htw₂ m
    exact ⟨ψ ≪≫ (AlgebraicGeometry.Scheme.Modules.pullback e.hom).mapIso χ ≪≫
      (AlgebraicGeometry.Scheme.Modules.pullbackComp e.hom e₂.hom).app _⟩

end
