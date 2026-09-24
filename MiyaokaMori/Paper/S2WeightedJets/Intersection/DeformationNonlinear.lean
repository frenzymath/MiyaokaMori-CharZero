import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S2WeightedJets.Intersection.DeformedJetAlgebra

/-! # Removing the nonlinear terms of the jet transition

The `λ`-rescaling of the jet transition functions gives a family of graded algebras over `C × 𝔸¹`: at `λ = 1` it is
the jet graded algebra, at `λ = 0` its linear (split) version, and the jet weights are preserved throughout
(Lemma 2.3 of the paper, "removing the nonlinear terms").
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem deformation_removing_nonlinear {k : Type u} [Field k] [CharZero k] {C : SmoothProjectiveCurve k}
    (Z : CategoryTheory.Over C.toScheme) [AlgebraicGeometry.IsAffineHom Z.hom] (sec : C.toScheme ⟶ Z.left)
    (hs : sec ≫ Z.hom = CategoryTheory.CategoryStruct.id _) [AlgebraicGeometry.IsClosedImmersion sec]
    (Zx : Z.left.Opens) (hsZx : ∀ c, sec.base c ∈ Zx) (n r : ℕ)
    [AlgebraicGeometry.SmoothOfRelativeDimension (n + 1) (Zx.ι ≫ Z.hom)]
    (E : AlgebraicGeometry.VectorBundle C.toVariety) (hE : E.rank = n + 1)
    (hEZ : Nonempty (E.toModules ≅ coneTangentBundle Z.hom sec hs))
    (hloc : ((jetGradedAlgebra (k := k) Z sec hs r).1).IsLocallyWeightedPolynomial
      (fun iq : ULift.{u} (Fin (n + 1) × Fin r) => ((iq.down.2 : ℕ) + 1)) (fun _ => Nat.succ_pos _)) :
    ∃ S : (AlgebraicGeometry.Scheme.affineLineOver C.toScheme).GradedQCAlgebra,
      S.IsLocallyWeightedPolynomial
          (fun iq : ULift.{u} (Fin (n + 1) × Fin r) => ((iq.down.2 : ℕ) + 1)) (fun _ => Nat.succ_pos _) ∧
      Nonempty (S.restrictToLambda (1 : k) ≅ (jetGradedAlgebra (k := k) Z sec hs r).1) ∧
      Nonempty (S.restrictToLambda (0 : k) ≅
        (@AlgebraicGeometry.Scheme.weightedSymAlgebra _ r (fun _ : Fin r => E.toModules) (fun _ => E.locallyFree) (fun _ => E.isFiniteType))) := by
  exact ⟨deformedJetAlgebra Z sec hs r, deformedJetAlgebra_spec Z sec hs Zx hsZx n r E hE hEZ hloc⟩

end
