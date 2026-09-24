import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedQcAlgebraPullback
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundle
import MiyaokaMori.AlgebraicGeometry.Morphisms.AffineLineOver
import MiyaokaMori.Paper.S2WeightedJets.Cone.ConeTangentBundle
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.GradedQuasicoherentAlgebra
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetGrading
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.LocallyWeightedPolynomialAlgebra
import MiyaokaMori.AlgebraicGeometry.Modules.RestrictToLambda
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.SheafOfModulesMonoidal
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.WeightedSymAlgebra
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPullbackQuasicoherent
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.PushforwardQcAlgebraMap
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.SheafSymmetricAlgebra
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.TruncatedJetAlgebra
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.Stacks01ic
import MiyaokaMori.Paper.S2WeightedJets.Intersection.DeformedJetAlgebra_IrrelevantPow
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPullbackUnitMul
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedQcAlgebraPullbackId
import MiyaokaMori.Paper.S2WeightedJets.Intersection.DeformedJetAlgebra_Construction
import MiyaokaMori.Paper.S2WeightedJets.Intersection.DeformedJetAlgebraLocallyWeightedPolynomial
import MiyaokaMori.Paper.S2WeightedJets.Intersection.DeformedJetAlgebraFiberAtZero

/-! # The deformed jet algebra

The graded algebra family of the first deformation: the extended Rees deformation
`R_j = Σ_e λ^e · π^*(S_+^{j-e})_j ⊆ π^*S_j` over `C × 𝔸¹` of the jet graded algebra `S`. It is locally a weighted
polynomial algebra, its fiber at `λ = 1` is the jet graded algebra and its fiber at `λ = 0` is the weighted
symmetric algebra of `E` (`deformedJetAlgebra_spec`). This is the step "removing the nonlinear terms" of
Lemma 2.3 of the paper.

The construction is spread over several files, with unchanged declaration names:
* `DeformedJetAlgebra_Construction`: `mulCoordPow`, the Rees pieces `reesDeformation.gen/part/incl`,
  `reesDeformation`, `deformedJetAlgebra`, `inclHom`, and the fiber at `λ = 1`
  (`reesDeformation_restrictToLambda_one`);
* `DeformedJetAlgebraLocallyWeightedPolynomial`: `reesDeformation_isLocallyWeightedPolynomial`;
* `DeformedJetAlgebraFiberAtZero`: `deformedJetAlgebra_restrictToLambda_zero`;
* this file assembles `deformedJetAlgebra_spec`. The imports are kept, as downstream modules reach the pieces
  through this module.

`deformedJetAlgebra_spec` carries the standing hypotheses of the paper (§2, the twisted affine cone:
`[IsClosedImmersion sec] (Zx : Z.left.Opens) (hsZx : ∀ c, sec.base c ∈ Zx)
[SmoothOfRelativeDimension (n+1) (Zx.ι ≫ Z.hom)]`), which are the hypotheses of
`jetGradedAlgebra_isLocallyWeightedPolynomial`. Without them the third component (`λ = 0 ≅ weightedSymAlgebra E`)
is false: take `C = ℙ¹`, `Z = Spec_C (Sym L₁^∨ ×_{O_C} Sym L₂^∨)`, `L₁ = O(1)`, `L₂ = O`, `sec` the zero section,
`r = n = 1`; then `hloc`, `hE`, `hEZ` hold with `E = O_C²`, but the fiber at `0` is `Sym(O(-1) ⊕ O) ≇ Sym(O_C²)`
(see `DeformedJetAlgebraFiberAtZero`). The first two components need no smoothness; they are available separately
as `deformedJetAlgebra_isLocallyWeightedPolynomial` and `deformedJetAlgebra_restrictToLambda_one`, which
`deformationFamily_flat`, `deformationFamily_projective` and `deformationFamily_fiber_one` use.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Component 1 of `deformedJetAlgebra_spec`, separately: the deformed jet algebra is locally a weighted polynomial algebra
with the jet weights whenever the jet algebra is (`reesDeformation_isLocallyWeightedPolynomial`; no smoothness
needed). -/
theorem deformedJetAlgebra_isLocallyWeightedPolynomial {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (Z : CategoryTheory.Over C.toScheme) [AlgebraicGeometry.IsAffineHom Z.hom] (sec : C.toScheme ⟶ Z.left)
    (hs : sec ≫ Z.hom = CategoryTheory.CategoryStruct.id _) (n r : ℕ)
    (hloc : ((jetGradedAlgebra (k := k) Z sec hs r).1).IsLocallyWeightedPolynomial
      (fun iq : ULift.{u} (Fin (n + 1) × Fin r) => ((iq.down.2 : ℕ) + 1)) (fun _ => Nat.succ_pos _)) :
    (deformedJetAlgebra Z sec hs r).IsLocallyWeightedPolynomial
      (fun iq : ULift.{u} (Fin (n + 1) × Fin r) => ((iq.down.2 : ℕ) + 1)) (fun _ => Nat.succ_pos _) :=
  AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation_isLocallyWeightedPolynomial _ _ _ hloc

/-- Component 2 of `deformedJetAlgebra_spec`, separately: at `λ = 1` the deformed jet algebra is the jet graded algebra
(`reesDeformation_restrictToLambda_one`, for any `S`; no hypotheses). -/
theorem deformedJetAlgebra_restrictToLambda_one {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (Z : CategoryTheory.Over C.toScheme) [AlgebraicGeometry.IsAffineHom Z.hom] (sec : C.toScheme ⟶ Z.left)
    (hs : sec ≫ Z.hom = CategoryTheory.CategoryStruct.id _) (r : ℕ) :
    Nonempty ((deformedJetAlgebra Z sec hs r).restrictToLambda (1 : k) ≅ (jetGradedAlgebra (k := k) Z sec hs r).1) :=
  AlgebraicGeometry.Scheme.GradedQCAlgebra.reesDeformation_restrictToLambda_one _

/-- The deformed jet algebra has the three properties needed for the first deformation: it is locally a
weighted polynomial algebra (with the jet weights), its fiber at `λ = 1` is the jet graded algebra, and its
fiber at `λ = 0` is the weighted symmetric algebra of `E` (`E ≅ s^*T_{Z/C}`).
Assembled from `reesDeformation_isLocallyWeightedPolynomial` (for any locally weighted polynomial `S`),
`reesDeformation_restrictToLambda_one` (for any `S`) and `deformedJetAlgebra_restrictToLambda_zero`.
The hypotheses `[IsClosedImmersion sec] (Zx) (hsZx) [SmoothOfRelativeDimension (n+1) (Zx.ι ≫ Z.hom)]` are the
standing hypotheses of the paper; the third component is false without them (counterexample in the module
docstring). `hloc` is kept although it follows from them (`jetGradedAlgebra_isLocallyWeightedPolynomial`),
since the first and third components consume it directly. -/
theorem deformedJetAlgebra_spec {k : Type u} [Field k] [CharZero k] {C : SmoothProjectiveCurve k}
    (Z : CategoryTheory.Over C.toScheme) [AlgebraicGeometry.IsAffineHom Z.hom] (sec : C.toScheme ⟶ Z.left)
    (hs : sec ≫ Z.hom = CategoryTheory.CategoryStruct.id _) [AlgebraicGeometry.IsClosedImmersion sec]
    (Zx : Z.left.Opens) (hsZx : ∀ c, sec.base c ∈ Zx) (n r : ℕ)
    [AlgebraicGeometry.SmoothOfRelativeDimension (n + 1) (Zx.ι ≫ Z.hom)]
    (E : AlgebraicGeometry.VectorBundle C.toVariety) (hE : E.rank = n + 1)
    (hEZ : Nonempty (E.toModules ≅ coneTangentBundle Z.hom sec hs))
    (hloc : ((jetGradedAlgebra (k := k) Z sec hs r).1).IsLocallyWeightedPolynomial
      (fun iq : ULift.{u} (Fin (n + 1) × Fin r) => ((iq.down.2 : ℕ) + 1)) (fun _ => Nat.succ_pos _)) :
    (deformedJetAlgebra Z sec hs r).IsLocallyWeightedPolynomial
        (fun iq : ULift.{u} (Fin (n + 1) × Fin r) => ((iq.down.2 : ℕ) + 1)) (fun _ => Nat.succ_pos _) ∧
      Nonempty ((deformedJetAlgebra Z sec hs r).restrictToLambda (1 : k) ≅ (jetGradedAlgebra (k := k) Z sec hs r).1) ∧
      Nonempty ((deformedJetAlgebra Z sec hs r).restrictToLambda (0 : k) ≅
        (@AlgebraicGeometry.Scheme.weightedSymAlgebra _ r (fun _ : Fin r => E.toModules) (fun _ => E.locallyFree) (fun _ => E.isFiniteType))) :=
  ⟨deformedJetAlgebra_isLocallyWeightedPolynomial Z sec hs n r hloc,
    deformedJetAlgebra_restrictToLambda_one Z sec hs r,
    deformedJetAlgebra_restrictToLambda_zero Z sec hs Zx hsZx n r E hE hEZ hloc⟩

end
