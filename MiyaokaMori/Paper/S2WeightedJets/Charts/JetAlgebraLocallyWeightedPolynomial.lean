import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.Paper.S2WeightedJets.Cone.ConeTangentBundle
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.Paper.S2WeightedJets.Charts.GradedPieceLocallyFree
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetGrading
import MiyaokaMori.Paper.S2WeightedJets.Charts.JetGradedAlgebraLocalWeightedChart
import MiyaokaMori.Paper.S2WeightedJets.Charts.JetLocalCoordinates
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetSpecIso
import MiyaokaMori.Paper.S2WeightedJets.Charts.JetWeightOfOrderQ
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.LocallyWeightedPolynomialAlgebra
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedPolynomialQCAlgebra
import MiyaokaMori.Paper.S2WeightedJets.Cone.ConeTangentBundleLocalFrame

/-! # The jet algebra is locally a weighted polynomial algebra

On the affine opens `U` on which `E = s^*T_{Z/C}` is trivial, which cover `C`, the graded jet
algebra is a weighted polynomial algebra `S|_U ≅ O_U[x_{i,q}]` (`1 ≤ q ≤ k`, `x_{i,q}` of
weight `q`) (§2.2 of the paper).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem jetGradedAlgebra_isLocallyWeightedPolynomial {k' : Type u} [Field k'] {C : SmoothProjectiveCurve k'}
    (Z : CategoryTheory.Over C.toScheme) [AlgebraicGeometry.IsAffineHom Z.hom]
    (s : C.toScheme ⟶ Z.left) (hs : s ≫ Z.hom = CategoryTheory.CategoryStruct.id C.toScheme)
    [AlgebraicGeometry.IsClosedImmersion s]
    (Zx : Z.left.Opens) (hsZx : ∀ c, s.base c ∈ Zx) (n : ℕ)
    [AlgebraicGeometry.SmoothOfRelativeDimension (n + 1) (Zx.ι ≫ Z.hom)] (r : ℕ) :
    ((jetGradedAlgebra (k := k') Z s hs r).1).IsLocallyWeightedPolynomial
      (fun iq : ULift.{u} (Fin (n + 1) × Fin r) => ((iq.down.2 : ℕ) + 1)) (fun _ => Nat.succ_pos _) := by
  classical
  choose U hU hframe using fun x : C.toScheme =>
    coneTangentBundle_exists_affine_frame Z.hom s hs Zx hsZx n x
  let w : ULift.{u} (Fin (n + 1) × Fin r) → ℕ :=
    fun iq => ((iq.down.2 : ℕ) + 1)
  let e : ∀ x : C.toScheme,
      ((jetGradedAlgebra (k := k') Z s hs r).1).toGradedAffineAlgebra.toAffineAlgebra.sections
        (AlgebraicGeometry.Scheme.affineSite (U x)) ≃+*
      MvPolynomial (ULift.{u} (Fin (n + 1) × Fin r)) Γ(C.toScheme, (U x).1) :=
    fun x => (jetGradedAlgebra_localWeightedChart_of_smooth Z s hs Zx hsZx n r (U x) (hframe x)).choose
  let chart : C.toScheme → C.toScheme.AffineZariskiSite := U
  have hcover : ∀ x : C.toScheme, x ∈ (chart x).toOpens := by
    intro x
    exact hU x
  have hcovers : ∀ x : C.toScheme, ∃ i, x ∈ (chart i).toOpens := by
    intro x
    exact ⟨x, hcover x⟩
  have hchart : ∀ x : C.toScheme, ∀ m : ℕ,
      ∀ a : ((jetGradedAlgebra (k := k') Z s hs r).1).toGradedAffineAlgebra.toAffineAlgebra.sections
        (AlgebraicGeometry.Scheme.affineSite (chart x)),
      a ∈ ((jetGradedAlgebra (k := k') Z s hs r).1).toGradedAffineAlgebra.grading
          (AlgebraicGeometry.Scheme.affineSite (chart x)) m ↔
        ((e x) a).IsWeightedHomogeneous w m := by
    intro x m a
    exact (jetGradedAlgebra_localWeightedChart_of_smooth Z s hs Zx hsZx n r (U x) (hframe x)).choose_spec.1 m a
  have hunit : ∀ x : C.toScheme, ∀ a : Γ(C.toScheme, (chart x).toOpens),
      (e x) (((jetGradedAlgebra (k := k') Z s hs r).1).toGradedAffineAlgebra.toAffineAlgebra.unitHom
        (AlgebraicGeometry.Scheme.affineSite (chart x)) a) = MvPolynomial.C a := by
    intro x a
    exact (jetGradedAlgebra_localWeightedChart_of_smooth Z s hs Zx hsZx n r (U x) (hframe x)).choose_spec.2 a
  change Nonempty ((jetGradedAlgebra (k := k') Z s hs r).1.toGradedAffineAlgebra.WeightedPolynomialAtlas w)
  refine ⟨{
    I := C.toScheme
    chart := chart
    covers := hcovers
    equiv := fun x => e x
    equiv_grading := hchart
    equiv_unit := hunit }⟩

end
