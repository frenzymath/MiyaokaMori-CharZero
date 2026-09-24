import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.ClosedSubvariety
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.VarietyLineBundle
import MiyaokaMori.AlgebraicGeometry.Divisors.LineBundle.OXOne
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.SmoothProjectiveVariety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.AlgebraicGeometry.Varieties.FiniteCover
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.ModulesLineBundleZpow
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensor
import MiyaokaMori.Paper.S2WeightedJets.Ygg.PaperYgg
import MiyaokaMori.AlgebraicGeometry.Modules.SectionIsZeroAt
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.VarietyChosenEmbedding
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.BasedJetConeCoordinate
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.BasedJetOverRho
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundlePullback
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleTensor
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleTensorPower
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.ThickeningSectionsTruncated
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotLineCoefficientMap
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.Stacks01ct

/-! # The coefficients of a based jet and the nowhere-zero condition

The positive-order cone coefficients `c_{ℓ,q} ∈ H^0(C̃, ρ^*A ⊗ L^{-q})` of a based jet `ȷ` (`BasedJet.coefficient`),
and the condition "the normalized coefficient tuple is nowhere zero": at every point some `c_{ℓ,q}` (`1 ≤ q ≤ κ`)
does not vanish. In the proof of Lemma 3.1 of the paper ("they are regular, and at each
point at least one is a unit") this is the condition on the normalized chart coordinates, via the correspondence
between jet charts and cone coordinates: all positive-order chart coordinates vanish at a point iff the jet at
that point is the constant seed jet iff all `c_{ℓ,q}` vanish there.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The `q`-th order cone coefficient `c_{ℓ,q} ∈ H^0(C̃, ρ^*A ⊗ L^{-q})`: the coefficient of `ξ^q` in the expansion
of the `ℓ`-th cone coordinate of `J` (uniquely determined by the expansion (4.1)). -/
noncomputable def BasedJet.coefficient {k : Type u} [Field k] {X : SmoothProjectiveVariety k}
    {C : SmoothProjectiveCurve k} {f : C.toScheme ⟶ X.toScheme} [MMSetup f] {ρ : FiniteCover k C}
    {L : LineBundle ρ.source.toVariety} {κ : ℕ} (J : BasedJet f ρ L κ)
    (ℓ : Fin (X.embDim + 1)) (q : ℕ) :
    (((((LineBundle.pullback (X := ρ.source.toVariety) (Y := C.toVariety) ρ.hom
          (LineBundle.pullback (X := C.toVariety) (Y := X.toVariety) f (X.OX 1))).zpow 1).tensor
        (L.zpow (-(q : ℤ)))).toModules.val.obj (Opposite.op ⊤)) : Type u) :=
  /- the `q`-th component of the cone coordinate `P_ℓ` under the truncated decomposition
     `Γ(C̃_(κ)(L), p^*M) ≃ ⊕_{q ≤ κ} H^0(M ⊗ L^{-q})` (for `q > κ` the definition of `xiCoefficientThickening`
     gives `0`) -/
  xiCoefficientThickening L
    (LineBundle.pullback (X := ρ.source.toVariety) (Y := C.toVariety) ρ.hom
      (LineBundle.pullback (X := C.toVariety) (Y := X.toVariety) f (X.OX 1))) κ q (J.coneCoordinate ℓ)

/-- The normalized coefficient tuple of `J` is nowhere zero: at every point of `C̃` some positive-order
coefficient `c_{ℓ,q}` (`1 ≤ q ≤ κ`) does not vanish, i.e. the jet of `J` at no point is the constant seed jet
(equivalently, in the paper's terms, at each point at least one normalized coordinate is a unit). -/
def NormalizedTupleNowhereZero {k : Type u} [Field k] {X : SmoothProjectiveVariety k}
    {C : SmoothProjectiveCurve k} {f : C.toScheme ⟶ X.toScheme} [MMSetup f] {ρ : FiniteCover k C}
    {L : LineBundle ρ.source.toVariety} {κ : ℕ} (J : BasedJet f ρ L κ) : Prop :=
  ∀ y : ρ.source.toScheme, ∃ (ℓ : Fin (X.embDim + 1)) (q : ℕ), 1 ≤ q ∧ q ≤ κ ∧
    ¬ IsZeroAt (J.coefficient ℓ q) y

end
