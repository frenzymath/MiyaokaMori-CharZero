import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedQcAlgebraPullback
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierDivisor
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.ClosedSubvariety
import MiyaokaMori.AlgebraicGeometry.Divisors.LineBundle.DivisorLineBundle
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.SmoothProjectiveVariety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.EvaluateHomogeneousAtSections
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.GradedQuasicoherentAlgebra
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.HomogeneousCoordinateSections
import MiyaokaMori.Paper.S2WeightedJets.Cone.HomogeneousIdealGenerators
import MiyaokaMori.Paper.S2WeightedJets.Cone.HyperplaneBundlePullback
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.IdealSheafToModules
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetGrading
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPullbackLineBundlePow
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveEmbedding
import MiyaokaMori.Paper.S2WeightedJets.Cone.PuncturedConeOpen
import MiyaokaMori.Paper.S2WeightedJets.Cone.PuncturedConeToProduct
import MiyaokaMori.AlgebraicGeometry.Chow.DivisorOperator.RatDivisorOperator
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.RelativeProjTwistQC
import MiyaokaMori.Paper.S2WeightedJets.Cone.SeedLineBundleIsLineBundle
import MiyaokaMori.Paper.S2WeightedJets.Cone.SeedSection
import MiyaokaMori.Paper.S2WeightedJets.Cone.SeedSectionEquationsVanish
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.SufficientlyDivisible
import MiyaokaMori.Paper.S2WeightedJets.Ygg.TautologicalClass
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.TwistInvertibleSufficientlyDivisible
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.TwistedAffineCone
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.TwistedAffineConeAffineHom
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.VarietyChosenEmbedding
import MiyaokaMori.Paper.S2WeightedJets.Ygg.WeightedProjectivization

/-! # Notation for the weighted jet construction

This file packages the data fixed at the beginning of §2 of the paper — the projective
embedding `X ⊂ ℙ^N`, homogeneous generators of its ideal and the homogeneous coordinate
sections of `f` — into the class `MMSetup f`, and defines from it the twisted affine cone `𝒵`
with its seed section `s` (Definition 2.1), the graded jet algebra `S`
(`jetAlgebra f κ`), `Y_k^GG = Proj_C S` (`YGG f κ`) with `π_k` (`YGG.proj f κ`), the
polarization `B_k = O(m)` (`polarization f κ m`), the rational class `H_k = (1/m) c₁(B_k)`
(`tautClass f κ m`), and divisor classes pulled back from `C` (`ratPullbackOp π D`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The data fixed at the beginning of §2 of the paper. The embedding is not a field: the paper's
`X ⊂ ℙ^N` is the chosen embedding `X.embedding` (with `N = X.embDim`). The fields are homogeneous
generators `E` of degree `≤ δ` of the ideal of `X`, and the homogeneous coordinate sections
`f_ℓ ∈ H⁰(C, A)` of `f`, where `A = f^*O_X(1) = seedLineBundle X.embedding f`. -/
class MMSetup {K : Type u} [Field K] {X : SmoothProjectiveVariety K} {C : SmoothProjectiveCurve K}
    (f : C.toScheme ⟶ X.toScheme) where
  δ : ℕ
  E : EmbeddingEquations K X.embedding δ
  coord : Fin (X.embDim + 1) → ((seedLineBundle X.embedding f).val.obj (Opposite.op ⊤) : Type u)
  hcoord : IsHomogeneousCoordinateTuple X.embedding f coord

variable {K : Type u} [Field K] {X : SmoothProjectiveVariety K} {C : SmoothProjectiveCurve K}
  (f : C.toScheme ⟶ X.toScheme) [D : MMSetup f]

/-- Notation: `N = X.embDim`, the dimension of the ambient projective space. -/
abbrev MMSetup.N : ℕ := X.embDim

/-- Notation: `e = X.embedding`, the chosen projective embedding of `X`. -/
abbrev MMSetup.e : ProjectiveEmbedding K X.toScheme X.embDim := X.embedding

/-- The twisted affine cone `𝒵 ⊂ Tot(A^{⊕(N+1)})` cut out by the homogeneous equations `F_j`
(Definition 2.1 of the paper). -/
noncomputable def MMSetup.cone : CategoryTheory.Over C.toScheme :=
  twistedAffineCone (seedLineBundle X.embedding f) X.embDim D.E.deg D.E.F D.E.homogeneous

instance MMSetup.cone_isAffineHom : AlgebraicGeometry.IsAffineHom (MMSetup.cone f).hom :=
  twistedAffineCone_isAffineHom _ _ _ _ _

/-- The seed section `s = (f_0, …, f_N) : C → 𝒵`; the equations `F_j(f_0, …, f_N) = 0` are
`seedSection_equations_vanish`. -/
noncomputable def MMSetup.seed :
    { s : C.toScheme ⟶ (MMSetup.cone f).left //
      s ≫ (MMSetup.cone f).hom = CategoryTheory.CategoryStruct.id C.toScheme } :=
  seedSection (seedLineBundle X.embedding f) X.embDim D.coord D.E.deg D.E.F D.E.homogeneous
    (seedSection_equations_vanish X.embedding D.E f D.coord D.hcoord)

/-- The punctured cone `𝒵^× ⊂ 𝒵`, the complement of the zero section. -/
noncomputable def MMSetup.punctured : (MMSetup.cone f).left.Opens :=
  puncturedCone (seedLineBundle X.embedding f) X.embDim D.E.deg D.E.deg_pos D.E.F D.E.homogeneous

/-- The projection `𝒵^× → C ×_k X → X` sending a nonzero vector to its projective class; it is
defined only on the punctured cone, not on the vertex section. -/
noncomputable def MMSetup.toX : (MMSetup.punctured f).toScheme ⟶ X.toScheme :=
  puncturedConeToProduct X.embedding D.E (seedLineBundle X.embedding f) D.E.deg_pos ≫
    CategoryTheory.Limits.pullback.snd _ _

/-- The graded algebra `S = ⊕ S_d` of the relative based `κ`-jets (the jet coordinate algebra with
its weight grading). -/
noncomputable def jetAlgebra (κ : ℕ) : C.toScheme.GradedQCAlgebra :=
  (jetGradedAlgebra (k := K) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).1

/-- The weighted projectivization `Y_k^GG = Proj_C S`. -/
noncomputable def YGG (κ : ℕ) : AlgebraicGeometry.Scheme.{u} :=
  (weightedJetProjectivization (k := K) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ).left

/-- The structure morphism `π_k : Y_k^GG → C`. -/
noncomputable def YGG.proj (κ : ℕ) : YGG f κ ⟶ C.toScheme :=
  weightedJetProjection (k := K) (MMSetup.cone f) (MMSetup.seed f).1 (MMSetup.seed f).2 κ

instance YGG.over (κ : ℕ) : (YGG f κ).Over (AlgebraicGeometry.Spec (CommRingCat.of K)) :=
  ⟨YGG.proj f κ ≫ (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of K))⟩

/-- The polarization `B_k = O_{Y_k^GG}(m)`. -/
noncomputable def polarization (κ m : ℕ) : (YGG f κ).Modules :=
  AlgebraicGeometry.Scheme.relativeProj.twist (jetAlgebra f κ) (m : ℤ)

instance polarization_isLineBundle (κ m : ℕ) [Fact ((jetAlgebra f κ).SufficientlyDivisible m)] :
    (polarization f κ m).IsLineBundle :=
  AlgebraicGeometry.Scheme.relativeProj.isLineBundle_twist _ m Fact.out

/-- The rational tautological class `H_k = (1/m) c₁(B_k)`, as a `ℚ`-divisor operator. -/
noncomputable def tautClass (κ m : ℕ) [Fact ((jetAlgebra f κ).SufficientlyDivisible m)] :
    AlgebraicGeometry.RatDivisorOp (YGG f κ) :=
  (m : ℚ)⁻¹ • AlgebraicGeometry.ratDivisorOpOfLineBundle (polarization f κ m)

/-- The class `π^*[D]` of a divisor pulled back from the base curve, as a `ℚ`-divisor operator. -/
noncomputable def ratPullbackOp {Y : AlgebraicGeometry.Scheme.{u}} (π : Y ⟶ C.toScheme)
    (Dv : CartierDivisor C.toVariety) : AlgebraicGeometry.RatDivisorOp Y :=
  AlgebraicGeometry.ratDivisorOpOfLineBundle
    ((AlgebraicGeometry.Scheme.Modules.pullback π).obj Dv.lineBundle.toModules)

end
