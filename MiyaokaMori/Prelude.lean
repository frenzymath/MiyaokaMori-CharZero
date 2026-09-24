import Mathlib.Tactic
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf  -- `PresheafOfModules.Derivation`, `DifferentialsConstruction` (relative differentials)
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
import Mathlib.Algebra.Category.ModuleCat.Presheaf.PushforwardZeroMonoidal  -- `Monoidal`/`LaxMonoidal` instances of `pushforward₀OfCommRingCat`
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.Algebra.Category.ModuleCat.Products
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization
import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.Algebra.DualNumber
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Mathlib.Algebra.Homology.EulerCharacteristic
import Mathlib.Algebra.Module.Lattice
import Mathlib.Algebra.Polynomial.Homogenize
import Mathlib.AlgebraicGeometry.AffineSpace
import Mathlib.AlgebraicGeometry.Birational.Composition
import Mathlib.AlgebraicGeometry.Group.Affine
import Mathlib.AlgebraicGeometry.Modules.Tilde
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
import Mathlib.AlgebraicGeometry.QuasiAffine
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Cardinality
import Mathlib.Analysis.Convex.Cone.Closure
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt  -- `HasExt`/`EnoughInjectives` instances of Grothendieck abelian categories
import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.CategoryTheory.Functor.OfSequence
import Mathlib.CategoryTheory.Limits.EpiMono
import Mathlib.CategoryTheory.Localization.Monoidal.Basic
import Mathlib.CategoryTheory.Localization.Monoidal.Braided  -- `Localization.Monoidal.braidingNatIso`
import Mathlib.CategoryTheory.Localization.Monoidal.Functor
import Mathlib.CategoryTheory.Preadditive.Projective.Resolution
import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Mathlib.Combinatorics.Quiver.ReflQuiver  -- the `⟶` notation goes through the `ReflQuiver.toQuiver` instance
import Mathlib.FieldTheory.FinTrdeg
import Mathlib.Geometry.Convex.Cone.Face.Basic
import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import Mathlib.LinearAlgebra.TensorProduct.Decomposition
import Mathlib.NumberTheory.Harmonic.Int
import Mathlib.Order.CompletePartialOrder  -- the instance chain of `sSup`/`⨆` goes through `CompletePartialOrder.toSupSet`
import Mathlib.RingTheory.DualNumber  -- the `IsLocalRing (DualNumber R)` instance
import Mathlib.RingTheory.HopfAlgebra.MonoidAlgebra  -- `Coalgebra`/`HopfAlgebra` instances of `LaurentPolynomial` (the group object `𝔾ₘ` needs `HopfAlgebra`)
import Mathlib.RingTheory.DedekindDomain.FiniteAdeleRing
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.MvPowerSeries.Trunc
import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Regular.RegularSequence
import Mathlib.RingTheory.TensorProduct.Nontrivial
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Sheaves.Flasque
import MiyaokaMori.Paper.S2WeightedJets.Jets.BasedAffineJet
import MiyaokaMori.RingTheory.GlobalTruncatedParameter
import MiyaokaMori.RingTheory.WeightedSubstitutionOrdinaryScale
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModuleDual
import MiyaokaMori.AlgebraicGeometry.Modules.ExteriorPower.ModuleExteriorPower
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveEmbeddingSections
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.SchemeOverResidue
import MiyaokaMori.RingTheory.GradedRing.IdealFractionChart
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModuleGenericFiber
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModulePullbackStalkTensor
import MiyaokaMori.AlgebraicGeometry.Modules.Flat.ModuleRelativeFlatness
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.ModuleSheafExactness
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModuleTensorPowers
import MiyaokaMori.RingTheory.GradedRing.ReesAlgebraGrading
import MiyaokaMori.AlgebraicGeometry.Blowup.SurfaceBlowup
import MiyaokaMori.RingTheory.TruncatedJetRing
import MiyaokaMori.AlgebraicGeometry.Varieties.Normalization.CurveFieldNormalization
import MiyaokaMori.AlgebraicGeometry.Varieties.FunctionField.FiniteCurveField
import MiyaokaMori.AlgebraicGeometry.Varieties.Points.ReducedPointClosure
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothCurveGeometry
import MiyaokaMori.AlgebraicGeometry.Blowup.StrictTransformClosure
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.AlgebraicCycles
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierAlgebraicCycle
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierLocalData
import MiyaokaMori.AlgebraicGeometry.Morphisms.ClosedImmersionCycles
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.IntegralFundamentalCycle
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.OneCycleCartierRelation
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.PrincipalCartierDivisor
import MiyaokaMori.AlgebraicGeometry.Chow.Pushforward.ProperPushforward
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ZeroCycleDegree
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ZeroCycleDegreeAdditivity
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedProj
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.WeightedProjTwisting

/-! # Prelude

The common import header of the library: every module of `MiyaokaMori` imports this file, directly
or through its own imports.

It imports `Mathlib.Tactic` together with the Mathlib modules that the library uses most (rather
than all of `Mathlib`, whose import closure is roughly twice as large and would be paid by every
file), plus a small number of the library's own foundational modules. Some of the Mathlib imports
are needed only for instances that are found through them (the trailing comments say which).
A Mathlib module needed by many files should be added here rather than to the individual files. -/
