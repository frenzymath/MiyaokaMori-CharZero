import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedQcAlgebraPullback
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierDivisorPullback
import MiyaokaMori.Paper.S1Intro.TangentBundlePullback
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundlePullback
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.SectionPullbackAlong
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotalSpaceVectorBundle
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpaceZeroSection
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedPolynomialAlgebraPullback
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundlePullback
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.NefPullback

/-! # Restricting sections on the total space to the zero section

A global section of the pulled-back module `p^*M` on the total space `p : Tot(V) → X`, restricted along
the zero section `σ₀ : X → Tot(V)`, gives a global section of `M`:
`σ₀^*(p^*M) ≅ (σ₀ ≫ p)^*M = (𝟙_X)^*M ≅ M` (`pullbackComp`, `pullbackCongr` with
`zeroSection_comp : σ₀ ≫ p = 𝟙`, `pullbackId`), applied to `sectionPullbackAlong σ₀ s`. Used to state
equalities such as "the restriction of the tuple of sections `P_ℓ` to the zero section equals the seed
section", with both sides in the sections of the same module `M`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

noncomputable def AlgebraicGeometry.Scheme.restrictToZeroSection {X : AlgebraicGeometry.Scheme.{u}}
    (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType] {M : X.Modules}
    (s : (((AlgebraicGeometry.Scheme.Modules.pullback
      (AlgebraicGeometry.Scheme.totalSpace V).hom).obj M).val.obj (Opposite.op ⊤) : Type u)) :
    (M.val.obj (Opposite.op ⊤) : Type u) :=
  ((AlgebraicGeometry.Scheme.Modules.pullbackComp (AlgebraicGeometry.Scheme.zeroSection V)
        (AlgebraicGeometry.Scheme.totalSpace V).hom).app M ≪≫
      (AlgebraicGeometry.Scheme.Modules.pullbackCongr
        (AlgebraicGeometry.Scheme.zeroSection_comp V)).app M ≪≫
      (AlgebraicGeometry.Scheme.Modules.pullbackId X).app M).hom.app ⊤
    (sectionPullbackAlong (AlgebraicGeometry.Scheme.zeroSection V) s)

end
