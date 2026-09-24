import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedAlgebraTotal
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.GradedQuasicoherentAlgebra

/-! # Graded projections and inclusions of the total algebra

The `q`-th graded projection `⊕_m S_m → S_q` and graded inclusion `S_q → ⊕_m S_m` of a graded
quasi-coherent algebra, with `ι_q ≫ π_q = 𝟙`. (Used for the `q`-th component of `⊕_q L^{-q}`.)
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The `q`-th graded projection `⊕_m S_m → S_q`: the `desc` of the coproduct with the identity (via
`eqToHom`) on the `q`-th component and `0` elsewhere. -/
noncomputable def AlgebraicGeometry.Scheme.GradedQCAlgebra.totalProj {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) (q : ℕ) : S.total.carrier ⟶ S.part q :=
  show (∐ S.part) ⟶ S.part q from
    CategoryTheory.Limits.Sigma.desc fun m =>
      if h : m = q then CategoryTheory.eqToHom (congrArg S.part h) else 0

/-- The `q`-th graded inclusion `S_q → ⊕_m S_m`. -/
noncomputable def AlgebraicGeometry.Scheme.GradedQCAlgebra.totalIncl {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) (q : ℕ) : S.part q ⟶ S.total.carrier :=
  show S.part q ⟶ (∐ S.part) from CategoryTheory.Limits.Sigma.ι S.part q

/-- `ι_q ≫ π_q = 𝟙`. -/
theorem AlgebraicGeometry.Scheme.GradedQCAlgebra.totalIncl_totalProj {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) (q : ℕ) :
    S.totalIncl q ≫ S.totalProj q = CategoryTheory.CategoryStruct.id _ :=
  (CategoryTheory.Limits.Sigma.ι_desc _ _).trans (by simp)

end
