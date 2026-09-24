import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.GradedQuasicoherentAlgebra
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensor
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.SheafOfModulesMonoidal

/-! # The category of graded quasi-coherent algebra sheaves

Morphisms between graded quasi-coherent algebra sheaves and the resulting category structure: a
morphism is a family of degreewise module-sheaf maps `S_m → T_m` compatible with multiplication and
unit; composition and identities are taken degreewise. This gives meaning to isomorphisms `S ≅ T` of
graded algebras (as used in "locally a weighted polynomial algebra", Lemma 2.2
of the paper).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open scoped CategoryTheory.MonoidalCategory

structure AlgebraicGeometry.Scheme.GradedQCAlgebra.Hom {X : AlgebraicGeometry.Scheme.{u}}
    (S T : X.GradedQCAlgebra) where
  app : ∀ m, S.part m ⟶ T.part m
  map_mul : ∀ m n, S.mul m n ≫ app (m + n) = (app m ⊗ₘ app n) ≫ T.mul m n
  map_one : S.one ≫ app 0 = T.one

instance {X : AlgebraicGeometry.Scheme.{u}} : CategoryTheory.Category X.GradedQCAlgebra where
  Hom := AlgebraicGeometry.Scheme.GradedQCAlgebra.Hom
  id S := ⟨fun m => 𝟙 _, by simp, by simp⟩
  comp φ ψ := ⟨fun m => φ.app m ≫ ψ.app m, by simp [reassoc_of% φ.map_mul, ψ.map_mul], by simp [reassoc_of% φ.map_one, ψ.map_one]⟩

end
