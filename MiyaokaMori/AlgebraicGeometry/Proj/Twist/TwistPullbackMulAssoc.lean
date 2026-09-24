import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.TwistPullbackMulAssocComponents

/-! # Associativity of `twistPullbackMul`: the assembly

`twistPullbackMul_assoc'`: the two components `twistPairMul_assoc_add_assoc` and `pullbackPairMul_assoc_tensorAssocIso`
(`TwistPullbackMulAssocComponents`) are combined by the abstract coherence lemma `combMul_assoc_conj`
(`TensorPairMul`) after rewriting `twistPullbackMul` as `τ ≫ combMul` (`twistPullbackMul_eq`) and unfolding
`tensorMapHom` and `tensorAssocIso`. Kept in its own module because the final `exact` (unification of the abstract
statement with the concrete one) takes about 18 s. `twistPullbackMul_assoc` in `TwistPullbackPow` is an alias. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.relativeProj

variable {X : AlgebraicGeometry.Scheme.{u}} (S : X.GradedQCAlgebra)

/-- **Associativity of `twistPullbackMul`** (the statement of `twistPullbackMul_assoc`):
`(μ_{a,b} ⊗ 𝟙) ≫ μ_{a+b,c} = tensorAssocIso ≫ (𝟙 ⊗ μ_{b,c}) ≫ μ_{a,b+c} ≫ (eqToHom ⊗ π^*α⁻¹)`. -/
theorem twistPullbackMul_assoc' (a b c : ℤ) (M N R : X.Modules) :
    AlgebraicGeometry.Scheme.Modules.tensorMapHom (twistPullbackMul S a b M N) (𝟙 _) ≫
        twistPullbackMul S (a + b) c (AlgebraicGeometry.Scheme.Modules.tensor M N) R =
      (AlgebraicGeometry.Scheme.Modules.tensorAssocIso _ _ _).hom ≫
        AlgebraicGeometry.Scheme.Modules.tensorMapHom (𝟙 _) (twistPullbackMul S b c N R) ≫
        twistPullbackMul S a (b + c) M (AlgebraicGeometry.Scheme.Modules.tensor N R) ≫
        AlgebraicGeometry.Scheme.Modules.tensorMapHom
          (CategoryTheory.eqToHom (congrArg (AlgebraicGeometry.Scheme.relativeProj.twist S) (add_assoc a b c).symm))
          ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).map
            (AlgebraicGeometry.Scheme.Modules.tensorAssocIso M N R).inv) := by
  rw [twistPullbackMul_eq, twistPullbackMul_eq, twistPullbackMul_eq, twistPullbackMul_eq,
    AlgebraicGeometry.Scheme.Modules.tensorAssocIso_hom_eq]
  unfold AlgebraicGeometry.Scheme.Modules.tensorMapHom
  exact MiyaokaMori.combMul_assoc_conj AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj
    (twistPairMul S b c) (twistPairMul S a (b + c)) (twistPairMul S a b) (twistPairMul S (a + b) c)
    (CategoryTheory.eqToHom (congrArg (AlgebraicGeometry.Scheme.relativeProj.twist S) (add_assoc a b c).symm))
    (AlgebraicGeometry.Scheme.Modules.pullbackPairMul _ N R)
    (AlgebraicGeometry.Scheme.Modules.pullbackPairMul _ M (AlgebraicGeometry.Scheme.Modules.tensor N R))
    (AlgebraicGeometry.Scheme.Modules.pullbackPairMul _ M N)
    (AlgebraicGeometry.Scheme.Modules.pullbackPairMul _ (AlgebraicGeometry.Scheme.Modules.tensor M N) R)
    ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).map
      (AlgebraicGeometry.Scheme.Modules.tensorAssocIso M N R).inv)
    (twistPairMul_assoc_add_assoc S a b c)
    (AlgebraicGeometry.Scheme.Modules.pullbackPairMul_assoc_tensorAssocIso (AlgebraicGeometry.Scheme.relativeProj S).hom M N R)

end AlgebraicGeometry.Scheme.relativeProj

end
