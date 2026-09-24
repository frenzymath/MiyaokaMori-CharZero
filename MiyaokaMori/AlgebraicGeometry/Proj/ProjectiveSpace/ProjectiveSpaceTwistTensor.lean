import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModulesStalkFunctor
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpace
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModulesDual
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensor
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.ProjTwistBasicOpen
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.ProjTwistingSheaf
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpaceCoordinate
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.SerreTwistIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.SerreTwistProjectiveSpace
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.Stacks01ms
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.Stacks01ah
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.Stacks01ct
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModuleLocalIso
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.TensorRightInvertibleEquivalence

/-! # Tensor products and duals of the twisting sheaves on `P^n`

Multiplication and duality of the Serre twists on projective space:
`O(a) ⊗ O(b) ≅ O(a + b)`, `O(a)^∨ ≅ O(-a)`, and `O(0) ≅ O`.

Reference: Stacks 01MS.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
open scoped CategoryTheory.MonoidalCategory

noncomputable section

theorem projectiveSpaceTwist_tensor {k : Type u} [Field k] (n : ℕ) (a b : ℤ) :
    Nonempty (AlgebraicGeometry.Scheme.Modules.tensor (projectiveSpaceTwist k n a) (projectiveSpaceTwist k n b)
      ≅ projectiveSpaceTwist k n (a + b)) := by
  letI : GradedAlgebra (AlgebraicGeometry.Proj.projectiveGrading k n) :=
    MvPolynomial.gradedAlgebra
  let φ := AlgebraicGeometry.Proj.twistMul (AlgebraicGeometry.Proj.projectiveGrading k n) a b
  have hφ : CategoryTheory.IsIso φ := by
    apply AlgebraicGeometry.Scheme.Modules.moduleHom_isIso_of_locally_isIso φ
    intro x
    have hmem : x ∈ ⨆ i : Fin (n + 1),
        AlgebraicGeometry.Proj.basicOpen (AlgebraicGeometry.Proj.projectiveGrading k n)
          (MvPolynomial.X i) := by
      rw [projectiveSpace_iSup_basicOpen_X k n]
      trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hmem
    let U := AlgebraicGeometry.Proj.basicOpen (AlgebraicGeometry.Proj.projectiveGrading k n) (MvPolynomial.X i)
    have hlocal : CategoryTheory.IsIso
        ((AlgebraicGeometry.Scheme.Modules.restrictFunctor U.ι).map φ) := by
      have hh := (AlgebraicGeometry.Proj.twist_mul_isIso_on_basicOpen
        (AlgebraicGeometry.Proj.projectiveGrading k n) (MvPolynomial.X i)
        (MvPolynomial.mem_homogeneousSubmodule 1 _ |>.mpr (MvPolynomial.isHomogeneous_X k i))
        (by decide : 0 < 1) a b).2
      have ha : a * (↑(1 : ℕ) : ℤ) = a := by norm_num
      rw [ha] at hh
      simpa [U, φ] using hh
    exact ⟨U, hi, hlocal⟩
  exact ⟨@CategoryTheory.asIso _ _ _ _ φ hφ⟩

theorem projectiveSpaceTwist_dual {k : Type u} [Field k] (n : ℕ) (a : ℤ) :
    Nonempty (AlgebraicGeometry.Scheme.Modules.dual (projectiveSpaceTwist k n a) ≅ projectiveSpaceTwist k n (-a)) := by
  letI : GradedAlgebra (AlgebraicGeometry.Proj.projectiveGrading k n) :=
    MvPolynomial.gradedAlgebra
  let A : (ProjectiveSpace n k).Modules := projectiveSpaceTwist k n 0
  let FA := CategoryTheory.MonoidalCategory.tensorRight A
  letI : FA.IsEquivalence :=
    AlgebraicGeometry.Scheme.Modules.isEquivalence_tensorRight_of_isLineBundle A
  have eAA₀ : A ⊗ A ≅ A := by
    let e : AlgebraicGeometry.Scheme.Modules.tensor
        (projectiveSpaceTwist k n 0) (projectiveSpaceTwist k n 0) ≅
        projectiveSpaceTwist k n (0 + 0) := Classical.choice (projectiveSpaceTwist_tensor n 0 0)
    simpa [A] using
      (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj A A).symm ≪≫ e
  have eAunit : A ≅ 𝟙_ (ProjectiveSpace n k).Modules := by
    let eF : FA.obj A ≅ FA.obj (𝟙_ (ProjectiveSpace n k).Modules) :=
      eAA₀ ≪≫ (CategoryTheory.MonoidalCategory.leftUnitor A).symm
    exact (FA.asEquivalence.fullyFaithfulFunctor).preimageIso eF
  have eML₀ :
      (projectiveSpaceTwist k n (-a) : (ProjectiveSpace n k).Modules) ⊗
        projectiveSpaceTwist k n a ≅ A := by
    exact (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj
      (projectiveSpaceTwist k n (-a)) (projectiveSpaceTwist k n a)).symm ≪≫
      (Classical.choice (projectiveSpaceTwist_tensor n (-a) a)) ≪≫
      CategoryTheory.eqToIso (by
        rw [show (-a) + a = 0 by ring])
  let L : (ProjectiveSpace n k).Modules := projectiveSpaceTwist k n a
  let M : (ProjectiveSpace n k).Modules := projectiveSpaceTwist k n (-a)
  let FL := CategoryTheory.MonoidalCategory.tensorRight L
  letI : FL.IsEquivalence :=
    AlgebraicGeometry.Scheme.Modules.isEquivalence_tensorRight_of_isLineBundle L
  have eDual :
      FL.obj (AlgebraicGeometry.Scheme.Modules.dual L) ≅ FL.obj M := by
    let u : (AlgebraicGeometry.Scheme.Modules.dual (projectiveSpaceTwist k n a)) ⊗
        projectiveSpaceTwist k n a ≅ 𝟙_ (ProjectiveSpace n k).Modules :=
      β_ _ _ ≪≫
        (AlgebraicGeometry.Scheme.Modules.nonempty_tensorObj_dual_iso_tensorUnit
          (projectiveSpaceTwist k n a)).some
    simpa [FL, L, M, A] using (u ≪≫ eAunit.symm) ≪≫ eML₀.symm
  exact ⟨(FL.asEquivalence.fullyFaithfulFunctor).preimageIso eDual⟩

end
