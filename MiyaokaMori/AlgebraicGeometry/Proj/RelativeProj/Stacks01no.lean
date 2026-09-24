import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.ProjMapTwistComparison
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.QcPullbackAffineSections
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedQcAlgebraSectionsRing
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.GradedQuasicoherentAlgebra
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.ProjTwistingSheaf
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.Stacks01n2

/-! # Restriction of Proj to a smaller affine open (Stacks 01NO, 01NP)

Stacks 01NO + 01NP: for affine opens `U ⊆ U′`, the restriction `A(U′) → A(U)` induces
`r : Proj A(U) → Proj A(U′)`, and the square `Proj A(U) → Proj A(U′)` over `U → U′` is a pullback;
moreover there is a canonical isomorphism `θ : r^*O_{Proj A(U′)}(n) ≅ O_{Proj A(U)}(n)` compatible
with multiplication and transitive for `U ⊆ U′ ⊆ U″`. This is the local input of the relative Proj
`Y_k^GG = Proj_C 𝒮` of §2 of the paper.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
open scoped HomogeneousIdeal

noncomputable section

theorem AlgebraicGeometry.Scheme.GradedQCAlgebra.isPullback_projMap
    {R R' A B : Type u} [CommRing R] [CommRing R'] [Algebra R R'] [CommRing A] [Algebra R A]
    [CommRing B] [Algebra R B] [Algebra R' B] [IsScalarTower R R' B]
    (𝒜 : ℕ → Submodule R A) (ℬ : ℕ → Submodule R' B)
    [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
    (f : 𝒜 →+*ᵍ ℬ) (hf : ℬ₊ ≤ 𝒜₊.map f) (fR : A →ₐ[R] B)
    (hfR : ∀ a, fR a = f a) (hbc : IsBaseChange R' fR.toLinearMap) :
    CategoryTheory.IsPullback
      (AlgebraicGeometry.Proj.map f hf)
      (AlgebraicGeometry.Proj.toSpecZero ℬ ≫
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap R' (ℬ 0))))
      (AlgebraicGeometry.Proj.toSpecZero 𝒜 ≫
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap R (𝒜 0))))
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap R R'))) := by
  exact AlgebraicGeometry.Proj.isPullback_of_isBaseChange 𝒜 ℬ f hf fR hfR hbc

/-- The twisting-sheaf part of Stacks 01NO: `θ` is an isomorphism. For a quasi-coherent graded algebra
and affine opens `U ⊆ U′` one has `A(U) = O(U) ⊗_{O(U′)} A(U′)`, so `twistPullbackHom` is the
base-change isomorphism of Stacks 01N2. -/
theorem AlgebraicGeometry.Scheme.GradedQCAlgebra.isIso_projMapTwistHom
    {R R' A B : Type u} [CommRing R] [CommRing R'] [Algebra R R'] [CommRing A] [Algebra R A]
    [CommRing B] [Algebra R B] [Algebra R' B] [IsScalarTower R R' B]
    (𝒜 : ℕ → Submodule R A) (ℬ : ℕ → Submodule R' B)
    [GradedAlgebra 𝒜] [GradedAlgebra ℬ]
    (f : 𝒜 →+*ᵍ ℬ) (hf : ℬ₊ ≤ 𝒜₊.map f) (fR : A →ₐ[R] B)
    (hfR : ∀ a, fR a = f a) (hbc : IsBaseChange R' fR.toLinearMap) (n : ℤ) :
    CategoryTheory.IsIso (AlgebraicGeometry.Proj.twistPullbackHom f hf n) := by
  exact AlgebraicGeometry.Proj.isIso_twistPullbackHom 𝒜 ℬ f hf fR hfR hbc n
end
