import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPullbackTensor
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorMonoidalIso
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.DualPullbackCommute
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.ModulesLineBundleZpow

/-! # Pullback of line bundles and their integer tensor powers

The pullback of a line bundle is a line bundle, and pullback commutes with integer tensor powers:
`g^*(L^p) ≅ (g^*L)^p`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

/-- Functoriality of the tensor product in both variables for isomorphisms (via
`tensorIsoTensorObj`, using the `⊗` of the monoidal structure). -/
private def tensorMapIso {X : Scheme.{u}} {M M' N N' : X.Modules} (a : M ≅ M') (b : N ≅ N') :
    Scheme.Modules.tensor M N ≅ Scheme.Modules.tensor M' N' :=
  Scheme.Modules.tensorIsoTensorObj M N ≪≫
    CategoryTheory.MonoidalCategory.tensorIso (C := X.Modules) a b ≪≫
    (Scheme.Modules.tensorIsoTensorObj M' N').symm

/-- Pullback commutes with the tensor power `AlgebraicGeometry.Scheme.Modules.moduleTensorPower` (`O_X` in degree `0`,
`L ⊗ (·)^{⊗n}` in degree `n+1`): `g^*(L^{⊗n}) ≅ (g^*L)^{⊗n}`. By induction: degree `0` is
`pullbackUnitIso`; in degree `n+1`, `pullback_tensor` turns `g^*(L ⊗ L^{⊗n})` into
`g^*L ⊗ g^*(L^{⊗n})` and the induction hypothesis acts on the second factor. -/
private theorem pullback_moduleTensorPower {X Y : Scheme.{u}} (g : X ⟶ Y) (L : Y.Modules) :
    ∀ n : ℕ, Nonempty ((Scheme.Modules.pullback g).obj (AlgebraicGeometry.Scheme.Modules.moduleTensorPower L n) ≅
      AlgebraicGeometry.Scheme.Modules.moduleTensorPower ((Scheme.Modules.pullback g).obj L) n)
  | 0 => ⟨Scheme.Modules.pullbackUnitIso g⟩
  | n + 1 => by
    obtain ⟨ih⟩ := pullback_moduleTensorPower g L n
    obtain ⟨e⟩ := Scheme.Modules.pullback_tensor g L (AlgebraicGeometry.Scheme.Modules.moduleTensorPower L n)
    exact ⟨e ≪≫ tensorMapIso (CategoryTheory.Iso.refl _) ih⟩

/-- The tensor power depends only on the isomorphism class of the module (induction on the power). -/
private def moduleTensorPowerMapIso {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N) :
    ∀ n : ℕ, AlgebraicGeometry.Scheme.Modules.moduleTensorPower M n ≅ AlgebraicGeometry.Scheme.Modules.moduleTensorPower N n
  | 0 => CategoryTheory.Iso.refl _
  | n + 1 => tensorMapIso e (moduleTensorPowerMapIso e n)

end AlgebraicGeometry.Scheme.Modules

/-- The pullback of a line bundle `L` is a line bundle, and `g^*(L^p) ≅ (g^*L)^p` for all `p : ℤ`. -/
theorem AlgebraicGeometry.Scheme.Modules.pullback_linePow {X Y : AlgebraicGeometry.Scheme.{u}}
    (g : X ⟶ Y) (L : Y.Modules) [L.IsLineBundle] (p : ℤ) :
    ((AlgebraicGeometry.Scheme.Modules.pullback g).obj L).IsLineBundle ∧
      Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback g).obj (L ^ p) ≅
        ((AlgebraicGeometry.Scheme.Modules.pullback g).obj L) ^ p) := by
  refine ⟨inferInstance, ?_⟩
  cases p with
  | ofNat n =>
    -- `L ^ (n : ℤ) = AlgebraicGeometry.Scheme.Modules.moduleTensorPower L n` (definition of `Scheme.Modules.zpow`)
    exact AlgebraicGeometry.Scheme.Modules.pullback_moduleTensorPower g L n
  | negSucc n =>
    -- L ^ (Int.negSucc n) = AlgebraicGeometry.Scheme.Modules.moduleTensorPower (dual L) (n+1)
    obtain ⟨e₁⟩ := AlgebraicGeometry.Scheme.Modules.pullback_moduleTensorPower g
      (AlgebraicGeometry.Scheme.Modules.dual L) (n + 1)
    obtain ⟨e₂⟩ := AlgebraicGeometry.Scheme.Modules.dual_pullback g L
    exact ⟨e₁ ≪≫ AlgebraicGeometry.Scheme.Modules.moduleTensorPowerMapIso e₂.symm (n + 1)⟩

end
