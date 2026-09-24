import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorMonoidalIso
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.VarietyLineBundle
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.IdealSheafToModules
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModulesDual
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.ModulesLineBundleZpow
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensor
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.SheafOfModulesMonoidal
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleTensor
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleTensorPower
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleZpowAddIso
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.Stacks01ct

/-! # Negative powers of a bundled line bundle

The canonical isomorphism `L^{-q} ≅ moduleNegativePower L q` between the negative powers of `LineBundle.zpow`
and the negative tensor power, and the coefficient line bundle
`coefficientLineModule M L q ≅ (M^{1}) ⊗ L^{-q}` (the coefficients `c_{ℓ,q} ∈ H^0(ρ^*A ⊗ L^{-q})`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/- The canonical isomorphism between `L^{-q}` (`LineBundle.zpow` at `-(q : ℤ)`) and
   `moduleNegativePower L q = (L^∨)^{⊗q}`: by cases on `q` both sides agree by definition (for `q = 0` both are
   `O_X`; for `q = n + 1`, `-(↑(n+1)) = Int.negSucc n`), so take the identity. -/

noncomputable def LineBundle.zpowNegIso {k : Type u} [Field k] {X : Variety k} (L : LineBundle X) :
    (q : ℕ) → ((L.zpow (-(q : ℤ))).toModules ≅ AlgebraicGeometry.Scheme.Modules.moduleNegativePower L.toModules q)
  | 0 => CategoryTheory.Iso.refl _
  | _ + 1 => CategoryTheory.Iso.refl _

/- The canonical isomorphism between the two spellings of the coefficient line bundle:
   `coefficientLineModule M L q = Modules.tensor M (L^∨)^{⊗q}` and `(M.zpow 1).tensor (L.zpow (-q))`. The two
   factors use `zpowOneIso` (`M^1 ≅ M`) and `zpowNegIso` above; the tensor product acts on morphisms through
   `Modules.tensor ≅ ⊗`. -/

noncomputable def LineBundle.coefficientModuleIso {k : Type u} [Field k] {X : Variety k}
    (L M : LineBundle X) (q : ℕ) :
    AlgebraicGeometry.Scheme.Modules.coefficientLineModule M.toModules L.toModules q ≅
      ((M.zpow 1).tensor (L.zpow (-(q : ℤ)))).toModules :=
  AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj M.toModules
      (AlgebraicGeometry.Scheme.Modules.moduleNegativePower L.toModules q) ≪≫
    CategoryTheory.MonoidalCategory.tensorIso M.zpowOneIso.symm (L.zpowNegIso q).symm ≪≫
    (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj (M.zpow 1).toModules
      (L.zpow (-(q : ℤ))).toModules).symm

end
