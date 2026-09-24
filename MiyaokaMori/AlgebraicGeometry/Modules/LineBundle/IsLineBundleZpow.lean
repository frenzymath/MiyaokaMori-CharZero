import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModulesDual
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.ModulesLineBundleZpow
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModuleTensorPowerIsoTensorPow
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.Stacks01ct

/-! # Integer tensor powers of a line bundle are line bundles

Statement: `X` a scheme, `L` a module on `X`. (1) Being a line bundle depends only on the isomorphism
class: if `M ≅ N` and `M` is a line bundle then so is `N`; (2) if `L` is a line bundle then the
left-recursive tensor power `moduleTensorPower L n` is a line bundle (`n : ℕ`); (3) if `L` is a line
bundle then the integer tensor power `L ^ p` is a line bundle (`p : ℤ`). (3) is registered as an instance,
so that every module writing `L ^ p` obtains it by `inferInstance`.

Proof:
1. (1) Take a local trivialization `U ∋ x`, `i : M|_U ≅ O_U` of `M`; the restriction functor
   `Scheme.Modules.restrictFunctor U.ι` sends `e.symm : N ≅ M` to `N|_U ≅ M|_U`, and composing with `i`
   gives `N|_U ≅ O_U`.
2. (2) `moduleTensorPowerIsoTensorPow L n : moduleTensorPower L n ≅ Scheme.Modules.tensorPow L n`; the
   instance `SheafOfModules.IsLineBundle.tensorPow` says that the right-recursive tensor power is a line
   bundle; transport back along the inverse isomorphism by (1).
3. (3) By cases on `p`: for `p = (n : ℕ)`, `L ^ p` is by definition of `Scheme.Modules.zpow` equal to
   `moduleTensorPower L n`, use (2); for `p = Int.negSucc n`, `L ^ p` is `moduleNegativePower L (n+1)`,
   by definition `moduleTensorPower (moduleSheafDual L) (n+1)`, and the dual is a line bundle
   (`SheafOfModules.IsLineBundle.dual`), then use (2).

Reference: Stacks 01CT (tensor products and duals of invertible sheaves are invertible).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Being a line bundle depends only on the isomorphism class (`restrict` is a functor). Not an instance
(it would make instance search diverge). -/
theorem SheafOfModules.IsLineBundle.of_iso {X : AlgebraicGeometry.Scheme.{u}} {M N : X.Modules}
    (e : M ≅ N) [M.IsLineBundle] : N.IsLineBundle where
  locally_trivial x := by
    obtain ⟨U, hxU, ⟨i⟩⟩ := SheafOfModules.IsLineBundle.locally_trivial (M := M) x
    exact ⟨U, hxU, ⟨(AlgebraicGeometry.Scheme.Modules.restrictFunctor U.ι).mapIso e.symm ≪≫ i⟩⟩

/-- The left-recursive tensor power preserves line bundles (for the right-recursive version see
`IsLineBundle.tensorPow`). -/
instance SheafOfModules.IsLineBundle.moduleTensorPower {X : AlgebraicGeometry.Scheme.{u}}
    (L : X.Modules) [L.IsLineBundle] (n : ℕ) : (AlgebraicGeometry.Scheme.Modules.moduleTensorPower L n).IsLineBundle :=
  SheafOfModules.IsLineBundle.of_iso
    (AlgebraicGeometry.Scheme.Modules.moduleTensorPowerIsoTensorPow L n).symm

/-- Integer tensor powers of a line bundle are line bundles. -/
instance SheafOfModules.IsLineBundle.zpow {X : AlgebraicGeometry.Scheme.{u}} (L : X.Modules)
    [L.IsLineBundle] (p : ℤ) : (L ^ p).IsLineBundle := by
  cases p with
  | ofNat n => exact SheafOfModules.IsLineBundle.moduleTensorPower L n
  | negSucc n =>
    have : (AlgebraicGeometry.Scheme.Modules.moduleSheafDual L).IsLineBundle := SheafOfModules.IsLineBundle.dual L
    exact SheafOfModules.IsLineBundle.moduleTensorPower (AlgebraicGeometry.Scheme.Modules.moduleSheafDual L) (n + 1)

end
