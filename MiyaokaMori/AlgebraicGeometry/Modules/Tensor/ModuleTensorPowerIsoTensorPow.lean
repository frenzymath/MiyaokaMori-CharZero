import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorPower
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.ModulesLineBundleZpow
import MiyaokaMori.AlgebraicGeometry.Cohomology.EulerCharacteristic.EulerCharacteristic
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafCohomologyLinearMap

/-! # The two tensor powers agree

For a sheaf of modules `L` on a scheme `X` and `n ∈ ℕ`, the left-multiplication tensor power
`moduleTensorPower L n` (`L^{⊗0} = O`, `L^{⊗(n+1)} = L ⊗ L^{⊗n}`; this defines `L ^ (n : ℤ)`) and the
right-multiplication tensor power `tensorPow L n` (`tensorPow (n+1) = tensorPow n ⊗ L`; used for
`IsAmple`, Stacks 0B5T, 01Q3) are isomorphic; hence their `H^i` are `K`-linearly isomorphic, their
`h^i` agree and their Euler characteristics agree.

Proof:
1. Induction on `n`. For `n = 0` both sides are `SheafOfModules.unit`; take the identity.
2. For `n + 1`: `L ⊗ L^{⊗n} ≅ L^{⊗n} ⊗ L` (the braiding, sheafified) `≅ tensorPow L n ⊗ L`
   (functoriality of the induction hypothesis in the first variable: `moduleTensor` is the
   sheafification of the sectionwise tensor presheaf, so whisker the presheaf isomorphism on the right
   and sheafify). Only the braiding is used, no associator.
3. Invariance of cohomology and `χ`: isomorphic sheaves of modules have `K`-linearly isomorphic `H^i`
   (`SheafCohomologyLinearMap`).

This is used to put the Euler characteristic `χ(L ^ p)` given by the Snapper polynomial and the
`H^i(tensorPow L n)` given by Serre vanishing into one inequality.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

set_option backward.isDefEq.respectTransparency false in
/-- Swapping the two factors: the braiding of the sectionwise tensor presheaf, sheafified (the same
construction as `AlgebraicGeometry.Scheme.Modules.moduleTensorSymmetry`). -/
def tensorSymmIso (M N : X.Modules) : Scheme.Modules.tensor M N ≅ Scheme.Modules.tensor N M :=
  (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso
    (BraidedCategory.braiding (C := _root_.PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat RingCat)) M.val N.val)

/-- Functoriality of `moduleTensor` in isomorphisms of the first variable. -/
def tensorIsoLeft {M M' : X.Modules} (e : M ≅ M') (N : X.Modules) :
    Scheme.Modules.tensor M N ≅ Scheme.Modules.tensor M' N :=
  (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso
    (MonoidalCategory.whiskerRightIso ((SheafOfModules.forget X.ringCatSheaf).mapIso e) N.val)

/-- Functoriality of `moduleTensor` in isomorphisms of the second variable. -/
def tensorIsoRight (M : X.Modules) {N N' : X.Modules} (e : N ≅ N') :
    Scheme.Modules.tensor M N ≅ Scheme.Modules.tensor M N' :=
  (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).mapIso
    (MonoidalCategory.whiskerLeftIso M.val ((SheafOfModules.forget X.ringCatSheaf).mapIso e))

/-- The left-multiplication tensor power is isomorphic to the right-multiplication tensor power. -/
def moduleTensorPowerIsoTensorPow (L : X.Modules) :
    (n : ℕ) → (AlgebraicGeometry.Scheme.Modules.moduleTensorPower L n ≅ Scheme.Modules.tensorPow L n)
  | 0 => Iso.refl _
  | n + 1 =>
    tensorSymmIso L (AlgebraicGeometry.Scheme.Modules.moduleTensorPower L n) ≪≫
      tensorIsoLeft (moduleTensorPowerIsoTensorPow L n) L

/-- The integer power at a natural number is isomorphic to the right-multiplication tensor power. -/
def zpowNatIsoTensorPow (L : X.Modules) (n : ℕ) :
    L ^ ((n : ℕ) : ℤ) ≅ Scheme.Modules.tensorPow L n :=
  moduleTensorPowerIsoTensorPow L n

/-- With coefficients: `F ⊗ (L ^ n) ≅ F ⊗ tensorPow L n` (the vanishing of Stacks 0B5T is stated for
`F ⊗ tensorPow L n`). -/
def tensorZpowNatIsoTensorTensorPow (F L : X.Modules) (n : ℕ) :
    Scheme.Modules.tensor F (L ^ ((n : ℕ) : ℤ)) ≅
      Scheme.Modules.tensor F (Scheme.Modules.tensorPow L n) :=
  tensorIsoRight F (zpowNatIsoTensorPow L n)

section Invariance

variable (K : Type u) [Field K] [X.Over (Spec (CommRingCat.of K))]

/-- The `H^i` of the two tensor powers are `K`-linearly isomorphic. -/
def sheafCohomologyZpowNatEquiv (L : X.Modules) (n i : ℕ) :
    sheafCohomology X (L ^ ((n : ℕ) : ℤ)) i ≃ₗ[K]
      sheafCohomology X (Scheme.Modules.tensorPow L n) i :=
  sheafCohomology.mapIsoOver K (zpowNatIsoTensorPow L n) i

theorem finrank_sheafCohomology_zpow_nat (L : X.Modules) (n i : ℕ) :
    Module.finrank K (sheafCohomology X (L ^ ((n : ℕ) : ℤ)) i) =
      Module.finrank K (sheafCohomology X (Scheme.Modules.tensorPow L n) i) :=
  sheafCohomology.finrank_eq_of_iso K (zpowNatIsoTensorPow L n) i

theorem subsingleton_sheafCohomology_zpow_nat_iff (L : X.Modules) (n i : ℕ) :
    Subsingleton (sheafCohomology X (L ^ ((n : ℕ) : ℤ)) i) ↔
      Subsingleton (sheafCohomology X (Scheme.Modules.tensorPow L n) i) :=
  (sheafCohomology.mapIso (zpowNatIsoTensorPow L n) i).toEquiv.subsingleton_congr

/-- `χ(L ^ n) = χ(tensorPow L n)`: the Snapper polynomial (stated for `L ^ p`) applies to `tensorPow`. -/
theorem sheafEulerCharacteristic_zpow_nat (L : X.Modules) (n : ℕ) :
    sheafEulerCharacteristic (k := K) X (L ^ ((n : ℕ) : ℤ)) =
      sheafEulerCharacteristic (k := K) X (Scheme.Modules.tensorPow L n) :=
  sheafEulerCharacteristic_eq_of_iso (zpowNatIsoTensorPow L n)

end Invariance

end AlgebraicGeometry.Scheme.Modules

end
