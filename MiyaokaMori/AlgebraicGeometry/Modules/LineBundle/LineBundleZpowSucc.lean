import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.ModulesLineBundleZpow
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModuleTensorPowerIsoTensorPow
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.Stacks01ct
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModuleTensorAssociator
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModuleTensorUnit

/-! # `L^{n+1} ≅ L^n ⊗ L` for integer powers of a line bundle

`L^{n+1} ≅ L^n ⊗ L` for a line bundle `L` and every `n : ℤ`, where `L ^ n` is the integer tensor power
(`n ≥ 0`: `moduleTensorPower L n = L ⊗ (L ⊗ ⋯)`; `n < 0`: the same power of the dual `L^∨`). This is the
only property of the exponents used in the proof of Snapper's theorem (Stacks 0BEM): the induction there is
run for an abstract family `𝓜 i : ℤ → X.Modules` with `𝓜 i (n+1) ≅ 𝓜 i n ⊗ L i`, so that it can be pulled
back to a closed subscheme without comparing `i^*(L^n)` with `(i^*L)^n`.

Proof: `n = m ≥ 0`: `L^{m+1} = L ⊗ L^m ≅ L^m ⊗ L` (symmetry). `n = −(m+1)`: with `D = L^∨`,
`L^{−(m+1)} = D ⊗ D^m` and `L^{−(m+1)} ⊗ L = (D ⊗ D^m) ⊗ L ≅ (D ⊗ L) ⊗ D^m ≅ (L ⊗ D) ⊗ D^m ≅ O ⊗ D^m ≅ D^m
= L^{−m}` (associativity, symmetry, `L ⊗ L^∨ ≅ O` = Stacks 01CT `tensor_dual_iso`, left unit).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- `(D ⊗ P) ⊗ L ≅ P` when `L ⊗ D ≅ O_X`. -/
def cancelLeftIso {L D : X.Modules} (c : L.tensor D ≅ SheafOfModules.unit X.ringCatSheaf)
    (P : X.Modules) : (D.tensor P).tensor L ≅ P :=
  AlgebraicGeometry.Scheme.Modules.moduleTensorAssociator D P L ≪≫ tensorIsoRight D (tensorSymmIso P L) ≪≫
    (AlgebraicGeometry.Scheme.Modules.moduleTensorAssociator D L P).symm ≪≫
    tensorIsoLeft (tensorSymmIso D L ≪≫ c) P ≪≫ AlgebraicGeometry.Scheme.Modules.moduleTensorLeftUnitIso P

/-- `L^{n+1} ≅ L^n ⊗ L` for every integer `n`. -/
theorem zpow_succ_iso (L : X.Modules) [L.IsLineBundle] (n : ℤ) :
    Nonempty (L ^ (n + 1) ≅ (L ^ n).tensor L) := by
  obtain ⟨c⟩ := SheafOfModules.IsLineBundle.tensor_dual_iso L
  cases n with
  | ofNat m =>
    have h : (Int.ofNat m : ℤ) + 1 = Int.ofNat (m + 1) := rfl
    rw [h]
    exact ⟨tensorSymmIso L (AlgebraicGeometry.Scheme.Modules.moduleTensorPower L m)⟩
  | negSucc m =>
    cases m with
    | zero =>
      have h : Int.negSucc 0 + 1 = Int.ofNat 0 := by decide
      rw [h]
      exact ⟨(cancelLeftIso c (SheafOfModules.unit X.ringCatSheaf)).symm⟩
    | succ m =>
      have h : Int.negSucc (m + 1) + 1 = Int.negSucc m := by
        rw [Int.negSucc_eq, Int.negSucc_eq]; push_cast; ring
      rw [h]
      exact ⟨(cancelLeftIso c (AlgebraicGeometry.Scheme.Modules.moduleTensorPower (AlgebraicGeometry.Scheme.Modules.moduleSheafDual L) (m + 1))).symm⟩

end AlgebraicGeometry.Scheme.Modules

end
