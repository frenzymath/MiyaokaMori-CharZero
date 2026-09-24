import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafHasextInstance
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafCohomologyModule
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafCohomologyTopIso

/-! # Module structures on `Ext` and on the cohomology presheaf

The `Γ(X,⊤)`-module structures needed for the linear version of `H'(M, n, ⊤) ≃ H(M, n)`.

* `extModule`: for an arbitrary first variable `A`, the `Γ(X,⊤)`-module structure on `Ext(A, M)`
  induced by the endomorphisms `M.smulEnd r` (multiplication by a global function `r`). For
  `A` = the constant sheaf this is `Scheme.Modules.moduleSheafH` (the one used by
  `sheafCohomology`); for `A = ℤ[h_U]^#` it gives the module structure on `H'(M, n, U)`
  (`moduleSheafH'`).
The linear isomorphism itself (`sheafCohomologyTopLinearEquiv`) is in
`SheafCohomologyTopLinearEquiv.lean`. (The split into two modules is only for compile time: both
places check the large definitional equality between `↥(H' n U)` and `Ext (ℤ[h_U]^#) M n`.)

Source: Stacks 01XB.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option warn.classDefReducibility false

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- In a general abelian category: if a commutative ring `R` acts on an object `Y` through
`μ : R → End Y` (compatible with one, multiplication, addition and zero; `μ` is contravariant in
multiplication, which does not matter since `R` is commutative), then `Ext A Y n` is an `R`-module
with scalar multiplication "postcomposition with `mk₀ (μ r)`". The first variable `A` is arbitrary;
this gives the module structures on `Sheaf.H` (`A` = constant sheaf) and on `Sheaf.H'`
(`A = ℤ[h_U]^#`) by one formula. -/
def CategoryTheory.Abelian.Ext.moduleOfEndHom {C : Type*} [CategoryTheory.Category C]
    [CategoryTheory.Abelian C] [CategoryTheory.HasExt C] {R : Type*} [CommRing R] (A Y : C)
    (μ : R → (Y ⟶ Y)) (hone : μ 1 = 𝟙 Y) (hmul : ∀ r s, μ (r * s) = μ r ≫ μ s)
    (hadd : ∀ r s, μ (r + s) = μ r + μ s) (hzero : μ 0 = 0) (n : ℕ) :
    Module R (CategoryTheory.Abelian.Ext A Y n) where
  smul r α := α.comp (CategoryTheory.Abelian.Ext.mk₀ (μ r)) (add_zero n)
  one_smul α := by
    show α.comp (CategoryTheory.Abelian.Ext.mk₀ (μ 1)) (add_zero n) = α
    rw [hone, CategoryTheory.Abelian.Ext.comp_mk₀_id]
  mul_smul r s α := by
    show α.comp (CategoryTheory.Abelian.Ext.mk₀ (μ (r * s))) (add_zero n)
      = (α.comp (CategoryTheory.Abelian.Ext.mk₀ (μ s)) (add_zero n)).comp
          (CategoryTheory.Abelian.Ext.mk₀ (μ r)) (add_zero n)
    rw [mul_comm, hmul, ← CategoryTheory.Abelian.Ext.mk₀_comp_mk₀,
      ← CategoryTheory.Abelian.Ext.comp_assoc_of_third_deg_zero]
  smul_zero r := CategoryTheory.Abelian.Ext.zero_comp _ _ _ _ _
  smul_add r α β := CategoryTheory.Abelian.Ext.add_comp _ _ _ _
  add_smul r s α := by
    show α.comp (CategoryTheory.Abelian.Ext.mk₀ (μ (r + s))) (add_zero n) = _
    rw [hadd, CategoryTheory.Abelian.Ext.mk₀_add, CategoryTheory.Abelian.Ext.comp_add]
    rfl
  zero_smul α := by
    show α.comp (CategoryTheory.Abelian.Ext.mk₀ (μ 0)) (add_zero n) = 0
    rw [hzero, CategoryTheory.Abelian.Ext.mk₀_zero, CategoryTheory.Abelian.Ext.comp_zero]

namespace AlgebraicGeometry

open CategoryTheory.Abelian AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- For any first variable `A`, the `Γ(X,⊤)`-module structure on `Ext(A, M)` given by the
multiplication endomorphisms by global functions. Literally the same formula as
`Scheme.Modules.moduleSheafH` (the case `A` = constant sheaf). -/
def Scheme.Modules.extModule
    (A : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (M : X.Modules) (n : ℕ) :
    Module Γ(X, ⊤) (Ext A M.toAddCommGrpSheaf n) :=
  Ext.moduleOfEndHom A M.toAddCommGrpSheaf M.smulEnd (smulEnd_one M) (smulEnd_mul M)
    (smulEnd_add M) (smulEnd_zero M) n

/-- The `Γ(X,⊤)`-module structure on `H'(M, n, U)`. -/
instance Scheme.Modules.moduleSheafH' (M : X.Modules) (n : ℕ) (U : X.Opens) :
    Module Γ(X, ⊤) (M.toAddCommGrpSheaf.H' n U : Type u) :=
  Scheme.Modules.extModule _ M n

end AlgebraicGeometry

end
