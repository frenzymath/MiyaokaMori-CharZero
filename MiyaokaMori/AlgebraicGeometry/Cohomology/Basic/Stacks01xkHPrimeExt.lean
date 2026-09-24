import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafCohomologyTopLinearEquiv
import MiyaokaMori.AlgebraicGeometry.Cohomology.Vanishing.Stacks01xb
import MiyaokaMori.CategoryTheory.ExtActionMayerVietoris
import Mathlib.Topology.Sheaves.MayerVietoris

/-! # `Sheaf.H'` of a module as `Ext` with the `Γ(X, O_X)`-action

**`Sheaf.H'` of a module on a scheme, read as `Ext` with the `Γ(X, O_X)`-action, and the bridges
to the existing library.**

For a module `M` on a scheme `X` with underlying abelian sheaf `F = M.toAddCommGrpSheaf`, Mathlib's
`F.H' n V` is by definition `Ext (ℤ[h_V]^#, F, n)` where `ℤ[h_V]^# = (freeSheafFunctor X).obj V`.
`Γ(X, ⊤)` acts on `F` by `M.smulEnd` (multiplication by a global function), which is an
`ExtAction Γ(X, ⊤) F` (`smulEndAction`); the resulting module
structure on `E M V n := Ext (ℤ[h_V]^#, F, n)` is *definitionally* `Scheme.Modules.moduleSheafH'`.
The generic Mayer–Vietoris machinery of `ExtAction` applies to the image under
`freeSheafFunctor X` of the Mayer–Vietoris square of two opens (`mvShortExact`: its short complex is
literally Mathlib's `MayerVietorisSquare.shortComplex`, which is short exact).

Bridges: `eTopLinearEquiv : E M ⊤ n ≃ₗ[Γ(X,⊤)] sheafCohomology X M n`
(`sheafCohomologyTopLinearEquiv`) and
`subsingleton_E_of_isAffineOpen` (Serre vanishing on affine opens, Stacks 01XB).

The module structures are *local* instances (`smulEndAction`, `ExtAction.module`); no global instance
is added. Each concrete declaration here costs the kernel several seconds (instance-path comparison on
`Ext` for the concrete `HasExt` instance of the sheaf category, Mathlib's
`IsGrothendieckAbelian.hasExt` at universe `u` via the shortcut `sheafAddCommGrpHasExt`), so this
file is kept short.

Source: Mathlib `Sites/SheafCohomology/Basic.lean`, `Sites/SheafCohomology/MayerVietoris.lean`. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

open CategoryTheory.Abelian CategoryTheory.Abelian.Ext

variable {X : AlgebraicGeometry.Scheme.{u}} (M : X.Modules)

/-- The free abelian sheaf functor `V ↦ ℤ[h_V]^#` on the opens of `X` (the first variable of
`Sheaf.H'`). -/
abbrev freeSheafFunctor (X : AlgebraicGeometry.Scheme.{u}) :
    X.Opens ⥤ Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  yoneda ⋙ (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙
    presheafToSheaf (Opens.grothendieckTopology X) _

/-- `Γ(X, ⊤)` acts on the abelian sheaf underlying `M` by multiplication (`M.smulEnd`). -/
@[instance_reducible] def smulEndAction : ExtAction Γ(X, ⊤) M.toAddCommGrpSheaf where
  μ := M.smulEnd
  μ_one := smulEnd_one M
  μ_mul := smulEnd_mul M
  μ_add := smulEnd_add M
  μ_zero := smulEnd_zero M

attribute [local instance] smulEndAction ExtAction.module

/-- `E M V n = Ext(ℤ[h_V]^#, M, n)`: the cohomology `H'ⁿ(V, M)` of the open `V`, in `Ext` form
(definitionally `M.toAddCommGrpSheaf.H' n V`, with the same `Γ(X, ⊤)`-module structure). -/
abbrev E (V : X.Opens) (n : ℕ) : Type u :=
  Ext ((freeSheafFunctor X).obj V) M.toAddCommGrpSheaf n

/-- `E M ⊤ n ≃ₗ[Γ(X,⊤)] H^n(X, M)`: `sheafCohomologyTopLinearEquiv` read on `E`. -/
def eTopLinearEquiv (n : ℕ) : E M ⊤ n ≃ₗ[Γ(X, ⊤)] AlgebraicGeometry.sheafCohomology X M n :=
  sheafCohomologyTopLinearEquiv M n

/-- Serre vanishing (Stacks 01XB) read on `E`: `H'ᵖ(U, M) = 0` for `U` affine, `p > 0`,
`M` quasi-coherent. -/
theorem subsingleton_E_of_isAffineOpen [M.IsQuasicoherent] {U : X.Opens} (hU : IsAffineOpen U)
    (p : ℕ) (hp : 0 < p) : Subsingleton (E M U p) :=
  sheafCohomology'_affineOpen_vanishing M hU p hp

/-- The Mayer–Vietoris square `ℤ[V ⊓ W] → ℤ[V], ℤ[W] → ℤ[V ⊔ W]` of two opens, on free abelian
sheaves (written out as a structure literal so that its projections reduce immediately; it is
definitionally the image of `Opens.mayerVietorisSquare V W` under `freeSheafFunctor X`). -/
abbrev mvSquare (V W : X.Opens) : Square (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) where
  X₁ := (freeSheafFunctor X).obj (V ⊓ W)
  X₂ := (freeSheafFunctor X).obj V
  X₃ := (freeSheafFunctor X).obj W
  X₄ := (freeSheafFunctor X).obj (V ⊔ W)
  f₁₂ := (freeSheafFunctor X).map (homOfLE inf_le_left)
  f₁₃ := (freeSheafFunctor X).map (homOfLE inf_le_right)
  f₂₄ := (freeSheafFunctor X).map (homOfLE le_sup_left)
  f₃₄ := (freeSheafFunctor X).map (homOfLE le_sup_right)
  fac := by
    rw [← (freeSheafFunctor X).map_comp, ← (freeSheafFunctor X).map_comp]
    exact congrArg _ (Subsingleton.elim _ _)

omit M in
/-- The short complex `ℤ[V ⊓ W] → ℤ[V] ⊞ ℤ[W] → ℤ[V ⊔ W]` is short exact (Mathlib's
`MayerVietorisSquare.shortComplex_shortExact` for `Opens.mayerVietorisSquare V W`; the two short
complexes are definitionally equal). -/
theorem mvShortExact (V W : X.Opens) : (mvSquare (X := X) V W).mvShortComplex.ShortExact :=
  (Opens.mayerVietorisSquare V W).shortComplex_shortExact

/-- Transport of the localization property of a restriction map along an equality of the target
open. -/
theorem isLocalizedModule_precompLinear_congr (S : Submonoid Γ(X, ⊤)) {V W₁ W₂ : X.Opens}
    (e : W₁ = W₂) (h₁ : W₁ ≤ V) (h₂ : W₂ ≤ V) (q : ℕ)
    (h : IsLocalizedModule S
      (precompLinear Γ(X, ⊤) M.toAddCommGrpSheaf ((freeSheafFunctor X).map (homOfLE h₁)) q)) :
    IsLocalizedModule S
      (precompLinear Γ(X, ⊤) M.toAddCommGrpSheaf ((freeSheafFunctor X).map (homOfLE h₂)) q) := by
  subst e
  exact h

end AlgebraicGeometry.Scheme.Modules

end
