import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafHasextInstance
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.CohomologyLongExactSequence
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafCohomologyLes

/-! # The module structure on sheaf cohomology

The linear structure on sheaf cohomology: `H^n(X, M)` (`Sheaf.H`, an `Ext` group) is a
`Γ(X, O_X)`-module, a global function `r` acting through the endomorphism "multiplication by `r`"
of `M` and the functoriality of `Ext`; when `X` is an `R`-scheme it becomes an `R`-module via
`R → Γ(X, O_X)`. `sheafCohomology X M n` is the version packaged in `ModuleCat Γ(X, ⊤)`.

Universes: `Sheaf.H.{u} … : Type u`, i.e. sheaf cohomology under Mathlib's `HasExt.{u}`
(`IsGrothendieckAbelian.hasExt`; shortcut instance `sheafAddCommGrpHasExt`), which is the same type
as in Mathlib's `TopCat`-level statements (Stacks 02UZ etc.); no universe bridge is needed.

The dimensions `h^i` and the Euler characteristic `χ` used in the paper are taken with respect to
this linear structure.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The underlying abelian sheaf of an `O_X`-module. -/
noncomputable abbrev AlgebraicGeometry.Scheme.Modules.toAddCommGrpSheaf {X : AlgebraicGeometry.Scheme.{u}}
    (M : X.Modules) : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} :=
  (SheafOfModules.toSheaf X.ringCatSheaf).obj M

/-- Restricting a global function `r` to `U` and then to `V` is the same as restricting it directly
to `V` (homs in `Opens` form a subsingleton). -/
private theorem AlgebraicGeometry.Scheme.Modules.res_top_res
    {X : AlgebraicGeometry.Scheme.{u}} (r : Γ(X, ⊤)) {U V : (Opens X)ᵒᵖ} (f : U ⟶ V) :
    (X.ringCatSheaf.obj.map f) ((X.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op) r)
      = (X.presheaf.map (homOfLE (le_top : V.unop ≤ ⊤)).op) r := by
  show (ConcreteCategory.hom (X.presheaf.map f))
      ((ConcreteCategory.hom (X.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op)) r) = _
  rw [← CategoryTheory.comp_apply, ← Functor.map_comp,
    Subsingleton.elim ((homOfLE (le_top : U.unop ≤ ⊤)).op ≫ f)
      (homOfLE (le_top : V.unop ≤ ⊤)).op]

/-- The multiplication endomorphism `μ_r` of the underlying abelian sheaf of `M` by a global
function `r` (multiplication by `r|_U` on an open `U`). -/

noncomputable def AlgebraicGeometry.Scheme.Modules.smulEnd {X : AlgebraicGeometry.Scheme.{u}}
    (M : X.Modules) (r : Γ(X, ⊤)) : M.toAddCommGrpSheaf ⟶ M.toAddCommGrpSheaf where
  hom :=
    { app := fun U => ModuleCat.smul (M.val.obj U)
        (X.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op r)
      -- naturality: `PresheafOfModules.smul_map` and functoriality of restriction in `O_X`
      naturality := fun U V f => by
        have h := (M.val.smul_map f
          (X.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op r)).symm
        rw [AlgebraicGeometry.Scheme.Modules.res_top_res r f] at h
        exact h }

namespace AlgebraicGeometry.Scheme.Modules

theorem smulEnd_app {X : AlgebraicGeometry.Scheme.{u}} (M : X.Modules) (r : Γ(X, ⊤))
    (U : (Opens X)ᵒᵖ) :
    (M.smulEnd r).hom.app U = ModuleCat.smul (M.val.obj U)
      (X.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op r) := rfl

theorem smulEnd_one {X : AlgebraicGeometry.Scheme.{u}} (M : X.Modules) :
    M.smulEnd 1 = 𝟙 _ := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun U => ?_))
  rw [smulEnd_app, map_one]
  exact map_one (ModuleCat.smul (M.val.obj U))

theorem smulEnd_mul {X : AlgebraicGeometry.Scheme.{u}} (M : X.Modules) (r s : Γ(X, ⊤)) :
    M.smulEnd (r * s) = M.smulEnd r ≫ M.smulEnd s := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun U => ?_))
  have hres : (X.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op) (r * s)
      = (X.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op) s *
        (X.presheaf.map (homOfLE (le_top : U.unop ≤ ⊤)).op) r := by
    rw [map_mul, mul_comm]
  rw [smulEnd_app, hres]
  exact map_mul (ModuleCat.smul (M.val.obj U)) _ _

theorem smulEnd_add {X : AlgebraicGeometry.Scheme.{u}} (M : X.Modules) (r s : Γ(X, ⊤)) :
    M.smulEnd (r + s) = M.smulEnd r + M.smulEnd s := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun U => ?_))
  rw [smulEnd_app, map_add]
  exact map_add (ModuleCat.smul (M.val.obj U)) _ _

theorem smulEnd_zero {X : AlgebraicGeometry.Scheme.{u}} (M : X.Modules) :
    M.smulEnd 0 = 0 := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun U => ?_))
  rw [smulEnd_app, map_zero]
  exact map_zero (ModuleCat.smul (M.val.obj U))

/-- The zero morphism induces the zero map on cohomology (`Sheaf.H.map` is additive). -/
private theorem H_map_zero_apply {X : AlgebraicGeometry.Scheme.{u}} (M : X.Modules) (n : ℕ)
    (α : CategoryTheory.Sheaf.H M.toAddCommGrpSheaf n) :
    Sheaf.H.map (0 : M.toAddCommGrpSheaf ⟶ M.toAddCommGrpSheaf) n α = 0 := by
  have h := Sheaf.H.map_add_apply (F := M.toAddCommGrpSheaf) (G := M.toAddCommGrpSheaf)
    (n := n) 0 0 α
  rw [add_zero] at h
  have h2 : Sheaf.H.map (0 : M.toAddCommGrpSheaf ⟶ M.toAddCommGrpSheaf) n α + 0
      = Sheaf.H.map (0 : M.toAddCommGrpSheaf ⟶ M.toAddCommGrpSheaf) n α
        + Sheaf.H.map (0 : M.toAddCommGrpSheaf ⟶ M.toAddCommGrpSheaf) n α := by
    rw [add_zero]; exact h
  exact (add_left_cancel h2).symm

end AlgebraicGeometry.Scheme.Modules

/-- The `Γ(X, ⊤)`-module structure on `H^n(X, M)`: `r • α` is `α` postcomposed with `mk₀ (μ_r)`. -/
noncomputable instance AlgebraicGeometry.Scheme.Modules.moduleSheafH {X : AlgebraicGeometry.Scheme.{u}}
    (M : X.Modules) (n : ℕ) : Module Γ(X, ⊤) (CategoryTheory.Sheaf.H.{u} M.toAddCommGrpSheaf n : Type u) where
  smul r α := α.comp (CategoryTheory.Abelian.Ext.mk₀ (M.smulEnd r)) (add_zero n)
  one_smul α := by
    show Sheaf.H.map (M.smulEnd 1) n α = α
    rw [smulEnd_one, Sheaf.H.map_id_apply]
  mul_smul r s α := by
    show Sheaf.H.map (M.smulEnd (r * s)) n α
      = Sheaf.H.map (M.smulEnd r) n (Sheaf.H.map (M.smulEnd s) n α)
    rw [mul_comm, smulEnd_mul, Sheaf.H.map_comp_apply]
  smul_zero r := by
    show Sheaf.H.map (M.smulEnd r) n 0 = 0
    exact map_zero _
  smul_add r α β := by
    show Sheaf.H.map (M.smulEnd r) n (α + β) = _
    exact map_add _ _ _
  add_smul r s α := by
    show Sheaf.H.map (M.smulEnd (r + s)) n α = _
    rw [smulEnd_add, Sheaf.H.map_add_apply]
    rfl
  zero_smul α := by
    show Sheaf.H.map (M.smulEnd 0) n α = 0
    rw [smulEnd_zero]
    exact AlgebraicGeometry.Scheme.Modules.H_map_zero_apply M n α

/-- Sheaf cohomology `H^n(X, M)` of an `O_X`-module, as an object of `ModuleCat Γ(X, ⊤)`. -/
noncomputable def AlgebraicGeometry.sheafCohomology (X : AlgebraicGeometry.Scheme.{u}) (M : X.Modules)
    (n : ℕ) : ModuleCat.{u} Γ(X, ⊤) :=
  ModuleCat.of Γ(X, ⊤) (CategoryTheory.Sheaf.H.{u} M.toAddCommGrpSheaf n : Type u)

/-- On an `R`-scheme: restriction of scalars along `R ≅ Γ(Spec R, ⊤) → Γ(X, ⊤)`. -/

noncomputable instance AlgebraicGeometry.sheafCohomology.moduleOver {R : Type u} [CommRing R]
    (X : AlgebraicGeometry.Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (CommRingCat.of R))] (M : X.Modules) (n : ℕ) :
    Module R (AlgebraicGeometry.sheafCohomology X M n) :=
  Module.compHom _ (((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
    (X ↘ AlgebraicGeometry.Spec (CommRingCat.of R)).appTop).hom)

end
