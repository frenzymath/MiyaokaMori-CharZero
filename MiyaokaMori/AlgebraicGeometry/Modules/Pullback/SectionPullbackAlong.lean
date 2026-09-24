import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle

/-! # Pullback of a global section along a morphism

The pullback `g^*s ∈ Γ(X, g^*M)` of a global section `s ∈ Γ(Y, M)` along `g : X ⟶ Y`: the
component at `⊤` of the unit `M → g_*g^*M` of the pullback–pushforward adjunction.

`sectionPullbackAlong` is the one definition of the pullback of a global section; its body is
the adjunction unit itself. `AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback` is a reducible **`abbrev`** of
`sectionPullbackAlong` whose only job is the type spelling: `sectionPullbackAlong g s` is typed
`(… .val.obj (op ⊤) : Type u)`, the abbrev is typed `Γ(g^*M, ⊤)` (`= (g^*M).presheaf.obj (op ⊤)`,
`rfl` but not syntactically equal), which is the spelling the `pullbackOn` API of
`ModuleSectionPullback` rewrites against (with the other spelling, `rw [restrictIso_hom_restrict]`
in `ModuleChartPullback`, the `OfNat` numeral in `pullback_unit_one`, and the `•` in
`QcPullbackAffineSections` fail). Both spellings are one definition; `unfold`/`simp` see through
the abbrev.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

/-- Pull back a global section `s ∈ Γ(Y, M)` along `g : X ⟶ Y` to `g^*s ∈ Γ(X, g^*M)`: the component at `⊤` of
the unit `M ⟶ g_* g^* M` of the pullback–pushforward adjunction of sheaves of modules. -/
noncomputable def sectionPullbackAlong {X Y : AlgebraicGeometry.Scheme.{u}}
    (g : X ⟶ Y) {M : Y.Modules} (s : (M.val.obj (Opposite.op ⊤) : Type u)) :
    ((((AlgebraicGeometry.Scheme.Modules.pullback g).obj M).val.obj
      (Opposite.op ⊤)) : Type u) :=
  ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M).app ⊤ s

/-- The `Γ(-, ⊤)`-typed spelling of `sectionPullbackAlong g s` (a reducible alias, not a second definition): the
pulled-back global section as an element of `Γ(g^*M, ⊤)`. Used by the `pullbackOn` API
(`ModuleSectionPullback`) and its users; see the module docstring for why the spelling matters. -/
abbrev AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback {X Y : AlgebraicGeometry.Scheme.{u}} (g : X ⟶ Y) {M : Y.Modules}
    (s : Γ(M, ⊤)) : Γ((AlgebraicGeometry.Scheme.Modules.pullback g).obj M, ⊤) :=
  sectionPullbackAlong g s

/-- The two spellings are one term (`rfl`). To reach the `Γ`-typed spelling (and then rewrite with the `pullbackOn`
API), rewrite with this lemma; unfolding `sectionPullbackAlong` goes straight to the adjunction unit. **Use it with explicit arguments** (`rw [sectionPullbackAlong_eq_pullback g s]`) or
use a `change` to the `Γ`-typed spelling: an occurrence `sectionPullbackAlong g s` whose argument `s` is itself
`Γ`-typed (e.g. `s : Γ(M, ⊤)` from a statement, or `s = sectionPullbackAlong h t`) is not type-correct at reducible
transparency, so `simp only [sectionPullbackAlong_eq_pullback]` / `rw` with metavariables cannot abstract it.
`erw` with a
`pullbackOn`-API lemma unifies the two spellings at default transparency and needs no bridge. -/
theorem sectionPullbackAlong_eq_pullback {X Y : AlgebraicGeometry.Scheme.{u}} (g : X ⟶ Y) {M : Y.Modules}
    (s : (M.val.obj (Opposite.op ⊤) : Type u)) :
    sectionPullbackAlong g s = AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback g s := rfl

end
