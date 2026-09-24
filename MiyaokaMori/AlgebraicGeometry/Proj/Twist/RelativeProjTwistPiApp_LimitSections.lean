import MiyaokaMori.Prelude

/-! # Sections of a limit of `𝒪_Y`-modules

Statement. Let `Y` be a scheme, `D : J ⥤ Y.Modules` a diagram of `𝒪_Y`-modules and `c` a limit cone of `D`
(for example `c.pt = lim D`). For every open `Ω ⊆ Y`, the sections `Γ(Ω, c.pt)` are the compatible families:
* (`limitCone_sections_ext`) two sections `s, t ∈ Γ(Ω, c.pt)` with `(c.π.app j).app Ω s = (c.π.app j).app Ω t`
  for every `j` are equal;
* (`limitCone_sections_exists`) every family `x_j ∈ Γ(Ω, D j)` with `(D.map f).app Ω (x_i) = x_j` for all
  `f : i ⟶ j` is `(c.π.app j).app Ω s` for some `s ∈ Γ(Ω, c.pt)`.

Proof. `Scheme.Modules.Hom.app φ Ω` is the underlying map of `(SheafOfModules.evaluation _ (op Ω)).map φ`
(by definition). Evaluation at `op Ω` preserves limits of sheaves of modules (Mathlib
`SheafOfModules.evaluationPreservesLimit`), and so does the forgetful functor `ModuleCat → Type`
(`ModuleCat.forget_preservesLimits`); hence the image of `c` under `E := evaluation ⋙ forget` is a limit cone
in `Type` (`isLimitOfPreserves`), and `Types.isLimitEquivSections` identifies `Γ(Ω, c.pt)` with the sections
`(D ⋙ E).sections` (compatible families), the identification being `s ↦ (j ↦ (c.π.app j).app Ω s)`
(`Types.isLimitEquivSections_apply`, `Types.isLimitEquivSections_symm_apply`). Injectivity of that
identification is the first statement, surjectivity the second.

Source: Stacks 01LI (proof; sections of the glued module), Mathlib `SheafOfModules.evaluationPreservesLimit`.
Edge cases: `Ω = ∅` (all groups are zero; both statements trivial); `J` empty (the limit is the
terminal object, `Γ(Ω, c.pt)` is a singleton: `ext` says exactly that, `exists` is trivially satisfied).
-/

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {Y : Scheme.{u}}

/-- Sections over `Ω` as a set-valued functor on `𝒪_Y`-modules: evaluation at `op Ω` followed by the
forgetful functor `ModuleCat Γ(Y, Ω) ⥤ Type`. -/
def sectionsType (Ω : Y.Opens) : Y.Modules ⥤ Type u :=
  SheafOfModules.evaluation Y.ringCatSheaf (op Ω) ⋙ CategoryTheory.forget _

/-- `sectionsType Ω` preserves all limits (evaluation preserves limits of sheaves of modules; so does the
forgetful functor of `ModuleCat`). Not a global instance: use
`have := sectionsType_preservesLimitsOfSize Ω` locally. -/
theorem sectionsType_preservesLimitsOfSize (Ω : Y.Opens) :
    PreservesLimitsOfSize.{u, u} (sectionsType Ω) := by
  unfold sectionsType
  exact @comp_preservesLimits _ _ _ _ _ _ _ _
    (SheafOfModules.evaluationPreservesLimitsOfSize.{u, u} Y.ringCatSheaf (op Ω))
    ModuleCat.forget_preservesLimitsOfSize.{u, u, u}

/-- `Hom.app` is the action of `sectionsType Ω` on morphisms (definitional). -/
theorem sectionsType_map_apply {M N : Y.Modules} (φ : M ⟶ N) (Ω : Y.Opens) (x : Γ(M, Ω)) :
    (sectionsType Ω).map φ x = φ.app Ω x := rfl

variable {J : Type u} [Category.{u} J] {D : J ⥤ Y.Modules}

/-- Sections of a limit cone are determined by their projections. -/
theorem limitCone_sections_ext {c : Cone D} (hc : IsLimit c) (Ω : Y.Opens) {s t : Γ(c.pt, Ω)}
    (h : ∀ j, (c.π.app j).app Ω s = (c.π.app j).app Ω t) : s = t := by
  have := sectionsType_preservesLimitsOfSize (Y := Y) Ω
  have hc' : IsLimit ((sectionsType Ω).mapCone c) := isLimitOfPreserves (sectionsType Ω) hc
  exact (Types.isLimitEquivSections hc').injective (Subtype.ext (funext fun j => h j))

/-- Every compatible family of sections of the `D j` over `Ω` comes from a section of the limit. -/
theorem limitCone_sections_exists {c : Cone D} (hc : IsLimit c) (Ω : Y.Opens)
    (x : ∀ j, Γ(D.obj j, Ω)) (hx : ∀ {i j : J} (f : i ⟶ j), (D.map f).app Ω (x i) = x j) :
    ∃ s : Γ(c.pt, Ω), ∀ j, (c.π.app j).app Ω s = x j := by
  have := sectionsType_preservesLimitsOfSize (Y := Y) Ω
  have hc' : IsLimit ((sectionsType Ω).mapCone c) := isLimitOfPreserves (sectionsType Ω) hc
  refine ⟨(Types.isLimitEquivSections hc').symm ⟨x, fun f => hx f⟩, fun j => ?_⟩
  exact Types.isLimitEquivSections_symm_apply hc' ⟨x, fun f => hx f⟩ j

end AlgebraicGeometry.Scheme.Modules

end
