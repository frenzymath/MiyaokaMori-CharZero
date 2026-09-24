import MiyaokaMori.Prelude

/-! # Exterior powers of sheaves of modules

The exterior power `⋀^n E` of an `O_X`-module (the sheafification of the presheaf exterior power),
the ingredient of the determinant line bundle.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The exterior power `⋀^n E` of an `O_X`-module, spelled in the `Scheme.Modules` namespace: a reducible
alias (`abbrev`) of `AlgebraicGeometry.Scheme.Modules.moduleExteriorPower X E n`, the sheafification of the sectionwise exterior-power
presheaf `moduleExteriorPresheaf`. Being reducible, the two spellings are interchangeable for `simp`, `rw`,
`exact` and instance search. -/
abbrev AlgebraicGeometry.Scheme.Modules.exteriorPower
    {X : AlgebraicGeometry.Scheme.{u}} (E : X.Modules) (n : ℕ) : X.Modules :=
  AlgebraicGeometry.Scheme.Modules.moduleExteriorPower X E n

/-- Probe (not used anywhere): a hypothesis stated for the `moduleExteriorPower` spelling rewrites a goal
stated for the `Scheme.Modules.exteriorPower` spelling with plain `rw` (the two spellings sit in argument
position under the common head `Functor.obj`, and `rw` unifies arguments at instances transparency, which
unfolds an `abbrev` but not a `def`) — under the `def` this `rw` failed with "did not find instance of the
pattern". -/
example {X : AlgebraicGeometry.Scheme.{u}} (E : X.Modules) (n : ℕ) (U : X.Opens)
    (A : ModuleCat.{u} Γ(X, U))
    (h : (AlgebraicGeometry.Scheme.Modules.moduleExteriorPower X E n).val.obj (op U) = A) :
    (AlgebraicGeometry.Scheme.Modules.exteriorPower E n).val.obj (op U) = A := by
  rw [h]

end
