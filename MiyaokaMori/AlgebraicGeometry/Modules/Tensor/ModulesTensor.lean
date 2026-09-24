import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.SheafOfModulesMonoidal

/-! # Tensor product of sheaves of modules

The tensor product `V ⊗_{O_X} W` of two `O_X`-modules (the sheafification of the presheaf tensor
product).

The tensor product has **one** definition in the library: `AlgebraicGeometry.Scheme.Modules.moduleTensor`
(`ModuleTensorPowers`, the sheafification of Mathlib's sectionwise tensor presheaf
`PresheafOfModules.Monoidal.tensorObj`), which carries the section API (`moduleTensorSection`,
`moduleTensorSection_restrict`, symmetry, unit, associator, …).
`AlgebraicGeometry.Scheme.Modules.tensor` is only the spelling of that definition in the
`Scheme.Modules` namespace. It is an `abbrev`, so both spellings are the same term up to reducible
unfolding and `simp`/`rw`/instance search treat them alike (see the `example`s at the end of this
file).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The tensor product `V ⊗_{O_X} W` of two `O_X`-module sheaves, spelled in the `Scheme.Modules`
namespace. This is an `abbrev` (reducible) of the one definition `AlgebraicGeometry.Scheme.Modules.moduleTensor`, not a
second definition: `Scheme.Modules.tensor V W` and `AlgebraicGeometry.Scheme.Modules.moduleTensor V W` are interchangeable for
`simp`, `rw`, `exact` and instance search. -/
abbrev AlgebraicGeometry.Scheme.Modules.tensor {X : AlgebraicGeometry.Scheme.{u}}
    (V W : X.Modules) : X.Modules :=
  AlgebraicGeometry.Scheme.Modules.moduleTensor V W

/-- Check (not used anywhere): a lemma stated for the `moduleTensor` spelling rewrites a goal stated
for the `Scheme.Modules.tensor` spelling with plain `rw`. -/
example {X : AlgebraicGeometry.Scheme.{u}} {M N : X.Modules} {U V : X.Opens} (j : V ⟶ U)
    (s : Γ(M, U)) (t : Γ(N, U)) :
    (AlgebraicGeometry.Scheme.Modules.tensor M N).presheaf.map j.op
        (AlgebraicGeometry.Scheme.Modules.moduleTensorSection s t) =
      AlgebraicGeometry.Scheme.Modules.moduleTensorSection (M.presheaf.map j.op s) (N.presheaf.map j.op t) := by
  rw [AlgebraicGeometry.Scheme.Modules.moduleTensorSection_restrict]

/-- Check (not used anywhere): the two spellings are interchangeable for `simp` as well. -/
example {X : AlgebraicGeometry.Scheme.{u}} {M N : X.Modules} {U V : X.Opens} (j : V ⟶ U)
    (s : Γ(M, U)) (t : Γ(N, U)) :
    (AlgebraicGeometry.Scheme.Modules.tensor M N).presheaf.map j.op
        (AlgebraicGeometry.Scheme.Modules.moduleTensorSection s t) =
      AlgebraicGeometry.Scheme.Modules.moduleTensorSection (M.presheaf.map j.op s) (N.presheaf.map j.op t) := by
  simp

end
