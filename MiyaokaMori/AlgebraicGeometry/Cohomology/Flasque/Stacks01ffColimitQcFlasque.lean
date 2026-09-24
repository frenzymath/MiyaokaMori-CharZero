import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.Flasque.Stacks01ffQcFlasque
import MiyaokaMori.AlgebraicGeometry.Cohomology.Flasque.Stacks01ffSectionsColimit

/-! # A filtered colimit of flasque sheaves is qc-flasque

On a quasi-separated space with a basis of quasi-compact opens, a filtered colimit of flasque abelian sheaves is
qc-flasque (`TopCat.Sheaf.IsQcFlasque`): for quasi-compact opens `U ≤ V`, every section of `colim I` over `U`
comes from some `I_j(U)` (`sections_colimit_bijective_of_isCompact`), extends to `I_j(V)` since `I_j`
is flasque, and its image in `(colim I)(V)` restricts to the given section.

Used for Stacks 01FF (Čech-free route via Kempf's qc-flasque sheaves) with `I_j` injective, hence
flasque (Stacks 09SX). -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section

namespace TopCat.Sheaf

/-- Let `X` be quasi-separated with a basis of quasi-compact opens, `J` small filtered and
`I : J ⥤ Sh(X, Ab)` with every `I_j` flasque. Then `colim I` is qc-flasque.

**Proof.** Let `U ≤ V` be quasi-compact opens and `t ∈ (colim I)(U)`. By the surjectivity half of
`TopCat.Sheaf.sections_colimit_bijective_of_isCompact` (applied to `U`) there are `j` and `s ∈ I_j(U)` with
`ι_j(s) = t`. Since `I_j` is flasque, `I_j(V) → I_j(U)` is surjective: `s = s'|_U` for some `s' ∈ I_j(V)`.
Then `ι_j(s') ∈ (colim I)(V)` and, by naturality of `ι_j : I_j ⟶ colim I` with respect to the restriction
`U ≤ V`, `ι_j(s')|_U = ι_j(s'|_U) = ι_j(s) = t`. Edge cases: `U = ∅` is trivial (`(colim I)(∅) = 0`); `J` is
nonempty because it is filtered, so `j` exists. Only the surjectivity half of the sections lemma is used. -/
theorem isQcFlasque_colimit_of_isFlasque {X : TopCat.{u}} [QuasiSeparatedSpace X]
    (hB : TopologicalSpace.Opens.IsBasis {U : TopologicalSpace.Opens X | IsCompact (U : Set X)})
    {J : Type u} [CategoryTheory.SmallCategory J] [CategoryTheory.IsFiltered J]
    (I : J ⥤ CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (hI : ∀ j, TopCat.Sheaf.IsFlasque (I.obj j)) :
    TopCat.Sheaf.IsQcFlasque (CategoryTheory.Limits.colimit I) := by
  intro U V hU hV h t
  obtain ⟨j, s, hs⟩ := (TopCat.Sheaf.sections_colimit_bijective_of_isCompact hB I U hU).1 t
  have := hI j
  obtain ⟨s', hs'⟩ := TopCat.Sheaf.IsQcFlasque.of_isFlasque (I.obj j) hU hV h s
  refine ⟨(colimit.ι I j).hom.app (op V) s', ?_⟩
  rw [← hs, ← hs', ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply,
    (colimit.ι I j).hom.naturality]

end TopCat.Sheaf

end
