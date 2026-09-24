import MiyaokaMori.Prelude

/-! # Qc-flasque sheaves

Quasi-compact-flasque ("qc-flasque") abelian sheaves on a topological space: `F(V) → F(U)` is surjective for
all quasi-compact opens `U ≤ V`. This is the notion of Kempf, "Some elementary proofs of basic theorems in the
cohomology of quasi-coherent sheaves", Rocky Mountain J. Math. 10 (1980), §2 (there for sheaves on a
quasi-compact quasi-separated scheme; only the topology is used). Every flasque sheaf is qc-flasque.

The notion replaces "flasque" in the Hartshorne III.2.5 / Stacks 09SY argument: on a compact quasi-separated
space with a basis of quasi-compact opens, qc-flasque sheaves are acyclic (`Stacks01ffQcFlasqueAcyclic.lean`),
and a filtered colimit of flasque (e.g. injective) sheaves is qc-flasque
(`Stacks01ffColimitQcFlasque.lean`), which gives the Čech-free proof of the acyclicity of a filtered
colimit of injectives used in Stacks 01FF. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section

namespace TopCat.Sheaf

variable {X : TopCat.{u}}

/-- An abelian sheaf `F` on `X` is **qc-flasque** if for all quasi-compact opens `U ≤ V` the restriction map
`F(V) → F(U)` is surjective (Kempf 1980, §2). Edge cases: `U = ∅` is quasi-compact and `F(∅) = 0`, so the
condition is vacuous there; on a space with no quasi-compact opens other than `∅` every sheaf is qc-flasque.
The definition is a `Prop`-valued `def` (not a class): it is passed around as an explicit hypothesis. -/
def IsQcFlasque (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) : Prop :=
  ∀ {U V : TopologicalSpace.Opens X}, IsCompact (U : Set X) → IsCompact (V : Set X) → (h : U ≤ V) →
    Function.Surjective (F.obj.map (CategoryTheory.homOfLE h).op)

/-- A flasque sheaf is qc-flasque: all its restriction maps are epimorphisms of abelian groups, i.e.
surjective (`AddCommGrpCat.epi_iff_surjective`). -/
theorem IsQcFlasque.of_isFlasque (F : CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    [TopCat.Sheaf.IsFlasque F] : TopCat.Sheaf.IsQcFlasque F := by
  intro U V _ _ h
  exact (AddCommGrpCat.epi_iff_surjective _).1 (TopCat.Presheaf.IsFlasque.epi (F := F.obj) _)

end TopCat.Sheaf

end
