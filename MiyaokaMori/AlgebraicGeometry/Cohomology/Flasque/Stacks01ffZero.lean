import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.Flasque.Stacks01ffSes
import MiyaokaMori.AlgebraicGeometry.Cohomology.Flasque.Stacks01ffSectionsColimit

/-! # Stacks 01FF in degree zero

The case `q = 0` of Stacks 01FF (cohomology-lemma-quasi-separated-cohomology-colimit): `H^0(X, -) = Γ(X, -)`
(Mathlib `Sheaf.H.equiv₀`, natural by `H.equiv₀_naturality`), so `Stmt F 0` is the sections statement
`TopCat.Sheaf.sections_colimit_bijective_of_isCompact` at `U = ⊤`, which is compact since `X` is. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section

namespace Stacks01ff

variable {X : TopCat.{u}} {J : Type u} [SmallCategory J]

theorem isCompact_top [CompactSpace X] : IsCompact ((⊤ : Opens X) : Set X) := by
  rw [Opens.coe_top]; exact isCompact_univ

/-- Degree `0`: `H^0 = Γ(X, -)` and `sections_colimit_bijective_of_isCompact` with `U = X`. -/
theorem stmt_zero [CompactSpace X] [QuasiSeparatedSpace X] [IsFiltered J]
    (hB : Opens.IsBasis {U : Opens X | IsCompact (U : Set X)})
    (F : J ⥤ Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) : Stmt F 0 := by
  have hT : IsTerminal (⊤ : Opens X) := isTerminalTop
  have hA := TopCat.Sheaf.sections_colimit_bijective_of_isCompact hB F ⊤ isCompact_top
  constructor
  · intro x
    obtain ⟨j, s, hs⟩ := hA.1 (Sheaf.H.equiv₀ (colimit F) hT x)
    refine ⟨j, (Sheaf.H.equiv₀ (F.obj j) hT).symm s, ?_⟩
    apply (Sheaf.H.equiv₀ (colimit F) hT).injective
    rw [← Sheaf.H.map_apply, ← Sheaf.H.equiv₀_naturality, AddEquiv.apply_symm_apply, hs]
  · intro j e he
    have h1 : (colimit.ι F j).hom.app (op ⊤) (Sheaf.H.equiv₀ (F.obj j) hT e) = 0 := by
      rw [Sheaf.H.equiv₀_naturality, Sheaf.H.map_apply, he, map_zero]
    obtain ⟨k, a, ha⟩ := hA.2 j _ h1
    refine ⟨k, a, ?_⟩
    apply (Sheaf.H.equiv₀ (F.obj k) hT).injective
    rw [← Sheaf.H.map_apply, ← Sheaf.H.equiv₀_naturality, ha, map_zero]


end Stacks01ff

end
