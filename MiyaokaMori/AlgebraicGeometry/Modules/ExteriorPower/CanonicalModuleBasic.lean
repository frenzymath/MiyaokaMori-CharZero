import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.LocallyFreeRank
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModuleDual
import MiyaokaMori.AlgebraicGeometry.Modules.ExteriorPower.ModuleExteriorPower
import MiyaokaMori.AlgebraicGeometry.Modules.ExteriorPower.ExteriorDualComparisonIso

/-!
# Exterior power versus dual

The comparison theorem for the sheafified exterior power: exterior power commutes with duality for
a finite locally free module of specified rank (`moduleExteriorPower_dual_iso`, used by `DetDualIso`).

Sources: Stacks Project, `modules.tex`, Symmetric and exterior powers (`lemma-local-tensor-algebra`,
`lemma-pullback-tensor-algebra`) and Rank and determinant.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Proj

universe u

variable {k : Type u} [Field k]

/-- Exterior power commutes with duality for a finite locally free module of specified rank.

The exterior degree `n` is independent of the local rank `r`; both may be zero.
The finite local-frame hypothesis is needed for this duality comparison.
-/
theorem moduleExteriorPower_dual_iso (X : AlgebraicGeometry.Proj.SchemeOver k) (M : X.scheme.Modules)
    (r n : ℕ) (hM : IsLocallyFreeRank X M r) :
    Nonempty (moduleExteriorPower X.scheme (moduleSheafDual M) n ≅
      moduleSheafDual (moduleExteriorPower X.scheme M n)) := by
  -- The isomorphism is the canonical comparison morphism `exteriorDualComparison M n`; it is invertible
  -- by `exteriorDualComparison_isIso_of_local_frames`.
  have := exteriorDualComparison_isIso_of_local_frames M n r hM.local_frame
  exact ⟨asIso (exteriorDualComparison M n)⟩

end AlgebraicGeometry.Scheme.Modules
