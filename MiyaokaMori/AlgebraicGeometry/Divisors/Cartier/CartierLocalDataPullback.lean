import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierDivisorPullback
import MiyaokaMori.AlgebraicGeometry.Divisors.Weil.CartierToWeilUniqueHelpers
import MiyaokaMori.AlgebraicGeometry.Divisors.LineBundle.DivisorLineBundleLocalEquation
import MiyaokaMori.AlgebraicGeometry.Varieties.FunctionField.CurveStalkFunctionField

/-! # Local data of Cartier divisors: local equations and pullback

Two facts about local data of Cartier divisors (Stacks 02OO(2), 01WV):

1. `IsLocalData.exists_isLocalEquation_ofLocalData`: if `(U_i, g_i)` is local data
   (`CartierDivisor.IsLocalData`), then on every nonempty `U_i` the divisor `ofLocalData U g` has a
   local equation `t ∈ 𝒦^*(U_i)` (`IsLocalEquation`) whose value at the generic point is `g_i`.
   Proof: `ofLocalData` is `Classical.epsilon` of exactly this property, and the property is
   satisfiable (`CartierToWeilEpsilon.exists_quotient_section`); packaged in
   `CartierToWeilLocalSection.local_section_ofLocalData`.
2. `IsLocalData.pullback` (and its helper `mem_range_algebraMap_pullback`): for a dominant `f : X → Y`
   of varieties, the pulled-back data `(f^{-1}U_i, f^♯ g_i)` is again local data (Stacks 02OO(2)).
   It lives in `MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierDivisorPullback`, where the
   choice-free definition of `CartierDivisor.pullback` needs it, and is reachable from here through
   that import.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace CartierDivisor

variable {k : Type u} [Field k]

/-- On a nonempty member `U_i` of local data `(U, g)`, the divisor `ofLocalData U g` has a local
equation with generic value `g_i`. -/
theorem IsLocalData.exists_isLocalEquation_ofLocalData {X : Variety k} {ι : Type u}
    {U : ι → X.toScheme.Opens} {g : ι → (X.toScheme.functionField)ˣ} (hUg : IsLocalData U g)
    (i : ι) [hne : Nonempty (U i)] :
    ∃ t : X.toScheme.rationalFunctionsUnitsSheaf.val.obj (op (U i)),
      X.toScheme.rationalUnitsSectionToFunctionField (U i) t = g i ∧
      IsLocalEquation (ofLocalData U g) (U i) t := by
  obtain ⟨⟨x, hx⟩⟩ := hne
  obtain ⟨t, ht, hloc⟩ := CartierToWeilLocalSection.local_section_ofLocalData U g hUg x i hx
  exact ⟨t, ht, hloc⟩

end CartierDivisor

end
