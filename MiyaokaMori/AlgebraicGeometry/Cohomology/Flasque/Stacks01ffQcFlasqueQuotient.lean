import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.Flasque.Stacks01ffQcFlasqueSurjective

/-! # Quotients of qc-flasque sheaves

In a short exact sequence `0 → F → G → H → 0` of abelian sheaves on a quasi-separated space with a basis of
quasi-compact opens, if `F` is qc-flasque and `G` is flasque then `H` is qc-flasque (Kempf 1980 §2; the
qc-analogue of Mathlib `TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂`). Used in the induction of
`Stacks01ffQcFlasqueAcyclic.lean`. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section

namespace TopCat.Sheaf

variable {X : TopCat.{u}}

/-- (Kempf 1980 §2.) `0 → F → G → H → 0` short exact, `F` qc-flasque, `G` flasque, `X`
quasi-separated with a basis of quasi-compact opens. Then `H` is qc-flasque.

**Proof.** Let `U ≤ V` be quasi-compact opens and `q ∈ H(U)`. By
`IsQcFlasque.surjective_app_of_shortExact` (`U` quasi-compact, `F` qc-flasque) `q = g(b)` for some
`b ∈ G(U)`; as `G` is flasque, `b = b'|_U` with `b' ∈ G(V)`; then `g(b') ∈ H(V)` restricts to
`g(b'|_U) = g(b) = q` by naturality of `g`. -/
theorem IsQcFlasque.of_shortExact [QuasiSeparatedSpace X]
    (hB : TopologicalSpace.Opens.IsBasis {U : TopologicalSpace.Opens X | IsCompact (U : Set X)})
    {S : CategoryTheory.ShortComplex (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})}
    (hS : S.ShortExact) (h₁ : TopCat.Sheaf.IsQcFlasque S.X₁) [TopCat.Sheaf.IsFlasque S.X₂] :
    TopCat.Sheaf.IsQcFlasque S.X₃ := by
  intro U V hU hV h q
  obtain ⟨b, hb⟩ := TopCat.Sheaf.IsQcFlasque.surjective_app_of_shortExact hB hS h₁ U hU q
  obtain ⟨b', hb'⟩ := TopCat.Sheaf.IsQcFlasque.of_isFlasque S.X₂ hU hV h b
  refine ⟨S.g.hom.app (op V) b', ?_⟩
  rw [← TopCat.Sheaf.app_res, hb', hb]

end TopCat.Sheaf

end
