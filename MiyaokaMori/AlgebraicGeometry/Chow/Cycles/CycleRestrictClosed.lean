import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.FirstChernCapPointGeneric
import MiyaokaMori.AlgebraicGeometry.Chow.Pushforward.ClosedImmersionPushforwardRatEquiv

/-! # Restriction of a cycle along a closed immersion

**Restriction of cycles along a closed immersion**: for a closed immersion `i : Z ⟶ X` and a cycle `c` on
`X`, let `(i^♭c)(z′) := c (i z′)`. Local finiteness follows from the injectivity of the closed embedding
(the support of the preimage injects into the original support). Accompanying lemma: when the support of
`c` lies in the image of `i`, `i_*(i^♭c) = c`.

Used for the support refinement of the Gysin map (Stacks 02T9: `c_1(L) ∩ α` is the pushforward of a
class in `CH_*(Z(s))`), where a cycle supported on `D = Z(s)` is pulled back to `D` and pushed forward
again.

Source: Stacks 02T9 (lemma-gysin-fundamental), Stacks 02RZ; the restriction itself is the Lean form of
the usual identification in Fulton, Intersection Theory, §1.4, of cycles supported on a closed subscheme
with cycles on that subscheme.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.AlgebraicCycle

/-- Restriction of a cycle along a closed immersion: `(i^♭c)(z′) = c (i z′)`, with local finiteness proved. -/
def restrictClosed {Z X : AlgebraicGeometry.Scheme.{u}} (i : Z ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion i] (c : AlgebraicGeometry.AlgebraicCycle X ℤ) :
    AlgebraicGeometry.AlgebraicCycle Z ℤ where
  toFun z' := c (i.base z')
  supportWithinDomain' := by simp
  supportLocallyFiniteWithinDomain' := by
    intro z' _
    obtain ⟨t, ht, hfin⟩ := c.supportLocallyFiniteWithinDomain' (i.base z') (by trivial)
    refine ⟨i.base ⁻¹' t, ?_, ?_⟩
    · exact ContinuousAt.preimage_mem_nhds (i.base.hom.continuous.continuousAt) ht
    · have hsub : (i.base ⁻¹' t) ∩ Function.support (fun z' => c (i.base z'))
          ⊆ i.base ⁻¹' (t ∩ Function.support (c : X → ℤ)) := by
        rintro w ⟨hw₁, hw₂⟩
        exact ⟨hw₁, hw₂⟩
      refine Set.Finite.subset ?_ hsub
      exact hfin.preimage
        (((AlgebraicGeometry.IsClosedImmersion.isClosedEmbedding i).injective).injOn)

@[simp]
theorem restrictClosed_apply {Z X : AlgebraicGeometry.Scheme.{u}} (i : Z ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion i] (c : AlgebraicGeometry.AlgebraicCycle X ℤ) (z' : Z) :
    restrictClosed i c z' = c (i.base z') := rfl

/-- A cycle supported in the image of `i` is unchanged by restricting and pushing forward:
`i_*(i^♭c) = c`.

Proof: both sides are cycles on `X`; compare pointwise. Let `x ∈ X`.
* If `x ∉ Set.range i.base`: the right side `c x = 0` (as `supp c ⊆ range i.base`); the coefficient of
  `properPushforward` at `x` is a sum over the points of `i⁻¹{x}` (definition of `AlgebraicCycle.map`),
  which is empty, hence `0`.
* If `x = i z′`: the underlying map of a closed immersion is a closed embedding (injective), and the
  residue field extension `κ(x) → κ(z′)` at `z′` is an isomorphism (the stalk map of a closed immersion is
  surjective, `IsClosedImmersion.stalkMap_surjective`), so the weights `Order.height` of
  `AlgebraicCycle.map` agree and the sum has the single term `z′`, giving `(i^♭c)(z′) = c x`.
  These are the computations of `MiyaokaMori.ClosedImmersionPushforward` for closed immersions.

Source: Stacks 02RZ / Fulton §1.4 (identification of cycles on a closed subscheme with cycles supported
on it). -/
theorem properPushforward_restrictClosed {Z X : AlgebraicGeometry.Scheme.{u}} (i : Z ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion i] [AlgebraicGeometry.IsProper i]
    (c : AlgebraicGeometry.AlgebraicCycle X ℤ)
    (hc : Function.support (c : X → ℤ) ⊆ Set.range i.base) :
    AlgebraicGeometry.AlgebraicCycle.properPushforward i (restrictClosed i c) = c := by
  ext x
  by_cases hx : x ∈ Set.range i.base
  · obtain ⟨z', rfl⟩ := hx
    exact MiyaokaMori.FirstChernCapPointGeneric.properPushforward_closedImmersion_apply i
      (restrictClosed i c) z'
  · have h0 : c x = 0 := by
      by_contra h; exact hx (hc h)
    rw [h0]
    exact MiyaokaMori.ClosedImmersionPushforward.properPushforward_apply_of_notMem_range i _ hx

end AlgebraicGeometry.AlgebraicCycle

end
