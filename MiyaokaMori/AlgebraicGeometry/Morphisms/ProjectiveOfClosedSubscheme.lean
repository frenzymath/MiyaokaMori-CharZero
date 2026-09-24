import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProjectiveOverField

/-! # Closed subschemes of a projective `k`-scheme are projective

A closed subscheme of a projective `k`-scheme is again projective over `k`.

Reference: Stacks Project, Tags 01WC / 0B45 (a composition of closed immersions is a closed immersion);
`IsProjectiveOver` is defined as "there exists a `k`-closed immersion into some `ProjectiveSpace N k`",
so the lemma is just a composition.

Typical use: in the induction proving Snapper's theorem for projective schemes, `X` is replaced by a
`d`-dimensional integral closed subscheme or by an effective Cartier divisor, and both must be shown to
be projective again.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- A `k`-closed subscheme of a projective `k`-scheme is projective: compose `Z ↪ X` with `X ↪ P^N_k`. -/
theorem IsProjectiveOver.of_isClosedImmersion {k : Type u} [Field k]
    {Z X : AlgebraicGeometry.Scheme.{u}}
    [Z.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (ι : Z ⟶ X) [AlgebraicGeometry.IsClosedImmersion ι]
    [ι.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (hX : IsProjectiveOver k X) : IsProjectiveOver k Z := by
  obtain ⟨N, i, hi, hio⟩ := hX
  have : AlgebraicGeometry.IsClosedImmersion i := hi
  have : i.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) := hio
  refine ⟨N, ι ≫ i, inferInstance, ⟨?_⟩⟩
  rw [Category.assoc, hio.1,
    (inferInstance : ι.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))).1]

end
