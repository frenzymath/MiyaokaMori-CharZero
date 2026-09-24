import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.RationalEquivalence.RationalEquivalenceX
import MiyaokaMori.AlgebraicGeometry.Chow.Pushforward.Stacks02s2SchemeGenerator
import MiyaokaMori.AlgebraicGeometry.Chow.Pushforward.Stacks02s2SchemeLocallyFinite

/-! # Proper pushforward preserves rational equivalence (Stacks 02S2, scheme version)

Stacks 02S2 at the level of schemes: for a proper morphism between schemes locally of finite type over a
field, the pushforward of cycles preserves rational equivalence (the descent step for the pushforward on
Chow groups).

Of the three branches of the Stacks proof (`W′ = p(W)`, `dim_δ W′ < k / = k / = k+1`), only the third
needs the pullback of rational functions along a dominant morphism: it is the norm formula of Stacks 02RT,
whose function field embedding `R(W′) → R(W)` is `AlgebraicGeometry.functionFieldAlgebra`. The second
branch (`dim_δ W′ = k`) needs the rational function `f_η` on the generic fiber `W_η`, i.e. the transport of
`f ∈ R(W)` along `W_η → W`, given (for line bundles, with `L = O` for functions) by
`RationalSectionPullbackDominant.lean`. The first branch needs no new tool.

Route:
1. `ratEquivZero` is the pointwise sum of a **locally finite** family `{(w_j, c_j)}`. The pushforward
   commutes with such infinite sums (`properPushforward_apply_finsum`), and the image family `{f(w_j)}` is
   still locally finite in `Y` (`locallyFinitePoints_map_of_isProper`); both are in
   `Stacks02s2SchemeLocallyFinite.lean` (valid for any proper morphism).
2. A single generator: `f_* c_j = 0`, or it is a generator on `Y` with generic point `f(w_j)`
   (`properPushforward_eq_zero_or_isRatEquivGen`, `Stacks02s2SchemeGenerator.lean`). Since `X`, `Y` are
   only locally of finite type (neither separated nor quasi-compact), the point closures are not
   `Variety k`, so the scheme version of 02RT (`Stacks02rtScheme.lean`) is used; the branch
   `dim W' = dim W − 1` of the dimension-drop case reduces to
   `properPushforward_principalCycle_apply_genericPoint_eq_zero` (third paragraph of Stacks 02S2: a
   principal divisor on the generic fiber has degree zero, 02RU).
3. Conclude with the form `ratEquivZero_of_locallyFinite_sum` of the second paragraph of Stacks 02RZ
   (support sets `T_j = {f(w_j)}`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-
Scheme-level core of Stacks 02S2: (1) the pushforward preserves `Z_p`; (2) it sends rationally
trivial cycles to rationally trivial cycles. The theorem below contains the formal reduction
from `RationallyEquivalent` to this core.
-/
private theorem properPushforward_scheme_core
    {k : Type u} [Field k]
    {X Y : AlgebraicGeometry.Scheme.{u}}
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [Y.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.LocallyOfFiniteType (Y ↘ AlgebraicGeometry.Spec (CommRingCat.of k))]
    (f : X ⟶ Y) [f.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.IsProper f] (p : ℕ) :
    (∀ c : AlgebraicGeometry.AlgebraicCycle X ℤ,
      c ∈ AlgebraicGeometry.cycleSubgroup X p →
        AlgebraicGeometry.AlgebraicCycle.properPushforward f c ∈ AlgebraicGeometry.cycleSubgroup Y p) ∧
    (∀ c : AlgebraicGeometry.AlgebraicCycle X ℤ,
      c ∈ AlgebraicGeometry.cycleSubgroup X p →
      c ∈ AlgebraicGeometry.ratEquivZero X p →
        AlgebraicGeometry.AlgebraicCycle.properPushforward f c ∈ AlgebraicGeometry.ratEquivZero Y p) := by
  refine ⟨fun c hc => AlgebraicGeometry.properPushforward_mem_cycleSubgroup_of_mem f p hc, ?_⟩
  intro c _ hrat
  obtain ⟨J, w, cj, -, hg, hlf, hs⟩ := hrat
  refine AlgebraicGeometry.ratEquivZero_of_locallyFinite_sum
    (fun j => ({f.base (w j)} : Set Y)) ?_ _
    (fun j => AlgebraicGeometry.AlgebraicCycle.properPushforward f (cj j)) ?_ ?_
  · -- the image family `{f(w_j)}` is locally finite
    intro y
    obtain ⟨U, hU, hyU, hfin⟩ :=
      AlgebraicGeometry.locallyFinitePoints_map_of_isProper f hlf y
    refine ⟨U, hU.mem_nhds hyU, hfin.subset ?_⟩
    rintro j ⟨z, hz1, hz2⟩
    rw [Set.mem_singleton_iff] at hz1
    subst hz1
    exact hz2
  · -- the pushforward of each generator: zero, or a generator with generic point `f(w_j)`
    intro j
    rcases AlgebraicGeometry.properPushforward_eq_zero_or_isRatEquivGen (k := k) f p (w j) (cj j)
      (hg j) with h0 | hgen
    · have h0' : AlgebraicGeometry.AlgebraicCycle.properPushforward f (cj j) = 0 := h0
      rw [h0']; exact zero_mem _
    · exact AlgebraicGeometry.single_mem_ratEquivZeroOn (Set.mem_singleton _) hgen
  · -- the pushforward commutes with locally finite sums
    intro z
    exact AlgebraicGeometry.properPushforward_apply_finsum f hlf cj
      (fun j z hz => (hg j).specializes hz) c hs z

theorem AlgebraicGeometry.AlgebraicCycle.properPushforward_rationallyEquivalent {k : Type u} [Field k]
    {X Y : AlgebraicGeometry.Scheme.{u}} [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [Y.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.LocallyOfFiniteType (Y ↘ AlgebraicGeometry.Spec (CommRingCat.of k))]
    (f : X ⟶ Y) [f.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))] [AlgebraicGeometry.IsProper f]
    (p : ℕ) (α β : AlgebraicGeometry.AlgebraicCycle X ℤ) (h : AlgebraicGeometry.RationallyEquivalent p α β) :
    AlgebraicGeometry.RationallyEquivalent p (AlgebraicGeometry.AlgebraicCycle.properPushforward f α)
      (AlgebraicGeometry.AlgebraicCycle.properPushforward f β) := by
  rcases h with ⟨hα, hβ, hsub⟩
  have hcore := properPushforward_scheme_core (k := k) f p
  have hα' := hcore.1 α hα
  have hβ' := hcore.1 β hβ
  have hsub' := hcore.2 (α - β)
    ((AlgebraicGeometry.cycleSubgroup X p).sub_mem hα hβ) hsub
  refine ⟨hα', hβ', ?_⟩
  have hmap : AlgebraicGeometry.AlgebraicCycle.properPushforward f (α - β) =
      AlgebraicGeometry.AlgebraicCycle.properPushforward f α - AlgebraicGeometry.AlgebraicCycle.properPushforward f β := by
    change (AlgebraicGeometry.AlgebraicCycle.properPushforwardHom f) (α - β) =
      (AlgebraicGeometry.AlgebraicCycle.properPushforwardHom f) α -
        (AlgebraicGeometry.AlgebraicCycle.properPushforwardHom f) β
    exact (AlgebraicGeometry.AlgebraicCycle.properPushforwardHom f).map_sub α β
  rw [← hmap]
  exact hsub'

end
