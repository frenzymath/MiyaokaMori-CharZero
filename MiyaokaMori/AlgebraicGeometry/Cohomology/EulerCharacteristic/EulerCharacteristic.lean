import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.CoherentSheaf
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProperOverField
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.SchemeDimension
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafCohomologyModule
import MiyaokaMori.AlgebraicGeometry.Cohomology.EulerCharacteristic.EulerCharacteristicDef
import MiyaokaMori.AlgebraicGeometry.Cohomology.Coherent.Stacks02o6
import MiyaokaMori.AlgebraicGeometry.Cohomology.Vanishing.Stacks02uz
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.SchemeDimensionFinite

/-! # The Euler characteristic of a coherent sheaf

The Euler characteristic of a coherent sheaf, `χ(X,F) = ∑ (-1)^i dim_k H^i(X,F)`, is a genuine finite
alternating sum on a proper `k`-scheme: `sheafCohomology_finite_and_vanishing` combines finite
dimensionality (Stacks 02O6, `AlgebraicGeometry.finite_sheafCohomology_of_isProper`) with vanishing above
the dimension (Stacks 02UZ, `sheafCohomology_vanishing_noetherian_dimension`), through the two bridge
lemmas `sheafCohomology_finiteDimensional_of_isProperOver` and
`sheafCohomology_subsingleton_of_dimension_lt`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

-- The definition `sheafEulerCharacteristic` (with its usage discipline) lives in `EulerCharacteristicDef.lean`
-- (imported above), so that the cohomology infrastructure can use χ without importing `Stacks02o6` through
-- this file (which would create an import cycle with the 02O5/02O6 routes).

/-- In finite dimension, `topologicalKrullDim X ≤ X.dimension` (`X.dimension` is the dimension truncated to
`ℕ`: both `⊥` and `⊤` become `0`). For `X` empty the left side is `⊥` and the inequality is trivial; for `X`
nonempty both sides agree by `Scheme.dimension_spec`. Used in `SnapperPolynomial.lean`. -/
theorem AlgebraicGeometry.Scheme.topologicalKrullDim_le_dimension (X : AlgebraicGeometry.Scheme.{u})
    (h : topologicalKrullDim X ≠ ⊤) :
    topologicalKrullDim X ≤ (X.dimension : WithBot ℕ∞) := by
  by_cases hb : topologicalKrullDim X = ⊥
  · rw [hb]; exact bot_le
  · exact (X.dimension_spec hb h).le

/-- **Finite dimensionality**: `X` proper over `k`, `M` coherent ⇒ every `H^i(X, M)` is a
finite-dimensional `k`-vector space.

Source: Stacks 02O6 (`AlgebraicGeometry.finite_sheafCohomology_of_isProper`).

Proof: `IsProperOver k X` is `IsProper (X ↘ Spec k)`; `k` is a field, hence Noetherian; 02O6 with `A = k`,
`f = X ↘ Spec k` gives `Module.Finite k (sheafCohomology X M i)`, where the `k`-module structure comes from
`letI : X.Over (Spec k) := ⟨X ↘ Spec k⟩`, definitionally equal (by structure eta) to the `X.Over` instance
used here, so `exact` suffices. -/
theorem AlgebraicGeometry.sheafCohomology_finiteDimensional_of_isProperOver {k : Type u} [Field k]
    (X : AlgebraicGeometry.Scheme.{u})
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (hX : IsProperOver k X)
    (M : X.Modules) [M.IsCoherent] (i : ℕ) :
    FiniteDimensional k (AlgebraicGeometry.sheafCohomology X M i) := by
  have : AlgebraicGeometry.IsProper (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := hX
  exact AlgebraicGeometry.finite_sheafCohomology_of_isProper
    (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) M i

/-- **Vanishing above the dimension**: `X` proper over `k`, `i > dim X` ⇒ `H^i(X, M) = 0` (for every
`O_X`-module `M`, coherence not needed).

Source: Stacks 02UZ (Grothendieck vanishing, `sheafCohomology_vanishing_noetherian_dimension`).

Proof:
1. `X` proper over a field ⇒ locally of finite type ⇒ locally Noetherian
   (`LocallyOfFiniteType.isLocallyNoetherian`); universally closed ⇒ quasi-compact ⇒ `CompactSpace X`;
   together Mathlib's `IsNoetherian X`, whose underlying space is a Noetherian topological space
   (`IsNoetherian.noetherianSpace`).
2. `topologicalKrullDim X ≤ X.dimension`: for `X` nonempty, `topologicalKrullDim X ≠ ⊤` (locally of finite
   type over a field + quasi-compact), so `topologicalKrullDim X = (X.dimension : WithBot ℕ∞)`
   (`Scheme.topologicalKrullDim_eq_dimension`, no `0` fallback); for `X` empty, `IrreducibleCloseds X` is
   empty and `topologicalKrullDim X = ⊥ ≤ _`.
3. The carrier of `sheafCohomology X M i` is `Sheaf.H.{u} M.toAddCommGrpSheaf i` (the carrier of
   `ModuleCat.of`, the same type as Mathlib's `HasExt.{u}` used by 02UZ); 02UZ for the abelian sheaf
   `M.toAddCommGrpSheaf` and `p = i > dim X` gives `Subsingleton`, and `exact` closes the goal.

Edge case: for `X` empty, `dim X = 0`, and `H^i` is trivial for `i ≥ 1` (all cohomology on the empty space
vanishes); `i = 0` is excluded by the hypothesis. -/
theorem AlgebraicGeometry.sheafCohomology_subsingleton_of_dimension_lt {k : Type u} [Field k]
    (X : AlgebraicGeometry.Scheme.{u})
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (hX : IsProperOver k X)
    (M : X.Modules) (i : ℕ) (hi : X.dimension < i) :
    Subsingleton (AlgebraicGeometry.sheafCohomology X M i) := by
  have : AlgebraicGeometry.IsProper (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := hX
  have : AlgebraicGeometry.IsLocallyNoetherian X :=
    AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian
      (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
  have : CompactSpace X :=
    AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace
      (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
  have : AlgebraicGeometry.IsNoetherian X := ⟨⟩
  have hd : topologicalKrullDim X ≤ (X.dimension : WithBot ℕ∞) := by
    by_cases hne : Nonempty X
    · exact le_of_eq (AlgebraicGeometry.Scheme.topologicalKrullDim_eq_dimension X
        (AlgebraicGeometry.topologicalKrullDim_ne_top_of_isProperOver X hX))
    · have hbot : topologicalKrullDim X = ⊥ :=
        Order.krullDim_eq_bot_iff.mpr ⟨fun Z => hne ⟨Z.isIrreducible'.nonempty.choose⟩⟩
      rw [hbot]
      exact bot_le
  exact sheafCohomology_vanishing_noetherian_dimension hd M.toAddCommGrpSheaf i hi

/-- Finiteness (Stacks 02O6 + Grothendieck vanishing 02UZ): `X` proper over `k` (projective in the paper),
`M` coherent ⇒ every `H^i` is a finite-dimensional `k`-vector space and `H^i = 0` for `i > dim X`. Hence
neither fallback in the definition of `sheafEulerCharacteristic` (`finrank` = 0 in infinite dimension,
`finsum` = 0 on infinite support) is triggered. Assembled from
`sheafCohomology_finiteDimensional_of_isProperOver` and `sheafCohomology_subsingleton_of_dimension_lt`. -/
theorem AlgebraicGeometry.sheafCohomology_finite_and_vanishing {k : Type u} [Field k]
    (X : AlgebraicGeometry.Scheme.{u})
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (hX : IsProperOver k X)
    (M : X.Modules) [M.IsCoherent] :
    (∀ i : ℕ, FiniteDimensional k (AlgebraicGeometry.sheafCohomology X M i)) ∧
      ∀ i : ℕ, X.dimension < i → Subsingleton (AlgebraicGeometry.sheafCohomology X M i) :=
  ⟨fun i => AlgebraicGeometry.sheafCohomology_finiteDimensional_of_isProperOver X hX M i,
    fun i hi => AlgebraicGeometry.sheafCohomology_subsingleton_of_dimension_lt X hX M i hi⟩

/-- Hence `χ` is a genuine finite alternating sum `Σ_{i ≤ dim X} (-1)^i dim_k H^i` (from the previous
theorem). **Every lemma assigning a value to `χ` should go through this one** (see the docstring of
`sheafEulerCharacteristic`). -/
theorem AlgebraicGeometry.sheafEulerCharacteristic_eq_sum {k : Type u} [Field k]
    (X : AlgebraicGeometry.Scheme.{u})
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (hX : IsProperOver k X)
    (M : X.Modules) [M.IsCoherent] :
    AlgebraicGeometry.sheafEulerCharacteristic (k := k) X M
      = ∑ i ∈ Finset.range (X.dimension + 1), (-1 : ℤ) ^ i *
          (Module.finrank k (AlgebraicGeometry.sheafCohomology X M i) : ℤ) := by
  unfold AlgebraicGeometry.sheafEulerCharacteristic
  refine finsum_eq_sum_of_support_subset _ (fun i hi => ?_)
  by_contra h
  have hlt : X.dimension < i := by simpa [Finset.mem_range, Nat.lt_succ_iff] using h
  have := (AlgebraicGeometry.sheafCohomology_finite_and_vanishing X hX M).2 i hlt
  exact hi (by simp [Module.finrank_zero_of_subsingleton])

end
