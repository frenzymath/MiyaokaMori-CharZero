import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.FiniteCover
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.WeightedOrderIntegral
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.FinitelyManyNonzeroWeightedOrders
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.ParameterLineBundleRationalSection

/-! # The integer weight function `y ↦ w_y` of a chart family
(step 1 of the proof of Lemma 3.1 of the paper)

> For `y ∈ C̃`, choose a jet chart whose base open contains `ρ(y)`, and put
> `w_y = min_{i,q} ord_y(b_{α,i,q})/q ∈ ℤ`. This number is independent of the chart. … Only finitely
> many `w_y` are nonzero.

This module contains the jet-free part of that step: given, for every chart `α` of a family covering
`C`, a nonzero tuple `b α` of rational functions on `C̃` whose nonzero entries have `(q+1)`-th roots,
and given that the weighted orders of `b α` and `b β` agree at every codimension-one point over
`V α ∩ V β`, it produces the integer-valued, finitely supported function `w` with
`w y = weightedOrderQ (b α) y` whenever `ρ(y) ∈ V α`. Chart independence itself is supplied by the jet
transition (`affineJetCoord_jetTransitionRelated`, `AffineJetChartTransition`).

-/
set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

variable {k : Type u} [Field k] {C : SmoothProjectiveCurve k}

/-- **The weight function of a chart family** (Lemma 3.1 of the paper). Let `ρ : C̃ → C` be a finite
cover, `(V α)` a family of opens covering `C`, and for each `α` a nonzero tuple `b α` of rational
functions on `C̃` (weight `q + 1` on `b α i q`) whose nonzero entries have `(q+1)`-th roots. Assume the
weighted orders are chart independent: `weightedOrderQ (b α) y = weightedOrderQ (b β) y` whenever
`y` has coheight `1` and `ρ(y) ∈ V α ∩ V β`. Then there is `w : C̃ → ℤ` with finite support such that
`w y = weightedOrderQ (b α) y` for every `α` with `ρ(y) ∈ V α`.

Proof. Define `w y := (weightedOrderQ (b α(y)) y).num` for a chart `α(y)` with `ρ(y) ∈ V α(y)`
(`hcover`); the denominator is `1` by `weightedOrder_den_eq_one` (from the roots), so `(w y : ℚ) = weightedOrderQ (b α(y)) y`. For any other `α` with `ρ(y) ∈ V α`: if
`coheight y = 1` the two weighted orders agree by hypothesis; otherwise `y` is the generic point
(`SmoothProjectiveCurve.eq_genericPoint_of_coheight_ne_one`) and both are `0`
(`weightedOrder_genericPoint`). Finite support: `C` is compact, so finitely many `V α₁, …, V αₘ`
cover it; if `w y ≠ 0` pick `αⱼ` with `ρ(y) ∈ V αⱼ`, then `weightedOrderQ (b αⱼ) y = w y ≠ 0`, and each
set `{y | weightedOrderQ (b αⱼ) y ≠ 0}` is finite (`finite_support_weightedOrder`). -/
theorem exists_weightFunction_of_chartIndependent (ρ : FiniteCover k C) {n κ : ℕ}
    {ι : Type u} {V : ι → C.toScheme.Opens} (hcover : ∀ c : C.toScheme, ∃ α, c ∈ V α)
    (b : ι → Fin (n + 1) → Fin κ → ρ.source.toScheme.functionField)
    (hne : ∀ α, ∃ i q, b α i q ≠ 0)
    (hroot : ∀ α (i : Fin (n + 1)) (q : Fin κ), b α i q ≠ 0 →
      ∃ c : ρ.source.toScheme.functionField, c ^ ((q : ℕ) + 1) = b α i q)
    (hind : ∀ α β (y : ρ.source.toScheme), Order.coheight y = 1 →
      ρ.hom.base y ∈ V α → ρ.hom.base y ∈ V β →
      weightedOrderQ (b α) (hne α) y = weightedOrderQ (b β) (hne β) y) :
    ∃ w : ρ.source.toScheme → ℤ, (Function.support w).Finite ∧
      ∀ α (y : ρ.source.toScheme), ρ.hom.base y ∈ V α →
        (w y : ℚ) = weightedOrderQ (b α) (hne α) y := by
  classical
  -- the chart attached to a point of `C̃`
  let α₀ : ρ.source.toScheme → ι := fun y => Classical.choose (hcover (ρ.hom.base y))
  have hα₀ : ∀ y, ρ.hom.base y ∈ V (α₀ y) := fun y => Classical.choose_spec (hcover (ρ.hom.base y))
  let w : ρ.source.toScheme → ℤ := fun y => (weightedOrderQ (b (α₀ y)) (hne (α₀ y)) y).num
  have hw : ∀ y, (w y : ℚ) = weightedOrderQ (b (α₀ y)) (hne (α₀ y)) y := fun y =>
    Rat.coe_int_num_of_den_eq_one (weightedOrder_den_eq_one (b (α₀ y)) (hne (α₀ y)) (hroot (α₀ y)) y)
  -- chart independence, including the generic point
  have hind' : ∀ α (y : ρ.source.toScheme), ρ.hom.base y ∈ V α →
      weightedOrderQ (b (α₀ y)) (hne (α₀ y)) y = weightedOrderQ (b α) (hne α) y := by
    intro α y hy
    by_cases hco : Order.coheight y = 1
    · exact hind (α₀ y) α y hco (hα₀ y) hy
    · have hη := SmoothProjectiveCurve.eq_genericPoint_of_coheight_ne_one ρ.source y hco
      subst hη
      rw [weightedOrder_genericPoint, weightedOrder_genericPoint]
  refine ⟨w, ?_, fun α y hy => (hw y).trans (hind' α y hy)⟩
  -- finite support via a finite subcover of `C`
  have : CompactSpace C.toScheme :=
    AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace
      (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun α => ((V α : Set C.toScheme)))
    (fun α => (V α).isOpen) (fun c _ => Set.mem_iUnion.mpr (hcover c))
  have hsub : Function.support w ⊆
      ⋃ α ∈ t, {y : ρ.source.toScheme | weightedOrderQ (b α) (hne α) y ≠ 0} := by
    intro y hy
    obtain ⟨α, hαt, hyα⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ (ρ.hom.base y)))
    refine Set.mem_iUnion₂.mpr ⟨α, hαt, ?_⟩
    change weightedOrderQ (b α) (hne α) y ≠ 0
    intro h0
    apply Function.mem_support.mp hy
    have h1 : (w y : ℚ) = 0 := by rw [hw y, hind' α y hyα, h0]
    exact_mod_cast h1
  exact Set.Finite.subset (Set.Finite.biUnion t.finite_toSet fun α _ =>
    finite_support_weightedOrder (b α) (hne α)) hsub

end
