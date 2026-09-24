import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.FirstChernCapPointwise
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.SchemeFundamentalCycle
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.PointClosureKrullDim
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.FirstChernCapFundamentalCycle

/-! # The cap of the first Chern class with the fundamental class (Stacks 02SJ)

Let `X` be an integral scheme, locally Noetherian and locally of finite type over a field `k`, with
`dim X = m ≥ 1`, and `L` a line bundle.
(F1) At the cycle level, `firstChernCapCycleAux L m [X]_m = firstChernCapPoint L η`.
(PC) A principal cycle `div(g)` on `X` is an `IsRatEquivGen X (m−1) η`, hence rationally trivial.
(F2) For **any** nonzero rational section `s` of `L`: `div_L(s) ∈ Z_{m−1}(X)`, and in the Chow group
`c_1(L) ∩ [X] = [div_L(s)]` (the definition of Stacks 02SJ in the encoding of this library).

Proof:
1. (F1): for `X` integral, `[X]_m` is the indicator of the generic point (`fundamentalCycle_of_isIntegral`),
   so the finite sum has only the term at `η`.
2. (PC): `ι_η` is an isomorphism; transport along `(ι_η)⁻¹` (`PointClosureTransport`) gives `f′`, then push
   back along `ι_η` (Stacks 02R5 + Mathlib's `AlgebraicCycle.map_id`).
3. (F2): `firstChernCapPoint_genericPoint` gives `capPoint L η = div_L(s′)`; Stacks 02SH (change of section)
   gives `div_L(s′) = div_L(s) + div(g)`; conclude with (PC).

(F1), (PC) and the small dimension lemmas live in `FirstChernCapFundamentalCycle.lean`, which imports
nothing from the `firstChernClass` layer, so that the proof of Stacks 02ST can use them.

Source: Stacks 02SJ, 02SH.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u
open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
namespace AlgebraicGeometry
open MiyaokaMori.FirstChernCapPointClosurePushforward MiyaokaMori.FirstChernCapPointGeneric
  MiyaokaMori.PointClosureTransport MiyaokaMori.ClosedImmersionPushforward
/-- (F2) **Stacks 02SJ**: for `X` integral, `c_1(L) ∩ [X]` is the class of the divisor of any nonzero
rational section of `L`. -/
theorem firstChernClass_fundamentalChowClass_eq_mk_rationalSectionDivisor {k : Type u} [Field k]
    {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))] [IsIntegral X] [IsLocallyNoetherian X]
    (L : X.Modules) [L.IsLineBundle] (d : ℕ) (hX : X.dimension = d + 1)
    (s : L.stalk (genericPoint X)) (hs : s ≠ 0) :
    ∃ h : L.rationalSectionDivisor s ∈ cycleSubgroup X d,
      firstChernClass L (d + 1) (X.fundamentalChowClass (d + 1)) =
        ChowGroup.mk ⟨L.rationalSectionDivisor s, h⟩ := by
  have hXk := Scheme.isLocallyOfFiniteTypeOverField_of_over (k := k) X
  have hdim := topologicalKrullDim_eq_of_dimension_pos hX
  have hmem : ∀ t : L.stalk (genericPoint X), L.rationalSectionDivisor t ∈ cycleSubgroup X d :=
    fun t z hz => Scheme.height_eq_of_coheight_eq_one (X ↘ Spec (CommRingCat.of k)) hdim
      (Scheme.Modules.rationalSectionDivisor_support L t z hz)
  refine ⟨hmem s, ?_⟩
  obtain ⟨s', hs', hcap⟩ := firstChernCapPoint_genericPoint L
  obtain ⟨g, hg⟩ := exists_rationalSectionDivisor_eq_add_principalCycle L s' s hs' hs
  have h1 : firstChernClass L (d + 1) (X.fundamentalChowClass (d + 1)) =
      ChowGroup.mk ⟨L.rationalSectionDivisor s', hmem s'⟩ := by
    refine (firstChernClass_mk' hXk L (d + 1) _).trans ?_
    show ChowGroup.mk (⟨firstChernCapCycleAux L (d + 1) (X.fundamentalCycle (d + 1)), _⟩ :
      ↥(cycleSubgroup X d)) = _
    congr 1
    exact Subtype.ext ((firstChernCapCycleAux_fundamentalCycle_of_isIntegral L hX).trans hcap)
  rw [h1, ← sub_eq_zero, ← map_sub]
  refine (QuotientAddGroup.eq_zero_iff _).mpr ?_
  rw [AddSubgroup.mem_addSubgroupOf]
  show L.rationalSectionDivisor s' - L.rationalSectionDivisor s ∈ ratEquivZero X d
  rw [hg, add_sub_cancel_left]
  exact single_mem_ratEquivZero
    (isRatEquivGen_principalCycle (height_genericPoint_of_dimension_pos hX) g)

end AlgebraicGeometry
end
