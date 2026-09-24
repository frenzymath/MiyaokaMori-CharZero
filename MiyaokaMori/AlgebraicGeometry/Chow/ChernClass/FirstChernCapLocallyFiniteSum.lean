import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.FirstChernCapCycle
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.LocallyFiniteCycleSum
import MiyaokaMori.AlgebraicGeometry.Chow.RationalEquivalence.RationalEquivalenceX

/-! # The cycle-level cap with `c_1(L)` commutes with locally finite sums

The cycle-level `c_1(L) ∩ −` (`firstChernCapCycleAux`) commutes with **locally finite sums**.

Source: the first paragraph of the proof of Stacks 02TI needs to split `c_1(L) ∩ Σ_j (i_j)_* div(f_j)`
into the sum of its terms. Stacks does this in one step with the proper pushforward along
`p : ∐ W_j → X`; here the sums are exchanged directly on the pointwise `finsum`
(`finsum_curry` + `Equiv.prodComm`), the required finiteness coming from "the support of
`capPoint L v` specializes from `v`" and "the family `{w j}` is locally finite".
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry

/-- `firstChernCapCycleAux L d −` commutes with the sum of a locally finite family: if `α = Σ_j c j`
(pointwise `finsum`), the support of each `c j` specializes from `w j`, and `{w j}` is locally finite,
then `c_1(L) ∩ α = Σ_j c_1(L) ∩ (c j)` (again a pointwise `finsum`). -/
theorem firstChernCapCycleAux_of_locallyFiniteSum {X : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsLocallyNoetherian X] (L : X.Modules) [L.IsLineBundle] (d : ℕ)
    {J : Type v} {w : J → X} {c : J → AlgebraicGeometry.AlgebraicCycle X ℤ}
    (hlf : AlgebraicGeometry.LocallyFinitePoints w)
    (hsup : ∀ (j : J) (t : X), c j t ≠ 0 → w j ⤳ t)
    (α : AlgebraicGeometry.AlgebraicCycle X ℤ) (hα : ∀ t, α t = ∑ᶠ j, c j t) (z : X) :
    AlgebraicGeometry.firstChernCapCycleAux L d α z
      = ∑ᶠ j, AlgebraicGeometry.firstChernCapCycleAux L d (c j) z := by
  classical
  have hstep : ∀ t : X, AlgebraicGeometry.firstChernCapTerm L d α z t
      = ∑ᶠ j, AlgebraicGeometry.firstChernCapTerm L d (c j) z t := by
    intro t
    by_cases ht : Order.height t = (d : ℕ∞)
    · have hL : AlgebraicGeometry.firstChernCapTerm L d α z t
          = α t * AlgebraicGeometry.firstChernCapPoint L t z := by
        simp only [AlgebraicGeometry.firstChernCapTerm, if_pos ht]
      have hR : ∀ j, AlgebraicGeometry.firstChernCapTerm L d (c j) z t
          = c j t * AlgebraicGeometry.firstChernCapPoint L t z := fun j => by
        simp only [AlgebraicGeometry.firstChernCapTerm, if_pos ht]
      rw [hL, hα t, finsum_mul, finsum_congr hR]
    · have hL : AlgebraicGeometry.firstChernCapTerm L d α z t = 0 := by
        simp only [AlgebraicGeometry.firstChernCapTerm, if_neg ht]
      have hR : ∀ j, AlgebraicGeometry.firstChernCapTerm L d (c j) z t = (0 : ℤ) := fun j => by
        simp only [AlgebraicGeometry.firstChernCapTerm, if_neg ht]
      rw [hL, finsum_congr hR, finsum_zero]
  obtain ⟨-, ⟨U, hUaff, rfl⟩, hzU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ z) isOpen_univ
  obtain ⟨U₀, hU₀, hzU₀, hJfin⟩ := hlf z
  have hFsupp : Function.support
      (fun q : X × J => AlgebraicGeometry.firstChernCapTerm L d (c q.2) z q.1) ⊆
      ⋃ j ∈ {j : J | w j ∈ U₀},
        ((U : Set X) ∩ Function.support (c j : X → ℤ)) ×ˢ ({j} : Set J) := by
    rintro ⟨t, j⟩ htj
    obtain ⟨-, hcj, hcap⟩ := AlgebraicGeometry.firstChernCapTerm_ne_zero L htj
    have htz : t ⤳ z := AlgebraicGeometry.firstChernCapPoint_specializes L hcap
    have hwj : w j ∈ U₀ := ((hsup j t hcj).trans htz).mem_open hU₀ hzU₀
    exact Set.mem_biUnion hwj ⟨⟨htz.mem_open U.isOpen hzU, hcj⟩, rfl⟩
  have hFfin : Function.HasFiniteSupport
      (fun q : X × J => AlgebraicGeometry.firstChernCapTerm L d (c q.2) z q.1) :=
    (hJfin.biUnion (fun j _ =>
      (((c j).locallyFiniteSupport.finite_inter_support_of_isCompact
        hUaff.isCompact).prod (Set.finite_singleton j)))).subset hFsupp
  have hGfin : Function.HasFiniteSupport
      (fun q : J × X => AlgebraicGeometry.firstChernCapTerm L d (c (Equiv.prodComm J X q).2) z
        (Equiv.prodComm J X q).1) :=
    hFfin.preimage (Equiv.injective (Equiv.prodComm J X)).injOn
  show (∑ᶠ t : X, AlgebraicGeometry.firstChernCapTerm L d α z t)
    = ∑ᶠ j, ∑ᶠ t : X, AlgebraicGeometry.firstChernCapTerm L d (c j) z t
  rw [finsum_congr hstep,
    ← finsum_curry (fun q : X × J => AlgebraicGeometry.firstChernCapTerm L d (c q.2) z q.1) hFfin,
    ← finsum_comp_equiv (Equiv.prodComm J X)
      (f := fun q : X × J => AlgebraicGeometry.firstChernCapTerm L d (c q.2) z q.1)]
  exact finsum_curry _ hGfin

end AlgebraicGeometry

end
