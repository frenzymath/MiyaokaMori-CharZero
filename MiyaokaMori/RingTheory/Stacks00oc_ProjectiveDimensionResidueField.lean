import MiyaokaMori.Prelude
import Mathlib.RingTheory.Regular.ProjectiveDimension
import Mathlib.RingTheory.RegularLocalRing.Defs
import MiyaokaMori.RingTheory.RegularLocalRing.Stacks00nqRegularSequence
import MiyaokaMori.RingTheory.RegularLocalRing.ProjectiveDimensionTools

/-! # The projective dimension of the residue field of a regular local ring

**`pd κ = dim R` for a regular local ring** (the equality part of Stacks 00OC; Stacks 00OA/00O7,
Matsumura Thm 19.2, Bruns–Herzog Cor. 2.2.6 direction "regular ⇒ `pd κ = dim R`").

Proof. Let `d = dim R = spanFinrank 𝔪` and choose generators `x₁, …, x_d` of `𝔪`. By Stacks 00NQ
(`IsRegularLocalRing.isWeaklyRegular_of_span_eq_maximalIdeal`) they form a regular sequence (in `𝔪`, so `IsRegular`). Mathlib's
`ModuleCat.projectiveDimension_quotient_eq_length` gives `pd (R/(x₁,…,x_d)) = d`, and
`R/(x₁,…,x_d) = R/𝔪 = κ`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory IsLocalRing

noncomputable section

/-- **`pd κ = dim R` over a regular local ring** (Stacks 00OC equality part; via the regular
sequence generating `𝔪`, Stacks 00NQ). -/
theorem IsRegularLocalRing.projectiveDimension_residueField
    (R : Type u) [CommRing R] [IsRegularLocalRing R] :
    projectiveDimension (ModuleCat.of R (ResidueField R)) = ringKrullDim R := by
  classical
  obtain ⟨s, hcard, hspan⟩ :=
    (IsNoetherian.noetherian (maximalIdeal R)).exists_span_finset_card_eq_spanFinrank
  set d := (maximalIdeal R).spanFinrank with hd_def
  have hd : ringKrullDim R = d := (IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)).symm
  let e : Fin d ≃ s := (s.equivFin.trans (finCongr hcard)).symm
  let x : Fin d → R := fun i => (e i : R)
  have hrange : Set.range x = (s : Set R) := by
    ext r
    constructor
    · rintro ⟨i, rfl⟩; exact (e i).2
    · intro hr; exact ⟨e.symm ⟨r, hr⟩, by simp [x]⟩
  have hx : Ideal.span (Set.range x) = maximalIdeal R := by rw [hrange]; exact hspan
  have hwr := IsRegularLocalRing.isWeaklyRegular_of_span_eq_maximalIdeal hd x hx
  have hmem : ∀ r ∈ List.ofFn x, r ∈ maximalIdeal R := by
    intro r hr
    rw [List.mem_ofFn] at hr
    obtain ⟨i, rfl⟩ := hr
    rw [← hx]
    exact Ideal.subset_span ⟨i, rfl⟩
  have hreg : RingTheory.Sequence.IsRegular R (List.ofFn x) :=
    RingTheory.Sequence.IsRegular.of_isWeaklyRegular_of_mem_maximalIdeal R hmem hwr
  have hpd := ModuleCat.projectiveDimension_quotient_eq_length.{u, u} (List.ofFn x) hreg
  have hideal : Ideal.ofList (List.ofFn x) = maximalIdeal R := by
    rw [← hx]
    show Ideal.span {r | r ∈ List.ofFn x} = _
    congr 1
    ext r
    simp only [Set.mem_ofPred_eq, List.mem_ofFn', Set.mem_range]
  let e2 : Shrink.{u} (R ⧸ Ideal.ofList (List.ofFn x)) ≃ₗ[R] ResidueField R :=
    (Shrink.linearEquiv R _).trans (Submodule.quotEquivOfEq _ _ hideal)
  rw [ModuleCat.projectiveDimension_eq_of_linearEquiv_of e2] at hpd
  rw [hpd, List.length_ofFn, hd]

end
