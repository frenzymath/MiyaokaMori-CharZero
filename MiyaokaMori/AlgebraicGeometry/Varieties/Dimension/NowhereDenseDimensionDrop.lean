import MiyaokaMori.Prelude
import Mathlib.Topology.KrullDimension
import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.GDelta.Basic

/-! # Dimension drop for nowhere dense subsets

Dimension drop for nowhere dense subsets of a Noetherian space, the topological input of the
dévissage in Snapper's theorem (Stacks 0BEM, steps "remove embedded points" and "denominator
ideal"): if `Y` is a Noetherian topological space and `T ⊆ Y` is nowhere dense,
then `dim T + 1 ≤ dim Y`; in the form used, `dim Y ≤ e + 1 → dim T ≤ e`.

Proof (Stacks 0BEM uses this silently: "`dim Supp Q < dim X`"). Let `Z₀ ⊊ ⋯ ⊊ Zₘ` be a chain of
irreducible closed subsets of `T`. Their closures in `Y` form a chain of the same length of irreducible
closed subsets of `Y` (`IrreducibleCloseds.map` along the inducing map `T → Y` is strictly monotone).
The top term `Z̄ₘ` lies in an irreducible component `C` of `Y`. In a Noetherian space there are finitely
many irreducible components, so `U := Y ∖ ⋃_{C' ≠ C} C'` is open; it is contained in `C` (every point
lies in some component) and nonempty (otherwise `C ⊆ ⋃_{C' ≠ C} C'`, so by irreducibility `C ⊆ C'` for
some `C' ≠ C`, contradicting maximality). If `Z̄ₘ = C` then `U ⊆ C ⊆ closure T`, so `U ⊆ interior
(closure T) = ∅`, a contradiction. Hence `Z̄ₘ ⊊ C` and the chain extends by one step.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

open TopologicalSpace Topology Order

namespace TopologicalSpace

variable {Y : Type*} [TopologicalSpace Y]

/-- In a Noetherian space, every irreducible component contains a nonempty open subset
(the complement of the union of the other components). -/
theorem exists_isOpen_nonempty_subset_of_mem_irreducibleComponents [NoetherianSpace Y]
    {C : Set Y} (hC : C ∈ irreducibleComponents Y) :
    ∃ U : Set Y, IsOpen U ∧ U.Nonempty ∧ U ⊆ C := by
  classical
  set S : Set (Set Y) := irreducibleComponents Y \ {C} with hSdef
  have hSfin : S.Finite := NoetherianSpace.finite_irreducibleComponents.subset Set.sdiff_subset
  refine ⟨(⋃₀ S)ᶜ, ?_, ?_, ?_⟩
  · refine isOpen_compl_iff.mpr ?_
    rw [Set.sUnion_eq_biUnion]
    exact hSfin.isClosed_biUnion fun s hs => isClosed_of_mem_irreducibleComponents s hs.1
  · by_contra h
    rw [Set.not_nonempty_iff_eq_empty, Set.compl_empty_iff] at h
    have hsub : C ⊆ ⋃₀ S := h ▸ Set.subset_univ C
    have hmem := mem_of_subset_sUnion_irreducibleComponents C hC S hSfin Set.sdiff_subset hsub
    exact hmem.2 rfl
  · intro y hy
    have hy' : y ∈ ⋃₀ irreducibleComponents Y := by
      rw [sUnion_irreducibleComponents]; trivial
    obtain ⟨C', hC', hyC'⟩ := hy'
    by_cases hCC : C' = C
    · exact hCC ▸ hyC'
    · exact absurd ⟨C', ⟨hC', hCC⟩, hyC'⟩ hy

/-- **Dimension drop for nowhere dense subsets** of a Noetherian space:
`dim Y ≤ e + 1 → dim T ≤ e` for `T ⊆ Y` nowhere dense. -/
theorem topologicalKrullDim_le_of_isNowhereDense [NoetherianSpace Y] {T : Set Y}
    (hT : IsNowhereDense T) {e : ℕ} (hY : topologicalKrullDim Y ≤ ((e + 1 : ℕ) : WithBot ℕ∞)) :
    topologicalKrullDim T ≤ (e : WithBot ℕ∞) := by
  unfold topologicalKrullDim krullDim at hY ⊢
  refine iSup_le fun p => ?_
  -- push the chain to `Y`
  have hf : StrictMono (IrreducibleCloseds.map (Subtype.val : T → Y) continuous_subtype_val) :=
    IrreducibleCloseds.map_strictMono_of_isInducing IsInducing.subtypeVal
  let p' : LTSeries (IrreducibleCloseds Y) := p.map _ hf
  obtain ⟨C, hC, hsub⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    (p'.last : Set Y) p'.last.isIrreducible
  let Cc : IrreducibleCloseds Y := ⟨C, hC.1, isClosed_of_mem_irreducibleComponents C hC⟩
  have hlast : (p'.last : Set Y) ⊆ closure T := by
    show closure (Subtype.val '' (p.last : Set T)) ⊆ closure T
    refine closure_mono ?_
    rintro _ ⟨t, -, rfl⟩
    exact t.2
  have hlt : p'.last < Cc := by
    refine lt_of_le_of_ne hsub fun heq => ?_
    obtain ⟨U, hUo, hUne, hUC⟩ := exists_isOpen_nonempty_subset_of_mem_irreducibleComponents hC
    have hCsub : C ⊆ closure T := by
      have : (Cc : Set Y) ⊆ closure T := heq ▸ hlast
      exact this
    have hUint : U ⊆ interior (closure T) := interior_maximal (hUC.trans hCsub) hUo
    rw [hT] at hUint
    exact hUne.ne_empty (Set.subset_empty_iff.mp hUint)
  let q : LTSeries (IrreducibleCloseds Y) := p'.snoc Cc hlt
  have hq : ((q.length : ℕ) : WithBot ℕ∞) ≤ ((e + 1 : ℕ) : WithBot ℕ∞) :=
    le_trans (le_iSup (fun r : LTSeries (IrreducibleCloseds Y) => ((r.length : ℕ) : WithBot ℕ∞)) q) hY
  have hlen : q.length = p.length + 1 := by simp [q, p']
  have hq' : q.length ≤ e + 1 := by exact_mod_cast hq
  have hp : p.length ≤ e := by omega
  exact_mod_cast hp

/-- The form used in 0BEM: `T ⊆ S ⊆ X`, `T` nowhere dense in the subspace `S`, `dim S ≤ e + 1`;
then `dim T ≤ e`. (`X` Noetherian; every subspace of a Noetherian space is Noetherian.) -/
theorem topologicalKrullDim_le_of_isNowhereDense_preimage {X : Type*} [TopologicalSpace X]
    [NoetherianSpace X] {S T : Set X} (hTS : T ⊆ S)
    (hnd : IsNowhereDense (Subtype.val ⁻¹' T : Set S)) {e : ℕ}
    (hS : topologicalKrullDim S ≤ ((e + 1 : ℕ) : WithBot ℕ∞)) :
    topologicalKrullDim T ≤ (e : WithBot ℕ∞) := by
  have h1 : topologicalKrullDim (Subtype.val ⁻¹' T : Set S) ≤ (e : WithBot ℕ∞) :=
    topologicalKrullDim_le_of_isNowhereDense hnd hS
  refine le_trans ?_ h1
  let g : T → (Subtype.val ⁻¹' T : Set S) := fun t => ⟨⟨t.1, hTS t.2⟩, t.2⟩
  have hg : Continuous g :=
    (continuous_subtype_val.subtype_mk _).subtype_mk _
  have hcomp : IsInducing ((Subtype.val : S → X) ∘ (Subtype.val : (Subtype.val ⁻¹' T : Set S) → S) ∘ g) := by
    have : ((Subtype.val : S → X) ∘ (Subtype.val : (Subtype.val ⁻¹' T : Set S) → S) ∘ g)
        = (Subtype.val : T → X) := funext fun t => rfl
    rw [this]
    exact IsInducing.subtypeVal
  have hind : IsInducing g :=
    IsInducing.of_comp hg (continuous_subtype_val.comp continuous_subtype_val) hcomp
  exact hind.topologicalKrullDim_le

end TopologicalSpace
