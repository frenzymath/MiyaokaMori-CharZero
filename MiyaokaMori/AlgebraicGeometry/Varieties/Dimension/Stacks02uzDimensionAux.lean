import MiyaokaMori.Prelude

/-! # Topological lemmas for Grothendieck vanishing (Stacks 02UZ)

Two purely topological facts used in the induction of Stacks 02UZ (`Stacks02uz.lean`):
1. a proper closed subset of an irreducible space has strictly smaller Krull dimension
   (`topologicalKrullDim_lt_of_isClosed_of_ne_univ`);
2. in a Noetherian space, the union of all irreducible components except one has strictly fewer
   irreducible components (`ncard_irreducibleComponents_sUnion_sdiff_lt`), which is the measure for
   the "reduce to the irreducible case" induction.

Source: Stacks 02UZ (cohomology-proposition-vanishing-Noetherian), proof; Stacks 0052. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open TopologicalSpace Topology Set Order

noncomputable section

/-- **Proper closed subsets of an irreducible space have strictly smaller dimension**
(the "height is strictly monotone" step of Stacks 02UZ):
if `X` is irreducible with `dim X < m + 1` and `Z ⊊ X` is closed, then `dim Z < m`.

Proof: a chain `Z₀ ⊂ … ⊂ Z_m` of irreducible closed subsets of `Z` maps (closure of the image
under the closed embedding, `IrreducibleCloseds.map`, strictly monotone since the embedding is
inducing) to a chain in `X` all of whose members lie in `Z ≠ X`; appending `X` itself (irreducible,
closed) gives a chain of length `m + 1` in `X`, contradicting `dim X < m + 1`. -/
theorem topologicalKrullDim_lt_of_isClosed_of_ne_univ {X : Type u} [TopologicalSpace X]
    [IrreducibleSpace X] {Z : Set X} (hZ : IsClosed Z) (hne : Z ≠ univ) {m : ℕ}
    (hX : topologicalKrullDim X < (m + 1 : ℕ)) : topologicalKrullDim Z < m := by
  by_contra h
  rw [not_lt] at h
  obtain ⟨l, hl⟩ := Order.le_krullDim_iff.mp h
  let f : IrreducibleCloseds Z → IrreducibleCloseds X :=
    IrreducibleCloseds.map Subtype.val continuous_subtype_val
  have hf : StrictMono f := IrreducibleCloseds.map_strictMono_of_isInducing IsInducing.subtypeVal
  let l' : LTSeries (IrreducibleCloseds X) := l.map f hf
  let top : IrreducibleCloseds X := ⟨univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
  have hlt : l'.last < top := by
    have hsub : (f l.last : Set X) ⊆ Z := by
      show closure (Subtype.val '' (l.last : Set Z)) ⊆ Z
      exact hZ.closure_subset_iff.mpr (by
        rintro _ ⟨y, _, rfl⟩
        exact y.2)
    refine lt_of_le_of_ne (fun x _ => trivial) ?_
    intro heq
    apply hne
    have : (l'.last : Set X) = univ := congrArg (fun s : IrreducibleCloseds X => (s : Set X)) heq
    have h2 : (l'.last : Set X) ⊆ Z := hsub
    exact univ_subset_iff.mp (this ▸ h2)
  let l'' : LTSeries (IrreducibleCloseds X) := l'.snoc top hlt
  have h1 : (l''.length : WithBot ℕ∞) ≤ topologicalKrullDim X := LTSeries.length_le_krullDim l''
  have h2 : l''.length = m + 1 := by
    rw [← hl]
    rfl
  rw [h2] at h1
  exact absurd hX (not_lt.mpr h1)

/-- An irreducible subset `Y ⊆ W` of the ambient space is irreducible as a subset of the subspace `W`
(its preimage under `Subtype.val`). Direct from the definition: opens of `W` are traces of opens of
the ambient space. -/
theorem isIrreducible_preimage_val_of_subset {X : Type u} [TopologicalSpace X] {W Y : Set X}
    (hY : IsIrreducible Y) (hYW : Y ⊆ W) : IsIrreducible ((Subtype.val : W → X) ⁻¹' Y) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨y, hy⟩ := hY.nonempty
    exact ⟨⟨y, hYW hy⟩, hy⟩
  · intro u v hu hv ⟨a, ha, hau⟩ ⟨b, hb, hbv⟩
    obtain ⟨u', hu', rfl⟩ := isOpen_induced_iff.mp hu
    obtain ⟨v', hv', rfl⟩ := isOpen_induced_iff.mp hv
    obtain ⟨z, hzY, hzu, hzv⟩ := hY.2 u' v' hu' hv' ⟨a, ha, hau⟩ ⟨b, hb, hbv⟩
    exact ⟨⟨z, hYW hzY⟩, hzY, hzu, hzv⟩

/-- **Reduction to fewer irreducible components** (Stacks 02UZ, step "reduce to irreducible"):
for a Noetherian space `X` and an irreducible component `Z`, the closed subspace
`W := ⋃ (irreducible components ≠ Z)` has strictly fewer irreducible components than `X`.

Proof: `C ↦ Subtype.val '' C` maps components of `W` injectively into `irreducibleComponents X \ {Z}`:
the image of a component `C` is irreducible and lies in the finite union of the closed sets
`Y ∈ irreducibleComponents X \ {Z}`, hence in one of them (`isIrreducible_iff_sUnion_isClosed`);
`val ⁻¹' Y` is an irreducible closed subset of `W` containing `C`, so equals `C` by maximality, and
`val '' C = Y`. Then `ncard` of the components of `W` is `≤ ncard (irreducibleComponents X \ {Z})
< ncard (irreducibleComponents X)` (finite by `NoetherianSpace.finite_irreducibleComponents`). -/
theorem ncard_irreducibleComponents_sUnion_sdiff_lt {X : Type u} [TopologicalSpace X]
    [NoetherianSpace X] {Z : Set X} (hZ : Z ∈ irreducibleComponents X) :
    (irreducibleComponents (⋃₀ (irreducibleComponents X \ {Z}) : Set X)).ncard <
      (irreducibleComponents X).ncard := by
  classical
  set T : Set (Set X) := irreducibleComponents X \ {Z} with hT
  set W : Set X := ⋃₀ T with hW
  have hfin : (irreducibleComponents X).Finite := NoetherianSpace.finite_irreducibleComponents
  have hTfin : T.Finite := hfin.subset sdiff_subset
  have hTclosed : ∀ Y ∈ T, IsClosed Y := fun Y hY =>
    isClosed_of_mem_irreducibleComponents Y hY.1
  have hmaps : MapsTo (fun C : Set W => (Subtype.val : W → X) '' C) (irreducibleComponents W) T := by
    intro C hC
    have hCirr : IsIrreducible ((Subtype.val : W → X) '' C) :=
      hC.1.image _ continuous_subtype_val.continuousOn
    have hCsub : (Subtype.val : W → X) '' C ⊆ ⋃₀ T := by
      rintro _ ⟨c, _, rfl⟩
      exact c.2
    obtain ⟨Y, hYT, hCY⟩ := (isIrreducible_iff_sUnion_isClosed.mp hCirr) hTfin.toFinset
      (fun Y hY => hTclosed Y (hTfin.mem_toFinset.mp hY)) (by rwa [hTfin.coe_toFinset])
    rw [hTfin.mem_toFinset] at hYT
    have hYW : Y ⊆ W := subset_sUnion_of_mem hYT
    have hD : IsIrreducible ((Subtype.val : W → X) ⁻¹' Y) :=
      isIrreducible_preimage_val_of_subset hYT.1.1 hYW
    have hCD : C ⊆ (Subtype.val : W → X) ⁻¹' Y := fun c hc => hCY ⟨c, hc, rfl⟩
    have hDC : (Subtype.val : W → X) ⁻¹' Y ⊆ C := hC.2 hD hCD
    have hCeq : C = (Subtype.val : W → X) ⁻¹' Y := le_antisymm hCD hDC
    have himg : (Subtype.val : W → X) '' C = Y := by
      rw [hCeq, Subtype.image_preimage_coe, inter_eq_right.mpr hYW]
    show Subtype.val '' C ∈ T
    rw [himg]
    exact hYT
  have hinj : InjOn (fun C : Set W => (Subtype.val : W → X) '' C) (irreducibleComponents W) :=
    (Set.image_injective.mpr Subtype.val_injective).injOn
  calc (irreducibleComponents W).ncard ≤ T.ncard := ncard_le_ncard_of_injOn _ hmaps hinj hTfin
    _ < (irreducibleComponents X).ncard := ncard_sdiff_singleton_lt_of_mem hZ hfin

end
