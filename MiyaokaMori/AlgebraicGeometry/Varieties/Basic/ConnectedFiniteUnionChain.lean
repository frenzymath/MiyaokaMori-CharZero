import MiyaokaMori.Prelude

/-! # Chains of components in a connected finite union

If a finite union of closed sets is connected, then any two of the sets are joined by a chain
of sets in which consecutive members intersect.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem exists_chain_of_connected {α : Type*} [TopologicalSpace α] {ι : Type*} [Fintype ι]
    (T : ι → Set α) (hcl : ∀ i, IsClosed (T i)) (hne : ∀ i, (T i).Nonempty)
    (hconn : IsConnected (⋃ i, T i)) (i j : ι) :
    ∃ l : List ι, l.head? = some i ∧ l.getLast? = some j ∧
      l.IsChain (fun a b => (T a ∩ T b).Nonempty) := by
  classical
  let R : ι → ι → Prop := fun a b => (T a ∩ T b).Nonempty
  -- Turn a reflexive-transitive relation witness into the explicit list used by
  -- the chain argument.  The append boundary is identified by the previous
  -- list's last element.
  have rtg_to_list {a b : ι}
      (h : Relation.ReflTransGen R a b) :
      ∃ l : List ι, l.head? = some a ∧ l.getLast? = some b ∧ l.IsChain R := by
    induction h with
    | refl =>
        exact ⟨[a], by simp, by simp, List.IsChain.singleton _⟩
    | @tail b c h hab ih =>
        obtain ⟨l, hhead, hlast, hchain⟩ := ih
        refine ⟨l ++ [c], ?_, ?_, ?_⟩
        · simpa [List.head?_append, hhead]
        · simp
        · apply (List.isChain_append).2
          refine ⟨hchain, List.IsChain.singleton _, ?_⟩
          intro x hx y hy
          simp [hlast] at hx
          simp at hy
          subst x
          subst y
          exact hab
  have hreach : ∀ j, Relation.ReflTransGen R i j := by
    intro j
    by_contra hnot
    let U : Set α := ⋃ a : {a // Relation.ReflTransGen R i a}, T a
    let V : Set α := ⋃ a : {a // ¬ Relation.ReflTransGen R i a}, T a
    have hU : IsClosed U := by
      dsimp [U]
      apply isClosed_iUnion_of_finite
      intro a
      exact hcl a
    have hV : IsClosed V := by
      dsimp [V]
      apply isClosed_iUnion_of_finite
      intro a
      exact hcl a
    have hsub : (⋃ a, T a) ⊆ U ∪ V := by
      intro x hx
      obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hx
      by_cases hra : Relation.ReflTransGen R i a
      · exact Or.inl (Set.mem_iUnion.mpr ⟨⟨a, hra⟩, ha⟩)
      · exact Or.inr (Set.mem_iUnion.mpr ⟨⟨a, hra⟩, ha⟩)
    have hUmem : ((⋃ a, T a) ∩ U).Nonempty := by
      obtain ⟨x, hx⟩ := hne i
      exact ⟨x, Set.mem_iUnion.mpr ⟨i, hx⟩,
        Set.mem_iUnion.mpr ⟨⟨i, Relation.ReflTransGen.refl⟩, hx⟩⟩
    have hVmem : ((⋃ a, T a) ∩ V).Nonempty := by
      obtain ⟨x, hx⟩ := hne j
      exact ⟨x, Set.mem_iUnion.mpr ⟨j, hx⟩,
        Set.mem_iUnion.mpr ⟨⟨j, hnot⟩, hx⟩⟩
    obtain ⟨x, hxS, hxU, hxV⟩ :=
      (isPreconnected_closed_iff.mp hconn.isPreconnected U V hU hV hsub hUmem hVmem)
    obtain ⟨a, ha⟩ := Set.mem_iUnion.mp hxU
    obtain ⟨b, hb⟩ := Set.mem_iUnion.mp hxV
    have hab_ne : a.1 ≠ b.1 := by
      intro hab
      exact b.2 (hab ▸ a.2)
    have habR : R a.1 b.1 := by
      exact ⟨x, ha, hb⟩
    exact b.2 (Relation.ReflTransGen.tail a.2 habR)
  obtain ⟨l, hhead, hlast, hchain⟩ := rtg_to_list (hreach j)
  exact ⟨l, hhead, hlast, hchain⟩

end
