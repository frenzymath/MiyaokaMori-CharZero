import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.ConstantSheaf.ConstantInclusionUnitSection

/-! # Level sets of a morphism `j_!ℤ_U ⟶ ℤ_X` (Stacks 0A38, proof, paragraph 1)

`exists_levelSets`: for `U` quasi-compact and `f : j_!ℤ_U ⟶ ℤ_X` ("a section `s` of `ℤ_X` over `U`"), there is a
finite family of quasi-compact opens `L_i ⊆ U` covering `U` and integers `z_i` with
`ρ_{L_i,U} ≫ f = z_i • c_{L_i}` ("`s|_{L_i}` is the constant section `z_i`").

Proof. `s := f_U(e_U) ∈ ℤ_X(U)` is locally a constant section (`exists_locally_constSec`); by quasi-compactness
finitely many opens `W_q ⊆ U` (`q ∈ t`) with `s|_{W_q} = z_q` cover `U`. Two of them meeting at a point carry the
same value (`constSec_injective` on the nonempty intersection), so the level sets `L_q := ⋃_{z_{q'} = z_q} W_{q'}`
are pairwise disjoint or equal, cover `U`, and `L_q = U ∩ (⋃_{z_{q'} ≠ z_q} W_{q'})ᶜ` is closed in `U`, hence
quasi-compact (`IsCompact.inter_right`). `s|_{L_q} = z_q` by separatedness of `ℤ_X` (`eq_of_locally_eq'`), and
`ρ_{L_q,U} ≫ f = z_q • c_{L_q}` follows by evaluating on the unit section (`hom_ext_of_unitSection`,
`restrictExtend_unitSection`, `zsmul_constantInclusion_unitSection`).

Source: Stacks 0A38, proof, paragraph 1. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section

namespace TopCat.Sheaf

variable {X : TopCat.{u}}

/-- membership in a finite infimum of opens -/
theorem mem_finset_inf_iff {ι : Type*} (K : Finset ι) (V : ι → Opens X) (x : X) :
    x ∈ K.inf V ↔ ∀ k ∈ K, x ∈ V k := by
  change x ∈ ((K.inf V : Opens X) : Set X) ↔ _
  rw [Opens.coe_finset_inf, Finset.inf_set_eq_iInter, Set.mem_iInter₂]
  rfl

/-- membership in a finite supremum of opens -/
theorem mem_finset_sup_iff {ι : Type*} (K : Finset ι) (V : ι → Opens X) (x : X) :
    x ∈ K.sup V ↔ ∃ k ∈ K, x ∈ V k := by
  change x ∈ ((K.sup V : Opens X) : Set X) ↔ _
  rw [Opens.coe_finset_sup, Finset.sup_set_eq_biUnion, Set.mem_iUnion₂]
  simp only [Function.comp_apply, exists_prop, SetLike.mem_coe]

/-- **level-set decomposition** of a morphism `f : j_!ℤ_U ⟶ ℤ_X` over a quasi-compact open `U` -/
theorem exists_levelSets (U : Opens X) (hU : IsCompact (U : Set X)) (f : extendByZeroConstant U ⟶ constZ X) :
    ∃ (ι : Type u) (_ : Fintype ι) (L : ι → Opens X) (hL : ∀ i, L i ≤ U) (z : ι → ℤ),
      (∀ i, IsCompact ((L i : Opens X) : Set X)) ∧ U ≤ iSup L ∧
      ∀ i, restrictExtend U (hL i) ≫ f = z i • constantInclusion (L i) := by
  classical
  set s : (constZ X).obj.obj (op U) := (f.hom.app (op U)).hom (unitSection U) with hs
  -- local constancy at every point of `U`
  have hloc := fun q : U => exists_locally_constSec (T := X) U s q.1 q.2
  choose W hWU hqW z hz using hloc
  -- finite subcover
  obtain ⟨t, ht⟩ := hU.elim_finite_subcover (fun q : U => ((W q : Opens X) : Set X)) (fun q => (W q).isOpen)
    (fun x hx => Set.mem_iUnion.2 ⟨⟨x, hx⟩, hqW ⟨x, hx⟩⟩)
  -- two members of the cover meeting at a point carry the same value
  have hsep : ∀ a b : U, ∀ x : X, x ∈ W a → x ∈ W b → z a = z b := by
    intro a b x hxa hxb
    have h1 : ((constZ X).obj.map (homOfLE (inf_le_left : W a ⊓ W b ≤ W a)).op).hom
        (((constZ X).obj.map (homOfLE (hWU a)).op).hom s) = constSec (W a ⊓ W b) (z a) := by
      rw [hz a, constSec_res]
    have h2 : ((constZ X).obj.map (homOfLE (inf_le_right : W a ⊓ W b ≤ W b)).op).hom
        (((constZ X).obj.map (homOfLE (hWU b)).op).hom s) = constSec (W a ⊓ W b) (z b) := by
      rw [hz b, constSec_res]
    rw [map_comp_hom_apply] at h1 h2
    have h12 : (homOfLE (hWU a)).op ≫ (homOfLE (inf_le_left : W a ⊓ W b ≤ W a)).op =
        (homOfLE (hWU b)).op ≫ (homOfLE (inf_le_right : W a ⊓ W b ≤ W b)).op :=
      Quiver.Hom.unop_inj (Subsingleton.elim _ _)
    rw [h12, h2] at h1
    exact (constSec_injective (W a ⊓ W b) ⟨x, hxa, hxb⟩ h1).symm
  -- level sets
  let ι := {q : U // q ∈ t}
  let L : ι → Opens X := fun q => (t.filter (fun q' => z q' = z q.1)).sup W
  have hL : ∀ q, L q ≤ U := fun q => Finset.sup_le fun q' _ => hWU q'
  have hmemL : ∀ (q : ι) (x : X), x ∈ L q ↔ ∃ q' ∈ t, z q' = z q.1 ∧ x ∈ W q' := by
    intro q x
    rw [mem_finset_sup_iff]
    constructor
    · rintro ⟨q', hq', hx⟩
      exact ⟨q', (Finset.mem_filter.1 hq').1, (Finset.mem_filter.1 hq').2, hx⟩
    · rintro ⟨q', hq't, hzq', hx⟩
      exact ⟨q', Finset.mem_filter.2 ⟨hq't, hzq'⟩, hx⟩
  have hcover : U ≤ iSup L := by
    intro x hx
    obtain ⟨q, hqt, hxq⟩ := Set.mem_iUnion₂.1 (ht hx)
    rw [Opens.mem_iSup]
    exact ⟨⟨q, hqt⟩, (hmemL ⟨q, hqt⟩ x).2 ⟨q, hqt, rfl, hxq⟩⟩
  -- restriction of `s` to a level set
  have hresL : ∀ q : ι, ((constZ X).obj.map (homOfLE (hL q)).op).hom s = constSec (L q) (z q.1) := by
    intro q
    refine TopCat.Sheaf.eq_of_locally_eq' (constZ X)
      (fun q' : {q' : U // q' ∈ t.filter (fun q' => z q' = z q.1)} => W q'.1) (L q)
      (fun q' => homOfLE (Finset.le_sup q'.2)) (Finset.sup_le fun q' hq' => le_iSup_of_le ⟨q', hq'⟩ le_rfl) _ _
      fun q' => ?_
    rw [map_comp_hom_apply, constSec_res]
    have h12 : (homOfLE (hL q)).op ≫ (homOfLE (Finset.le_sup q'.2 : W q'.1 ≤ L q)).op =
        (homOfLE (hWU q'.1)).op :=
      Quiver.Hom.unop_inj (Subsingleton.elim _ _)
    rw [h12, hz q'.1]
    congr 1
    exact (Finset.mem_filter.1 q'.2).2
  -- quasi-compactness of the level sets: `L q = U ∩ (⋃ {W q' : z q' ≠ z q})ᶜ`
  have hcompact : ∀ q : ι, IsCompact ((L q : Opens X) : Set X) := by
    intro q
    have heq : ((L q : Opens X) : Set X) =
        (U : Set X) ∩ (⋃ q' ∈ t.filter (fun q' => z q' ≠ z q.1), ((W q' : Opens X) : Set X))ᶜ := by
      ext x
      constructor
      · intro hx
        refine ⟨hL q hx, ?_⟩
        rw [Set.mem_compl_iff, Set.mem_iUnion₂]
        rintro ⟨q', hq', hxq'⟩
        obtain ⟨a, _, hza, hxa⟩ := (hmemL q x).1 hx
        exact (Finset.mem_filter.1 hq').2 ((hsep q' a x hxq' hxa).trans hza)
      · rintro ⟨hxU, hx⟩
        rw [Set.mem_compl_iff, Set.mem_iUnion₂] at hx
        obtain ⟨a, hat, hxa⟩ := Set.mem_iUnion₂.1 (ht hxU)
        refine (hmemL q x).2 ⟨a, hat, ?_, hxa⟩
        by_contra hne
        exact hx ⟨a, Finset.mem_filter.2 ⟨hat, hne⟩, hxa⟩
    rw [heq]
    exact hU.inter_right (isOpen_biUnion fun q' _ => (W q').isOpen).isClosed_compl
  -- the morphisms `ρ ≫ f = z • c`
  refine ⟨ι, inferInstance, L, hL, fun q => z q.1, hcompact, hcover, fun q => ?_⟩
  apply hom_ext_of_unitSection
  change (f.hom.app (op (L q))).hom (((restrictExtend U (hL q)).hom.app (op (L q))).hom (unitSection (L q))) = _
  rw [restrictExtend_unitSection, zsmul_constantInclusion_unitSection, ← hresL q]
  exact congrArg (fun g => g.hom (unitSection U)) (f.hom.naturality (homOfLE (hL q)).op)

end TopCat.Sheaf

end
