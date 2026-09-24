import MiyaokaMori.Prelude

/-! # Quasi-compactness of the complement of a locally principal ideal sheaf

The open immersion of the complement of the support of a locally principal ideal sheaf is
quasi-compact (the "retrocompact" hypothesis of Stacks 07ZP / 080D for the exceptional locus of a
blowup pulled back to a fibre product).

Source: Stacks 080D, 07ZP; used in the proof of Stacks 080E (strict transforms).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme

/-- The open immersion
`j : Y ∖ supp D ↪ Y` of the complement of the support of a *locally principal* ideal sheaf `D`
(every point has an affine open neighbourhood `U` and `a ∈ Γ(Y, U)` with `D(U) = (a)`) is
quasi-compact.

Source: Stacks 080D / 07ZP (the retrocompactness hypothesis "the complement of `E'` is locally a
basic open, hence its inclusion is quasi-compact"); used here for the exceptional locus
`E' = supp((π⁻¹I)·O_P)` on `P = X ×_S Bl_I S`, which is locally principal because the exceptional
divisor of `Bl_I S` is an effective Cartier divisor (Stacks 0806(1)) and `comap` preserves local
principality (`strictTransform.exceptionalIdeal_comap_locallyPrincipal`).

Proof (the Lean proof below follows these steps):
1. `quasiCompact_iff_forall_isAffineOpen`: it suffices that for every affine open `U ⊆ Y` the
   preimage `j ⁻¹ᵁ U` is compact in the open subscheme `W := (supp D)ᶜ`. Since `W.ι` is an
   embedding, this is equivalent to compactness of its image `U ∩ W ⊆ Y`
   (`Topology.IsInducing.isCompact_iff`, `Scheme.Hom.image_preimage_eq_opensRange_inf`,
   `Opens.opensRange_ι`).
2. Cover `U`: for `x ∈ U` take from the hypothesis an affine `U_x ∋ x` with `D(U_x) = (a_x)`;
   by `IsAffineOpen.exists_basicOpen_le` choose `g_x ∈ Γ(U_x)` with `x ∈ D(g_x) ≤ U`. Put
   `W_x := D(g_x)`, affine (`IsAffineOpen.basicOpen`), and `D(W_x) = (a_x|_{W_x})`
   (`IdealSheafData.map_ideal`, `Ideal.map_span`, `Set.image_singleton`).
3. On `W_x`: `W_x ∩ supp D = V(a_x|_{W_x})` (`IdealSheafData.mem_support_iff_of_mem`,
   `Scheme.zeroLocus_span`, `Scheme.zeroLocus_singleton`), so `W_x ∩ W = Y.basicOpen (a_x|_{W_x})`
   is an affine open (`IsAffineOpen.basicOpen`), hence compact (`IsAffineOpen.isCompact`).
4. `U` is compact (`IsAffineOpen.isCompact`) and `U ⊆ ⋃ₓ W_x`, so finitely many `W_{x₁}, …, W_{xₙ}`
   cover `U` (`IsCompact.elim_finite_subcover`). Then
   `U ∩ W = ⋃ᵢ (W_{xᵢ} ∩ W)` is a finite union of compact sets (`Set.Finite.isCompact_biUnion`).
Edge cases: `D = ⊤` (`supp D = ∅`, `W = Y`, take `a = 1`); `D = ⊥` (`W = ∅`); `Y = ∅`: all trivial. -/
theorem IdealSheafData.quasiCompact_ι_compl_support_of_locallyPrincipal {Y : Scheme.{u}}
    (D : Y.IdealSheafData)
    (hD : ∀ x : Y, ∃ U : Y.affineOpens, x ∈ U.1 ∧ ∃ a : Γ(Y, U), D.ideal U = Ideal.span {a}) :
    QuasiCompact (Opens.ι (⟨(D.support : Set Y)ᶜ, D.support.isClosed.isOpen_compl⟩ : Y.Opens)) := by
  set W : Y.Opens := ⟨(D.support : Set Y)ᶜ, D.support.isClosed.isOpen_compl⟩ with hW
  -- Step 2-3: every point of an open `U` has an open neighbourhood `V ≤ U` with `V ∩ W` compact.
  have key : ∀ (U : Y.Opens), ∀ x ∈ U, ∃ V : Y.Opens, x ∈ V ∧ V ≤ U ∧
      IsCompact ((V : Set Y) ∩ (W : Set Y)) := by
    intro U x hxU
    obtain ⟨U₀, hxU₀, a, hDa⟩ := hD x
    obtain ⟨g, hgU, hxg⟩ := U₀.2.exists_basicOpen_le ⟨x, hxU⟩ hxU₀
    have hV : AlgebraicGeometry.IsAffineOpen (Y.basicOpen g) := U₀.2.basicOpen g
    have hVU₀ : Y.basicOpen g ≤ U₀.1 := Y.basicOpen_le g
    let a' : Γ(Y, Y.basicOpen g) := Y.presheaf.map (homOfLE hVU₀).op a
    have hDa' : D.ideal ⟨Y.basicOpen g, hV⟩ = Ideal.span {a'} := by
      rw [← D.map_ideal (U := ⟨Y.basicOpen g, hV⟩) hVU₀, hDa, Ideal.map_span, Set.image_singleton]
      rfl
    refine ⟨Y.basicOpen g, hxg, hgU, ?_⟩
    have hset : ((Y.basicOpen g : Set Y) ∩ (W : Set Y)) = (Y.basicOpen a' : Set Y) := by
      ext y
      constructor
      · rintro ⟨hyV, hyW⟩
        by_contra hy
        apply hyW
        show y ∈ D.support
        rw [D.mem_support_iff_of_mem (U := ⟨_, hV⟩) hyV, hDa', zeroLocus_span, zeroLocus_singleton]
        exact hy
      · intro hy
        have hyV : y ∈ Y.basicOpen g := Y.basicOpen_le a' hy
        refine ⟨hyV, fun hyD => ?_⟩
        have hyD' : y ∈ D.support := hyD
        rw [D.mem_support_iff_of_mem (U := ⟨_, hV⟩) hyV, hDa', zeroLocus_span,
          zeroLocus_singleton] at hyD'
        exact hyD' hy
    rw [hset]
    exact (hV.basicOpen a').isCompact
  -- Step 1: reduce to compactness of `U ∩ W` for affine `U`.
  rw [quasiCompact_iff_forall_isAffineOpen]
  intro U hU
  rw [W.ι.isOpenEmbedding.isEmbedding.isCompact_iff]
  have himg : W.ι.base '' ((W.ι ⁻¹ᵁ U : W.toScheme.Opens) : Set W.toScheme) =
      (U : Set Y) ∩ (W : Set Y) := by
    rw [← Scheme.Hom.coe_image, W.ι.image_preimage_eq_opensRange_inf, Opens.opensRange_ι,
      Opens.coe_inf, Set.inter_comm]
  rw [himg]
  -- Step 4: finitely many of the `V x` cover the compact `U`.
  choose! V hxV hVU hVc using key U
  obtain ⟨t, ht⟩ := hU.isCompact.elim_finite_subcover (fun x : U => (V x : Set Y))
    (fun x => (V x).isOpen) (fun y hy => Set.mem_iUnion.mpr ⟨⟨y, hy⟩, hxV y hy⟩)
  have heq : (U : Set Y) ∩ (W : Set Y) = ⋃ x ∈ t, ((V x : Set Y) ∩ (W : Set Y)) := by
    ext y
    constructor
    · rintro ⟨hyU, hyW⟩
      obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.mp (ht hyU)
      exact Set.mem_iUnion₂.mpr ⟨x, hx, hyx, hyW⟩
    · intro hy
      obtain ⟨x, -, hyx, hyW⟩ := Set.mem_iUnion₂.mp hy
      exact ⟨hVU x x.2 hyx, hyW⟩
  rw [heq]
  exact t.finite_toSet.isCompact_biUnion fun x _ => hVc x x.2

end AlgebraicGeometry.Scheme

end
