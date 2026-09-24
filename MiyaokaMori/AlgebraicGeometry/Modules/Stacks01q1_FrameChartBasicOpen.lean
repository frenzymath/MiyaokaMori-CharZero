import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleNonvanishingLocus
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle

/-! # The nonvanishing locus of a line bundle section on a chart

Chart description of the nonvanishing locus of a line bundle (the local form of Stacks 01CY): if `e`
is a frame of `L` on an open `W`, `t ∈ Γ(X, L)` and `f := coord_e(t|_W) ∈ Γ(X, W)` (i.e.
`t|_W = f • e`), then

  `W ⊓ X_t = X.basicOpen f`.

This is the first step of the route to Stacks 01PV (`IsAffineOpen.inf_nonvanishingLocus`): on an
open with a frame, `X_t` is a basic open. The two inclusions are proved as in
`isOpen_setOf_germ_notMem_maximalIdeal_smul`; here the argument is packaged as a reusable equality.

References: Stacks 01CY (`modules-lemma-s-open`); the sentence "`U ∩ X_s = D(f)`" in the proof of
Stacks 01PV.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- **Chart description**: if `e` is a frame of `L` on `W`, `t ∈ Γ(X, L)` and `f = coord_e(t|_W)`,
then `W ⊓ X_t = X.basicOpen f`.

Proof: for `y ∈ W`, taking germs gives `t_y = f_y • e_y` (`coord_smul_frame` + `germ_smul'`).
* `⊆`: if `y ∈ W ⊓ X_t` and `f_y` is not a unit, then `f_y ∈ 𝔪_y`, so `t_y ∈ 𝔪_y L_y`,
  contradicting `y ∈ X_t`.
* `⊇`: if `y ∈ X.basicOpen f ⊆ W` and `f_y = u` is a unit, then `e_y = u⁻¹ • t_y`; if `t_y ∈ 𝔪_y L_y`
  then `e_y ∈ 𝔪_y L_y`, contradicting the fact that the germ of a frame is not in `𝔪_y L_y`
  (`IsFrame.germ_notMem_maximalIdeal_smul`). -/
theorem IsFrame.inf_nonvanishingLocus_eq_basicOpen (L : X.Modules) [L.IsLineBundle]
    (t : Γ(L, ⊤)) {W : X.Opens} {e : Γ(L, W)} (hf : IsFrame L W e) :
    W ⊓ L.nonvanishingLocus t = X.basicOpen (hf.coord le_rfl (L.res le_top t)) := by
  set f : Γ(X, W) := hf.coord le_rfl (L.res le_top t) with hfdef
  have hse : L.res le_top t = f • e := by
    have h := hf.coord_smul_frame le_rfl (L.res le_top t)
    rw [res_self] at h
    exact h.symm
  have key : ∀ (y : X) (hy : y ∈ W),
      L.presheaf.germ ⊤ y trivial t = X.presheaf.germ W y hy f • L.presheaf.germ W y hy e := by
    intro y hy
    have h0 : L.presheaf.germ W y hy (L.res le_top t) = L.presheaf.germ ⊤ y trivial t :=
      TopCat.Presheaf.germ_res_apply _ _ _ _ _
    rw [← h0, hse, germ_smul']
  apply TopologicalSpace.Opens.ext
  ext y
  rw [TopologicalSpace.Opens.coe_inf, Set.mem_inter_iff, SetLike.mem_coe, SetLike.mem_coe,
    SetLike.mem_coe, mem_nonvanishingLocus]
  constructor
  · rintro ⟨hyW, hyt⟩
    rw [X.mem_basicOpen f y hyW]
    by_contra hnu
    refine hyt ?_
    rw [key y hyW]
    exact Submodule.smul_mem_smul (N := (⊤ : Submodule (X.presheaf.stalk y) (L.stalk y)))
      ((IsLocalRing.mem_maximalIdeal _).mpr hnu) Submodule.mem_top
  · intro hy
    have hyW : y ∈ W := X.basicOpen_le f hy
    obtain ⟨u, hu'⟩ := (X.mem_basicOpen f y hyW).mp hy
    refine ⟨hyW, fun hcon => hf.germ_notMem_maximalIdeal_smul hyW ?_⟩
    have he : L.presheaf.germ W y hyW e =
        (↑u⁻¹ : X.presheaf.stalk y) • L.presheaf.germ ⊤ y trivial t := by
      rw [key y hyW, ← hu', smul_smul, Units.inv_mul, one_smul]
    rw [he]
    exact Submodule.smul_mem _ _ hcon

end AlgebraicGeometry.Scheme.Modules

end
