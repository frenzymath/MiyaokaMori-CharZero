import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.Frame
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleNonvanishingLocus
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.ZeroSchemeOfSection

/-! # The support of the zero scheme of a section is the complement of its nonvanishing locus

Statement: for a global section `s` of a line bundle `L`, the support `Z(s)` of its zero-scheme ideal
sheaf `idealSheafOfSection L s` (Stacks 01WX/01X0: generated on an affine open `U` by the "local
equations" `φ(s|_U)` of `s`) satisfies `y ∈ Z(s) ⟺ s_y ∈ 𝔪_y L_y`; hence
`Z(s)ᶜ = L.nonvanishingLocus s` (the `X_s` of Stacks 01CY).

Proof (one frame suffices): take an affine open `W ∋ y` and a frame `e` at `y`
(`exists_affine_frame_le`), `s|_W = c • e` with `c := coord_e(s|_W)`; then `s_y = c_y • e_y`.
* `c ∈ I(W)`: take `φ := coord_e` (`Γ(X,W)`-linear), `φ(s|_W) = c`.
* `I(W) ⊆ (c)`: `φ(s|_W) = φ(c • e) = c · φ(e)`.
* `y ∈ Z(s) ⟺ y ∈ zeroLocus I(W)` (`IdealSheafData.mem_support_iff_of_mem`, `W` affine)
  `⟺ ∀ a ∈ I(W), y ∉ D(a)`. By the two points above this is equivalent to `y ∉ D(c)`
  (`D(t·c) = D(t) ⊓ D(c)`), i.e. `c_y` is not a unit (`Scheme.mem_basicOpen`), i.e. `c_y ∈ 𝔪_y`.
* `c_y ∈ 𝔪_y ⟹ s_y = c_y • e_y ∈ 𝔪_y L_y`; conversely, if `c_y` is a unit then `e_y = c_y⁻¹ • s_y`,
  so `s_y ∈ 𝔪_y L_y` would give `e_y ∈ 𝔪_y L_y`, contradicting
  `IsFrame.germ_notMem_maximalIdeal_smul` (Nakayama for one generator).

References: Stacks 01WX/01X0 (zero-scheme ideal sheaf), 01CY (`X_s`). Used to replace "the complement
of the support of the zero scheme" by `nonvanishingLocus`, in terms of which `splitCoordBasicOpen` is
defined.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme

/-- `y ∈ supp Z(s) ⟺ s_y ∈ 𝔪_y L_y` (`L` a line bundle, `s` a global section; Stacks 01WX/01X0 + 01CY). -/
theorem mem_idealSheafOfSection_support_iff {X : AlgebraicGeometry.Scheme.{u}}
    (L : X.Modules) [L.IsLineBundle] (s : (L.val.obj (Opposite.op ⊤) : Type u)) (y : X) :
    y ∈ (AlgebraicGeometry.Scheme.idealSheafOfSection L s).support ↔
      L.presheaf.germ ⊤ y trivial (show Γ(L, ⊤) from s) ∈
        (IsLocalRing.maximalIdeal (X.presheaf.stalk y)) •
          (⊤ : Submodule (X.presheaf.stalk y) (L.stalk y)) := by
  obtain ⟨W, hW, -, hyW, e, hf⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_affine_frame_le L (U := ⊤) (p := y) trivial
  set sW : Γ(L, W) := L.res (le_top : W ≤ ⊤) (show Γ(L, ⊤) from s) with hsW
  set c := hf.coord le_rfl sW with hcdef
  have hc : c • L.res le_rfl e = sW := hf.coord_smul_frame le_rfl sW
  -- s_y = c_y • e_y
  have hgerm : L.presheaf.germ ⊤ y trivial (show Γ(L, ⊤) from s) =
      X.presheaf.germ W y hyW c • L.presheaf.germ W y hyW e := by
    have h1 : L.presheaf.germ ⊤ y trivial (show Γ(L, ⊤) from s) = L.presheaf.germ W y hyW sW :=
      (TopCat.Presheaf.germ_res_apply L.presheaf (CategoryTheory.homOfLE (le_top : W ≤ ⊤)) y hyW
        _).symm
    rw [h1, ← hc, AlgebraicGeometry.Scheme.Modules.germ_smul',
      AlgebraicGeometry.Scheme.Modules.res_self]
  -- c ∈ I(W): take φ := coord_e
  have hcI : c ∈ (AlgebraicGeometry.Scheme.idealSheafOfSection L s).ideal ⟨W, hW⟩ := by
    show c ∈ Ideal.span (Set.range fun φ : Γ(L, W) →ₗ[Γ(X, W)] Γ(X, W) =>
      φ (L.presheaf.map (CategoryTheory.homOfLE le_top).op (show Γ(L, ⊤) from s)))
    exact Ideal.subset_span ⟨(hf.coordEquiv le_rfl).toLinearMap, rfl⟩
  -- I(W) ⊆ (c): φ(s|_W) = φ(c • e) = c · φ(e)
  have hI : (AlgebraicGeometry.Scheme.idealSheafOfSection L s).ideal ⟨W, hW⟩ ≤ Ideal.span {c} := by
    show Ideal.span (Set.range fun φ : Γ(L, W) →ₗ[Γ(X, W)] Γ(X, W) =>
      φ (L.presheaf.map (CategoryTheory.homOfLE le_top).op (show Γ(L, ⊤) from s))) ≤ _
    rw [Ideal.span_le]
    rintro _ ⟨φ, rfl⟩
    show φ sW ∈ Ideal.span {c}
    rw [← hc, map_smul, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self c)
  rw [AlgebraicGeometry.Scheme.IdealSheafData.mem_support_iff_of_mem
    (I := AlgebraicGeometry.Scheme.idealSheafOfSection L s) (U := ⟨W, hW⟩) hyW,
    AlgebraicGeometry.Scheme.mem_zeroLocus_iff, hgerm]
  constructor
  · -- y ∈ Z(s) ⇒ c_y is not a unit ⇒ s_y = c_y • e_y ∈ 𝔪_y L_y
    intro h
    have hnu : ¬ IsUnit (X.presheaf.germ W y hyW c) := fun hu =>
      h c hcI ((X.mem_basicOpen c y hyW).mpr hu)
    have hmem : (X.presheaf.germ W y hyW c) •
        (show AlgebraicGeometry.Scheme.Modules.stalk L y from L.presheaf.germ W y hyW e) ∈
        (IsLocalRing.maximalIdeal (X.presheaf.stalk y)) •
          (⊤ : Submodule (X.presheaf.stalk y) (AlgebraicGeometry.Scheme.Modules.stalk L y)) :=
      Submodule.smul_mem_smul ((IsLocalRing.mem_maximalIdeal _).mpr hnu) Submodule.mem_top
    exact hmem
  · -- s_y ∈ 𝔪_y L_y ⇒ for all a ∈ I(W) ⊆ (c), y ∉ D(a): otherwise c_y is a unit and e_y ∈ 𝔪_y L_y, contradiction
    intro hmem a haI hya
    obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp (hI haI)
    rw [AlgebraicGeometry.Scheme.basicOpen_mul] at hya
    obtain ⟨u, hu'⟩ : IsUnit (X.presheaf.germ W y hyW c) := (X.mem_basicOpen c y hyW).mp hya.2
    refine hf.germ_notMem_maximalIdeal_smul hyW ?_
    have he : L.presheaf.germ W y hyW e =
        (↑u⁻¹ : X.presheaf.stalk y) • (X.presheaf.germ W y hyW c • L.presheaf.germ W y hyW e) := by
      rw [smul_smul, ← hu', Units.inv_mul, one_smul]
    rw [he]
    exact Submodule.smul_mem _ _ hmem

/-- The complement of the support of the zero scheme is the nonvanishing locus `X_s` (as a set of
points of `X`). -/
theorem idealSheafOfSection_support_compl_eq_nonvanishingLocus {X : AlgebraicGeometry.Scheme.{u}}
    (L : X.Modules) [L.IsLineBundle] (s : (L.val.obj (Opposite.op ⊤) : Type u)) :
    (SetLike.coe (AlgebraicGeometry.Scheme.idealSheafOfSection L s).support)ᶜ =
      ((AlgebraicGeometry.Scheme.Modules.nonvanishingLocus L (show Γ(L, ⊤) from s) : X.Opens) :
        Set X) := by
  ext y
  simp only [Set.mem_compl_iff, SetLike.mem_coe, mem_idealSheafOfSection_support_iff]
  exact Iff.rfl

end AlgebraicGeometry.Scheme

end
