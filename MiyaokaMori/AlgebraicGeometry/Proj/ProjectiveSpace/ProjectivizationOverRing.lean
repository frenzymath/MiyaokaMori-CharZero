import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpaceOverChartRatio
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.FrameLocus
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleNonvanishingLocus
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.Frame
import MiyaokaMori.AlgebraicGeometry.Modules.SectionIsZeroAt
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.HomogeneousTupleLocalCoordinates
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveTupleRestriction
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveTupleFrameChange

/-! # The projectivization morphism of a nowhere-vanishing tuple over a ring

The projectivization morphism of a nowhere-vanishing tuple of sections **over a commutative ring `R`**
(Hartshorne II.7.1 over `R`; Stacks 01VU): `V` a scheme with a morphism `f : V → Spec R`, `M` a line
bundle on `V`, `P_0, …, P_N ∈ Γ(V, M)` without common zero. On `V_ℓ = {P_ℓ ≠ 0}` the ratios
`r_{ℓ,j} = P_j/P_ℓ ∈ Γ(V_ℓ, O)` (`projectivizationRatio`, base-independent) define an `R`-algebra map
`R[T_0..T_N] → Γ(V_ℓ, O)` (`projectivizationChartEvalOver`), hence `g_ℓ : V_ℓ → P^N_R` (Mathlib
`Proj.fromOfGlobalSections`); the `g_ℓ` agree on overlaps (`projectivizationChartMorphismOver_agree`:
`r_{m,j} = r_{ℓ,j} · r_{m,ℓ}` on `V_ℓ ∩ V_m`, so the two evaluations differ by the unit `r_{m,ℓ}`, and
`Proj.fromOfGlobalSections` is invariant under such a homogeneous unit change — the generic
`fromOfGlobalSections_naturality` / `fromOfGlobalSections_unit_scale`) and glue to
`φ = projectivizationMorphismOver f M P hP : V ⟶ ProjectiveSpaceOver N R` with
`φ ≫ (P^N_R → Spec R) = f` and `φ⁻¹(D_+(T_ℓ)) = V_ℓ`. The chart map `V_ℓ → D_+(T_ℓ)` is a closed
immersion when `V_ℓ` is affine and the chart evaluation is surjective, and `φ` is an immersion when the
charts of a covering family of indices are closed immersions (Stacks 01VS).

**This module is the primary construction.** The field-level module
`Paper/S3PositiveLine/Realization/ProjectivizationOfNowhereZeroTuple.lean` (`projectivizationMorphism` etc.) is a
layer of `abbrev`s over this one (`R := k`, `f := V ↘ Spec k`); the base-free charts, ratios and frame lemmas
are defined here. The gluing uses the two generic lemmas on `Proj.fromOfGlobalSections` rather than a
field-specific gluing datum.

References: Hartshorne II.7.1; Stacks 01VU, 01VS.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ## Sections are frames on their non-vanishing locus (Stacks 01CY, second half); the charts `V_ℓ` and the ratios `r_{ℓ,j}`

The field-level module `Paper/S3PositiveLine/Realization/ProjectivizationOfNowhereZeroTuple.lean` imports this
module and defines its `projectivizationChartEval` / `projectivizationChartMorphism` / `projectivizationCover` /
`projectivizationMorphism` / `projectivizationChartMap` as `abbrev`s of the `…Over` constructions below at
`R := k`, `f := V ↘ Spec k`. Everything in this block is base-free.

The ratio `projectivizationRatio` is defined constructively, through the three lemmas
`IsFrame.of_iSup` (being a frame is a local property, by gluing of sheaves),
`IsFrame.le_nonvanishingLocus` and `isFrame_res_nonvanishingLocus`. -/

namespace AlgebraicGeometry.Scheme.Modules

/-- **Being a frame is a local property**: if `W` is covered by the opens `V i` and `e` is a frame on
every `V i`, then `e` is a frame on `W`. Injectivity uses the separation axiom of the structure sheaf;
surjectivity glues local coordinates in the structure sheaf (the compatibility on overlaps follows from
injectivity on each piece), and the sheaf condition of `M` shows that the glued `r` satisfies
`r • e = x`. -/
theorem IsFrame.of_iSup {X : AlgebraicGeometry.Scheme.{u}} {M : X.Modules} {W : X.Opens}
    {e : Γ(M, W)} {ι : Type v}
    (V : ι → X.Opens) (hVW : ∀ i, V i ≤ W) (hcover : W ≤ iSup V)
    (hfr : ∀ i, IsFrame M (V i) (M.res (hVW i) e)) : IsFrame M W e := by
  intro W' hW'
  set O : ι → X.Opens := fun i => W' ⊓ V i with hOdef
  have hOW' : ∀ i, O i ≤ W' := fun _ => inf_le_left
  have hOV : ∀ i, O i ≤ V i := fun _ => inf_le_right
  have hcov : W' ≤ iSup O := by
    intro p hp
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hcover (hW' hp))
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, ⟨hp, hi⟩⟩
  constructor
  · intro r r' hrr
    refine X.sheaf.eq_of_locally_eq' O W' (fun i => homOfLE (hOW' i)) hcov r r' fun i => ?_
    refine (hfr i (O i) (hOV i)).1 ?_
    have h1 := congrArg (M.res (hOW' i)) hrr
    rw [M.res_smul, M.res_smul, M.res_res] at h1
    simp only [M.res_res]
    exact h1
  · intro x
    have hx : ∀ i, ∃ r : Γ(X, O i), r • M.res (hOV i) (M.res (hVW i) e) = M.res (hOW' i) x :=
      fun i => (hfr i (O i) (hOV i)).2 _
    choose r hr using hx
    simp only [M.res_res] at hr
    have hcompat : TopCat.Presheaf.IsCompatible X.presheaf O r := by
      intro i j
      refine (hfr i (O i ⊓ O j) (inf_le_left.trans (hOV i))).1 ?_
      simp only [M.res_res]
      have h1 := congrArg (M.res (inf_le_left : O i ⊓ O j ≤ O i)) (hr i)
      have h2 := congrArg (M.res (inf_le_right : O i ⊓ O j ≤ O j)) (hr j)
      rw [M.res_smul, M.res_res, M.res_res] at h1
      rw [M.res_smul, M.res_res, M.res_res] at h2
      exact h1.trans h2.symm
    obtain ⟨rr, hrr, -⟩ :=
      X.sheaf.existsUnique_gluing' O W' (fun i => homOfLE (hOW' i)) hcov r hcompat
    let sglue : Γ(X, W') := rr
    refine ⟨sglue, ?_⟩
    refine TopCat.Sheaf.eq_of_locally_eq' ⟨M.presheaf, M.isSheaf⟩ O W'
      (fun i => homOfLE (hOW' i)) hcov _ _ fun i => ?_
    show M.res (hOW' i) (sglue • M.res hW' e) = M.res (hOW' i) x
    rw [M.res_smul, M.res_res]
    have hh : X.presheaf.map (homOfLE (hOW' i)).op sglue = r i := hrr i
    rw [hh]
    exact hr i

/-- A frame is nowhere vanishing: if `s` is a frame on `V`, then `V ⊆ X_s`. -/
theorem IsFrame.le_nonvanishingLocus {X : AlgebraicGeometry.Scheme.{u}} {L : X.Modules}
    [L.IsLineBundle] {s : Γ(L, ⊤)} {V : X.Opens}
    (hf : IsFrame L V (L.res le_top s)) : V ≤ L.nonvanishingLocus s := by
  intro y hy
  rw [AlgebraicGeometry.Scheme.Modules.mem_nonvanishingLocus]
  have h := IsFrame.germ_notMem_maximalIdeal_smul hf hy
  rwa [TopCat.Presheaf.germ_res_apply] at h

/-- **`s` is a frame on its non-vanishing locus `X_s`** (Stacks 01CY, second half): at `x` take a
frame `(W, e)` and the coordinate `f = coord e s`; on `X.basicOpen f` the section `f` is a unit
(`RingedSpace.isUnit_res_basicOpen`), so `s` is a frame there (`IsFrame.of_isUnit_coord`); these
opens cover `X_s`, and `IsFrame.of_iSup` glues. -/
theorem isFrame_res_nonvanishingLocus {X : AlgebraicGeometry.Scheme.{u}} (L : X.Modules)
    [L.IsLineBundle] (s : Γ(L, ⊤)) :
    IsFrame L (L.nonvanishingLocus s) (L.res le_top s) := by
  have key : ∀ x : X, x ∈ L.nonvanishingLocus s →
      ∃ V : X.Opens, x ∈ V ∧ IsFrame L V (L.res le_top s) := by
    intro x hx
    obtain ⟨W, hxW, e, hf⟩ := exists_frame L x
    set f : Γ(X, W) := hf.coord le_rfl (L.res le_top s) with hfdef
    have hle : X.basicOpen f ≤ W := X.basicOpen_le f
    have hmem : x ∈ X.basicOpen f := by
      rw [X.mem_basicOpen f x hxW]
      by_contra hnu
      refine hx ?_
      have hse : L.res le_top s = f • L.res le_rfl e :=
        (IsFrame.coord_smul_frame hf le_rfl _).symm
      have hkey : L.presheaf.germ ⊤ x trivial s =
          X.presheaf.germ W x hxW f • L.presheaf.germ W x hxW e := by
        have h0 : L.presheaf.germ W x hxW (L.res le_top s) = L.presheaf.germ ⊤ x trivial s :=
          TopCat.Presheaf.germ_res_apply _ _ _ _ _
        rw [← h0, hse, res_self, germ_smul']
      rw [hkey]
      exact Submodule.smul_mem_smul (N := (⊤ : Submodule (X.presheaf.stalk x) (L.stalk x)))
        ((IsLocalRing.mem_maximalIdeal _).mpr hnu) Submodule.mem_top
    refine ⟨X.basicOpen f, hmem, ?_⟩
    have hcoord : IsFrame.coord (IsFrame.restrict hf hle) le_rfl (L.res (hle.trans le_top) s) =
        X.presheaf.map (homOfLE hle).op f := by
      refine IsFrame.coord_unique (IsFrame.restrict hf hle) le_rfl _ _ ?_
      have h1 := congrArg (L.res hle) (IsFrame.coord_smul_frame hf le_rfl (L.res le_top s))
      rw [L.res_smul, L.res_res, L.res_res] at h1
      rw [L.res_res]
      exact h1
    have hu : IsUnit (IsFrame.coord (IsFrame.restrict hf hle) le_rfl
        (L.res (hle.trans le_top) s)) := by
      rw [hcoord]
      exact X.toRingedSpace.isUnit_res_basicOpen f
    exact IsFrame.of_isUnit_coord (IsFrame.restrict hf hle) hu
  choose! V hxV hfV using key
  refine IsFrame.of_iSup (ι := (L.nonvanishingLocus s : Set X))
    (fun p => V p.1) (fun p => IsFrame.le_nonvanishingLocus (hfV p.1 p.2)) ?_ ?_
  · intro p hp
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨p, hp⟩, hxV p hp⟩
  · intro p
    rw [L.res_res]
    exact hfV p.1 p.2

end AlgebraicGeometry.Scheme.Modules

/-- The open set `V_ℓ = {v | P_ℓ(v) ≠ 0}`, the non-vanishing locus of `P_ℓ`. -/

def projectivizationChart {V : AlgebraicGeometry.Scheme.{u}} {M : V.Modules} [M.IsLineBundle] {N : ℕ}
    (P : Fin (N + 1) → (M.val.obj (Opposite.op ⊤) : Type u)) (ℓ : Fin (N + 1)) : V.Opens :=
  M.nonvanishingLocus (P ℓ)

/-- `P_ℓ` is a frame on `V_ℓ` (`isFrame_res_nonvanishingLocus`). -/

theorem projectivizationChart_isFrame {V : AlgebraicGeometry.Scheme.{u}} {M : V.Modules}
    [M.IsLineBundle] {N : ℕ}
    (P : Fin (N + 1) → (M.val.obj (Opposite.op ⊤) : Type u)) (ℓ : Fin (N + 1)) :
    AlgebraicGeometry.Scheme.Modules.IsFrame M (projectivizationChart P ℓ)
      (M.res (le_top : projectivizationChart P ℓ ≤ ⊤) (P ℓ)) :=
  AlgebraicGeometry.Scheme.Modules.isFrame_res_nonvanishingLocus M (P ℓ)

/-- The ratio `r_{ℓ,j} = P_j / P_ℓ ∈ Γ(V_ℓ, O)`: the section `r` with `r · P_ℓ|_{V_ℓ} = P_j|_{V_ℓ}`.
Since `P_ℓ` is a frame on `V_ℓ` (`projectivizationChart_isFrame`), the ratio is the coordinate of
`P_j|` in this frame (`IsFrame.coord`). Its defining property is `projectivizationRatio_smul`, its
uniqueness `projectivizationRatio_unique`. -/

noncomputable def projectivizationRatio {V : AlgebraicGeometry.Scheme.{u}} {M : V.Modules}
    [M.IsLineBundle] {N : ℕ}
    (P : Fin (N + 1) → (M.val.obj (Opposite.op ⊤) : Type u)) (ℓ j : Fin (N + 1)) :
    Γ(V, projectivizationChart P ℓ) :=
  AlgebraicGeometry.Scheme.Modules.IsFrame.coord (projectivizationChart_isFrame P ℓ) le_rfl
    (M.res (le_top : projectivizationChart P ℓ ≤ ⊤) (P j))

/-- **Defining property of the ratio**: `r_{ℓ,j} · P_ℓ|_{V_ℓ} = P_j|_{V_ℓ}`. -/

theorem projectivizationRatio_smul {V : AlgebraicGeometry.Scheme.{u}} {M : V.Modules}
    [M.IsLineBundle] {N : ℕ}
    (P : Fin (N + 1) → (M.val.obj (Opposite.op ⊤) : Type u)) (ℓ j : Fin (N + 1)) :
    projectivizationRatio P ℓ j •
        M.res (le_rfl : projectivizationChart P ℓ ≤ projectivizationChart P ℓ)
          (M.res (le_top : projectivizationChart P ℓ ≤ ⊤) (P ℓ)) =
      M.res (le_top : projectivizationChart P ℓ ≤ ⊤) (P j) :=
  AlgebraicGeometry.Scheme.Modules.IsFrame.coord_smul_frame (projectivizationChart_isFrame P ℓ)
    le_rfl _

/-- **Uniqueness of the ratio**: `r_{ℓ,j}` is the only section `r` with `r · P_ℓ| = P_j|`. -/

theorem projectivizationRatio_unique {V : AlgebraicGeometry.Scheme.{u}} {M : V.Modules}
    [M.IsLineBundle] {N : ℕ}
    (P : Fin (N + 1) → (M.val.obj (Opposite.op ⊤) : Type u)) (ℓ j : Fin (N + 1))
    (r : Γ(V, projectivizationChart P ℓ))
    (hr : r • M.res (le_rfl : projectivizationChart P ℓ ≤ projectivizationChart P ℓ)
          (M.res (le_top : projectivizationChart P ℓ ≤ ⊤) (P ℓ)) =
        M.res (le_top : projectivizationChart P ℓ ≤ ⊤) (P j)) :
    projectivizationRatio P ℓ j = r :=
  AlgebraicGeometry.Scheme.Modules.IsFrame.coord_unique (projectivizationChart_isFrame P ℓ)
    le_rfl _ r hr

/-- `r_{ℓ,ℓ} = 1` (the key to the irrelevant-ideal condition). -/

theorem projectivizationRatio_self {V : AlgebraicGeometry.Scheme.{u}} {M : V.Modules}
    [M.IsLineBundle] {N : ℕ}
    (P : Fin (N + 1) → (M.val.obj (Opposite.op ⊤) : Type u)) (ℓ : Fin (N + 1)) :
    projectivizationRatio P ℓ ℓ = 1 :=
  projectivizationRatio_unique P ℓ ℓ 1 (by
    rw [AlgebraicGeometry.Scheme.Modules.res_self, one_smul])

section Ratios

variable {V : AlgebraicGeometry.Scheme.{u}} {M : V.Modules} [M.IsLineBundle] {N : ℕ}
  (P : Fin (N + 1) → (M.val.obj (Opposite.op ⊤) : Type u))

/-- The defining identity of the ratio, restricted to an open `W ⊆ V_ℓ`: `r_{ℓ,j}|_W • P_ℓ|_W = P_j|_W`. -/
theorem projectivizationRatio_res_smul {W : V.Opens} (ℓ j : Fin (N + 1))
    (h : W ≤ projectivizationChart P ℓ) :
    V.presheaf.map (homOfLE h).op (projectivizationRatio P ℓ j) • M.res (le_top : W ≤ ⊤) (P ℓ) =
      M.res (le_top : W ≤ ⊤) (P j) := by
  have h1 := congrArg (M.res h) (projectivizationRatio_smul P ℓ j)
  rw [AlgebraicGeometry.Scheme.Modules.res_self, M.res_smul, M.res_res, M.res_res] at h1
  exact h1

/-- **Cocycle identity of the ratios**: on `V_ℓ ∩ V_m`, `r_{m,j} = r_{ℓ,j} · r_{m,ℓ}`
(both sides times the frame `P_m` give `P_j`). -/
theorem projectivizationRatio_res_eq_mul (ℓ m j : Fin (N + 1)) :
    V.presheaf.map (homOfLE (inf_le_right : projectivizationChart P ℓ ⊓ projectivizationChart P m ≤
        projectivizationChart P m)).op (projectivizationRatio P m j) =
      V.presheaf.map (homOfLE (inf_le_left : projectivizationChart P ℓ ⊓ projectivizationChart P m ≤
          projectivizationChart P ℓ)).op (projectivizationRatio P ℓ j) *
        V.presheaf.map (homOfLE (inf_le_right : projectivizationChart P ℓ ⊓ projectivizationChart P m ≤
          projectivizationChart P m)).op (projectivizationRatio P m ℓ) := by
  have hℓ : projectivizationChart P ℓ ⊓ projectivizationChart P m ≤ projectivizationChart P ℓ :=
    inf_le_left
  have hm : projectivizationChart P ℓ ⊓ projectivizationChart P m ≤ projectivizationChart P m :=
    inf_le_right
  have hfm : AlgebraicGeometry.Scheme.Modules.IsFrame M
      (projectivizationChart P ℓ ⊓ projectivizationChart P m) (M.res hm (M.res le_top (P m))) :=
    (projectivizationChart_isFrame P m).restrict hm
  refine (hfm _ le_rfl).1 ?_
  change _ • M.res le_rfl (M.res hm (M.res le_top (P m))) =
    _ • M.res le_rfl (M.res hm (M.res le_top (P m)))
  rw [AlgebraicGeometry.Scheme.Modules.res_self, M.res_res,
    projectivizationRatio_res_smul P m j hm, mul_smul, projectivizationRatio_res_smul P m ℓ hm,
    projectivizationRatio_res_smul P ℓ j hℓ]

/-- On `V_ℓ ∩ V_m`, `r_{ℓ,m} · r_{m,ℓ} = 1`. -/
theorem projectivizationRatio_res_mul_res (ℓ m : Fin (N + 1)) :
    V.presheaf.map (homOfLE (inf_le_left : projectivizationChart P ℓ ⊓ projectivizationChart P m ≤
        projectivizationChart P ℓ)).op (projectivizationRatio P ℓ m) *
      V.presheaf.map (homOfLE (inf_le_right : projectivizationChart P ℓ ⊓ projectivizationChart P m ≤
        projectivizationChart P m)).op (projectivizationRatio P m ℓ) = 1 := by
  have hℓ : projectivizationChart P ℓ ⊓ projectivizationChart P m ≤ projectivizationChart P ℓ :=
    inf_le_left
  have hm : projectivizationChart P ℓ ⊓ projectivizationChart P m ≤ projectivizationChart P m :=
    inf_le_right
  have hfm : AlgebraicGeometry.Scheme.Modules.IsFrame M
      (projectivizationChart P ℓ ⊓ projectivizationChart P m) (M.res hm (M.res le_top (P m))) :=
    (projectivizationChart_isFrame P m).restrict hm
  refine (hfm _ le_rfl).1 ?_
  change _ • M.res le_rfl (M.res hm (M.res le_top (P m))) =
    _ • M.res le_rfl (M.res hm (M.res le_top (P m)))
  rw [AlgebraicGeometry.Scheme.Modules.res_self, M.res_res, one_smul, mul_smul,
    projectivizationRatio_res_smul P m ℓ hm, projectivizationRatio_res_smul P ℓ m hℓ]

/-- The charts `V_ℓ` form an open cover of `V` (`hP`: the `P_ℓ` have no common zero). Base-free
version of `projectivizationCover`. -/
noncomputable def projectivizationCoverOver (M : V.Modules) [M.IsLineBundle]
    (P : Fin (N + 1) → (M.val.obj (Opposite.op ⊤) : Type u))
    (hP : ∀ v : V, ∃ ℓ, ¬ IsZeroAt (P ℓ) v) : V.OpenCover :=
  V.openCoverOfIsOpenCover (projectivizationChart P) (by
    rw [IsOpenCover, eq_top_iff]
    intro v _
    obtain ⟨ℓ, hℓ⟩ := hP v
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨ℓ, hℓ⟩)

end Ratios

section OverRing

variable {R : Type u} [CommRing R] {V : AlgebraicGeometry.Scheme.{u}}
  (f : V ⟶ AlgebraicGeometry.Spec (CommRingCat.of R))

/-- The `R`-algebra map `R[T_0,…,T_N] → Γ(V_ℓ, O)`, `T_j ↦ r_{ℓ,j}` (`R` acts through `f`). -/
noncomputable def projectivizationChartEvalOver {M : V.Modules} [M.IsLineBundle] {N : ℕ}
    (P : Fin (N + 1) → (M.val.obj (Opposite.op ⊤) : Type u)) (ℓ : Fin (N + 1)) :
    MvPolynomial (Fin (N + 1)) R →+* Γ((projectivizationChart P ℓ).toScheme, ⊤) :=
  MvPolynomial.eval₂Hom
    ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
      ((projectivizationChart P ℓ).ι ≫ f).appTop).hom
    (fun j => (projectivizationChart P ℓ).topIso.inv.hom (projectivizationRatio P ℓ j))

/-- `T_ℓ ↦ r_{ℓ,ℓ} = 1`. -/
theorem projectivizationChartEvalOver_X_self {M : V.Modules} [M.IsLineBundle] {N : ℕ}
    (P : Fin (N + 1) → (M.val.obj (Opposite.op ⊤) : Type u)) (ℓ : Fin (N + 1)) :
    projectivizationChartEvalOver f P ℓ (MvPolynomial.X ℓ) = 1 := by
  rw [projectivizationChartEvalOver, MvPolynomial.eval₂Hom_X', projectivizationRatio_self, map_one]

/-- `T_ℓ ↦ 1` is a unit. -/
theorem projectivizationChartEvalOver_X_isUnit {M : V.Modules} [M.IsLineBundle] {N : ℕ}
    (P : Fin (N + 1) → (M.val.obj (Opposite.op ⊤) : Type u)) (ℓ : Fin (N + 1)) :
    IsUnit (projectivizationChartEvalOver f P ℓ (MvPolynomial.X ℓ)) := by
  rw [projectivizationChartEvalOver_X_self]
  exact isUnit_one

/-- The image of the irrelevant ideal is the unit ideal (`T_ℓ` is homogeneous of degree 1 and maps to 1). -/
theorem projectivizationChartEvalOver_irrelevant_map_eq_top {M : V.Modules} [M.IsLineBundle] {N : ℕ}
    (P : Fin (N + 1) → (M.val.obj (Opposite.op ⊤) : Type u)) (ℓ : Fin (N + 1)) :
    (HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)).toIdeal.map
        (projectivizationChartEvalOver f P ℓ) = ⊤ := by
  rw [Ideal.eq_top_iff_one]
  have hmem0 : (MvPolynomial.X ℓ : MvPolynomial (Fin (N + 1)) R) ∈
      HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) :=
    HomogeneousIdeal.mem_irrelevant_of_mem _ (i := 1) Nat.one_pos
      ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_X R ℓ))
  have hmem : (MvPolynomial.X ℓ : MvPolynomial (Fin (N + 1)) R) ∈
      (HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)).toIdeal :=
    hmem0
  have h := Ideal.mem_map_of_mem (projectivizationChartEvalOver f P ℓ) hmem
  rwa [projectivizationChartEvalOver_X_self] at h

/-- The chart morphism `g_ℓ : V_ℓ → P^N_R` (Mathlib `Proj.fromOfGlobalSections`). -/
noncomputable def projectivizationChartMorphismOver {M : V.Modules} [M.IsLineBundle] {N : ℕ}
    (P : Fin (N + 1) → (M.val.obj (Opposite.op ⊤) : Type u)) (ℓ : Fin (N + 1)) :
    (projectivizationChart P ℓ).toScheme ⟶ ProjectiveSpaceOver N R :=
  AlgebraicGeometry.Proj.fromOfGlobalSections (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
    (projectivizationChartEvalOver f P ℓ)
    (projectivizationChartEvalOver_irrelevant_map_eq_top f P ℓ)

/-- `Proj.fromOfGlobalSections` depends only on the ring map (proof-irrelevant in the ideal condition). -/
theorem Proj.fromOfGlobalSections_congr {A σ : Type u} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] {T : AlgebraicGeometry.Scheme.{u}}
    {e e' : A →+* Γ(T, ⊤)} (h : e = e')
    (he : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map e = ⊤) :
    AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 e he =
      AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 e' (h ▸ he) := by
  subst h
  rfl

/-- **The chart morphisms agree on overlaps.** On `W = V_x ∩ V_y` both `g_x|_W` and `g_y|_W` are
`Proj.fromOfGlobalSections` of the restricted evaluations (`fromOfGlobalSections_naturality`), and these
differ by the homogeneous unit `u = r_{y,x}|_W` (`r_{y,j} = r_{x,j} · r_{y,x}`,
`projectivizationRatio_res_eq_mul`), which does not change the morphism
(`fromOfGlobalSections_unit_scale`). -/
theorem projectivizationChartMorphismOver_agree (M : V.Modules) [M.IsLineBundle] {N : ℕ}
    (P : Fin (N + 1) → (M.val.obj (Opposite.op ⊤) : Type u))
    (hP : ∀ v : V, ∃ ℓ, ¬ IsZeroAt (P ℓ) v) :
    ∀ x y : (projectivizationCoverOver M P hP).I₀,
      CategoryTheory.Limits.pullback.fst ((projectivizationCoverOver M P hP).f x)
            ((projectivizationCoverOver M P hP).f y) ≫
          projectivizationChartMorphismOver f P x =
        CategoryTheory.Limits.pullback.snd ((projectivizationCoverOver M P hP).f x)
            ((projectivizationCoverOver M P hP).f y) ≫
          projectivizationChartMorphismOver f P y := by
  intro x y
  change Fin (N + 1) at x y
  change CategoryTheory.Limits.pullback.fst
        (projectivizationChart P x).ι (projectivizationChart P y).ι ≫
        projectivizationChartMorphismOver f P x =
      CategoryTheory.Limits.pullback.snd
        (projectivizationChart P x).ι (projectivizationChart P y).ι ≫
        projectivizationChartMorphismOver f P y
  rw [← cancel_epi (AlgebraicGeometry.isPullback_opens_inf (projectivizationChart P x)
    (projectivizationChart P y)).isoPullback.hom]
  simp only [IsPullback.isoPullback_hom_fst_assoc, IsPullback.isoPullback_hom_snd_assoc]
  -- the overlap and the two restrictions
  set W : V.Opens := projectivizationChart P x ⊓ projectivizationChart P y with hW
  have hx : W ≤ projectivizationChart P x := inf_le_left
  have hy : W ≤ projectivizationChart P y := inf_le_right
  -- the constants and the coordinates of the restricted evaluations
  let c : R →+* Γ(W.toScheme, ⊤) :=
    ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (W.ι ≫ f).appTop).hom
  let p : Fin (N + 1) → Γ(W.toScheme, ⊤) := fun j =>
    W.topIso.inv.hom (V.presheaf.map (homOfLE hx).op (projectivizationRatio P x j))
  let a : Γ(W.toScheme, ⊤) :=
    W.topIso.inv.hom (V.presheaf.map (homOfLE hy).op (projectivizationRatio P y x))
  have ha : IsUnit a := by
    refine ⟨Units.mkOfMulEqOne a
      (W.topIso.inv.hom (V.presheaf.map (homOfLE hx).op (projectivizationRatio P x y))) ?_, rfl⟩
    rw [← map_mul, mul_comm, projectivizationRatio_res_mul_res P x y, map_one]
  have hconst : ∀ (U : V.Opens) (h : W ≤ U),
      ((V.homOfLE h).appTop).hom.comp
        ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (U.ι ≫ f).appTop).hom = c := by
    intro U h
    change (((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (U.ι ≫ f).appTop) ≫
      (V.homOfLE h).appTop).hom = _
    rw [Category.assoc, ← AlgebraicGeometry.Scheme.Hom.comp_appTop, ← Category.assoc,
      AlgebraicGeometry.Scheme.homOfLE_ι]
  have hcoord : ∀ (U : V.Opens) (h : W ≤ U) (s : Γ(V, U)),
      (V.homOfLE h).appTop.hom (U.topIso.inv.hom s) =
        W.topIso.inv.hom (V.presheaf.map (homOfLE h).op s) := fun U h s =>
    AlgebraicGeometry.Proj.HomogeneousTupleLocalCoordinates.topIso_inv_restrict h s
  have hex : ((V.homOfLE hx).appTop).hom.comp (projectivizationChartEvalOver f P x) =
      MvPolynomial.eval₂Hom c p := by
    rw [projectivizationChartEvalOver, MvPolynomial.comp_eval₂Hom, hconst]
    congr 1
    funext j
    exact hcoord _ hx _
  have hey : ((V.homOfLE hy).appTop).hom.comp (projectivizationChartEvalOver f P y) =
      MvPolynomial.eval₂Hom c (fun j => a * p j) := by
    rw [projectivizationChartEvalOver, MvPolynomial.comp_eval₂Hom, hconst]
    congr 1
    funext j
    rw [hcoord _ hy, projectivizationRatio_res_eq_mul P x y j, map_mul, mul_comm]
  have hscale : ∀ (d : ℕ) (F : MvPolynomial (Fin (N + 1)) R),
      F ∈ MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R d →
        MvPolynomial.eval₂Hom c (fun j => (ha.unit : Γ(W.toScheme, ⊤)) * p j) F =
          (ha.unit : Γ(W.toScheme, ⊤)) ^ d * MvPolynomial.eval₂Hom c p F := by
    intro d F hF
    exact AlgebraicGeometry.Proj.ProjectiveTupleFrameChange.eval₂Hom_scale c p _
      ((MvPolynomial.mem_homogeneousSubmodule _ _).mp hF)
  unfold projectivizationChartMorphismOver
  rw [AlgebraicGeometry.Proj.ProjectiveTupleRestriction.fromOfGlobalSections_naturality,
    AlgebraicGeometry.Proj.ProjectiveTupleRestriction.fromOfGlobalSections_naturality,
    Proj.fromOfGlobalSections_congr _ hex, Proj.fromOfGlobalSections_congr _ hey]
  have hu : (fun j => a * p j) = fun j => (ha.unit : Γ(W.toScheme, ⊤)) * p j := by
    funext j
    rw [IsUnit.unit_spec]
  rw [Proj.fromOfGlobalSections_congr _ (congrArg (MvPolynomial.eval₂Hom c) hu)]
  exact (AlgebraicGeometry.Proj.ProjectiveTupleFrameChange.fromOfGlobalSections_unit_scale
    (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) (MvPolynomial.eval₂Hom c p)
    (MvPolynomial.eval₂Hom c (fun j => (ha.unit : Γ(W.toScheme, ⊤)) * p j)) ha.unit hscale _).symm

/-- **The projectivization morphism over `R`**: `φ : V ⟶ P^N_R`, glued from the chart morphisms. -/
noncomputable def projectivizationMorphismOver (M : V.Modules) [M.IsLineBundle] {N : ℕ}
    (P : Fin (N + 1) → (M.val.obj (Opposite.op ⊤) : Type u))
    (hP : ∀ v : V, ∃ ℓ, ¬ IsZeroAt (P ℓ) v) :
    V ⟶ ProjectiveSpaceOver N R :=
  (projectivizationCoverOver M P hP).glueMorphisms
    (fun ℓ => projectivizationChartMorphismOver f P ℓ)
    (projectivizationChartMorphismOver_agree f M P hP)

/-- `φ` restricts to `g_ℓ` on `V_ℓ`. -/
theorem projectivizationMorphismOver_restrict (M : V.Modules) [M.IsLineBundle] {N : ℕ}
    (P : Fin (N + 1) → (M.val.obj (Opposite.op ⊤) : Type u))
    (hP : ∀ v : V, ∃ ℓ, ¬ IsZeroAt (P ℓ) v) (ℓ : Fin (N + 1)) :
    (projectivizationChart P ℓ).ι ≫ projectivizationMorphismOver f M P hP =
      projectivizationChartMorphismOver f P ℓ := by
  have hglue :=
    (projectivizationCoverOver M P hP).ι_glueMorphisms
      (fun j => projectivizationChartMorphismOver f P j)
      (projectivizationChartMorphismOver_agree f M P hP) ℓ
  change (projectivizationCoverOver M P hP).f ℓ ≫
      (projectivizationCoverOver M P hP).glueMorphisms
        (fun j => projectivizationChartMorphismOver f P j)
        (projectivizationChartMorphismOver_agree f M P hP) = _
  exact hglue

/-- **`φ` is a morphism over `Spec R`**: `φ ≫ (P^N_R → Spec R) = f`. -/
theorem projectivizationMorphismOver_comp_toSpecBase (M : V.Modules) [M.IsLineBundle] {N : ℕ}
    (P : Fin (N + 1) → (M.val.obj (Opposite.op ⊤) : Type u))
    (hP : ∀ v : V, ∃ ℓ, ¬ IsZeroAt (P ℓ) v) :
    projectivizationMorphismOver f M P hP ≫ ProjectiveSpaceOver.toSpecBase N R = f := by
  apply (projectivizationCoverOver M P hP).hom_ext
  intro ℓ
  rw [← Category.assoc]
  change ((projectivizationChart P ℓ).ι ≫ projectivizationMorphismOver f M P hP) ≫ _ = _
  rw [projectivizationMorphismOver_restrict f M P hP]
  change Fin (N + 1) at ℓ
  change projectivizationChartMorphismOver f P ℓ ≫
      (AlgebraicGeometry.Proj.toSpecZero
        (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) ≫
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom
          (algebraMap R ((MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) 0)))) =
    (projectivizationChart P ℓ).ι ≫ f
  rw [← Category.assoc, projectivizationChartMorphismOver,
    AlgebraicGeometry.Proj.fromOfGlobalSections_toSpecZero, Category.assoc,
    ← AlgebraicGeometry.Spec.map_comp, ← CommRingCat.ofHom_comp]
  have heval : ((projectivizationChartEvalOver f P ℓ).comp
      (algebraMap ((MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) 0)
        (MvPolynomial (Fin (N + 1)) R))).comp
        (algebraMap R ((MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R) 0)) =
      ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
        ((projectivizationChart P ℓ).ι ≫ f).appTop).hom := by
    ext c
    simp [projectivizationChartEvalOver]
  rw [heval]
  change (projectivizationChart P ℓ).toScheme.toSpecΓ ≫
      AlgebraicGeometry.Spec.map
        ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
          ((projectivizationChart P ℓ).ι ≫ f).appTop) =
    (projectivizationChart P ℓ).ι ≫ f
  rw [AlgebraicGeometry.Spec.map_comp, ← Category.assoc,
    ← AlgebraicGeometry.Scheme.toSpecΓ_naturality, Category.assoc,
    AlgebraicGeometry.toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]

/-- **`φ⁻¹(D_+(T_i)) = V_i`**. -/
theorem projectivizationMorphismOver_preimage_basicOpen (M : V.Modules) [M.IsLineBundle] {N : ℕ}
    (P : Fin (N + 1) → (M.val.obj (Opposite.op ⊤) : Type u))
    (hP : ∀ v : V, ∃ ℓ, ¬ IsZeroAt (P ℓ) v) (i : Fin (N + 1)) :
    projectivizationMorphismOver f M P hP ⁻¹ᵁ
        AlgebraicGeometry.Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
          (MvPolynomial.X i) =
      projectivizationChart P i := by
  have hchart : ∀ ℓ : Fin (N + 1),
      ((projectivizationChart P ℓ).ι ≫ projectivizationMorphismOver f M P hP) ⁻¹ᵁ
          AlgebraicGeometry.Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
            (MvPolynomial.X i) =
        (projectivizationChart P ℓ).toScheme.basicOpen
          ((projectivizationChart P ℓ).topIso.inv.hom (projectivizationRatio P ℓ i)) := by
    intro ℓ
    rw [projectivizationMorphismOver_restrict, projectivizationChartMorphismOver,
      AlgebraicGeometry.Proj.fromOfGlobalSections_preimage_basicOpen _ _ _ Nat.one_pos
        ((MvPolynomial.mem_homogeneousSubmodule 1 _).mpr (MvPolynomial.isHomogeneous_X R i)),
      projectivizationChartEvalOver, MvPolynomial.eval₂Hom_X']
  apply le_antisymm
  · intro v hv
    obtain ⟨ℓ, hℓ⟩ := hP v
    have hv' : (⟨v, hℓ⟩ : projectivizationChart P ℓ) ∈
        ((projectivizationChart P ℓ).ι ≫ projectivizationMorphismOver f M P hP) ⁻¹ᵁ
          AlgebraicGeometry.Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
            (MvPolynomial.X i) := by
      rw [AlgebraicGeometry.Scheme.Hom.mem_preimage, AlgebraicGeometry.Scheme.Hom.comp_apply]
      exact hv
    rw [hchart] at hv'
    have hvb : v ∈ V.basicOpen (projectivizationRatio P ℓ i) := by
      rw [← AlgebraicGeometry.Scheme.Opens.ι_image_basicOpen_topIso_inv]
      exact (AlgebraicGeometry.Scheme.Opens.mem_ι_image_iff _).mpr hv'
    have hunit : IsUnit (V.presheaf.germ (projectivizationChart P ℓ) v hℓ
        (projectivizationRatio P ℓ i)) :=
      (V.mem_basicOpen _ v hℓ).mp hvb
    have hgerm : M.presheaf.germ ⊤ v trivial (P i) =
        V.presheaf.germ (projectivizationChart P ℓ) v hℓ (projectivizationRatio P ℓ i) •
          M.presheaf.germ ⊤ v trivial (P ℓ) := by
      have h := projectivizationRatio_smul P ℓ i
      rw [AlgebraicGeometry.Scheme.Modules.res_self] at h
      rw [← TopCat.Presheaf.germ_res_apply M.presheaf
          (homOfLE (le_top : projectivizationChart P ℓ ≤ ⊤)) v hℓ (P i),
        ← TopCat.Presheaf.germ_res_apply M.presheaf
          (homOfLE (le_top : projectivizationChart P ℓ ≤ ⊤)) v hℓ (P ℓ)]
      change M.presheaf.germ _ v hℓ (M.res le_top (P i)) =
        _ • M.presheaf.germ _ v hℓ (M.res le_top (P ℓ))
      rw [← h, AlgebraicGeometry.Scheme.Modules.germ_smul']
    show v ∈ M.nonvanishingLocus (P i)
    rw [AlgebraicGeometry.Scheme.Modules.mem_nonvanishingLocus]
    intro hmem
    apply hℓ
    show M.presheaf.germ ⊤ v trivial (P ℓ) ∈ _
    obtain ⟨u, hu⟩ := hunit
    have hPℓ : M.presheaf.germ ⊤ v trivial (P ℓ) =
        (↑u⁻¹ : V.presheaf.stalk v) • M.presheaf.germ ⊤ v trivial (P i) := by
      rw [hgerm, ← hu, smul_smul, Units.inv_mul, one_smul]
    rw [hPℓ]
    exact Submodule.smul_mem _ _ hmem
  · intro v hv
    have h1 : (⟨v, hv⟩ : projectivizationChart P i) ∈
        ((projectivizationChart P i).ι ≫ projectivizationMorphismOver f M P hP) ⁻¹ᵁ
          AlgebraicGeometry.Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
            (MvPolynomial.X i) := by
      rw [hchart, projectivizationRatio_self, map_one, AlgebraicGeometry.Scheme.basicOpen_one]
      trivial
    rw [AlgebraicGeometry.Scheme.Hom.mem_preimage, AlgebraicGeometry.Scheme.Hom.comp_apply] at h1
    exact h1

/-! ## The chart maps `g_ℓ : V_ℓ → D_+(T_ℓ)` and the immersion criterion -/

/-- The chart map `V_ℓ → D_+(T_ℓ)` (`ProjectiveSpaceOverChart.chartMap`). -/
noncomputable def projectivizationChartMapOver {M : V.Modules} [M.IsLineBundle] {N : ℕ}
    (P : Fin (N + 1) → (M.val.obj (Opposite.op ⊤) : Type u)) (ℓ : Fin (N + 1)) :
    (projectivizationChart P ℓ).toScheme ⟶
      (AlgebraicGeometry.Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
        (MvPolynomial.X ℓ)).toScheme :=
  ProjectiveSpaceOverChart.chartMap (projectivizationChart P ℓ).toScheme N
    (projectivizationChartEvalOver f P ℓ) ℓ (projectivizationChartEvalOver_X_isUnit f P ℓ)

/-- `g_ℓ ≫ D_+(T_ℓ).ι = V_ℓ.ι ≫ φ`. -/
theorem projectivizationChartMapOver_comp_ι (M : V.Modules) [M.IsLineBundle] {N : ℕ}
    (P : Fin (N + 1) → (M.val.obj (Opposite.op ⊤) : Type u))
    (hP : ∀ v : V, ∃ ℓ, ¬ IsZeroAt (P ℓ) v) (ℓ : Fin (N + 1)) :
    projectivizationChartMapOver f P ℓ ≫
        (AlgebraicGeometry.Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
          (MvPolynomial.X ℓ)).ι =
      (projectivizationChart P ℓ).ι ≫ projectivizationMorphismOver f M P hP := by
  rw [projectivizationMorphismOver_restrict]
  exact ProjectiveSpaceOverChart.chartMap_ι _ _ _
    (projectivizationChartEvalOver_irrelevant_map_eq_top f P ℓ) ℓ _

/-- `g_ℓ^♯(T_j/T_ℓ) = r_{ℓ,j}`. -/
theorem projectivizationChartMapOver_appTop_ratioSection {M : V.Modules} [M.IsLineBundle] {N : ℕ}
    (P : Fin (N + 1) → (M.val.obj (Opposite.op ⊤) : Type u)) (ℓ j : Fin (N + 1)) :
    (projectivizationChartMapOver f P ℓ).appTop (ProjectiveSpaceOverChart.ratioSection (R := R) N j ℓ) =
      (projectivizationChart P ℓ).topIso.inv.hom (projectivizationRatio P ℓ j) := by
  have h := ProjectiveSpaceOverChart.chartMap_appTop_ratio_mul
    (projectivizationChart P ℓ).toScheme N (projectivizationChartEvalOver f P ℓ) ℓ
    (projectivizationChartEvalOver_X_isUnit f P ℓ) j
  rw [projectivizationChartEvalOver_X_self, mul_one] at h
  rw [projectivizationChartMapOver, h, projectivizationChartEvalOver, MvPolynomial.eval₂Hom_X']

/-- **Closed immersion of a chart map**: if `V_ℓ` is affine and `R[T] → Γ(V_ℓ, O)` is surjective, then
`g_ℓ : V_ℓ → D_+(T_ℓ)` is a closed immersion (`Spec` of the surjective chart evaluation). -/
theorem isClosedImmersion_projectivizationChartMapOver {M : V.Modules} [M.IsLineBundle] {N : ℕ}
    (P : Fin (N + 1) → (M.val.obj (Opposite.op ⊤) : Type u)) (ℓ : Fin (N + 1))
    (haff : AlgebraicGeometry.IsAffineOpen (projectivizationChart P ℓ))
    (hsurj : Function.Surjective (projectivizationChartEvalOver f P ℓ)) :
    AlgebraicGeometry.IsClosedImmersion (projectivizationChartMapOver f P ℓ) := by
  have : AlgebraicGeometry.IsAffine (projectivizationChart P ℓ).toScheme := haff
  have hsurj' : Function.Surjective
      (ProjectiveSpaceOverChart.chartEvaluation N (projectivizationChartEvalOver f P ℓ)
        ℓ (projectivizationChartEvalOver_X_isUnit f P ℓ)) :=
    ProjectiveSpaceOverChart.chartEvaluation_surjective N _ ℓ
      (projectivizationChartEvalOver_X_self f P ℓ) hsurj
  have hcl : AlgebraicGeometry.IsClosedImmersion
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom
        (ProjectiveSpaceOverChart.chartEvaluation N (projectivizationChartEvalOver f P ℓ)
          ℓ (projectivizationChartEvalOver_X_isUnit f P ℓ)))) :=
    AlgebraicGeometry.IsClosedImmersion.spec_of_surjective _ hsurj'
  unfold projectivizationChartMapOver ProjectiveSpaceOverChart.chartMap
  infer_instance

/-- Generic: if `φ⁻¹ᵁ D = U` and `g : U → D` satisfies `g ≫ D.ι = U.ι ≫ φ`, then the restriction
`φ ∣_ D` is `g` up to the canonical identification of the sources. -/
theorem AlgebraicGeometry.morphismRestrict_eq_isoOfEq_comp {V W : AlgebraicGeometry.Scheme.{u}}
    (φ : V ⟶ W) (D : W.Opens) {U : V.Opens} (hpre : φ ⁻¹ᵁ D = U)
    (g : U.toScheme ⟶ D.toScheme) (hg : g ≫ D.ι = U.ι ≫ φ) :
    φ ∣_ D = (V.isoOfEq hpre).hom ≫ g := by
  rw [← cancel_mono D.ι, AlgebraicGeometry.morphismRestrict_ι, Category.assoc, hg,
    ← Category.assoc, AlgebraicGeometry.Scheme.isoOfEq_hom_ι]

/-- **Immersion criterion**: if the charts `V_ℓ`, `ℓ ∈ S`, cover `V` and each `g_ℓ` (`ℓ ∈ S`) is a closed
immersion, then `φ` is an immersion (`IsZariskiLocalAtTarget.of_range_subset_iSup`). -/
theorem isImmersion_projectivizationMorphismOver_of_charts (M : V.Modules) [M.IsLineBundle] {N : ℕ}
    (P : Fin (N + 1) → (M.val.obj (Opposite.op ⊤) : Type u))
    (hP : ∀ v : V, ∃ ℓ, ¬ IsZeroAt (P ℓ) v) (S : Set (Fin (N + 1)))
    (hcov : ∀ v : V, ∃ ℓ ∈ S, ¬ IsZeroAt (P ℓ) v)
    (hcl : ∀ ℓ ∈ S, AlgebraicGeometry.IsClosedImmersion (projectivizationChartMapOver f P ℓ)) :
    AlgebraicGeometry.IsImmersion (projectivizationMorphismOver f M P hP) := by
  have hRR : MorphismProperty.RespectsRight (C := AlgebraicGeometry.Scheme.{u})
      @AlgebraicGeometry.IsImmersion @AlgebraicGeometry.IsOpenImmersion :=
    ⟨fun i hi g hg => by
      have : AlgebraicGeometry.IsImmersion g := hg
      have : AlgebraicGeometry.IsOpenImmersion i := hi
      infer_instance⟩
  apply AlgebraicGeometry.IsZariskiLocalAtTarget.of_range_subset_iSup
    (P := @AlgebraicGeometry.IsImmersion)
    (U := fun ℓ : S => (AlgebraicGeometry.Proj.basicOpen
      (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
      (MvPolynomial.X ℓ.1) : (ProjectiveSpaceOver N R).Opens))
  · rintro _ ⟨v, rfl⟩
    obtain ⟨ℓ, hℓS, hv⟩ := hcov v
    have hv' : v ∈ projectivizationMorphismOver f M P hP ⁻¹ᵁ
        (AlgebraicGeometry.Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
          (MvPolynomial.X ℓ) : (ProjectiveSpaceOver N R).Opens) := by
      rw [projectivizationMorphismOver_preimage_basicOpen]
      exact hv
    rw [SetLike.mem_coe, TopologicalSpace.Opens.mem_iSup]
    exact ⟨⟨ℓ, hℓS⟩, hv'⟩
  · rintro ⟨ℓ, hℓ⟩
    show AlgebraicGeometry.IsImmersion (projectivizationMorphismOver f M P hP ∣_
      (AlgebraicGeometry.Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
        (MvPolynomial.X ℓ) : (ProjectiveSpaceOver N R).Opens))
    have hpre := projectivizationMorphismOver_preimage_basicOpen f M P hP ℓ
    have heq := AlgebraicGeometry.morphismRestrict_eq_isoOfEq_comp
      (projectivizationMorphismOver f M P hP)
      (AlgebraicGeometry.Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)
        (MvPolynomial.X ℓ) : (ProjectiveSpaceOver N R).Opens) hpre
      (projectivizationChartMapOver f P ℓ) (projectivizationChartMapOver_comp_ι f M P hP ℓ)
    have hcl' := hcl ℓ hℓ
    have himm : AlgebraicGeometry.IsImmersion
        ((V.isoOfEq hpre).hom ≫ projectivizationChartMapOver f P ℓ) := inferInstance
    exact (congrArg (fun g => AlgebraicGeometry.IsImmersion g) heq).mpr himm

/-- **Surjectivity of the chart evaluation from generators**: if `V_ℓ = W` carries `t_i ∈ Γ(V, W)` with
`R[y_1..y_m] → Γ(W, O)`, `y_i ↦ t_i` surjective, and each `t_i` is a ratio `P_{j(i)}/P_ℓ`, then
`R[T_0..T_N] → Γ(V_ℓ, O)`, `T_j ↦ r_{ℓ,j}` is surjective. -/
theorem projectivizationChartEvalOver_surjective_of_generators {M : V.Modules} [M.IsLineBundle] {N : ℕ}
    (P : Fin (N + 1) → (M.val.obj (Opposite.op ⊤) : Type u)) (ℓ : Fin (N + 1))
    {W : V.Opens} (hW : projectivizationChart P ℓ = W) {m : ℕ} (t : Fin m → Γ(V, W))
    (hsurj : Function.Surjective (MvPolynomial.eval₂Hom
      ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (W.ι ≫ f).appTop).hom
      (fun i => W.topIso.inv.hom (t i))))
    (hcoord : ∀ i, ∃ j, M.res (le_top : W ≤ ⊤) (P j) = t i • M.res (le_top : W ≤ ⊤) (P ℓ)) :
    Function.Surjective (projectivizationChartEvalOver f P ℓ) := by
  subst hW
  choose j hj using hcoord
  have hratio : ∀ i, projectivizationRatio P ℓ (j i) = t i := fun i =>
    projectivizationRatio_unique P ℓ (j i) (t i)
      (by rw [AlgebraicGeometry.Scheme.Modules.res_self]; exact (hj i).symm)
  intro y
  obtain ⟨q, rfl⟩ := hsurj y
  refine ⟨MvPolynomial.rename j q, ?_⟩
  have hfun : (fun i' => (projectivizationChart P ℓ).topIso.inv.hom (projectivizationRatio P ℓ i')) ∘
      j = fun i => (projectivizationChart P ℓ).topIso.inv.hom (t i) := by
    funext i
    simp only [Function.comp, hratio]
  rw [projectivizationChartEvalOver, MvPolynomial.eval₂Hom_rename, hfun]

end OverRing

end
