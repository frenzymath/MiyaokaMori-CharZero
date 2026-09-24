import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.ModuleSheafFrame

/-! # The frame locus of a local section

The **frame locus of a local section**: for `s ∈ Γ(M, U)` the open `M.frameLocusOn s ≤ U` is the union of all
opens `W ≤ U` on which `s|_W` is a frame (`IsFrame`, i.e. `r ↦ r • s|_{W'}` bijective for every `W' ≤ W`).
It generalises `frameLocus` (global sections) verbatim: `frameLocusOn` of a global section is `frameLocus`
(proved where it is needed, in `Stacks07rm_RelativeChartSections`). For a line bundle `M` this is the
nonvanishing locus `U_s` of Stacks 01CY, restricted to `U`.

Contents: `frameLocusOn_le`, `mem_frameLocusOn`, `IsFrame.le_frameLocusOn`, `IsFrame.of_sSup` (frames glue
along any family of opens — the sSup form of `IsFrame.of_iSup`, re-proved here to keep the import closure
small), `isFrame_res_frameLocusOn` (`s` is a frame on its frame locus), `frameLocusOn_eq_of_isFrame`
(characterisation as the largest frame open).

Used for the quasi-projective immersion into a relative Proj (Stacks 07RM): the charts of the immersion
`X → P(E)` are the frame loci of the local sections `φ(e) ∈ Γ(M, f⁻¹V)`. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- The frame locus of a local section `s ∈ Γ(M, U)`: the union of all opens `W ≤ U` on which `s|_W` is a frame. -/
def frameLocusOn (M : X.Modules) {U : X.Opens} (s : Γ(M, U)) : X.Opens :=
  sSup {W : X.Opens | ∃ h : W ≤ U, IsFrame M W (M.res h s)}

theorem frameLocusOn_le (M : X.Modules) {U : X.Opens} (s : Γ(M, U)) : M.frameLocusOn s ≤ U :=
  sSup_le fun _ hW => hW.1

theorem mem_frameLocusOn {M : X.Modules} {U : X.Opens} {s : Γ(M, U)} {x : X} :
    x ∈ M.frameLocusOn s ↔ ∃ (W : X.Opens) (h : W ≤ U), x ∈ W ∧ IsFrame M W (M.res h s) := by
  unfold frameLocusOn
  rw [Opens.mem_sSup]
  exact ⟨fun ⟨W, ⟨h, hf⟩, hx⟩ => ⟨W, h, hx, hf⟩, fun ⟨W, h, hx, hf⟩ => ⟨W, ⟨h, hf⟩, hx⟩⟩

theorem IsFrame.le_frameLocusOn {M : X.Modules} {U : X.Opens} {s : Γ(M, U)} {W : X.Opens} (h : W ≤ U)
    (hf : IsFrame M W (M.res h s)) : W ≤ M.frameLocusOn s :=
  le_sSup ⟨h, hf⟩

/-- **Frames glue** (sSup form): if `W` is covered by a family `𝒮` of opens `≤ W` on each of which `e` restricts
to a frame, then `e` is a frame on `W`. Injectivity uses the separation axiom of the structure sheaf,
surjectivity its gluing axiom (the compatibility of the local coordinates follows from injectivity on the
overlaps), and finally the sheaf condition of `M` identifies the glued coordinate. -/
theorem IsFrame.of_sSup {M : X.Modules} {W : X.Opens} {e : Γ(M, W)} (𝒮 : Set X.Opens)
    (h𝒮 : ∀ V ∈ 𝒮, V ≤ W) (hcover : W ≤ sSup 𝒮)
    (hfr : ∀ V (hV : V ∈ 𝒮), IsFrame M V (M.res (h𝒮 V hV) e)) : IsFrame M W e := by
  intro W' hW'
  let O : 𝒮 → X.Opens := fun V => W' ⊓ V.1
  have hOW' : ∀ V, O V ≤ W' := fun _ => inf_le_left
  have hOV : ∀ V : 𝒮, O V ≤ V.1 := fun _ => inf_le_right
  have hcov : W' ≤ iSup O := by
    intro p hp
    have hp' : p ∈ sSup 𝒮 := hcover (hW' hp)
    rw [Opens.mem_sSup] at hp'
    obtain ⟨V, hV, hpV⟩ := hp'
    exact Opens.mem_iSup.mpr ⟨⟨V, hV⟩, ⟨hp, hpV⟩⟩
  constructor
  · intro r r' hrr
    refine X.sheaf.eq_of_locally_eq' O W' (fun V => homOfLE (hOW' V)) hcov r r' fun V => ?_
    refine (hfr V.1 V.2 (O V) (hOV V)).1 ?_
    have h1 := congrArg (M.res (hOW' V)) hrr
    rw [M.res_smul, M.res_smul, M.res_res] at h1
    simp only [M.res_res]
    exact h1
  · intro x
    have hx : ∀ V : 𝒮, ∃ r : Γ(X, O V), r • M.res (hOV V) (M.res (h𝒮 V.1 V.2) e) = M.res (hOW' V) x :=
      fun V => (hfr V.1 V.2 (O V) (hOV V)).2 _
    choose r hr using hx
    simp only [M.res_res] at hr
    have hcompat : TopCat.Presheaf.IsCompatible X.presheaf O r := by
      intro i j
      refine (hfr i.1 i.2 (O i ⊓ O j) (inf_le_left.trans (hOV i))).1 ?_
      simp only [M.res_res]
      have h1 := congrArg (M.res (inf_le_left : O i ⊓ O j ≤ O i)) (hr i)
      have h2 := congrArg (M.res (inf_le_right : O i ⊓ O j ≤ O j)) (hr j)
      rw [M.res_smul, M.res_res, M.res_res] at h1
      rw [M.res_smul, M.res_res, M.res_res] at h2
      exact h1.trans h2.symm
    obtain ⟨rr, hrr, -⟩ :=
      X.sheaf.existsUnique_gluing' O W' (fun V => homOfLE (hOW' V)) hcov r hcompat
    let sglue : Γ(X, W') := rr
    refine ⟨sglue, ?_⟩
    refine TopCat.Sheaf.eq_of_locally_eq' ⟨M.presheaf, M.isSheaf⟩ O W'
      (fun V => homOfLE (hOW' V)) hcov _ _ fun V => ?_
    show M.res (hOW' V) (sglue • M.res hW' e) = M.res (hOW' V) x
    rw [M.res_smul, M.res_res]
    have hh : X.presheaf.map (homOfLE (hOW' V)).op sglue = r V := hrr V
    rw [hh]
    exact hr V

/-- `s` is a frame on its frame locus. -/
theorem isFrame_res_frameLocusOn (M : X.Modules) {U : X.Opens} (s : Γ(M, U)) :
    IsFrame M (M.frameLocusOn s) (M.res (M.frameLocusOn_le s) s) := by
  refine IsFrame.of_sSup {W : X.Opens | ∃ h : W ≤ U, IsFrame M W (M.res h s)}
    (fun W hW => le_sSup hW) le_rfl (fun W hW => ?_)
  obtain ⟨h, hf⟩ := hW
  convert hf using 2
  exact M.res_res _ _ _

/-- The frame locus is the largest open on which `s` is a frame. -/
theorem frameLocusOn_eq_of_isFrame {M : X.Modules} {U : X.Opens} {s : Γ(M, U)} {W : X.Opens} (h : W ≤ U)
    (hf : IsFrame M W (M.res h s)) (hmax : ∀ (W' : X.Opens) (h' : W' ≤ U), IsFrame M W' (M.res h' s) → W' ≤ W) :
    M.frameLocusOn s = W :=
  le_antisymm (hmax _ _ (M.isFrame_res_frameLocusOn s)) (hf.le_frameLocusOn h)

/-- Points of the frame locus: `x ∈ frameLocusOn s` iff `s` is a frame on some open neighbourhood of `x` inside `U`. -/
theorem mem_frameLocusOn_iff_exists_isFrame {M : X.Modules} {U : X.Opens} {s : Γ(M, U)} {x : X} :
    x ∈ M.frameLocusOn s ↔ ∃ (W : X.Opens) (h : W ≤ U), x ∈ W ∧ IsFrame M W (M.res h s) :=
  mem_frameLocusOn

end AlgebraicGeometry.Scheme.Modules

end
