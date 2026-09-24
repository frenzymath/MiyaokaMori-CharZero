import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.RegularSection

/-! # The frame locus of a global section

The **frame locus** `M.frameLocus s : X.Opens` of a global section `s` of a sheaf of modules `M` is
the union of all opens `W` on which `s|_W` is a frame of `M` (the largest open on which `s` freely
generates `M`; for a line bundle `L` it is `X_s = {x | s_x ∉ m_x L_x}`, Stacks 01CY).
`mem_frameLocus`, `IsFrame.le_frameLocus`; `s` is a frame iff its coordinate in any frame is a unit
(`IsFrame.of_isUnit_coord`, `IsFrame.isUnit_coord`).

Design: the frame locus is defined as a supremum of opens, so the definition carries no proof
obligation, and the property needed downstream — `s` generates `L` everywhere on `X_s` — is the
membership condition itself. The equivalence with the stalk condition for line bundles
(`frameLocus_eq_nonvanishingLocus`) is in a separate bridge module.

Reference: Stacks 01CY.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory Opposite TopologicalSpace

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- `X_s`: the union of all opens on which the restriction of `s` is a frame. -/
def frameLocus (M : X.Modules) (s : Γ(M, ⊤)) : X.Opens :=
  sSup {W : X.Opens | IsFrame M W (M.res le_top s)}

theorem mem_frameLocus {M : X.Modules} {s : Γ(M, ⊤)} {x : X} :
    x ∈ M.frameLocus s ↔ ∃ W : X.Opens, x ∈ W ∧ IsFrame M W (M.res le_top s) := by
  unfold frameLocus
  rw [Opens.mem_sSup]
  exact ⟨fun ⟨W, hW, hx⟩ ↦ ⟨W, hx, hW⟩, fun ⟨W, hx, hW⟩ ↦ ⟨W, hW, hx⟩⟩

theorem IsFrame.le_frameLocus {M : X.Modules} {s : Γ(M, ⊤)} {W : X.Opens}
    (h : IsFrame M W (M.res le_top s)) : W ≤ M.frameLocus s :=
  le_sSup h

/-- If `s` is a unit multiple of a frame, then `s` is a frame. -/
theorem IsFrame.of_isUnit_coord {M : X.Modules} {W : X.Opens} {e : Γ(M, W)} (hf : IsFrame M W e)
    {t : Γ(M, W)} (hu : IsUnit (hf.coord le_rfl t)) : IsFrame M W t := by
  intro W' h
  have ht : M.res h t = X.presheaf.map (homOfLE h).op (hf.coord le_rfl t) • M.res h e := by
    have := congrArg (M.res h) (hf.coord_smul_frame le_rfl t)
    rw [res_smul, res_self] at this
    exact this.symm
  have hu' : IsUnit (X.presheaf.map (homOfLE h).op (hf.coord le_rfl t)) := hu.map _
  obtain ⟨u, hu''⟩ := hu'
  have hfun : (fun r : Γ(X, W') ↦ r • M.res h t) =
      (fun r : Γ(X, W') ↦ r • M.res h e) ∘ (fun r : Γ(X, W') ↦ r * (u : Γ(X, W'))) := by
    funext r
    simp only [Function.comp_apply]
    rw [ht, ← hu'', mul_smul]
  rw [hfun]
  exact (hf W' h).comp (Units.mulRight_bijective u)

/-- Conversely, if `s` is a frame then its coordinate in any frame is a unit. -/
theorem IsFrame.isUnit_coord {M : X.Modules} {W : X.Opens} {e t : Γ(M, W)} (hf : IsFrame M W e)
    (ht : IsFrame M W t) : IsUnit (hf.coord le_rfl t) := by
  obtain ⟨u, hu⟩ := hf.exists_unit ht
  have : hf.coord le_rfl t = u := hf.coord_unique le_rfl t u (by rw [res_self]; exact hu)
  rw [this]
  exact u.isUnit

end AlgebraicGeometry.Scheme.Modules

end
