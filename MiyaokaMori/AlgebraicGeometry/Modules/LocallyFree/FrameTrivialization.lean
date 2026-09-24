import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.Frame

/-! # Frames give trivializations

A frame of a sheaf of modules `M` on an open `W` gives `M|_W ≅ O_W` (`IsFrame.trivialization`, the
isomorphism `1 ↦ e`). Hence `M.IsLineBundle ⟺` every point has an open neighbourhood with a frame
(`isLineBundle_iff_exists_frame`).

Design: a frame is a ring-theoretic condition on a section, a trivialization is a categorical
isomorphism; `Frame` gives "trivialization ⇒ frame", this file gives the converse. Together they
let "line bundle" be verified entirely by frames: the dual, an ideal sheaf or a tensor product is a
line bundle as soon as one writes down a frame. `homOfSection`, `isIso_of_bijective`,
`IsFrame.topTrivialization`, `IsFrame.restrict_top` and `IsFrame.restrictIso` with its
characterizing lemmas live in `ModuleSheafFrame`.

Reference: Stacks 01CR.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory Opposite TopologicalSpace

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

set_option backward.isDefEq.respectTransparency false

variable {X : Scheme.{u}}

/-- A frame gives a local trivialization `O_W ≅ M|_W`. -/
def IsFrame.trivialization {M : X.Modules} {W : X.Opens} {e : Γ(M, W)} (hf : IsFrame M W e) :
    Trivialization M where
  carrier := W
  iso := hf.restrict_top.topTrivialization.symm

@[simp] theorem IsFrame.trivialization_carrier {M : X.Modules} {W : X.Opens} {e : Γ(M, W)}
    (hf : IsFrame M W e) : hf.trivialization.carrier = W := rfl

/-- Line bundle ⟺ every point has an open neighbourhood with a frame. -/
theorem isLineBundle_iff_exists_frame (M : X.Modules) :
    M.IsLineBundle ↔ ∀ p : X, ∃ (W : X.Opens) (_ : p ∈ W) (e : Γ(M, W)), IsFrame M W e :=
  ⟨fun _ p ↦ exists_frame M p, fun h ↦ (isLineBundle_iff M).mpr fun p ↦ by
    obtain ⟨W, hp, e, he⟩ := h p
    exact ⟨he.trivialization, hp⟩⟩

end AlgebraicGeometry.Scheme.Modules

end
