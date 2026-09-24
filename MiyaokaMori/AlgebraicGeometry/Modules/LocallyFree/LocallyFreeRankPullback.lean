import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.LocallyFreeRank
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.AlgebraicGeometry.Restrict

/-!
# Pullback preserves the rank of a locally free module sheaf

The local frames are those of `AlgebraicGeometry.Scheme.Modules.IsLocallyFreeRank`. A frame on an open
subset of the target is pulled back along the restricted scheme morphism to
the inverse-image open subset. Restriction and pullback are compared using
the commuting square of the two open immersions, and the pullback of the same
free module sheaf supplies a frame with the original index set.

This helper supports the restriction of line modules. It
uses no curve presentation or Cartier-existence theorem. Rank zero and empty
schemes are included, and no compatibility with the specified field maps is
needed for the underlying module-sheaf pullback.

Source: Stacks Project, `modules.tex`, `definition-locally-free` and
`lemma-pullback-locally-free`; `chow.tex`, `definition-cap-c1` (Tag 02SO).
Its consumer is the proof of `exists_oneCycleCartierRepresentative`.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Proj

variable {k : Type u} [Field k]

set_option backward.isDefEq.respectTransparency false in
/-- Pulling back the same locally free module sheaf preserves its specified finite rank. -/
theorem isLocallyFreeRank_pullback {X Y : SchemeOver k} {L : X.scheme.Modules} {n : ℕ}
    (hL : IsLocallyFreeRank X L n) (f : Y.scheme ⟶ X.scheme) :
    IsLocallyFreeRank Y ((Scheme.Modules.pullback f).obj L) n := by
  constructor
  intro y
  obtain ⟨U, hy, ⟨e⟩⟩ := hL.local_frame (f y)
  have : (Opens.map (f ∣_ U).base).Final := final_of_representablyFlat _
  refine ⟨f ⁻¹ᵁ U, hy, ⟨?_⟩⟩
  exact
    (Scheme.Modules.restrictFunctorIsoPullback (f ⁻¹ᵁ U).ι).app
        ((Scheme.Modules.pullback f).obj L) ≪≫
      (Scheme.Modules.pullbackComp (f ⁻¹ᵁ U).ι f).app L ≪≫
      (Scheme.Modules.pullbackCongr (morphismRestrict_ι f U).symm).app L ≪≫
      ((Scheme.Modules.pullbackComp (f ∣_ U) U.ι).app L).symm ≪≫
      (Scheme.Modules.pullback (f ∣_ U)).mapIso
        (((Scheme.Modules.restrictFunctorIsoPullback U.ι).app L).symm ≪≫ e) ≪≫
      SheafOfModules.pullbackObjFreeIso (f ∣_ U).toRingCatSheafHom (ULift.{u} (Fin n))

end AlgebraicGeometry.Scheme.Modules
