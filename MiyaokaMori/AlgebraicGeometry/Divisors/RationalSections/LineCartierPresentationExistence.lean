import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.FiniteFrameCover
import MiyaokaMori.AlgebraicGeometry.Divisors.RationalSections.LineCartierFinitePresentation

/-!
# Cartier presentations from the actual finite frame cover

The Noetherian hypothesis supplies compactness. A finite subcover of the given rank-one
module's frames retains a point in every selected open, so all selected opens are nonempty.
The existing finite-frame construction then gives the Cartier equations of the specified
nonzero generic section and their unit ratios on entire overlaps.

Sources: Theorem 1.1 of the paper and the proof of Proposition 2.4; Stacks
Project `divisors.tex`, `section-c1`, and `chow.tex`, `definition-divisor-invertible-sheaf`.
-/

open AlgebraicGeometry AlgebraicGeometry.Divisors AlgebraicGeometry.Proj AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Divisors.LineCartierPresentationExistence

universe u

/-- A nonzero rational section of the same rank-one module on a Noetherian integral
scheme has a Cartier presentation by actual local frames and whole-overlap units. -/
theorem exists_lineCartierPresentation {k : Type u} [Field k]
    (X : SchemeOver k) [IsIntegral X.scheme] [IsNoetherian X.scheme]
    (M : X.scheme.Modules) (hM : IsLocallyFreeRank X M 1)
    (s : M.presheaf.stalk (genericPoint X.scheme)) (hs : s ≠ 0) :
    Nonempty (LineCartierPresentation X M s) := by
  classical
  obtain ⟨S, U, hU, hframe, hcover⟩ := hM.exists_finite_frame_cover
  exact ⟨LineCartierFinitePresentation.ofFiniteFrames X M U
    (fun i ↦ ⟨⟨i.val, hU i⟩⟩) hcover (fun i ↦ Classical.choice (hframe i)) s hs⟩

end AlgebraicGeometry.Divisors.LineCartierPresentationExistence
