import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.LocallyFreeRank
import Mathlib.Topology.Compactness.Compact

/-!
# Finite covers by actual module frames

On a compact scheme, the pointwise frames in `IsLocallyFreeRank` admit a finite subcover.
The selected opens retain their original points and isomorphisms for the same module sheaf.
In particular, each selected open is nonempty; no nonempty hypothesis on the whole scheme,
integrality, Noetherianity, or positive-rank assumption is needed.

This is the finite-cover step in the construction of a line Cartier presentation from local
frames. It does not construct the rational coordinates or their unit ratios. See Stacks,
`section-c1`, and the local-frame definition `AlgebraicGeometry.Scheme.Modules.IsLocallyFreeRank` (`LocallyFreeRank`).
-/

open AlgebraicGeometry CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Proj

universe u

variable {k : Type u} [Field k] {X : SchemeOver k} [CompactSpace X.scheme]
variable {M : X.scheme.Modules} {n : ℕ}

/-- A locally free module on a compact scheme has a finite cover by its actual nonempty frames. -/
theorem IsLocallyFreeRank.exists_finite_frame_cover (hM : IsLocallyFreeRank X M n) :
    ∃ (S : Finset X.scheme) (U : S → X.scheme.Opens),
      (∀ i : S, (i : X.scheme) ∈ U i) ∧
      (∀ i : S, Nonempty (M.restrict (U i).ι ≅
        SheafOfModules.free (R := (U i).toScheme.ringCatSheaf) (ULift.{u} (Fin n)))) ∧
      (⋃ i : S, (U i : Set X.scheme)) = Set.univ := by
  classical
  choose U hU hframe using hM.local_frame
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover
    (fun x : X.scheme ↦ (U x : Set X.scheme)) (fun x ↦ (U x).isOpen)
    (fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hU x⟩)
  refine ⟨S, fun i ↦ U i.val, fun i ↦ hU i.val, fun i ↦ hframe i.val, ?_⟩
  apply Set.Subset.antisymm (Set.subset_univ _)
  intro x hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hS hx)
  obtain ⟨hiS, hxi⟩ := Set.mem_iUnion.mp hi
  exact Set.mem_iUnion.mpr ⟨⟨i, hiS⟩, hxi⟩

end AlgebraicGeometry.Scheme.Modules
