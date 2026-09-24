import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorPowMapIso
import MiyaokaMori.AlgebraicGeometry.Modules.Ample.AmpleLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.NonvanishingLocusIsoInvariant
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle

/-! # Ampleness is invariant under isomorphism

Ampleness depends only on the isomorphism class of a line bundle: if `L ≅ L'` and `L` is ample,
then `L'` is ample.

Proof sketch: an isomorphism `e : L ≅ L'` induces `tensorPow L m ≅ tensorPow L' m`
(`tensorPowMapIso`); nonvanishing loci are invariant under isomorphisms of module sheaves
(`nonvanishingLocus_iso`), so the affine cover given by `IsAmple L` transports to `L'`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Ampleness is invariant under isomorphism of line bundles. -/
theorem AlgebraicGeometry.IsAmple.of_iso {X : AlgebraicGeometry.Scheme.{u}} {L L' : X.Modules}
    [L.IsLineBundle] [L'.IsLineBundle] (e : L ≅ L') (h : AlgebraicGeometry.IsAmple L) :
    AlgebraicGeometry.IsAmple L' := by
  obtain ⟨hcpt, hcov⟩ := h
  refine ⟨hcpt, fun x => ?_⟩
  obtain ⟨m, hm, s, hxs, haff⟩ := hcov x
  refine ⟨m, hm,
    (AlgebraicGeometry.Scheme.Modules.tensorPowMapIso e m).hom.app ⊤ s, ?_, ?_⟩
  · exact (AlgebraicGeometry.Scheme.Modules.mem_nonvanishingLocus_iso
      (AlgebraicGeometry.Scheme.Modules.tensorPowMapIso e m) s x).mpr hxs
  · rw [AlgebraicGeometry.Scheme.Modules.nonvanishingLocus_iso]
    exact haff

end
