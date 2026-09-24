import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorPowCanonicalIso
import MiyaokaMori.AlgebraicGeometry.Modules.Ample.AmpleLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.NonvanishingLocusIsoInvariant
import MiyaokaMori.Paper.S2WeightedJets.Cone.SeedSectionInPunctured
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.SectionPullbackNotZeroAt

/-! # Ampleness is invariant under pullback along isomorphisms

If `e : X' ⟶ X` is an isomorphism of schemes and `N` is an ample line bundle on `X`, then `e^*N` is
ample. This is the transport lemma needed in the proof of Stacks 01VJ to reduce to the pieces of an
affine cover (ampleness depends only on the isomorphism class of the scheme).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The nonvanishing locus of a pulled-back section, pointwise: `x ∈ (g^*N)_{g^*s} ↔ g x ∈ N_s` (for
any morphism of schemes `g`). The two directions are `isZeroAt_of_isZeroAt_sectionPullbackAlong` and
`isZeroAt_sectionPullbackAlong_of_isZeroAt`. -/
theorem AlgebraicGeometry.Scheme.Modules.mem_nonvanishingLocus_sectionPullbackAlong
    {X' X : AlgebraicGeometry.Scheme.{u}} (g : X' ⟶ X) (N : X.Modules) [N.IsLineBundle]
    (s : (N.val.obj (Opposite.op ⊤) : Type u)) (x : X') :
    x ∈ ((AlgebraicGeometry.Scheme.Modules.pullback g).obj N).nonvanishingLocus
        (sectionPullbackAlong g s) ↔ g.base x ∈ N.nonvanishingLocus s := by
  constructor
  · intro hx hcon
    exact hx (isZeroAt_sectionPullbackAlong_of_isZeroAt g N s x hcon)
  · intro hx hcon
    exact hx (isZeroAt_of_isZeroAt_sectionPullbackAlong g N s x hcon)

/-- The nonvanishing locus of a pulled-back section is the preimage of the original one:
`(g^*N)_{g^*s} = g⁻¹(N_s)`. -/
theorem AlgebraicGeometry.Scheme.Modules.nonvanishingLocus_sectionPullbackAlong
    {X' X : AlgebraicGeometry.Scheme.{u}} (g : X' ⟶ X) (N : X.Modules) [N.IsLineBundle]
    (s : (N.val.obj (Opposite.op ⊤) : Type u)) :
    ((AlgebraicGeometry.Scheme.Modules.pullback g).obj N).nonvanishingLocus
        (sectionPullbackAlong g s) = g ⁻¹ᵁ N.nonvanishingLocus s := by
  apply TopologicalSpace.Opens.ext
  ext x
  exact AlgebraicGeometry.Scheme.Modules.mem_nonvanishingLocus_sectionPullbackAlong g N s x

/-- **Ampleness is invariant under pullback along isomorphisms**: `e : X' ⟶ X` an isomorphism of
schemes, `N` ample ⇒ `e^*N` ample.

Proof: `X'` is quasi-compact (homeomorphic to `X`). For `x' : X'`, the ampleness data of `N` at
`e x'` give `m > 0` and `s ∈ Γ(X, N^{⊗m})` with `e x' ∈ X_s` affine. Put
`s' := θ(e^*s) ∈ Γ(X', (e^*N)^{⊗m})` (`θ = pullbackTensorPowIso e N m : e^*(N^{⊗m}) ≅ (e^*N)^{⊗m}`).
Then `X'_{s'} = X'_{e^*s}` (`nonvanishingLocus_iso`) `= e⁻¹(X_s)` (`nonvanishingLocus_sectionPullbackAlong`),
which contains `x'` and is affine (`IsAffineOpen.preimage_of_isIso`). -/
theorem AlgebraicGeometry.IsAmple.pullback_of_isIso {X' X : AlgebraicGeometry.Scheme.{u}}
    (e : X' ⟶ X) [IsIso e] (N : X.Modules) [N.IsLineBundle]
    (hN : AlgebraicGeometry.IsAmple N) :
    AlgebraicGeometry.IsAmple ((AlgebraicGeometry.Scheme.Modules.pullback e).obj N) := by
  obtain ⟨hcpt, hcov⟩ := hN
  refine ⟨(AlgebraicGeometry.Scheme.homeoOfIso (asIso e)).symm.compactSpace, fun x => ?_⟩
  obtain ⟨m, hm, s, hxs, haff⟩ := hcov (e.base x)
  refine ⟨m, hm,
    (AlgebraicGeometry.Scheme.Modules.pullbackTensorPowIso e N m).hom.app ⊤
      (sectionPullbackAlong e s), ?_, ?_⟩
  · exact (AlgebraicGeometry.Scheme.Modules.mem_nonvanishingLocus_iso
      (AlgebraicGeometry.Scheme.Modules.pullbackTensorPowIso e N m) _ x).mpr
      ((AlgebraicGeometry.Scheme.Modules.mem_nonvanishingLocus_sectionPullbackAlong e
        (N.tensorPow m) s x).mpr hxs)
  · exact (congrArg AlgebraicGeometry.IsAffineOpen
      ((AlgebraicGeometry.Scheme.Modules.nonvanishingLocus_iso
        (AlgebraicGeometry.Scheme.Modules.pullbackTensorPowIso e N m) _).trans
        (AlgebraicGeometry.Scheme.Modules.nonvanishingLocus_sectionPullbackAlong e
          (N.tensorPow m) s))).mpr (haff.preimage_of_isIso e)

end
