import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Morphisms.QuasiProjectiveMorphism
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProjectiveMorphism
import MiyaokaMori.AlgebraicGeometry.Modules.Ample.Stacks0892
import MiyaokaMori.AlgebraicGeometry.Modules.Stacks0892_QuasiAffineUnitAmple
import MiyaokaMori.AlgebraicGeometry.Morphisms.Stacks07rm

/-! # Projective completion of an affine scheme of finite type over a Noetherian base

Step 1 of Chow's lemma over a Noetherian affine base (`ChowLemmaNoetherianAffineBase.lean`; Stacks 0200 proof,
Stacks 01P9 + 07RM): an affine scheme `W` locally of finite type over a locally Noetherian scheme `S` is
quasi-projective over `S` (`isQuasiProjectiveMorphism_of_isAffine_of_isLocallyNoetherian`), hence, by
Stacks 07RM (`IsQuasiProjectiveMorphism.exists_isOpenImmersion_isProjectiveMorphism`, `Stacks07rm.lean`),
admits an open immersion over `S` into a projective `S`-scheme
(`exists_isOpenImmersion_isProjectiveMorphism_of_isAffine_of_isLocallyNoetherian`). The first is
`isQuasiProjectiveMorphism_of_isAffine` of `Stacks0200_Pieces.lean` with `Spec k` replaced by `S`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- An affine scheme locally of finite type over a locally Noetherian scheme `S` is quasi-projective over `S`
(Stacks 01VU/01P9: `W` is Noetherian, so every open of `W` is quasi-affine and the structure sheaf `O_W` is
ample, and stays ample after pulling back to the preimage of any affine open of `S`). This is
`isQuasiProjectiveMorphism_of_isAffine` (`Stacks0200_Pieces.lean`) with `Spec k` replaced by `S`; the proof
uses nothing about the field. -/
theorem AlgebraicGeometry.isQuasiProjectiveMorphism_of_isAffine_of_isLocallyNoetherian
    {W S : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsAffine W]
    [AlgebraicGeometry.IsLocallyNoetherian S] (w : W ⟶ S) [AlgebraicGeometry.LocallyOfFiniteType w] :
    AlgebraicGeometry.IsQuasiProjectiveMorphism w := by
  have : AlgebraicGeometry.IsLocallyNoetherian W :=
    AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian w
  refine ⟨inferInstance, inferInstance,
    ⟨SheafOfModules.unit W.ringCatSheaf, inferInstance, fun V => ?_⟩⟩
  refine AlgebraicGeometry.IsAmple.pullback_of_isQuasiAffine (w ⁻¹ᵁ V.1).ι ?_ _
    (AlgebraicGeometry.IsAmple.unit_of_isQuasiAffine W)
  intro V'
  have hc : CompactSpace ((w ⁻¹ᵁ V.1).ι ⁻¹ᵁ V'.1) :=
    isCompact_iff_compactSpace.mp ((w ⁻¹ᵁ V.1).ι.isCompact_preimage V'.2.isCompact)
  exact AlgebraicGeometry.Scheme.IsQuasiAffine.of_isImmersion
    (f := ((w ⁻¹ᵁ V.1).ι ⁻¹ᵁ V'.1).ι ≫ (w ⁻¹ᵁ V.1).ι)

/-- Projective completion (Stacks 01P9 + 07RM): an affine scheme `W` locally of finite type over a locally
Noetherian, quasi-compact, quasi-separated scheme `S` admits an open immersion `e : W ⟶ Z` over `S` into a
scheme `Z` projective over `S`. Proof: `w` is quasi-projective
(`isQuasiProjectiveMorphism_of_isAffine_of_isLocallyNoetherian`) and Stacks 07RM
(`IsQuasiProjectiveMorphism.exists_isOpenImmersion_isProjectiveMorphism`) gives `Z`, `e`, `f` with `e ≫ f = w`.
Edge cases: `W = ∅` (then `e` is the open immersion from the empty scheme) and `S = ∅` are covered by the same
proof; nothing requires `W ≠ ∅` or `S` connected. -/
theorem AlgebraicGeometry.exists_isOpenImmersion_isProjectiveMorphism_of_isAffine_of_isLocallyNoetherian
    {W S : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsAffine W]
    [AlgebraicGeometry.IsLocallyNoetherian S] [CompactSpace S] [QuasiSeparatedSpace S]
    (w : W ⟶ S) [AlgebraicGeometry.LocallyOfFiniteType w] :
    ∃ (Z : AlgebraicGeometry.Scheme.{u}) (e : W ⟶ Z) (f : Z ⟶ S),
      AlgebraicGeometry.IsOpenImmersion e ∧ AlgebraicGeometry.IsProjectiveMorphism f ∧ e ≫ f = w := by
  have := AlgebraicGeometry.isQuasiProjectiveMorphism_of_isAffine_of_isLocallyNoetherian w
  exact AlgebraicGeometry.IsQuasiProjectiveMorphism.exists_isOpenImmersion_isProjectiveMorphism w

end
