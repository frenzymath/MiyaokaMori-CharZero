import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.SerreTwistIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.VarietyChosenEmbedding

/-! # The line bundles `O_X(m)` of a projective embedding

`O_X(1)`: the pullback of the hyperplane bundle under the fixed projective embedding `X ↪ P^N`, and its
powers `O_X(m)`; this is the `A = f^*O_X(1)` of §1 of the paper and the `A_S` of Lemma 5.1.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- `O_X(m) = e^*O_{P^N}(m)` with `e = X.embedding`; the underlying module sheaf is `ProjectiveEmbedding.oX`
(the pullback of `MiyaokaMori.WeightedJets.ProjTwisting.sheaf`), packaged as a `LineBundle`. -/

noncomputable def SmoothProjectiveVariety.OX {k : Type u} [Field k]
    (X : SmoothProjectiveVariety k) (m : ℤ) : LineBundle X.toVariety :=
  { toModules := X.embedding.oX m
    rank := 1
    locallyFree := by
      haveI : (X.embedding.oX m).IsLineBundle := by
        unfold ProjectiveEmbedding.oX
        infer_instance
      exact SheafOfModules.IsLineBundle.isLocallyFree _
    isFiniteType := by
      haveI : (X.embedding.oX m).IsLineBundle := by
        unfold ProjectiveEmbedding.oX
        infer_instance
      exact SheafOfModules.IsLineBundle.isFiniteType _
    rank_eq_one := rfl
    rankAtStalk_eq := by
      intro x
      haveI : (X.embedding.oX m).IsLineBundle := by
        unfold ProjectiveEmbedding.oX
        infer_instance
      obtain ⟨U, hxU, hU⟩ :=
        SheafOfModules.IsLineBundle.locally_trivial (M := X.embedding.oX m) x
      obtain ⟨hU⟩ := hU
      let e0 : (AlgebraicGeometry.Scheme.Modules.pullback U.ι).obj (X.embedding.oX m) ≅
          SheafOfModules.unit U.toScheme.ringCatSheaf :=
        ((AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback U.ι).app
          (X.embedding.oX m)).symm ≪≫ hU
      let e : (AlgebraicGeometry.Scheme.Modules.pullback U.ι).obj (X.embedding.oX m) ≅
          SheafOfModules.free (R := U.toScheme.ringCatSheaf) (ULift (Fin 1)) :=
        e0 ≪≫ (AlgebraicGeometry.Divisors.LineGenericCoordinates.moduleFreeOneIsoUnit U.toScheme).symm
      simpa using AlgebraicGeometry.Scheme.Modules.rankAtStalk_of_restrict_iso_free
        (X.embedding.oX m) U (ULift (Fin 1)) e x hxU }

/-- The underlying module sheaf is the pullback of `O_{P^N}(m)` under the fixed embedding `X.embedding`. -/

theorem SmoothProjectiveVariety.OX_toModules {k : Type u} [Field k]
    (X : SmoothProjectiveVariety k) (m : ℤ) : (X.OX m).toModules = X.embedding.oX m :=
  rfl

end
