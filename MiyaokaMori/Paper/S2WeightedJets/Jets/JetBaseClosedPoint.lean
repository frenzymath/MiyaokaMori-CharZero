import MiyaokaMori.Paper.S2WeightedJets.Jets.JetBaseScheme

/-! # The closed point of the jet base

The closed immersion `Spec k ⟶ Spec k[t]/(t^{k+1})` given by `t ↦ 0`, used to take the constant term of a jet
(§2 of the paper: the constant term of a based jet is the seed section `s`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/- `t ↦ 0` is the ring homomorphism `GlobalTruncatedParameterAPI.epsilon r : k[t]/(t^{r+1}) →+* k`
   (the zero-section map); the morphism of schemes is its `Spec.map`. -/

noncomputable def jetBaseZero (k : Type u) [Field k] (r : ℕ) :
    AlgebraicGeometry.Spec (CommRingCat.of k) ⟶ jetBase k r :=
  AlgebraicGeometry.Spec.map (CommRingCat.ofHom (MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.epsilon (R := k) r))

instance jetBaseZero_isClosedImmersion (k : Type u) [Field k] (r : ℕ) :
    AlgebraicGeometry.IsClosedImmersion (jetBaseZero k r) := by
  unfold jetBaseZero
  apply AlgebraicGeometry.IsClosedImmersion.spec_of_surjective
  intro a
  refine ⟨MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.eta r a, ?_⟩
  exact DFunLike.congr_fun (MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.epsilon_eta r) a

end
