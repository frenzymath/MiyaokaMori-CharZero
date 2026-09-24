import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.FirstChernCapPointGeneric

/-! # Transport along isomorphisms of point closures

(θ) For a closed immersion `j` of an integral scheme `Z` into `X` with `j(η_Z) = x`, there is an
    isomorphism `e : Z ≅ X.pointClosure x` with `e ≫ ι_x = j` (the reduced closed subscheme
    structure on an irreducible closed subset is unique, Stacks 01J3); special case: for
    `W = X.pointClosure w` and `v ∈ W`, `W.pointClosure v ≅ X.pointClosure (ι_w v)` with
    `θ ≫ ι_{ι_w v} = ι_v ≫ ι_w`.
(P) Transport of principal cycles along an isomorphism `θ : W₁ → W₂`: `θ_* div(f) = div(f′)`.
(R) Transport of divisors of rational sections along `θ`: `θ_* div_{θ^*N}(s) = div_N(s′)`, `s′ ≠ 0`.

Proof sketch:
1. (θ): `Z` reduced makes `ker j` a radical ideal sheaf
   (`RingHom.ker_isRadical_iff_reduced_of_surjective`), so `ker j = vanishingIdeal (supp ker j)`
   (`vanishingIdeal_support`); `supp ker j = closure (range j) = range j = closure {j η_Z}` (closed
   maps commute with closure); `ker ι_x = vanishingIdeal (closure {x})` (`ker_subschemeι`). Equal
   kernels give the isomorphism (`IsClosedImmersion.isIso_lift`).
2. (P): `f′ := functionFieldMap (inv θ) f`; pointwise, use `ord_functionFieldMap` and
   `properPushforward_closedImmersion_apply`.
3. (R): as for the pushforward along `ι_η`, with `ι_η` replaced by an arbitrary isomorphism `θ`.

Source: Stacks 01J3 (uniqueness of the reduced induced structure).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u
open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
namespace MiyaokaMori.PointClosureTransport
open AlgebraicGeometry.Scheme.Modules MiyaokaMori.RationalSectionOrdRestrict MiyaokaMori.FirstChernCapPointGeneric
  MiyaokaMori.OrdOpenImmersion

/-- The kernel of a closed immersion with reduced source is a radical ideal sheaf. -/
theorem ker_eq_radical_of_isReduced {Y X : Scheme.{u}} (f : Y ⟶ X) [IsClosedImmersion f]
    [IsReduced Y] : f.ker = f.ker.radical := by
  ext U x
  have hr : (f.ker.ideal U).IsRadical := by
    rw [Scheme.Hom.ker_apply]
    exact (RingHom.ker_isRadical_iff_reduced_of_surjective
      (Scheme.Hom.app_surjective f U U.2)).mpr inferInstance
  rw [Scheme.IdealSheafData.radical_ideal, Ideal.radical_eq_iff.mpr hr]

/-- The image of a closed immersion `j` of an integral scheme `Z` into `X` is `closure {j η_Z}`. -/
theorem range_eq_closure_of_isClosedImmersion {Z X : Scheme.{u}} [IsIntegral Z] (j : Z ⟶ X)
    [IsClosedImmersion j] : Set.range j.base = closure {j.base (genericPoint Z)} := by
  have h1 : closure ({genericPoint Z} : Set Z) = Set.univ := (genericPoint_spec Z).def ▸ rfl
  rw [← Set.image_univ, ← h1, ← Set.image_singleton]
  exact (j.isClosedEmbedding.isClosedMap.closure_image_eq_of_continuous
    j.continuous _).symm

/-- A closed immersion `j` of an integral scheme `Z` into `X` is canonically isomorphic to the point
closure of the image of its generic point (the reduced induced structure on an irreducible closed
subset is unique, Stacks 01J3). -/
theorem exists_iso_pointClosure_of_isClosedImmersion {Z X : Scheme.{u}} [IsIntegral Z]
    (j : Z ⟶ X) [IsClosedImmersion j] (x : X) (hx : j.base (genericPoint Z) = x) :
    ∃ e : Z ≅ X.pointClosure x, e.hom ≫ X.pointClosureι x = j := by
  subst hx
  set x := j.base (genericPoint Z) with hx
  have hker : (X.pointClosureι x).ker = j.ker := by
    have h1 : (X.pointClosureι x).ker =
        Scheme.IdealSheafData.vanishingIdeal ⟨closure {x}, isClosed_closure⟩ := by
      unfold Scheme.pointClosureι
      exact Scheme.IdealSheafData.ker_subschemeι _
    have h2 : j.ker.support = ⟨closure {x}, isClosed_closure⟩ := by
      apply TopologicalSpace.Closeds.ext
      rw [j.support_ker, range_eq_closure_of_isClosedImmersion j, closure_closure]
      rfl
    rw [h1, ker_eq_radical_of_isReduced j, ← Scheme.IdealSheafData.vanishingIdeal_support, h2]
  have := IsClosedImmersion.isIso_lift (X.pointClosureι x) j hker
  exact ⟨asIso (IsClosedImmersion.lift (X.pointClosureι x) j hker.le),
    IsClosedImmersion.lift_fac _ _ _⟩

/-- Point closure of a point closure: for `W = X.pointClosure w` and `v ∈ W`,
`W.pointClosure v ≅ X.pointClosure (ι_w v)`, compatibly with the closed immersions into `X`. -/
theorem exists_iso_pointClosure_pointClosure {X : Scheme.{u}} (w : X) (v : X.pointClosure w) :
    ∃ θ : (X.pointClosure w).pointClosure v ≅ X.pointClosure ((X.pointClosureι w).base v),
      θ.hom ≫ X.pointClosureι ((X.pointClosureι w).base v) =
        (X.pointClosure w).pointClosureι v ≫ X.pointClosureι w := by
  refine exists_iso_pointClosure_of_isClosedImmersion
    ((X.pointClosure w).pointClosureι v ≫ X.pointClosureι w) _ ?_
  show (X.pointClosureι w).base (((X.pointClosure w).pointClosureι v).base _) = _
  rw [Scheme.pointClosureι_genericPoint]

/-- Transport of principal cycles along an isomorphism: `θ_* div(f) = div(f′)`. -/
theorem exists_principalCycle_eq_properPushforward_iso {W₁ W₂ : Scheme.{u}} [IsIntegral W₁]
    [IsIntegral W₂] [IsLocallyNoetherian W₁] [IsLocallyNoetherian W₂] (θ : W₁ ⟶ W₂) [IsIso θ]
    (f : W₁.functionFieldˣ) :
    ∃ f' : W₂.functionFieldˣ,
      AlgebraicGeometry.AlgebraicCycle.properPushforward θ (W₁.principalCycle f) = W₂.principalCycle f' := by
  refine ⟨Units.map (functionFieldMap (inv θ)).toMonoidHom f, ?_⟩
  ext z
  obtain ⟨z', rfl⟩ : ∃ z', θ.base z' = z := ⟨(inv θ).base z, by
    rw [← Scheme.Hom.comp_apply]; simp⟩
  refine (properPushforward_closedImmersion_apply θ _ z').trans ?_
  rw [Scheme.principalCycle_apply, Scheme.principalCycle_apply]
  show W₁.ord _ z' = W₂.ord (functionFieldMap (inv θ) (f : W₁.functionField)) (θ.base z')
  rw [ord_functionFieldMap (inv θ)]
  congr 1
  rw [← Scheme.Hom.comp_apply]; simp

/-- Transport of the divisor of a rational section along an isomorphism:
`θ_* div_{θ^*N}(s) = div_N(s′)`. -/
theorem exists_rationalSectionDivisor_eq_properPushforward_iso {W₁ W₂ : Scheme.{u}}
    [IsIntegral W₁] [IsIntegral W₂] [IsLocallyNoetherian W₁] [IsLocallyNoetherian W₂]
    (θ : W₁ ⟶ W₂) [IsIso θ] (N : W₂.Modules) [N.IsLineBundle]
    (s : ((Scheme.Modules.pullback θ).obj N).stalk (genericPoint W₁)) (hs : s ≠ 0) :
    ∃ s' : N.stalk (genericPoint W₂), s' ≠ 0 ∧
      AlgebraicGeometry.AlgebraicCycle.properPushforward θ
        (((Scheme.Modules.pullback θ).obj N).rationalSectionDivisor s)
        = N.rationalSectionDivisor s' := by
  let Lw := (Scheme.Modules.pullback θ).obj N
  let e : Lw ≅ N.restrict θ := ((Scheme.Modules.restrictFunctorIsoPullback θ).app N).symm
  have hs₁ := moduleStalkMap_iso_ne_zero e _ s hs
  refine ⟨genericStalkMap θ N (moduleStalkMap _ _ e.hom s), ?_, ?_⟩
  · intro h0
    exact hs₁ (genericStalkMap_injective θ N (h0.trans (genericStalkMap_zero θ N).symm))
  · ext z
    obtain ⟨z', rfl⟩ : ∃ z', θ.base z' = z := ⟨(inv θ).base z, by
      rw [← Scheme.Hom.comp_apply]; simp⟩
    refine (properPushforward_closedImmersion_apply θ _ z').trans ?_
    show Lw.rationalSectionOrd s z' = N.rationalSectionOrd _ (θ z')
    rw [rationalSectionOrd_iso e s hs z']
    exact rationalSectionOrd_restrict θ N _ hs₁ z'

end MiyaokaMori.PointClosureTransport
end
