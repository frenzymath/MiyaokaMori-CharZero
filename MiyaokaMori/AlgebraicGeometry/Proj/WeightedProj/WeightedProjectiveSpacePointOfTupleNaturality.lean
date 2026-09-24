import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedProjectiveRationalPoints
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveTupleRestriction

/-! # Naturality of `weightedProjectiveSpace.pointOfTuple` in the field

For a `k`-algebra homomorphism `φ : K → K'` of fields, precomposing the `K`-point of `P(w)` given
by a nonzero tuple `v` with `Spec φ : Spec K' → Spec K` gives the `K'`-point of the tuple `φ ∘ v`:
`Spec.map φ ≫ pointOfTuple K v = pointOfTuple K' (φ ∘ v)`. Both sides are
`Proj.fromOfGlobalSections` of a ring map `k[x_σ] → Γ(Spec K', ⊤)`, and `fromOfGlobalSections` is
natural in the scheme (`fromOfGlobalSections_naturality`, proved by `openCover.hom_ext` on the
cover by the `D(f(t))`); the two ring maps agree on the generators `C r` (`φ` is `k`-linear) and
`X i` (`ΓSpecIso_inv_naturality`).

Used in the affine lift after finite base change (Lemma 3.1 of the paper): the base
change `K₁ → K₂` and the transport `e⁻¹ : K₂ → K(C̃)` of the generic tuple.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- `Proj.fromOfGlobalSections` depends only on the ring map (eliminates the dependent proof
argument). -/
theorem AlgebraicGeometry.Proj.fromOfGlobalSections_congr' {A : Type u} [CommRing A]
    {σ' : Type u} [SetLike σ' A] [AddSubgroupClass σ' A] (𝒜 : ℕ → σ') [GradedRing 𝒜]
    {T : AlgebraicGeometry.Scheme.{u}} {f f' : A →+* Γ(T, ⊤)} (h : f = f')
    (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤)
    (hf' : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f' = ⊤) :
    AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 f hf =
      AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 f' hf' := by
  subst h; rfl

/-- The image of a nonzero tuple under an injective map of fields is nonzero. -/
theorem weightedProjectiveSpace.map_tuple_ne_zero {σ : Type u} {K K' : Type u} [Field K]
    [Field K'] (φ : K →+* K') (v : {v : σ → K // v ≠ 0}) :
    (fun i => φ ((v : σ → K) i)) ≠ 0 := by
  intro h
  apply v.property
  funext i
  have := congrFun h i
  simpa using (map_eq_zero φ).mp this

/-- **Naturality of `pointOfTuple` along `k`-algebra maps of fields**: for `φ : K →+* K'` with
`φ ∘ algebraMap k K = algebraMap k K'`,
`Spec.map φ ≫ pointOfTuple k w hw K v = pointOfTuple k w hw K' (φ ∘ v)`. -/
theorem weightedProjectiveSpace.SpecMap_pointOfTuple (k : Type u) [Field k] {σ : Type u}
    (w : σ → ℕ) (hw : ∀ i, 0 < w i) {K K' : Type u} [Field K] [Field K'] [Algebra k K]
    [Algebra k K'] (φ : K →+* K') (hφ : ∀ r : k, φ (algebraMap k K r) = algebraMap k K' r)
    (v : {v : σ → K // v ≠ 0}) :
    AlgebraicGeometry.Spec.map (CommRingCat.ofHom φ) ≫
        weightedProjectiveSpace.pointOfTuple k w hw K v =
      weightedProjectiveSpace.pointOfTuple k w hw K'
        ⟨fun i => φ ((v : σ → K) i), weightedProjectiveSpace.map_tuple_ne_zero φ v⟩ := by
  let _ : GradedRing (MvPolynomial.weightedHomogeneousSubmodule k w) :=
    MvPolynomial.weightedGradedAlgebra (R := k) w
  unfold weightedProjectiveSpace.pointOfTuple
  refine (AlgebraicGeometry.Proj.ProjectiveTupleRestriction.fromOfGlobalSections_naturality
    (MvPolynomial.weightedHomogeneousSubmodule k w)
    (AlgebraicGeometry.Spec.map (CommRingCat.ofHom φ)) _ _).trans ?_
  refine AlgebraicGeometry.Proj.fromOfGlobalSections_congr' _ ?_ _ _
  have nat : ∀ x : K, (AlgebraicGeometry.Spec.map (CommRingCat.ofHom φ)).appTop.hom
      ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom x) =
      (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of K')).inv.hom (φ x) := fun x => by
    have h := AlgebraicGeometry.Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ)
    exact (congrArg (fun ψ => ψ.hom x) h).symm
  refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      MvPolynomial.aeval_C, nat, hφ]
  · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      MvPolynomial.aeval_X, nat]

end
