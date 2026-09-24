import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.SeedBundlePullback
import MiyaokaMori.Paper.S3PositiveLine.Realization.MorphismNearZeroSectionCompat

/-! # The projectivization on the zero section

Statement: `P` is a tuple of sections of `A_ρ = ρ^*f^*O_X(1)` on `Tot(L)` restricting along the zero section to
the seed coordinates `ρ^*f_ℓ` (`hzero`), `Φ₀ : U → X` is the projectivization of `P` (`IsTupleProjectivization`),
and `z : C̃ → U` is the lift of the zero section to `U` (`z ≫ U.ι = 0_L`). Then `z ≫ Φ₀ = ρ ≫ f`, i.e. `Φ₀`
equals `f∘ρ` on the zero section (Theorem 4.2 of the paper: "restricts there to `f∘ρ`").

Proof: the same fact is `morphism_near_zero_zeroSection_compat` in `MorphismNearZeroSectionCompat` (there `A_ρ`
is written as two layers of `LineBundle.pullback` and `hzero` as
`sectionPullbackAlong ρ.hom (f^*(eqToHom …) (D.coord ℓ))`). `seedBundlePullback f ρ` is by definition
`LineBundle.pullback ρ.hom (LineBundle.pullback f (X.OX 1))`, so `P` and `hΦ` can be used directly, and
`seedCoordPullback` differs from the right-hand side of that `hzero` only by `sectionPullbackAlong_naturality`
(pull back first and then apply `ρ^*f^*eqToHom`, or apply `f^*eqToHom` first and then pull back). So this theorem
is a reformulation of that one.

The route of that theorem: cancel the monomorphism `emb := X.embedding.emb`; `projectivizationMorphism_pullback`
twice; the canonical isomorphism `θ : z^*U.ι^*M ≅ ρ^*A` (`pullbackComp`/`pullbackCongr`/`pullbackId`/`eqToHom`)
sends `z^*U.ι^*P` to `ρ^*D.coord` (which is exactly the content of `hzero` after unfolding
`restrictToZeroSection`); then `projectivizationMorphism_congr_iso`.

The component `sigma0 ≫ Phi0 = rho.hom ≫ f` of `RealizesJet` is the same fact in another signature.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- `Φ₀` composed with the lift `z` of the zero section equals `ρ ≫ f`. A reformulation of
`morphism_near_zero_zeroSection_compat`: `seedBundlePullback` unfolds by definition, and `seedCoordPullback`
corresponds via `sectionPullbackAlong_naturality`. -/
theorem zeroSectionLift_comp_eq_of_isTupleProjectivization {k : Type u} [Field k]
    {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}
    {f : C.toScheme ⟶ X.toScheme} [D : MMSetup f] {ρ : FiniteCover k C}
    {L : LineBundle ρ.source.toVariety}
    (P : Fin (X.embDim + 1) →
      (((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        (seedBundlePullback f ρ).toModules).val.obj
          (Opposite.op ⊤) : Type u))
    (hzero : ∀ ℓ, AlgebraicGeometry.Scheme.restrictToZeroSection L.toModules (P ℓ)
      = seedCoordPullback f ρ (D.coord ℓ))
    (U : (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.Opens)
    (Φ₀ : U.toScheme ⟶ X.toScheme) (hΦ : IsTupleProjectivization _ P U Φ₀)
    (z : ρ.source.toScheme ⟶ U.toScheme)
    (hz : z ≫ U.ι = AlgebraicGeometry.Scheme.zeroSection L.toModules) :
    z ≫ Φ₀ = ρ.hom ≫ f := by
  refine morphism_near_zero_zeroSection_compat (rho := ρ) (L := L) P ?_ U Φ₀ hΦ z hz
  intro ℓ
  have h1 : seedCoordPullback f ρ (D.coord ℓ) =
      sectionPullbackAlong ρ.hom
        ((((AlgebraicGeometry.Scheme.Modules.pullback f).map
          (CategoryTheory.eqToHom (X.OX_toModules 1).symm)).val.app (Opposite.op ⊤)).hom
          (D.coord ℓ)) :=
    (sectionPullbackAlong_naturality ρ.hom
      ((AlgebraicGeometry.Scheme.Modules.pullback f).map
        (CategoryTheory.eqToHom (X.OX_toModules 1).symm)) (D.coord ℓ)).symm
  exact (hzero ℓ).trans h1

end
