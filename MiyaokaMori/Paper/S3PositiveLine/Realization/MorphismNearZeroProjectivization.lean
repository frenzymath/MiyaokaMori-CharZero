import MiyaokaMori.Paper.S3PositiveLine.Realization.MorphismNearZeroData
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.ThickeningSectionsTruncated
import MiyaokaMori.AlgebraicGeometry.Morphisms.MorphismNearZeroNonvanishingOpen
import MiyaokaMori.Paper.S3PositiveLine.Realization.MorphismNearZeroFactorization

/-! # The projectivization near the zero section

Statement: given a tuple of sections `P` satisfying the truncated jet coordinate condition, the zero-section
coordinate condition and the vanishing of the homogeneous equations, there are an open neighbourhood `U` of the
zero section and a morphism `Φ₀ : U → X` such that `Φ₀` composed with the embedding equals the projectivization of `P`.

Proof:
1. Take the union of the nonvanishing loci of the `P_ℓ`; this is an open subscheme `U` on which `P` is nowhere all zero.
2. On the zero section `P` is identified by `hzero` with `D.coord`; the homogeneous coordinates of `MMSetup` have no
   common zero, so the zero section is contained in `U`.
3. Build `U → P^N` with `projectivizationMorphism`; `hvanish` and `projectivizationMorphism_factors` make it factor
   through the closed immersion of `X`, giving `Φ₀`.
4. Projectivization commutes with pullback, so this `Φ₀` satisfies the definition of `IsTupleProjectivization`.
Used in the proof of Theorem 4.2 of the paper.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
noncomputable section

theorem morphism_near_zero_projectivization_core {k : Type u} [Field k]
    {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}
    {f : C.toScheme ⟶ X.toScheme} [D : MMSetup f] {rho : FiniteCover k C}
    {L : LineBundle rho.source.toVariety} {kappa : ℕ} (jet : BasedJet f rho L kappa)
    (P : Fin (X.embDim + 1) →
      (((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        (LineBundle.pullback (X := rho.source.toVariety) (Y := C.toVariety) rho.hom
          (LineBundle.pullback (X := C.toVariety) (Y := X.toVariety) f (X.OX 1))).toModules).val.obj
          (Opposite.op ⊤) : Type u))
    (hjet : ∀ ℓ, BasedJet.coneCoordinate jet ℓ =
      restrictToThickening L (LineBundle.pullback (X := rho.source.toVariety) (Y := C.toVariety) rho.hom
        (LineBundle.pullback (X := C.toVariety) (Y := X.toVariety) f (X.OX 1))) kappa (P ℓ))
    (hzero : ∀ ℓ, AlgebraicGeometry.Scheme.restrictToZeroSection L.toModules (P ℓ) =
      sectionPullbackAlong rho.hom
        ((((AlgebraicGeometry.Scheme.Modules.pullback f).map
          (CategoryTheory.eqToHom (X.OX_toModules 1).symm)).val.app (Opposite.op ⊤)).hom (D.coord ℓ)))
    (hvanish : ∀ j, evalHomogeneousAtSections _ (D.E.F j) (D.E.homogeneous j) P = 0) :
    ∃ (U : (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.Opens)
      (Phi0 : U.toScheme ⟶ X.toScheme),
      IsTupleProjectivization
        ((AlgebraicGeometry.Scheme.Modules.pullback
          (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
          (LineBundle.pullback (X := rho.source.toVariety) (Y := C.toVariety) rho.hom
            (LineBundle.pullback (X := C.toVariety) (Y := X.toVariety) f (X.OX 1))).toModules) P U Phi0
      ∧ Set.range (AlgebraicGeometry.Scheme.zeroSection L.toModules).base ⊆
        (U : Set (AlgebraicGeometry.Scheme.totalSpace L.toModules).left) := by
  obtain ⟨U, hU, hU0⟩ :=
    morphism_near_zero_nonvanishing_open_core jet P hjet hzero hvanish
  obtain ⟨Phi0, hPhi⟩ :=
    morphism_near_zero_projectivization_factorization_core P hvanish U hU
  exact ⟨U, Phi0, hPhi, hU0⟩

end
