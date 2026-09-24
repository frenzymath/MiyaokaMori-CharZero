import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.BasedJetConeCoordinate
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.ConeCoordinateFiniteXiExpansionZeroSection
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.ConeCoordinateFiniteXiExpansionSeedCoordinateTransport

/-! # The cone coordinates of a based jet restrict to the seed coordinates on the zero section

The restriction along the zero section `σ₀ : C̃ → C̃_(κ)(L)` (`jetNeighborhood.restrictToZeroSection`) of the `ℓ`-th
cone coordinate of a based jet `ȷ` equals the pullback `ρ^*f_ℓ` along `ρ` of the seed coordinate `f_ℓ = D.coord ℓ`
(transported through `OX_toModules`). This is the coordinate form of `BasedJet.restrict` (`ȷ|_{C̃} = s ∘ ρ`), and
the origin of the constant term `ρ^*f_ℓ` of equation (4.1) of the paper.

All variable-level bookkeeping is in `ConeCoordinateFiniteXiExpansionSeedCoordinateTransport.lean`
(`restrictTransport_coneCoordinate_aux`); this file only instantiates it with the concrete objects.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- **The restriction of a cone coordinate to the zero section is the pullback of the seed coordinate**:
`restrictToZeroSection (coneCoordinate J ℓ) = ρ^*(f_ℓ)` (`f_ℓ = D.coord ℓ` transported by
`eqToHom (OX_toModules 1).symm`).

Source: §3 of the paper (definition of a based jet, `ȷ|_{C̃} = s ∘ ρ`) and Lemma 4.1
("Since `ȷ` restricts to `s ∘ ρ` on the zero section …").

## Proof
Write `A_s := seedLineBundle X.embedding f`, `V := Modules.pow A_s (N+1)`, `p := jetNeighborhood.proj L κ`,
`σ₀ := jetNeighborhood.zeroSection L κ` (`σ₀ ≫ p = 𝟙`, `zeroSection_proj`), `coneι : 𝒵.left ⟶ Tot(V).left`,
`σ_f := seedSection.totSection A_s N D.coord`,
`φ := (pullback ρ.hom).map ((pullback f).map (eqToHom (OX_toModules 1).symm))`.
After unfolding `restrictToZeroSection` and `coneCoordinate`, both sides are instances of the variable-level lemma
`restrictTransport_coneCoordinate_aux` (`…SeedCoordinateTransport.lean`), with inputs
`J.restrict : σ₀ ≫ J.hom = ρ.hom ≫ seed.1`, `seed.1 ≫ coneι = σ_f.1` (`IsClosedImmersion.lift_fac`) and `J.over`;
on the right-hand side `sectionPullbackAlong_naturality` first moves `φ` outside
`sectionPullbackAlong ρ.hom (D.coord ℓ)`.
Proof of that lemma: (1) naturality in `M` of the transport isomorphism chain; (2) the pseudofunctor
compatibilities of `pullbackComp` (Mathlib `pseudofunctor_associativity`, `pseudofunctor_right_unitality`)
replace `(pullbackComp σ₀ p) ∘ σ₀^*(pullbackComp p ρ)⁻¹` by `pullbackCongr ∘ pullbackComp σ₀ (p ≫ ρ)`;
(3) `totalSpaceHomEquiv_naturality_coordinate_of_eq` along `σ₀`;
(4) `σ₀ ≫ J.hom ≫ coneι = ρ.hom ≫ σ_f.1` (`Over.OverMorphism.ext`); (5) the same naturality along `ρ.hom`
(`T' = (C, 𝟙)`); (6) the `ℓ`-th coordinate of `σ_f` is `(pullbackId C).inv (D.coord ℓ)`
(`seedSection.totSection_coordinate`); (7) `sectionPullbackAlong_id/comp/congr`.
Edge cases: for `κ = 0`, `σ₀` is an isomorphism and the statement still makes sense; for `N = 0` there is a single
coordinate. -/
theorem BasedJet.restrictToZeroSection_coneCoordinate {k : Type u} [Field k]
    {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}
    {f : C.toScheme ⟶ X.toScheme} [D : MMSetup f] {ρ : FiniteCover k C}
    {L : LineBundle ρ.source.toVariety} {κ : ℕ} (J : BasedJet f ρ L κ)
    (ℓ : Fin (X.embDim + 1)) :
    jetNeighborhood.restrictToZeroSection L
        (LineBundle.pullback (X := ρ.source.toVariety) (Y := C.toVariety) ρ.hom
          (LineBundle.pullback (X := C.toVariety) (Y := X.toVariety) f (X.OX 1))) κ
        (BasedJet.coneCoordinate J ℓ)
      = sectionPullbackAlong ρ.hom
          ((((AlgebraicGeometry.Scheme.Modules.pullback f).map
            (CategoryTheory.eqToHom (X.OX_toModules 1).symm)).val.app (Opposite.op ⊤)).hom
              (D.coord ℓ)) := by
  have hn := sectionPullbackAlong_naturality ρ.hom
    ((AlgebraicGeometry.Scheme.Modules.pullback f).map (CategoryTheory.eqToHom (X.OX_toModules 1).symm)) (D.coord ℓ)
  refine Eq.trans ?_ hn.symm
  have hs : (MMSetup.seed f).1 ≫
      ((⨆ j, AlgebraicGeometry.Scheme.idealSheafOfSection _
        (homogeneousEquationSection (seedLineBundle X.embedding f) X.embDim (D.E.F j) (D.E.homogeneous j))).subschemeι :
        (MMSetup.cone f).left ⟶ (AlgebraicGeometry.Scheme.totalSpace
          (AlgebraicGeometry.Scheme.Modules.pow (seedLineBundle X.embedding f) (X.embDim + 1))).left)
      = (seedSection.totSection (seedLineBundle X.embedding f) X.embDim D.coord).1 :=
    AlgebraicGeometry.IsClosedImmersion.lift_fac
      ((⨆ j, AlgebraicGeometry.Scheme.idealSheafOfSection _
        (homogeneousEquationSection (seedLineBundle X.embedding f) X.embDim (D.E.F j) (D.E.homogeneous j))).subschemeι)
      (seedSection.totSection (seedLineBundle X.embedding f) X.embDim D.coord).1 _
  exact restrictTransport_coneCoordinate_aux (jetNeighborhood.zeroSection L κ) (jetNeighborhood.proj L κ)
    (jetNeighborhood.zeroSection_proj L κ) ρ.hom (seedLineBundle X.embedding f) X.embDim D.coord _
    (MMSetup.seed f).1 hs J.hom _ J.restrict
    ((AlgebraicGeometry.Scheme.Modules.pullback ρ.hom).map
      ((AlgebraicGeometry.Scheme.Modules.pullback f).map (CategoryTheory.eqToHom (X.OX_toModules 1).symm))) ℓ

end
