import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.SeedBundlePullback
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.BasedJetConeCoordinate
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ConeMorphismScaleOfCoordinatesConverse

/-! # Restriction of cone coordinates along an equal-scale morphism

Cone coordinates of a based jet that is scalar over an open set: if `ι_W ≫ J.hom = scale u (ι_W ≫ p ≫ ρ ≫ s)`
on `W = p⁻¹U`, then every cone coordinate of `J` restricted to `W` is `u` times the pulled-back seed
coordinate. Converse of `BasedJet.restrict_eq_scale_of_coneCoordinate`.

Source: §3 of the paper (scalar jets and the coordinates `P_ℓ` of `ȷ`) and Lemma 4.1
(the jet "would be scalar on an open set").
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- **Coordinates of a scalar jet.** Let `W := p⁻¹U ⊆ C̃_(κ)(L)` with inclusion `ι_W`, and suppose
`ι_W ≫ J.hom = TwistedCone.scale f u (ι_W ≫ p ≫ ρ ≫ s)` for a unit `u ∈ Γ(W, O)ˣ`. Then for every `ℓ`
`ι_W^*(P_ℓ) = u • ι_W^*(p^* ρ^* f_ℓ)`, where `P_ℓ = J.coneCoordinate ℓ` and `ρ^* f_ℓ = seedCoordPullback f ρ (D.coord ℓ)`.

**Proof (bookkeeping, all ingredients in the library).** Write `m : Over.mk (p ≫ ρ) ⟶ Tot(A^{⊕(N+1)})` for the
`C`-morphism with `m.left = J.hom ≫ ι_Z` used in the definition of `BasedJet.coneCoordinate` (`ι_Z` the closed
immersion of the cone `twistedAffineCone.ι`).
1. By `twistedAffineCone.scale_comp_ι`, `ι_W ≫ J.hom ≫ ι_Z = scaleTot u (ι_W ≫ p ≫ ρ ≫ s)`, and by definition
   `scaleTot u g = (totalSpaceHomEquiv)⁻¹ (u • totalSpaceHomEquiv (homMk (g ≫ ι_Z)))` over `g ≫ Z.hom = ι_W ≫ p ≫ ρ`.
2. The `ℓ`-th coordinate of the left side is, by `totalSpaceHomEquiv_naturality_coordinate_of_eq` (precomposition
   with `ι_W` = pullback of sections along `ι_W`, up to `pullbackComp`/`pullbackCongr`), the transport of
   `ι_W^*(coordinate_ℓ m)`. The `ℓ`-th coordinate of the right side is `u • coordinate_ℓ (homMk (ι_W ≫ p ≫ ρ ≫ s ≫ ι_Z))`
   by `totalSpaceHomEquiv_symm_smul_coordinate`; and `s ≫ ι_Z = seedSection.totSection` whose `ℓ`-th coordinate is `f_ℓ`
   (`seedSection.totSection_coordinate`), so precomposing with `ι_W ≫ p ≫ ρ` (naturality again) gives `(ι_W ≫ p ≫ ρ)^* f_ℓ`.
3. Unfold `BasedJet.coneCoordinate` (it is `coordinate_ℓ m` transported by `(pullbackComp p ρ).inv` and the
   `OX_toModules` change of bundle) and `seedCoordPullback`, and cancel the transports with
   `sectionPullbackAlong_comp`, `sectionPullbackAlong_congr`, `sectionPullbackAlong_naturality`
   (`ConeMorphismScaleOfCoordinatesHelpers`; the same bookkeeping as `sectionPullbackAlong_coord_transport`, in reverse).
The general converse `twistedAffineCone.coordinate_of_comp_eq_scale` and the reverse transport
`sectionPullbackAlong_coord_transport_rev` live in `ConeMorphismScaleOfCoordinatesConverse`; this module only
instantiates them (`m := homMk (J.hom ≫ ι_Z)`, `φ := (pullback f).map (eqToHom (OX_toModules 1).symm)`). -/
theorem BasedJet.coneCoordinate_restrict_of_eq_scale {k : Type u} [Field k]
    {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}
    {f : C.toScheme ⟶ X.toScheme} [D : MMSetup f] {ρ : FiniteCover k C}
    {L : LineBundle ρ.source.toVariety} {κ : ℕ} (J : BasedJet f ρ L κ)
    (U : ρ.source.toScheme.Opens)
    (u : Γ(((jetNeighborhood.proj L κ) ⁻¹ᵁ U).toScheme, ⊤)ˣ)
    (h : ((jetNeighborhood.proj L κ) ⁻¹ᵁ U).ι ≫ J.hom
      = TwistedCone.scale f u
          (((jetNeighborhood.proj L κ) ⁻¹ᵁ U).ι ≫ jetNeighborhood.proj L κ ≫ ρ.hom
            ≫ (MMSetup.seed f).1))
    (ℓ : Fin (X.embDim + 1)) :
    (sectionPullbackAlong ((jetNeighborhood.proj L κ) ⁻¹ᵁ U).ι (BasedJet.coneCoordinate J ℓ) :
        (((AlgebraicGeometry.Scheme.Modules.pullback ((jetNeighborhood.proj L κ) ⁻¹ᵁ U).ι).obj
          ((AlgebraicGeometry.Scheme.Modules.pullback (jetNeighborhood.proj L κ)).obj
            (seedBundlePullback f ρ).toModules)).val.obj (Opposite.op ⊤) : Type u))
      = (show ((jetNeighborhood.proj L κ) ⁻¹ᵁ U).toScheme.ringCatSheaf.obj.obj (Opposite.op ⊤) from
          (u : Γ(((jetNeighborhood.proj L κ) ⁻¹ᵁ U).toScheme, ⊤))) •
        sectionPullbackAlong ((jetNeighborhood.proj L κ) ⁻¹ᵁ U).ι
          (sectionPullbackAlong (jetNeighborhood.proj L κ)
            (seedCoordPullback f ρ (D.coord ℓ))) := by
  have hvan := seedSection_equations_vanish X.embedding D.E f D.coord D.hcoord
  let m : CategoryTheory.Over.mk (jetNeighborhood.proj L κ ≫ ρ.hom) ⟶
      AlgebraicGeometry.Scheme.totalSpace
        (AlgebraicGeometry.Scheme.Modules.pow (seedLineBundle X.embedding f) (X.embDim + 1)) :=
    CategoryTheory.Over.homMk
      (J.hom ≫ twistedAffineCone.ι (seedLineBundle X.embedding f) X.embDim D.E.deg D.E.F D.E.homogeneous)
      ((CategoryTheory.Category.assoc _ _ _).trans J.over)
  have h' : ((jetNeighborhood.proj L κ) ⁻¹ᵁ U).ι ≫ J.hom
      = TwistedCone.scale f u
          (((jetNeighborhood.proj L κ) ⁻¹ᵁ U).ι ≫ (jetNeighborhood.proj L κ ≫ ρ.hom) ≫ (MMSetup.seed f).1) :=
    h.trans (congrArg (TwistedCone.scale f u)
      (congrArg (fun g => ((jetNeighborhood.proj L κ) ⁻¹ᵁ U).ι ≫ g)
        (CategoryTheory.Category.assoc (jetNeighborhood.proj L κ) ρ.hom (MMSetup.seed f).1).symm))
  have hraw := twistedAffineCone.coordinate_of_comp_eq_scale (seedLineBundle X.embedding f) X.embDim
    D.E.deg D.E.F D.E.homogeneous D.coord hvan (jetNeighborhood.proj L κ ≫ ρ.hom) J.hom m rfl
    ((jetNeighborhood.proj L κ) ⁻¹ᵁ U).ι u h' ℓ
  exact sectionPullbackAlong_coord_transport_rev ((jetNeighborhood.proj L κ) ⁻¹ᵁ U).ι (jetNeighborhood.proj L κ) ρ.hom
    ((AlgebraicGeometry.Scheme.Modules.pullback f).map (CategoryTheory.eqToHom (X.OX_toModules 1).symm))
    u _ (D.coord ℓ) hraw

end
