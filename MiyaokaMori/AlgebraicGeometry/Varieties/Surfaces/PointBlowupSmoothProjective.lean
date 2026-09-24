import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Blowup.ReesAlgebraSheaf
import MiyaokaMori.AlgebraicGeometry.Varieties.Surfaces.SurfaceVanishingIdealPointNeBot
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietyLocallyNoetherian
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.DimensionOpenCoverSup
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProjectiveMorphism
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProjectiveMorphismComp
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProjectiveOverIffProjectiveMorphism
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.VarietyDimension
import MiyaokaMori.AlgebraicGeometry.Morphisms.RegularImpliesSmoothOverPerfectField
import MiyaokaMori.AlgebraicGeometry.Varieties.Surfaces.PointBlowupDimTwo
import MiyaokaMori.AlgebraicGeometry.Blowup.PointBlowupRegular
import MiyaokaMori.AlgebraicGeometry.Varieties.Surfaces.SmoothProjectiveSurface
import MiyaokaMori.AlgebraicGeometry.Varieties.Surfaces.SurfaceClosedPointRegularDimTwo
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietyQcqs
import MiyaokaMori.RingTheory.RegularLocalRing.Stacks00np
import MiyaokaMori.RingTheory.RegularLocalRing.Stacks00nq
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.Stacks01mi
import MiyaokaMori.AlgebraicGeometry.Blowup.Stacks01og
import MiyaokaMori.AlgebraicGeometry.Blowup.Stacks02nd
import MiyaokaMori.AlgebraicGeometry.Blowup.Stacks02ns
import MiyaokaMori.AlgebraicGeometry.Blowup.Stacks0804
import MiyaokaMori.AlgebraicGeometry.Blowup.Stacks0805
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.Stacks01b9
import MiyaokaMori.AlgebraicGeometry.Morphisms.Stacks01wc
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.Stacks01pb
import MiyaokaMori.AlgebraicGeometry.Blowup.Stacks0agq
import MiyaokaMori.AlgebraicGeometry.Varieties.Smooth.Stacks056s

/-! # The blowup of a smooth projective surface at a closed point is a smooth projective surface

The blowup of a smooth projective surface at a closed point is again a (connected) smooth
projective surface over `k`: locally `Bl_0 A^2` is covered by two charts isomorphic to `A^2`,
hence smooth; the relative `Proj` of the Rees algebra is projective over `S` and `S` is
projective, so the composite is projective; connectedness and `dim = 2` follow from the
isomorphism over `S ∖ {p}` and the exceptional fibre `≅ P^1`. (The point blowups used in the
resolution stay in the category of smooth projective surfaces; compare Hartshorne V.3 and
Stacks 0C5H.)

The statement includes the compatibility of the isomorphism `e` with the structure morphisms,
`e.hom ≫ (π ≫ (S ↘ Spec k)) = S' ↘ Spec k`, so that the seven properties of `pointBlowup`
(integral, separated, finite type, smooth, projective, connected, `dim = 2`) follow from it via
the transport lemmas `MiyaokaMori.IsoOverBase.*`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-! ## `Bl_p S` and its structure morphism over `k` -/

/-- The underlying scheme `Bl_p S = (Scheme.blowup 𝓘_p).left` of the blowup at a closed point `p`
(Stacks 01OG). -/
noncomputable abbrev AlgebraicGeometry.Scheme.blowupClosedPoint {k : Type u} [Field k]
    (S : SmoothProjectiveSurface k) (p : S.toScheme) (hp : IsClosed ({p} : Set S.toScheme)) :
    AlgebraicGeometry.Scheme.{u} :=
  (AlgebraicGeometry.Scheme.blowup
    (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)).left

/-- The blowup morphism `π : Bl_p S ⟶ S`. -/
noncomputable abbrev AlgebraicGeometry.Scheme.blowupClosedPoint.π {k : Type u} [Field k]
    (S : SmoothProjectiveSurface k) (p : S.toScheme) (hp : IsClosed ({p} : Set S.toScheme)) :
    AlgebraicGeometry.Scheme.blowupClosedPoint S p hp ⟶ S.toScheme :=
  (AlgebraicGeometry.Scheme.blowup
    (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)).hom

/-- The structure morphism `π ≫ (S ↘ Spec k)` of `Bl_p S` over `k` (the same as
`pointBlowup.structureHom`). -/
noncomputable abbrev AlgebraicGeometry.Scheme.blowupClosedPoint.structureHom {k : Type u} [Field k]
    (S : SmoothProjectiveSurface k) (p : S.toScheme) (hp : IsClosed ({p} : Set S.toScheme)) :
    AlgebraicGeometry.Scheme.blowupClosedPoint S p hp ⟶
      AlgebraicGeometry.Spec (CommRingCat.of k) :=
  AlgebraicGeometry.Scheme.blowupClosedPoint.π S p hp ≫
    (S.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))

/-! ## Auxiliary lemmas -/

/-- `Bl_p S` is integral: `S` is integral and the vanishing ideal sheaf of a closed point is
nonzero (Stacks 02ND). -/
theorem AlgebraicGeometry.Scheme.blowupClosedPoint_isIntegral {k : Type u} [Field k]
    (S : SmoothProjectiveSurface k) (p : S.toScheme) (hp : IsClosed ({p} : Set S.toScheme)) :
    AlgebraicGeometry.IsIntegral (AlgebraicGeometry.Scheme.blowupClosedPoint S p hp) := by
  haveI : AlgebraicGeometry.IsIntegral S.toScheme := by infer_instance
  exact AlgebraicGeometry.Scheme.blowup_isIntegral _ (S.vanishingIdeal_closedPoint_ne_bot p hp)

/-! ## Main statement -/

/-- The blowup of a smooth projective surface at a closed point is a smooth projective surface,
**with an isomorphism compatible with the structure morphisms over `k`**.

The compatibility (the equation in the conclusion) is needed: the seven properties of
`pointBlowup` (integral, separated, finite type, smooth, projective, connected, `dim = 2`) are
statements about the specific morphism `π ≫ (S ↘ Spec k)`, and none of them follows from a bare
isomorphism of schemes. -/
theorem AlgebraicGeometry.Scheme.blowup_closedPoint_smoothProjectiveSurface {k : Type u} [Field k]
    [PerfectField k] (S : SmoothProjectiveSurface k) (p : S.toScheme)
    (hp : IsClosed ({p} : Set S.toScheme)) :
    ∃ (S' : SmoothProjectiveSurface k)
      (e : S'.toScheme ≅ AlgebraicGeometry.Scheme.blowupClosedPoint S p hp),
      e.hom ≫ AlgebraicGeometry.Scheme.blowupClosedPoint.structureHom S p hp =
        S'.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k) := by
  haveI : AlgebraicGeometry.IsNoetherian S.toScheme :=
    { toIsLocallyNoetherian := inferInstance, toCompactSpace := inferInstance }
  haveI : AlgebraicGeometry.IsIntegral (AlgebraicGeometry.Scheme.blowupClosedPoint S p hp) :=
    AlgebraicGeometry.Scheme.blowupClosedPoint_isIntegral S p hp
  haveI : AlgebraicGeometry.IsProjectiveMorphism
      (AlgebraicGeometry.Scheme.blowupClosedPoint.π S p hp) :=
    AlgebraicGeometry.Scheme.blowup_isProjectiveMorphism _
  haveI : AlgebraicGeometry.IsProjectiveMorphism
      (S.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    (isProjectiveOver_iff_isProjectiveMorphism k S.toScheme).mp
      S.toSmoothProjectiveVariety.projective
  haveI hpm : AlgebraicGeometry.IsProjectiveMorphism
      (AlgebraicGeometry.Scheme.blowupClosedPoint.structureHom S p hp) :=
    _root_.IsProjectiveMorphism.comp _ _
  haveI : AlgebraicGeometry.IsProper
      (AlgebraicGeometry.Scheme.blowupClosedPoint.structureHom S p hp) :=
    AlgebraicGeometry.IsProjectiveMorphism.isProper _
  letI : (AlgebraicGeometry.Scheme.blowupClosedPoint S p hp).Over
      (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨AlgebraicGeometry.Scheme.blowupClosedPoint.structureHom S p hp⟩
  have hsep0 : AlgebraicGeometry.IsSeparated
      (AlgebraicGeometry.Scheme.blowupClosedPoint.structureHom S p hp) := inferInstance
  have hft0 : AlgebraicGeometry.IsOfFiniteType
      (AlgebraicGeometry.Scheme.blowupClosedPoint.structureHom S p hp) := {}
  haveI hsep : AlgebraicGeometry.IsSeparated
      (AlgebraicGeometry.Scheme.blowupClosedPoint S p hp ↘
        AlgebraicGeometry.Spec (CommRingCat.of k)) := hsep0
  haveI hft : AlgebraicGeometry.IsOfFiniteType
      (AlgebraicGeometry.Scheme.blowupClosedPoint S p hp ↘
        AlgebraicGeometry.Spec (CommRingCat.of k)) := hft0
  have hsmooth : IsSmoothOver k (AlgebraicGeometry.Scheme.blowupClosedPoint S p hp) :=
    (isSmoothOver_iff_regular _).mpr
      (AlgebraicGeometry.Scheme.blowupClosedPoint_isRegular S p hp)
  have hproj : IsProjectiveOver k (AlgebraicGeometry.Scheme.blowupClosedPoint S p hp) :=
    (isProjectiveOver_iff_isProjectiveMorphism k _).mpr hpm
  have hconn : ConnectedSpace (AlgebraicGeometry.Scheme.blowupClosedPoint S p hp).carrier :=
    inferInstance
  have hdim : ((topologicalKrullDim
      (AlgebraicGeometry.Scheme.blowupClosedPoint S p hp).carrier).unbotD 0).toNat = 2 := by
    rw [AlgebraicGeometry.Scheme.blowupClosedPoint_topologicalKrullDim S p hp]
    rfl
  exact ⟨⟨⟨{ carrier := AlgebraicGeometry.Scheme.blowupClosedPoint S p hp },
    hsmooth, hproj, hconn⟩, hdim⟩, Iso.refl _, Category.id_comp _⟩

end
