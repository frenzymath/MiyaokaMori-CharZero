import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Surfaces.PointBlowupSmoothProjective
import MiyaokaMori.AlgebraicGeometry.Morphisms.SmoothProjectiveSurfaceIsoTransfer
import MiyaokaMori.AlgebraicGeometry.Blowup.Stacks0805
import MiyaokaMori.AlgebraicGeometry.Blowup.Stacks0806IsBlowup
import MiyaokaMori.AlgebraicGeometry.Morphisms.BlowupIsoAwayFromCentre
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.VanishingIdealSingletonEqPointIdeal
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.ProjectiveLineIsSmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Surfaces.SurfaceClosedPointRegularDimTwo
import MiyaokaMori.AlgebraicGeometry.Blowup.Stacks0agq

/-! # Blowup of a smooth surface at a closed point

The blowup of a smooth projective surface at a closed point, as a smooth projective surface, and
its exceptional divisor.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/- The blowup at a closed point `p`; defined only for closed points (there is no point blowup at a
   non-closed point, and no default value is set). The underlying scheme is
   `Bl_p S = (Scheme.blowup (vanishingIdeal {p})).left` of Stacks 01OG, with structure morphism the
   blowup morphism followed by `S → Spec k`; integral, separated, finite type, smooth, projective,
   connected and two-dimensional are proof obligations (Stacks 0AGQ, 0AHH, 02NS), each a named
   theorem below, and the definition is assembled in three layers:
   `pointBlowup.variety` → `pointBlowup.smoothProjectiveVariety` → `pointBlowup`. -/

/-- The structure morphism `π ≫ (S ↘ Spec k)` of the blowup of `S` at the closed point `p`. -/
noncomputable abbrev pointBlowup.structureHom {k : Type u} [Field k] [PerfectField k] (S : SmoothProjectiveSurface k)
    (p : S.toScheme) (hp : IsClosed ({p} : Set S.toScheme)) :
    (AlgebraicGeometry.Scheme.blowup
      (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)).left ⟶
      AlgebraicGeometry.Spec (CommRingCat.of k) :=
  (AlgebraicGeometry.Scheme.blowup
      (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)).hom ≫
    (S.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))

/-- Integrality: the blowup of an integral scheme along a nonzero ideal sheaf is integral (Stacks
02ND: `Bl` is the `Proj` of the Rees algebra, and the Rees algebra of a domain is a domain). -/
theorem pointBlowup.isIntegral {k : Type u} [Field k] [PerfectField k] (S : SmoothProjectiveSurface k)
    (p : S.toScheme) (hp : IsClosed ({p} : Set S.toScheme)) :
    AlgebraicGeometry.IsIntegral
      (AlgebraicGeometry.Scheme.blowup
      (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)).left := by
  haveI : AlgebraicGeometry.IsIntegral S.toScheme := by infer_instance
  exact AlgebraicGeometry.Scheme.blowup_isIntegral _ (S.vanishingIdeal_closedPoint_ne_bot p hp)

/-- Separatedness, transported along the isomorphism over `k` of
`blowup_closedPoint_smoothProjectiveSurface` (`MiyaokaMori.IsoOverBase.isSeparated_of_isoOver`). -/
theorem pointBlowup.isSeparated {k : Type u} [Field k] [PerfectField k] (S : SmoothProjectiveSurface k)
    (p : S.toScheme) (hp : IsClosed ({p} : Set S.toScheme)) :
    AlgebraicGeometry.IsSeparated (pointBlowup.structureHom S p hp) := by
  obtain ⟨S', e, he⟩ :=
    AlgebraicGeometry.Scheme.blowup_closedPoint_smoothProjectiveSurface S p hp
  exact MiyaokaMori.IsoOverBase.isSeparated_of_isoOver e he inferInstance

/-- Finite type, transported along `MiyaokaMori.IsoOverBase.isOfFiniteType_of_isoOver`. -/
theorem pointBlowup.isOfFiniteType {k : Type u} [Field k] [PerfectField k] (S : SmoothProjectiveSurface k)
    (p : S.toScheme) (hp : IsClosed ({p} : Set S.toScheme)) :
    AlgebraicGeometry.IsOfFiniteType (pointBlowup.structureHom S p hp) := by
  obtain ⟨S', e, he⟩ :=
    AlgebraicGeometry.Scheme.blowup_closedPoint_smoothProjectiveSurface S p hp
  exact MiyaokaMori.IsoOverBase.isOfFiniteType_of_isoOver e he inferInstance

/-- The blowup `Bl_p S` as a variety over `k`. -/
noncomputable def pointBlowup.variety {k : Type u} [Field k] [PerfectField k] (S : SmoothProjectiveSurface k)
    (p : S.toScheme) (hp : IsClosed ({p} : Set S.toScheme)) : Variety k where
  carrier := (AlgebraicGeometry.Scheme.blowup
      (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)).left
  «over» := ⟨pointBlowup.structureHom S p hp⟩
  integral := pointBlowup.isIntegral S p hp
  separated := pointBlowup.isSeparated S p hp
  finiteType := pointBlowup.isOfFiniteType S p hp

/-- Smoothness, transported along `MiyaokaMori.IsoOverBase.isSmoothOver_of_isoOver`. The mathematical
content is `AlgebraicGeometry.Scheme.blowupClosedPoint_isRegular` (Stacks 0AGQ/0AGR);
`[PerfectField k]` is used for "regular iff smooth". -/
theorem pointBlowup.isSmoothOver {k : Type u} [Field k] [PerfectField k] (S : SmoothProjectiveSurface k)
    (p : S.toScheme) (hp : IsClosed ({p} : Set S.toScheme)) :
    IsSmoothOver k (pointBlowup.variety S p hp).carrier := by
  obtain ⟨S', e, he⟩ :=
    AlgebraicGeometry.Scheme.blowup_closedPoint_smoothProjectiveSurface S p hp
  have he' : e.hom ≫ ((pointBlowup.variety S p hp).carrier ↘
      AlgebraicGeometry.Spec (CommRingCat.of k)) =
      S'.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k) := he
  exact MiyaokaMori.IsoOverBase.isSmoothOver_of_isoOver
    (Y := (pointBlowup.variety S p hp).carrier) e he'
    S'.toSmoothProjectiveVariety.smooth

/-- Projectivity, transported along `MiyaokaMori.IsoOverBase.isProjectiveOver_of_isoOver`. -/
theorem pointBlowup.isProjectiveOver {k : Type u} [Field k] [PerfectField k] (S : SmoothProjectiveSurface k)
    (p : S.toScheme) (hp : IsClosed ({p} : Set S.toScheme)) :
    IsProjectiveOver k (pointBlowup.variety S p hp).carrier := by
  obtain ⟨S', e, he⟩ :=
    AlgebraicGeometry.Scheme.blowup_closedPoint_smoothProjectiveSurface S p hp
  have he' : e.hom ≫ ((pointBlowup.variety S p hp).carrier ↘
      AlgebraicGeometry.Spec (CommRingCat.of k)) =
      S'.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k) := he
  exact MiyaokaMori.IsoOverBase.isProjectiveOver_of_isoOver
    (Y := (pointBlowup.variety S p hp).carrier) e he'
    S'.toSmoothProjectiveVariety.projective

/-- Connectedness: immediate from integrality (irreducibility). -/
theorem pointBlowup.connectedSpace {k : Type u} [Field k] [PerfectField k] (S : SmoothProjectiveSurface k)
    (p : S.toScheme) (hp : IsClosed ({p} : Set S.toScheme)) :
    ConnectedSpace (pointBlowup.variety S p hp).carrier.carrier := by
  haveI : AlgebraicGeometry.IsIntegral (pointBlowup.variety S p hp).carrier := pointBlowup.isIntegral S p hp
  infer_instance

/-- The blowup `Bl_p S` as a smooth projective variety over `k`. -/
noncomputable def pointBlowup.smoothProjectiveVariety {k : Type u} [Field k] [PerfectField k] (S : SmoothProjectiveSurface k)
    (p : S.toScheme) (hp : IsClosed ({p} : Set S.toScheme)) : SmoothProjectiveVariety k where
  toVariety := pointBlowup.variety S p hp
  smooth := pointBlowup.isSmoothOver S p hp
  projective := pointBlowup.isProjectiveOver S p hp
  connected := pointBlowup.connectedSpace S p hp

/-- `dim Bl_p S = 2`, transported along the isomorphism of underlying schemes
(`MiyaokaMori.IsoOverBase.Variety.dim_eq_of_iso`). -/
theorem pointBlowup.dim_eq_two {k : Type u} [Field k] [PerfectField k] (S : SmoothProjectiveSurface k)
    (p : S.toScheme) (hp : IsClosed ({p} : Set S.toScheme)) :
    (pointBlowup.smoothProjectiveVariety S p hp).toVariety.dim = 2 := by
  obtain ⟨S', e, he⟩ :=
    AlgebraicGeometry.Scheme.blowup_closedPoint_smoothProjectiveSurface S p hp
  have e' : (pointBlowup.smoothProjectiveVariety S p hp).toVariety.carrier ≅
      S'.toSmoothProjectiveVariety.toVariety.carrier := e.symm
  rw [MiyaokaMori.IsoOverBase.Variety.dim_eq_of_iso _ _ e']
  exact S'.dim_eq_two

/-- The blowup of a smooth projective surface `S` at a closed point `p`, as a smooth projective
surface. -/
noncomputable def pointBlowup {k : Type u} [Field k] [PerfectField k] (S : SmoothProjectiveSurface k)
    (p : S.toScheme) (hp : IsClosed ({p} : Set S.toScheme)) : SmoothProjectiveSurface k where
  toSmoothProjectiveVariety := pointBlowup.smoothProjectiveVariety S p hp
  dim_eq_two := pointBlowup.dim_eq_two S p hp

/-- The blowup morphism `π : Bl_p S ⟶ S`. -/
noncomputable def pointBlowup.π {k : Type u} [Field k] [PerfectField k] (S : SmoothProjectiveSurface k)
    (p : S.toScheme) (hp : IsClosed ({p} : Set S.toScheme)) :
    (pointBlowup S p hp).toScheme ⟶ S.toScheme :=
  (AlgebraicGeometry.Scheme.blowup
    (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)).hom

/-- `pointBlowup` agrees with the blowup of Stacks 01OG. -/

theorem pointBlowup.iso_blowup {k : Type u} [Field k] [PerfectField k] (S : SmoothProjectiveSurface k)
    (p : S.toScheme) (hp : IsClosed ({p} : Set S.toScheme)) :
    ∃ e : (pointBlowup S p hp).toScheme ≅ (AlgebraicGeometry.Scheme.blowup
        (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)).left,
      e.hom ≫ (AlgebraicGeometry.Scheme.blowup
        (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)).hom = pointBlowup.π S p hp :=
  ⟨CategoryTheory.Iso.refl _, CategoryTheory.Category.id_comp _⟩

/- The exceptional curve `E = π⁻¹(p)_red`: the reduced closed subscheme given by the vanishing ideal
   sheaf (Mathlib's `IdealSheafData.vanishingIdeal`) of the closed set `π⁻¹(p)`, with `ι` its closed
   immersion. Integrality (`π⁻¹(p) ≅ P¹_{κ(p)}` is irreducible, Stacks 0AGQ), properness over `k`
   and one-dimensionality are proof obligations. -/

/-- The ideal sheaf of the exceptional curve: the vanishing ideal sheaf of the closed set `π⁻¹(p)`. -/

noncomputable abbrev pointBlowup.exceptionalIdeal {k : Type u} [Field k] [PerfectField k] (S : SmoothProjectiveSurface k)
    (p : S.toScheme) (hp : IsClosed ({p} : Set S.toScheme)) :
    (pointBlowup S p hp).toScheme.IdealSheafData :=
  (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal
    ⟨(pointBlowup.π S p hp).base ⁻¹' {p}, hp.preimage (pointBlowup.π S p hp).base.hom.continuous⟩)

/- Integrality and one-dimensionality of `E` are split into topological statements about the fibre
   `π⁻¹(p)` plus transport: reducedness comes from `vanishingIdeal_subscheme_isReduced`; the
   underlying space of `E` is homeomorphic to the fibre `π⁻¹(p)` via the closed immersion
   (`pointBlowup.exceptionalHomeomorph`); the mathematical content is `pointBlowup.fiber_isIrreducible`
   and `pointBlowup.fiber_topologicalKrullDim_eq_one` (Stacks 0AGQ: `π⁻¹(p) ≅ P¹_{κ(p)}`), both
   derived from `fiber_iso_projectiveLine` (assembled from Stacks 0805 and 0AGQ, with
   `AlgebraicGeometry.Scheme.flat_fromSpecStalk` and `pointBlowup.vanishingIdeal_comap_fromSpecStalk`
   providing the flatness hypothesis of 0805 and the identification of the centre for 0AGQ) and
   Mathlib's `Scheme.Hom.fiberHomeo`. -/

/-- The support of the exceptional curve is the set-theoretic fibre `π⁻¹(p)` (`range_subschemeι`,
`coe_support_vanishingIdeal`). -/
theorem pointBlowup.range_exceptionalIdeal_subschemeι {k : Type u} [Field k] [PerfectField k]
    (S : SmoothProjectiveSurface k) (p : S.toScheme) (hp : IsClosed ({p} : Set S.toScheme)) :
    Set.range (pointBlowup.exceptionalIdeal S p hp).subschemeι.base =
      (pointBlowup.π S p hp).base ⁻¹' {p} :=
  (AlgebraicGeometry.Scheme.IdealSheafData.range_subschemeι _).trans
    (AlgebraicGeometry.Scheme.IdealSheafData.coe_support_vanishingIdeal _)

/-- The underlying space of the exceptional curve `E` is homeomorphic to the fibre `π⁻¹(p)` (as a
subspace of `Bl_p S`): the closed immersion is a closed embedding with image `π⁻¹(p)`
(`IsEmbedding.toHomeomorph`, `Homeomorph.setCongr`). -/
noncomputable def pointBlowup.exceptionalHomeomorph {k : Type u} [Field k] [PerfectField k]
    (S : SmoothProjectiveSurface k) (p : S.toScheme) (hp : IsClosed ({p} : Set S.toScheme)) :
    (pointBlowup.exceptionalIdeal S p hp).subscheme ≃ₜ
      ((pointBlowup.π S p hp).base ⁻¹' {p} : Set (pointBlowup S p hp).toScheme) :=
  ((pointBlowup.exceptionalIdeal S p hp).subschemeι.isClosedEmbedding.isEmbedding.toHomeomorph).trans
    (Homeomorph.setCongr (pointBlowup.range_exceptionalIdeal_subschemeι S p hp))

/-- `E` is reduced: the closed subscheme of a vanishing ideal sheaf is reduced (Stacks 01J3,
`vanishingIdeal_subscheme_isReduced`). -/
theorem pointBlowup.exceptional_isReduced {k : Type u} [Field k] [PerfectField k]
    (S : SmoothProjectiveSurface k) (p : S.toScheme) (hp : IsClosed ({p} : Set S.toScheme)) :
    AlgebraicGeometry.IsReduced (pointBlowup.exceptionalIdeal S p hp).subscheme :=
  AlgebraicGeometry.Intersection.ReducedPointClosure.vanishingIdeal_subscheme_isReduced _


/-- `Spec O_{X,x} → X` is flat: `fromSpecStalk` is `Spec.map (germ)` (the stalk is the localization
of the section ring of an affine open at a prime, `IsAffineOpen.isLocalization_stalk`,
`IsLocalization.flat`) followed by the open immersion `hU.fromSpec`, and flatness is closed under
composition (Stacks 00HT: localizations are flat; used for Stacks 0805 with `g = Spec O_{S,p} → S`). -/
theorem AlgebraicGeometry.Scheme.flat_fromSpecStalk (X : AlgebraicGeometry.Scheme.{u}) (x : X) :
    AlgebraicGeometry.Flat (X.fromSpecStalk x) := by
  have key : ∀ {U : X.Opens} (hU : AlgebraicGeometry.IsAffineOpen U) (hx : x ∈ U),
      AlgebraicGeometry.Flat (hU.fromSpecStalk hx) := by
    intro U hU hx
    have : AlgebraicGeometry.Flat (AlgebraicGeometry.Spec.map (X.presheaf.germ U x hx)) := by
      rw [AlgebraicGeometry.Flat.SpecMap_iff]
      letI : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hx).hom.toAlgebra
      have := hU.isLocalization_stalk ⟨x, hx⟩
      exact RingHom.flat_algebraMap_iff.mpr
        (IsLocalization.flat _ (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl)
    unfold AlgebraicGeometry.IsAffineOpen.fromSpecStalk
    infer_instance
  unfold AlgebraicGeometry.Scheme.fromSpecStalk
  exact key _ _

/-- The pullback of the vanishing ideal sheaf of the closed point `p` along `Spec O_{S,p} → S` is the
ideal sheaf given by the maximal ideal `𝔪_p` (transported to `Γ(Spec O_{S,p})` via `ΓSpecIso`) —
the centre required by Stacks 0AGQ.

Proof: `vanishingIdeal {p} = (fromSpecResidueField p).ker` (`vanishingIdeal_singleton_eq_pointIdeal`);
`fromSpecResidueField p = Spec.map (residue p) ≫ fromSpecStalk p`, and `fromSpecStalk p` is a
monomorphism (a preimmersion), so `pullback (fromSpecStalk p) (fromSpecResidueField p)` is
`Spec κ(p)` with `fst = Spec.map (residue p)` (`IsKernelPair.id_of_mono`, `IsPullback.paste_horiz`);
by `ker_fst_of_isClosedImmersion` (`p` closed makes `fromSpecResidueField p` a closed immersion),
the comap is `(Spec.map (residue p)).ker = ofIdealTop (ker appTop)` (`ker_of_isAffine`); finally
`ΓSpecIso_naturality` and `IsLocalRing.residue_eq_zero_iff` identify this kernel with the image of
`𝔪_p` under `ΓSpecIso.inv`. -/
theorem pointBlowup.vanishingIdeal_comap_fromSpecStalk {k : Type u} [Field k] [PerfectField k]
    (S : SmoothProjectiveSurface k) (p : S.toScheme) (hp : IsClosed ({p} : Set S.toScheme)) :
    (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩).comap
        (S.toScheme.fromSpecStalk p) =
      AlgebraicGeometry.Scheme.IdealSheafData.ofIdealTop
        ((IsLocalRing.maximalIdeal (S.toScheme.presheaf.stalk p)).map
          (AlgebraicGeometry.Scheme.ΓSpecIso (S.toScheme.presheaf.stalk p)).inv.hom) := by
  rw [AlgebraicGeometry.Scheme.vanishingIdeal_singleton_eq_pointIdeal p hp]
  unfold MiyaokaMori.Statement.pointIdeal
  have : AlgebraicGeometry.IsClosedImmersion (S.toScheme.fromSpecResidueField p) :=
    AlgebraicGeometry.isClosed_singleton_iff_isClosedImmersion.mp hp
  rw [← AlgebraicGeometry.Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
  have hpb : IsPullback (AlgebraicGeometry.Spec.map (S.toScheme.residue p)) (𝟙 _)
      (S.toScheme.fromSpecStalk p) (S.toScheme.fromSpecResidueField p) := by
    have h1 : IsPullback (AlgebraicGeometry.Spec.map (S.toScheme.residue p)) (𝟙 _) (𝟙 _)
        (AlgebraicGeometry.Spec.map (S.toScheme.residue p)) :=
      IsPullback.of_vert_isIso ⟨by simp⟩
    have h2 := IsKernelPair.id_of_mono (S.toScheme.fromSpecStalk p)
    have := h1.paste_horiz h2
    simpa [AlgebraicGeometry.Scheme.fromSpecResidueField] using this
  rw [← AlgebraicGeometry.Scheme.Hom.ker_comp_of_isIso hpb.isoPullback.hom, hpb.isoPullback_hom_fst,
    AlgebraicGeometry.Scheme.ker_of_isAffine]
  congr 1
  ext x
  have hnat := congrArg (fun f => f.hom x)
    (AlgebraicGeometry.Scheme.ΓSpecIso_naturality (S.toScheme.residue p))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at hnat
  have hmap : (IsLocalRing.maximalIdeal (S.toScheme.presheaf.stalk p)).map
      (AlgebraicGeometry.Scheme.ΓSpecIso (S.toScheme.presheaf.stalk p)).inv.hom =
      (IsLocalRing.maximalIdeal (S.toScheme.presheaf.stalk p)).comap
      (AlgebraicGeometry.Scheme.ΓSpecIso (S.toScheme.presheaf.stalk p)).hom.hom :=
    Ideal.map_symm (AlgebraicGeometry.Scheme.ΓSpecIso
      (S.toScheme.presheaf.stalk p)).commRingCatIsoToRingEquiv
  have hinj : Function.Injective
      (AlgebraicGeometry.Scheme.ΓSpecIso (S.toScheme.residueField p)).hom.hom :=
    (AlgebraicGeometry.Scheme.ΓSpecIso (S.toScheme.residueField p)).commRingCatIsoToRingEquiv.injective
  rw [hmap, Ideal.mem_comap, RingHom.mem_ker, ← IsLocalRing.residue_eq_zero_iff,
    ← map_eq_zero_iff _ hinj, hnat]
  rfl

/-- **The fibre scheme is `≅ P¹_{κ(p)}`** (Stacks 0AGQ (1) for surfaces):
`Scheme.Hom.fiber π p = pullback π (fromSpecResidueField p)` is isomorphic to `ProjectiveLine κ(p)`.

Proof: `fromSpecResidueField p = Spec.map (residue) ≫ fromSpecStalk p`; pasting two base changes
(`pullbackRightPullbackFstIso`) writes the fibre as `pullback (pullback.fst g π) (Spec.map residue)`
(`g = fromSpecStalk p`); Stacks 0805 (`g` flat, `flat_fromSpecStalk`) identifies `pullback g π` with
`Bl_{I.comap g} Spec O_{S,p}`, and `vanishingIdeal_comap_fromSpecStalk` identifies the centre with
`𝔪_p`; `O_{S,p}` is a two-dimensional regular local ring (`stalk_regular_dim_two`), and Stacks 0AGQ
gives the final `≅ P¹_κ`. -/
theorem pointBlowup.fiber_iso_projectiveLine {k : Type u} [Field k] [PerfectField k]
    (S : SmoothProjectiveSurface k) (p : S.toScheme) (hp : IsClosed ({p} : Set S.toScheme)) :
    Nonempty ((pointBlowup.π S p hp).fiber p ≅
      ProjectiveLine (IsLocalRing.ResidueField (S.toScheme.presheaf.stalk p))) := by
  have : AlgebraicGeometry.Flat (S.toScheme.fromSpecStalk p) :=
    AlgebraicGeometry.Scheme.flat_fromSpecStalk _ _
  obtain ⟨hreg, hdim⟩ := S.stalk_regular_dim_two p hp
  obtain ⟨e₂⟩ : Nonempty (pullback (AlgebraicGeometry.Scheme.blowup
      ((AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩).comap
        (S.toScheme.fromSpecStalk p))).hom
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap (S.toScheme.presheaf.stalk p)
        (IsLocalRing.ResidueField (S.toScheme.presheaf.stalk p))))) ≅
      ProjectiveLine (IsLocalRing.ResidueField (S.toScheme.presheaf.stalk p))) := by
    rw [pointBlowup.vanishingIdeal_comap_fromSpecStalk S p hp]
    exact AlgebraicGeometry.blowup_regularLocalRing_dimTwo_exceptional
      (S.toScheme.presheaf.stalk p) hdim
  obtain ⟨e₁, he₁⟩ := AlgebraicGeometry.Scheme.blowup_flatBaseChange (S.toScheme.fromSpecStalk p)
    (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)
  have hφ : S.toScheme.fromSpecResidueField p =
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap (S.toScheme.presheaf.stalk p)
        (IsLocalRing.ResidueField (S.toScheme.presheaf.stalk p)))) ≫ S.toScheme.fromSpecStalk p := by
    rw [IsLocalRing.ResidueField.algebraMap_eq]
    rfl
  refine ⟨pullbackSymmetry _ _ ≪≫ pullback.congrHom hφ rfl ≪≫
    (pullbackRightPullbackFstIso _ _ _).symm ≪≫ pullbackSymmetry _ _ ≪≫
    (asIso (pullback.map (e₁.hom ≫ pullback.fst _ _) _ (pullback.fst _ _) _ e₁.hom (𝟙 _) (𝟙 _)
      (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm))).symm ≪≫
    pullback.congrHom he₁ rfl ≪≫ e₂⟩

/-- The fibre `π⁻¹(p) ⊂ Bl_p S` of the point blowup is an irreducible set (nonempty and irreducible).

Source: Stacks 0AGQ (1) (`resolve-lemma-blowup`): the blowup of a two-dimensional regular local
ring `(A, 𝔪, κ)` along `𝔪` has a closed immersion `r : X → P¹_A` with `r|_E : E ≅ P¹_κ`.

Proof: `fiber_iso_projectiveLine` gives `π.fiber p = pullback π (fromSpecResidueField p) ≅ P¹_{κ(p)}`;
Mathlib's `Scheme.Hom.fiberHomeo` identifies the underlying space of the fibre scheme with the
set-theoretic fibre `π⁻¹(p)`; `P¹_κ` is irreducible
(`AlgebraicGeometry.Proj.ProjectiveLineIrreducible.projectiveLine_irreducible`), transported along the
homeomorphism (`IsOpenEmbedding.irreducibleSpace`), and `isIrreducible_iff_irreducibleSpace`
finishes. -/
theorem pointBlowup.fiber_isIrreducible {k : Type u} [Field k] [PerfectField k]
    (S : SmoothProjectiveSurface k) (p : S.toScheme) (hp : IsClosed ({p} : Set S.toScheme)) :
    IsIrreducible ((pointBlowup.π S p hp).base ⁻¹' {p} : Set (pointBlowup S p hp).toScheme) := by
  obtain ⟨e⟩ := pointBlowup.fiber_iso_projectiveLine S p hp
  have : IrreducibleSpace (ProjectiveLine (IsLocalRing.ResidueField (S.toScheme.presheaf.stalk p))) :=
    AlgebraicGeometry.Proj.ProjectiveLineIrreducible.projectiveLine_irreducible _
  have : Nonempty ((pointBlowup.π S p hp).fiber p) :=
    Nonempty.map (AlgebraicGeometry.Scheme.homeoOfIso e).symm inferInstance
  have : IrreducibleSpace ((pointBlowup.π S p hp).fiber p) :=
    (AlgebraicGeometry.Scheme.homeoOfIso e).isOpenEmbedding.irreducibleSpace
  have : Nonempty ((pointBlowup.π S p hp).base ⁻¹' {p} : Set (pointBlowup S p hp).toScheme) :=
    Nonempty.map ((pointBlowup.π S p hp).fiberHomeo p) inferInstance
  exact isIrreducible_iff_irreducibleSpace.mpr
    ((pointBlowup.π S p hp).fiberHomeo p).symm.isOpenEmbedding.irreducibleSpace

/-- The underlying space of `E` is irreducible: transport of `fiber_isIrreducible` along the
homeomorphism `exceptionalHomeomorph` (`Subtype.irreducibleSpace`, `IsOpenEmbedding.irreducibleSpace`). -/
theorem pointBlowup.exceptional_irreducibleSpace {k : Type u} [Field k] [PerfectField k]
    (S : SmoothProjectiveSurface k) (p : S.toScheme) (hp : IsClosed ({p} : Set S.toScheme)) :
    IrreducibleSpace (pointBlowup.exceptionalIdeal S p hp).subscheme := by
  haveI : IrreducibleSpace
      ((pointBlowup.π S p hp).base ⁻¹' {p} : Set (pointBlowup S p hp).toScheme) :=
    Subtype.irreducibleSpace (pointBlowup.fiber_isIrreducible S p hp)
  haveI : Nonempty (pointBlowup.exceptionalIdeal S p hp).subscheme :=
    Nonempty.map (pointBlowup.exceptionalHomeomorph S p hp).symm inferInstance
  exact (pointBlowup.exceptionalHomeomorph S p hp).isOpenEmbedding.irreducibleSpace

/-- The exceptional divisor `E = π⁻¹(p)` (with its reduced structure) is integral: reduced
(`exceptional_isReduced`) and irreducible (`exceptional_irreducibleSpace`), by
`isIntegral_of_irreducibleSpace_of_isReduced`. -/
theorem pointBlowup.exceptional_isIntegral {k : Type u} [Field k] [PerfectField k] (S : SmoothProjectiveSurface k)
    (p : S.toScheme) (hp : IsClosed ({p} : Set S.toScheme)) :
    AlgebraicGeometry.IsIntegral (pointBlowup.exceptionalIdeal S p hp).subscheme := by
  haveI := pointBlowup.exceptional_isReduced S p hp
  haveI := pointBlowup.exceptional_irreducibleSpace S p hp
  exact AlgebraicGeometry.isIntegral_of_irreducibleSpace_of_isReduced _

/-- `E` is proper over `k`: a closed immersion is proper, `pointBlowup` is projective hence proper
over `k`, and the composite is proper. -/
theorem pointBlowup.exceptional_isProper {k : Type u} [Field k] [PerfectField k] (S : SmoothProjectiveSurface k)
    (p : S.toScheme) (hp : IsClosed ({p} : Set S.toScheme)) :
    AlgebraicGeometry.IsProper ((pointBlowup.exceptionalIdeal S p hp).subschemeι ≫
      ((pointBlowup S p hp).toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) := by
  haveI : AlgebraicGeometry.IsProper
      ((pointBlowup S p hp).toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ((isProjectiveOver_iff_isProper_and_isAmple k _).mp
      (pointBlowup S p hp).toSmoothProjectiveVariety.projective).1
  infer_instance

/-- The fibre `π⁻¹(p) ⊂ Bl_p S` of the point blowup (as a subspace) has topological Krull dimension `1`.

Source: as for `fiber_isIrreducible`, Stacks 0AGQ (1) (`E ≅ P¹_κ`).

Proof: transport twice with `IsHomeomorph.topologicalKrullDim_eq`, along `Scheme.Hom.fiberHomeo`
(set-theoretic fibre `≃ₜ` fibre scheme) and `fiber_iso_projectiveLine` (fibre scheme `≅ P¹_{κ(p)}`),
and conclude with `(ProjectiveLine.asSmoothProjectiveCurve κ).dim_one :
topologicalKrullDim (ProjectiveLine κ) = 1`. -/
theorem pointBlowup.fiber_topologicalKrullDim_eq_one {k : Type u} [Field k] [PerfectField k]
    (S : SmoothProjectiveSurface k) (p : S.toScheme) (hp : IsClosed ({p} : Set S.toScheme)) :
    topologicalKrullDim
      ((pointBlowup.π S p hp).base ⁻¹' {p} : Set (pointBlowup S p hp).toScheme) = 1 := by
  obtain ⟨e⟩ := pointBlowup.fiber_iso_projectiveLine S p hp
  rw [← IsHomeomorph.topologicalKrullDim_eq _ ((pointBlowup.π S p hp).fiberHomeo p).isHomeomorph,
    IsHomeomorph.topologicalKrullDim_eq _ (AlgebraicGeometry.Scheme.homeoOfIso e).isHomeomorph]
  exact (ProjectiveLine.asSmoothProjectiveCurve _).dim_one

/-- The exceptional divisor `E` is one-dimensional: `SchemeIsOneDimensional` is
`topologicalKrullDim = 1`, transported from the fibre (`fiber_topologicalKrullDim_eq_one`) along the
homeomorphism `exceptionalHomeomorph`. -/
theorem pointBlowup.exceptional_dim_eq_one {k : Type u} [Field k] [PerfectField k] (S : SmoothProjectiveSurface k)
    (p : S.toScheme) (hp : IsClosed ({p} : Set S.toScheme)) :
    SchemeIsOneDimensional (pointBlowup.exceptionalIdeal S p hp).subscheme := by
  unfold SchemeIsOneDimensional
  rw [IsHomeomorph.topologicalKrullDim_eq _ (pointBlowup.exceptionalHomeomorph S p hp).isHomeomorph]
  exact pointBlowup.fiber_topologicalKrullDim_eq_one S p hp

/-- The exceptional divisor of the blowup at `p`, as an integral curve in `Bl_p S`. -/
noncomputable def pointBlowup.exceptional {k : Type u} [Field k] [PerfectField k] (S : SmoothProjectiveSurface k)
    (p : S.toScheme) (hp : IsClosed ({p} : Set S.toScheme)) :
    IntegralCurve k (pointBlowup S p hp).toScheme where
  carrier := (pointBlowup.exceptionalIdeal S p hp).subscheme
  ι := (pointBlowup.exceptionalIdeal S p hp).subschemeι
  isIntegral := pointBlowup.exceptional_isIntegral S p hp
  isProper := pointBlowup.exceptional_isProper S p hp
  dim_eq_one := pointBlowup.exceptional_dim_eq_one S p hp

theorem pointBlowup.range_exceptional {k : Type u} [Field k] [PerfectField k] (S : SmoothProjectiveSurface k)
    (p : S.toScheme) (hp : IsClosed ({p} : Set S.toScheme)) :
    Set.range (pointBlowup.exceptional S p hp).ι.base = (pointBlowup.π S p hp).base ⁻¹' {p} := by
  exact (AlgebraicGeometry.Scheme.IdealSheafData.range_subschemeι _).trans
    (AlgebraicGeometry.Scheme.IdealSheafData.coe_support_vanishingIdeal _)


/-- `π` is an isomorphism over `S ∖ {p}` (Stacks 02OS (1)).

Proof: assembled from three lemmas:
1. `AlgebraicGeometry.Scheme.blowup_isBlowup` (a translation of `blowup_universalProperty`, Stacks
   0806): `pointBlowup.π` satisfies the universal property predicate
   `IsBlowup (vanishingIdeal ⟨{p}, hp⟩) π`;
2. `AlgebraicGeometry.Scheme.vanishingIdeal_singleton_eq_pointIdeal`:
   `vanishingIdeal ⟨{p}, hp⟩ = MiyaokaMori.Statement.pointIdeal S p`, rewriting 1 as
   `IsBlowup (pointIdeal S p) π`;
3. `MiyaokaMori.Statement.IsBlowup.isIso_morphismRestrict_pointIdeal` with `V = {p}ᶜ` (clearly `p ∉ V`)
   gives `IsIso (π ∣_ V)`. -/
theorem pointBlowup.iso_away {k : Type u} [Field k] [PerfectField k] (S : SmoothProjectiveSurface k)
    (p : S.toScheme) (hp : IsClosed ({p} : Set S.toScheme)) :
    IsIso ((pointBlowup.π S p hp) ∣_ (⟨{p}ᶜ, hp.isOpen_compl⟩ : S.toScheme.Opens)) := by
  have hb : MiyaokaMori.Statement.IsBlowup (MiyaokaMori.Statement.pointIdeal S.toScheme p)
      (pointBlowup.π S p hp) := by
    rw [← AlgebraicGeometry.Scheme.vanishingIdeal_singleton_eq_pointIdeal p hp]
    exact AlgebraicGeometry.Scheme.blowup_isBlowup _
  exact MiyaokaMori.Statement.IsBlowup.isIso_morphismRestrict_pointIdeal p (pointBlowup.π S p hp) hb
    ⟨{p}ᶜ, hp.isOpen_compl⟩ (fun h => h rfl)

end
