import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.CurveDimensionOne
import MiyaokaMori.AlgebraicGeometry.Blowup.BlowupIsoAwayFromCenter
import MiyaokaMori.AlgebraicGeometry.Varieties.Surfaces.PointBlowupSurface
import MiyaokaMori.AlgebraicGeometry.Morphisms.SmoothProjectiveSurfaceIsoTransfer
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.IntegralCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.Stacks0a213

/-! # The strict transform of an integral curve under a point blowup

The strict transform of an integral curve `Γ ⊆ S` under the blowup `π : Bl_p S → S` of a closed point
(the definition following Hartshorne II.7.15, and the "closure" characterisation of Hartshorne V.3,
p. 388), used for the fibre components in Lemma 5.1 of the paper (§5).

Route:
* The open set `away` of the closure model `AlgebraicGeometry.Blowup.StrictTransformClosureModel` is
  `(snd ≫ π)⁻¹({p}ᶜ)` (`away_eq_preimage`: `support_comap` twice).
* On `U = {p}ᶜ` the blowup `π` is an isomorphism (`pointBlowup_isIso_away`), so
  `away ≅ Γ_U ×_U Bl_U ≅ Γ_U = Γ.ι⁻¹(U)` (`restrictMap` is the open immersion given by `pullback.map`,
  `Scheme.Pullback.range_map` computes its image to be exactly `away`; the right leg being an isomorphism
  makes `pullback.fst` an isomorphism).
* `Γ_U` is nonempty (`Γ` is one-dimensional, hence not a point: `IntegralCurve.exists_base_ne`) and an
  open subscheme of the integral scheme `Γ`, hence integral; `model = ker(away.ι).subscheme` is the
  scheme-theoretic image of `away`: `toImage` is scheme-theoretically dominant, so the image is reduced
  (`isSchemeTheoreticallyDominant_toImage`, `IsSchemeTheoreticallyDominant.isReduced`), and dominant, so
  the image is irreducible; hence integral. Quasi-compactness comes from `Γ ×_S Bl` being locally
  Noetherian (`Bl` is of finite type over `k`).
* Dimension one: Stacks 0A21(3) (`topologicalKrullDim_opens_eq_of_irreducible`) twice,
  `dim model = dim (range openToModel) = dim away = dim Γ_U = dim Γ = 1`.
* `strictTransform_range`: `range i = snd '' closure(away) = closure(snd '' away)` (closed embedding), and
  `snd '' away = π⁻¹({p}ᶜ) ∩ range snd = π⁻¹({p}ᶜ) ∩ π⁻¹(range Γ.ι)` (`range_snd`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-! ## General lemmas: scheme-theoretic images -/

namespace AlgebraicGeometry

/-- For a quasi-compact morphism `f`, the morphism `f.toImage` to its scheme-theoretic image is
scheme-theoretically dominant (its kernel is zero): on the affine opens `imageι⁻¹(W)` (`W ⊆ Y` affine)
`toImage.app` is injective (`toImage_app_injective`), and these opens cover the image. -/
theorem Scheme.Hom.isSchemeTheoreticallyDominant_toImage {X Y : Scheme.{u}} (f : X ⟶ Y)
    [QuasiCompact f] : IsSchemeTheoreticallyDominant f.toImage := by
  constructor
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top
    (fun W : Y.affineOpens => ⟨f.imageι ⁻¹ᵁ W.1, W.2.preimage f.imageι⟩) ?_ ?_
  · rw [← Scheme.Hom.preimage_iSup, iSup_affineOpens_eq_top, Scheme.Hom.preimage_top]
  · intro W
    rw [Scheme.Hom.ker_apply, Scheme.IdealSheafData.ideal_bot, Pi.bot_apply]
    exact (RingHom.injective_iff_ker_eq_bot _).mp (f.toImage_app_injective W)

/-- The scheme-theoretic image of a quasi-compact morphism with reduced source is reduced. -/
theorem Scheme.Hom.isReduced_image {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [IsReduced X] :
    IsReduced f.image :=
  have := f.isSchemeTheoreticallyDominant_toImage
  IsSchemeTheoreticallyDominant.isReduced f.toImage

/-- The target of a dominant morphism with irreducible source is irreducible (the image is irreducible,
and the closure of a dense irreducible set is irreducible). -/
theorem irreducibleSpace_of_isDominant {X Y : Scheme.{u}} (f : X ⟶ Y) [IsDominant f]
    [IrreducibleSpace X] : IrreducibleSpace Y := by
  rw [irreducibleSpace_def]
  have h := (IrreducibleSpace.isIrreducible_univ X).image f.base
    f.base.hom.continuous.continuousOn
  rw [Set.image_univ] at h
  have h2 := h.closure
  rwa [f.denseRange.closure_range] at h2

end AlgebraicGeometry

/-! ## General lemmas: the closure model away from the centre -/

namespace AlgebraicGeometry.Blowup.StrictTransformClosureModel

open AlgebraicGeometry

variable {X B C : Scheme.{u}} (I : X.IdealSheafData) (b : B ⟶ X) (j : C ⟶ X)

/-- `away` is the preimage in `C ×_X B` of the complement `X ∖ supp I` of the centre. -/
theorem away_eq_preimage :
    away I b j = (pullback.snd j b ≫ b) ⁻¹ᵁ I.support.compl := by
  ext1
  simp only [away, exceptionalIdeal, Scheme.IdealSheafData.support_comap, Closeds.compl,
    Scheme.Hom.comp_preimage, Scheme.Hom.coe_preimage, Closeds.coe_preimage, Opens.coe_mk,
    Set.preimage_compl]

/-- The open immersion of the fibre product `C_U ×_U B_U` over an open set `U ⊆ X` into `C ×_X B`
(an `abbrev`, so that Mathlib's instance `pullback_map_isOpenImmersion` applies directly). -/
abbrev restrictMap (U : X.Opens) : pullback (j ∣_ U) (b ∣_ U) ⟶ pullback j b :=
  pullback.map (j ∣_ U) (b ∣_ U) j b (j ⁻¹ᵁ U).ι (b ⁻¹ᵁ U).ι U.ι
    (morphismRestrict_ι j U) (morphismRestrict_ι b U)

theorem range_restrictMap (U : X.Opens) :
    Set.range (restrictMap b j U).base =
      (((pullback.snd j b ≫ b) ⁻¹ᵁ U : (pullback j b).Opens) : Set ↥(pullback j b)) := by
  have h := Scheme.Pullback.range_map (j ∣_ U) (b ∣_ U) j b (j ⁻¹ᵁ U).ι (b ⁻¹ᵁ U).ι U.ι
    (morphismRestrict_ι j U) (morphismRestrict_ι b U)
  rw [Scheme.Opens.range_ι, Scheme.Opens.range_ι] at h
  change Set.range (restrictMap b j U) = _
  rw [h]
  have h1 : (pullback.fst j b) ⁻¹' ((j ⁻¹ᵁ U : C.Opens) : Set ↥C) =
      (((pullback.snd j b ≫ b) ⁻¹ᵁ U : (pullback j b).Opens) : Set ↥(pullback j b)) := by
    rw [← pullback.condition]
    rfl
  have h2 : (pullback.snd j b) ⁻¹' ((b ⁻¹ᵁ U : B.Opens) : Set ↥B) =
      (((pullback.snd j b ≫ b) ⁻¹ᵁ U : (pullback j b).Opens) : Set ↥(pullback j b)) := rfl
  rw [h1, h2, Set.inter_self]

/-- If `away = (snd ≫ b)⁻¹(U)`, then `away ≅ C_U ×_U B_U`. -/
def awayIso (U : X.Opens) (hU : away I b j = (pullback.snd j b ≫ b) ⁻¹ᵁ U) :
    (away I b j).toScheme ≅ pullback (j ∣_ U) (b ∣_ U) :=
  IsOpenImmersion.isoOfRangeEq (away I b j).ι (restrictMap b j U)
    (by rw [Scheme.Opens.range_ι, range_restrictMap, hU])

/-- If moreover `b` is an isomorphism over `U`, then `away ≅ C_U = j⁻¹(U)`. -/
def awayIsoRestrict (U : X.Opens) (hU : away I b j = (pullback.snd j b ≫ b) ⁻¹ᵁ U)
    [IsIso (b ∣_ U)] : (away I b j).toScheme ≅ (j ⁻¹ᵁ U).toScheme :=
  awayIso I b j U hU ≪≫ asIso (pullback.fst (j ∣_ U) (b ∣_ U))

theorem isIntegral_away (U : X.Opens) (hU : away I b j = (pullback.snd j b ≫ b) ⁻¹ᵁ U)
    [IsIso (b ∣_ U)] [IsIntegral C] [Nonempty (j ⁻¹ᵁ U)] : IsIntegral (away I b j).toScheme :=
  have : IsIntegral (j ⁻¹ᵁ U).toScheme := isIntegral_of_isOpenImmersion (j ⁻¹ᵁ U).ι
  IsIntegral.of_isIso (awayIsoRestrict I b j U hU).inv

/-- The scheme-theoretic closure (the closure model) of an integral scheme is integral. -/
theorem isIntegral_model [QuasiCompact (away I b j).ι] [IsIntegral (away I b j).toScheme] :
    IsIntegral (model I b j) := by
  have : IsReduced (model I b j) := (away I b j).ι.isReduced_image
  have : IsDominant (openToModel I b j) :=
    inferInstanceAs (IsDominant (away I b j).ι.toImage)
  have : IrreducibleSpace (model I b j) := irreducibleSpace_of_isDominant (openToModel I b j)
  exact isIntegral_of_irreducibleSpace_of_isReduced _

end AlgebraicGeometry.Blowup.StrictTransformClosureModel

/-- A one-dimensional integral curve is not a single point: for every `p` there is a point of `Γ` not
mapping to `p` (otherwise, `Γ.ι` being injective, `Γ` would be a single point of topological Krull
dimension `≤ 0`). -/
theorem IntegralCurve.exists_base_ne {k : Type u} [Field k] {X : AlgebraicGeometry.Scheme.{u}}
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (Γ : IntegralCurve k X) (p : X) :
    ∃ x : Γ.carrier, Γ.ι.base x ≠ p := by
  by_contra h
  push Not at h
  have hss : Subsingleton Γ.carrier :=
    ⟨fun a b => Γ.ι.isClosedEmbedding.injective (by rw [h a, h b])⟩
  have hsub' : Subsingleton (TopologicalSpace.IrreducibleCloseds Γ.carrier) := ⟨fun a b => by
    apply TopologicalSpace.IrreducibleCloseds.ext
    exact a.2.nonempty.eq_univ.trans b.2.nonempty.eq_univ.symm⟩
  have h0 : topologicalKrullDim Γ.carrier ≤ 0 := Order.krullDim_nonpos_of_subsingleton
  have h1 : topologicalKrullDim Γ.carrier = 1 := Γ.dim_eq_one
  rw [h1] at h0
  norm_num at h0

/-! ## The case of a point blowup -/

namespace strictTransform

variable {k : Type u} [Field k] [PerfectField k] {S : SmoothProjectiveSurface k}
  (p : S.toScheme) (hp : IsClosed ({p} : Set S.toScheme)) (Γ : IntegralCurve k S.toScheme)

/-- The complement of the centre `p`, as an open set of `S`. -/
abbrev awayOpen : S.toScheme.Opens := ⟨{p}ᶜ, hp.isOpen_compl⟩

/-- The open set `away` of the closure model is the preimage of `{p}ᶜ` under `snd ≫ π`. -/
theorem away_eq :
    AlgebraicGeometry.Blowup.StrictTransformClosureModel.away
        (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩) (pointBlowup.π S p hp) Γ.ι =
      (pullback.snd Γ.ι (pointBlowup.π S p hp) ≫ pointBlowup.π S p hp) ⁻¹ᵁ awayOpen p hp := by
  rw [AlgebraicGeometry.Blowup.StrictTransformClosureModel.away_eq_preimage]
  congr 1

/-- `π` is an isomorphism over `{p}ᶜ` (`pointBlowup_isIso_away`), stated as a theorem rather than an
instance. -/
theorem isIso_π_restrict : IsIso ((pointBlowup.π S p hp) ∣_ awayOpen p hp) :=
  pointBlowup_isIso_away S p hp (awayOpen p hp) (fun h => h rfl)

theorem nonempty_preimage : Nonempty (Γ.ι ⁻¹ᵁ awayOpen p hp) := by
  obtain ⟨x, hx⟩ := Γ.exists_base_ne p
  exact ⟨⟨x, hx⟩⟩

/-- `Bl_p S` is of finite type over `k`, hence locally Noetherian. -/
theorem isLocallyNoetherian_pointBlowup :
    AlgebraicGeometry.IsLocallyNoetherian (pointBlowup S p hp).toScheme :=
  AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian
    ((pointBlowup S p hp).toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))

/-- `Γ ×_S Bl` is locally Noetherian (`Γ.ι` is locally of finite type), so the open immersion `away.ι`
is quasi-compact. -/
theorem quasiCompact_away_ι :
    AlgebraicGeometry.QuasiCompact (AlgebraicGeometry.Blowup.StrictTransformClosureModel.away
        (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩) (pointBlowup.π S p hp) Γ.ι).ι :=
  haveI := isLocallyNoetherian_pointBlowup p hp
  inferInstance

theorem isIntegral_away :
    AlgebraicGeometry.IsIntegral (AlgebraicGeometry.Blowup.StrictTransformClosureModel.away
        (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩) (pointBlowup.π S p hp) Γ.ι).toScheme :=
  haveI := isIso_π_restrict p hp
  haveI := nonempty_preimage p hp Γ
  AlgebraicGeometry.Blowup.StrictTransformClosureModel.isIntegral_away _ _ _ (awayOpen p hp) (away_eq p hp Γ)

end strictTransform

/- The three properties of the strict transform (integral, proper over `k`, one-dimensional), stated as
   separate theorems. -/

/-- Integrality: `away ≅ Γ ∖ {p}` is integral (`π` is an isomorphism over `{p}ᶜ`), and `model` is its
scheme-theoretic image, hence reduced and irreducible. -/
theorem strictTransform.model_isIntegral {k : Type u} [Field k] [PerfectField k] {S : SmoothProjectiveSurface k}
    (p : S.toScheme) (hp : IsClosed ({p} : Set S.toScheme)) (Γ : IntegralCurve k S.toScheme) :
    AlgebraicGeometry.IsIntegral
      (AlgebraicGeometry.Blowup.StrictTransformClosureModel.model
      (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩) (pointBlowup.π S p hp) Γ.ι) :=
  haveI := strictTransform.quasiCompact_away_ι p hp Γ
  haveI := strictTransform.isIntegral_away p hp Γ
  AlgebraicGeometry.Blowup.StrictTransformClosureModel.isIntegral_model _ _ _

/-- Properness over `k`: `i` is a closed immersion (hence proper), `pointBlowup` is proper over `k`, and
the composite is proper. -/
theorem strictTransform.i_comp_isProper {k : Type u} [Field k] [PerfectField k] {S : SmoothProjectiveSurface k}
    (p : S.toScheme) (hp : IsClosed ({p} : Set S.toScheme)) (Γ : IntegralCurve k S.toScheme) :
    AlgebraicGeometry.IsProper
      ((AlgebraicGeometry.Blowup.StrictTransformClosureModel.i
      (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩) (pointBlowup.π S p hp) Γ.ι) ≫
        ((pointBlowup S p hp).toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) := by
  haveI : AlgebraicGeometry.IsProper
      ((pointBlowup S p hp).toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ((isProjectiveOver_iff_isProper_and_isAmple k _).mp
      (pointBlowup S p hp).toSmoothProjectiveVariety.projective).1
  infer_instance

/-- Dimension one: Stacks 0A21(3) twice, `dim model = dim (range openToModel) = dim away = dim Γ_U = dim Γ = 1`
(`model` is, via `i`, an irreducible scheme locally of finite type over `k`, and `range openToModel` is a
nonempty open subset of it). -/
theorem strictTransform.model_dim_eq_one {k : Type u} [Field k] [PerfectField k] {S : SmoothProjectiveSurface k}
    (p : S.toScheme) (hp : IsClosed ({p} : Set S.toScheme)) (Γ : IntegralCurve k S.toScheme) :
    SchemeIsOneDimensional
      (AlgebraicGeometry.Blowup.StrictTransformClosureModel.model
      (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩) (pointBlowup.π S p hp) Γ.ι) := by
  haveI hq := strictTransform.quasiCompact_away_ι p hp Γ
  haveI hM := strictTransform.model_isIntegral p hp Γ
  haveI hA := strictTransform.isIntegral_away p hp Γ
  haveI hI := strictTransform.isIso_π_restrict p hp
  letI : (AlgebraicGeometry.Blowup.StrictTransformClosureModel.model
      (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩) (pointBlowup.π S p hp) Γ.ι).Over
      (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨AlgebraicGeometry.Blowup.StrictTransformClosureModel.i
      (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩) (pointBlowup.π S p hp) Γ.ι ≫
      ((pointBlowup S p hp).toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  have : AlgebraicGeometry.LocallyOfFiniteType ((AlgebraicGeometry.Blowup.StrictTransformClosureModel.model
      (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩) (pointBlowup.π S p hp) Γ.ι) ↘
      AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    inferInstanceAs (AlgebraicGeometry.LocallyOfFiniteType (AlgebraicGeometry.Blowup.StrictTransformClosureModel.i
      (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩) (pointBlowup.π S p hp) Γ.ι ≫
      ((pointBlowup S p hp).toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))))
  have : AlgebraicGeometry.LocallyOfFiniteType (Γ.carrier ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    inferInstanceAs (AlgebraicGeometry.LocallyOfFiniteType
      (Γ.ι ≫ (S.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))))
  have : AlgebraicGeometry.IsOpenImmersion (AlgebraicGeometry.Blowup.StrictTransformClosureModel.openToModel
      (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩) (pointBlowup.π S p hp) Γ.ι) :=
    inferInstanceAs (AlgebraicGeometry.IsOpenImmersion (AlgebraicGeometry.Blowup.StrictTransformClosureModel.away
      (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩) (pointBlowup.π S p hp) Γ.ι).ι.toImage)
  have hne : (((AlgebraicGeometry.Blowup.StrictTransformClosureModel.openToModel
      (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩) (pointBlowup.π S p hp) Γ.ι).opensRange :
        (AlgebraicGeometry.Blowup.StrictTransformClosureModel.model
      (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩) (pointBlowup.π S p hp) Γ.ι).Opens) :
        Set ↥(AlgebraicGeometry.Blowup.StrictTransformClosureModel.model
      (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩) (pointBlowup.π S p hp) Γ.ι)).Nonempty := by
    rw [AlgebraicGeometry.Scheme.Hom.coe_opensRange]
    exact Set.range_nonempty _
  have h1 := AlgebraicGeometry.topologicalKrullDim_opens_eq_of_irreducible (k := k) _ _ hne
  have h2 := MiyaokaMori.IsoOverBase.topologicalKrullDim_eq_of_iso
    (AlgebraicGeometry.Blowup.StrictTransformClosureModel.openToModel
      (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩) (pointBlowup.π S p hp) Γ.ι).isoOpensRange
  have h3 := MiyaokaMori.IsoOverBase.topologicalKrullDim_eq_of_iso
    (AlgebraicGeometry.Blowup.StrictTransformClosureModel.awayIsoRestrict _ _ _ (strictTransform.awayOpen p hp)
      (strictTransform.away_eq p hp Γ))
  have h4 := AlgebraicGeometry.topologicalKrullDim_opens_eq_of_irreducible (k := k) Γ.carrier
    (Γ.ι ⁻¹ᵁ strictTransform.awayOpen p hp) (by obtain ⟨x, hx⟩ := Γ.exists_base_ne p; exact ⟨x, hx⟩)
  have h5 : topologicalKrullDim Γ.carrier = 1 := Γ.dim_eq_one
  unfold SchemeIsOneDimensional
  rw [← h1, ← h2, h3, h4, h5]

/-- The strict transform of the integral curve `Γ ⊆ S` under the point blowup `π : Bl_p S → S`, as an
integral curve in `Bl_p S`. It is built on the closure model with centre ideal `I_p = vanishingIdeal {p}`,
`b = π`, `j = Γ.ι`: remove the support of the pullback of `I_p` from `Γ ×_S Bl_p S` and take the
scheme-theoretic closure (Stacks 080D), which embeds into `Bl_p S` by the second projection `i`. -/
noncomputable def strictTransform {k : Type u} [Field k] [PerfectField k] {S : SmoothProjectiveSurface k}
    (p : S.toScheme) (hp : IsClosed ({p} : Set S.toScheme)) (Γ : IntegralCurve k S.toScheme) :
    IntegralCurve k (pointBlowup S p hp).toScheme where
  carrier := AlgebraicGeometry.Blowup.StrictTransformClosureModel.model
    (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩) (pointBlowup.π S p hp) Γ.ι
  ι := AlgebraicGeometry.Blowup.StrictTransformClosureModel.i
    (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩) (pointBlowup.π S p hp) Γ.ι
  isIntegral := strictTransform.model_isIntegral p hp Γ
  isProper := strictTransform.i_comp_isProper p hp Γ
  dim_eq_one := strictTransform.model_dim_eq_one p hp Γ

/-- The image of the strict transform is the closure of `π⁻¹(Γ ∖ {p})` (the characterisation of
Hartshorne V.3, p. 388). -/
theorem strictTransform_range {k : Type u} [Field k] [PerfectField k] {S : SmoothProjectiveSurface k}
    (p : S.toScheme) (hp : IsClosed ({p} : Set S.toScheme)) (Γ : IntegralCurve k S.toScheme) :
    Set.range (strictTransform p hp Γ).ι.base
      = closure ((pointBlowup.π S p hp).base ⁻¹' (Set.range Γ.ι.base \ {p})) := by
  haveI hq := strictTransform.quasiCompact_away_ι p hp Γ
  change Set.range (AlgebraicGeometry.Blowup.StrictTransformClosureModel.ι _ _ _ ≫
    pullback.snd Γ.ι (pointBlowup.π S p hp)).base = _
  rw [AlgebraicGeometry.Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  have hr := AlgebraicGeometry.Blowup.StrictTransformClosureModel.range_ι
    (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩) (pointBlowup.π S p hp) Γ.ι
  change Set.range (AlgebraicGeometry.Blowup.StrictTransformClosureModel.ι _ _ _).base = _ at hr
  rw [hr, ← (pullback.snd Γ.ι (pointBlowup.π S p hp)).isClosedEmbedding.closure_image_eq]
  congr 1
  rw [strictTransform.away_eq p hp Γ]
  change (pullback.snd Γ.ι (pointBlowup.π S p hp)).base ''
    ((pullback.snd Γ.ι (pointBlowup.π S p hp)).base ⁻¹' ((pointBlowup.π S p hp).base ⁻¹' {p}ᶜ)) = _
  rw [Set.image_preimage_eq_inter_range]
  have hs := AlgebraicGeometry.Scheme.Pullback.range_snd Γ.ι (pointBlowup.π S p hp)
  change Set.range (pullback.snd Γ.ι (pointBlowup.π S p hp)).base = _ at hs
  rw [hs]
  ext y
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff,
    Set.mem_sdiff]
  tauto

end
