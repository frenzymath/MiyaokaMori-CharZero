import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Morphisms.PullbackFromSpecStalkStalkMap
import MiyaokaMori.AlgebraicGeometry.Blowup.BlowupIsoAwayFromCenterAffineLeaf
import MiyaokaMori.AlgebraicGeometry.Varieties.Surfaces.SurfaceClosedPointRegularDimTwo
import MiyaokaMori.AlgebraicGeometry.Blowup.Stacks02ns
import MiyaokaMori.AlgebraicGeometry.Blowup.Stacks0805
import MiyaokaMori.AlgebraicGeometry.Morphisms.Stacks01wc
import MiyaokaMori.AlgebraicGeometry.Blowup.Stacks0agr
import MiyaokaMori.AlgebraicGeometry.Varieties.Smooth.Stacks056s

/-! # The blowup of a smooth projective surface at a closed point is regular

The blowup `Bl_p S` of a smooth projective surface at a closed point is a regular scheme (the
mathematical content of the smoothness of `Bl_p S`; over a perfect field regular ⟺ smooth).

Source: Stacks 0AGQ / 0AGR (the blowup of a two-dimensional regular local ring at its maximal ideal
is an irreducible regular scheme); Hartshorne V.3; used in the proof of Corollary 4.3 of the paper (§4).

Ingredients:
* local Noetherianity: the blowup is projective (Stacks 02NS), hence proper and locally of finite type
  (Stacks 01WC), and `LocallyOfFiniteType.isLocallyNoetherian`;
* over `S ∖ {p}`: `(blowup I).hom ∣_ {p}ᶜ` is an isomorphism (`isIso_reesAlgebra_projToOpen_of_ideal_eq_top`),
  and stalks are transported along open immersions and isomorphisms;
* on the exceptional fibre: Stacks 0805 (flat base change along `Spec O_{S,p} → S`), the fact that
  this base change does not change stalks (`stalkMap_pullback_snd_fromSpecStalk_bijective`), and
  Stacks 0AGR.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The restriction of the relative `Proj` to an affine open `U` is an isomorphism as soon as the chart
`projToOpen U` is an isomorphism (the same as `isIso_relativeProj_hom_restrict` in
`BlowupIsoAwayFromCentre.lean`; that module imports `PointBlowupSurface`, which this module cannot
import, hence the private copy). -/
private theorem isIso_relativeProj_hom_restrict_aux {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedAffineAlgebra) (U : X.AffineZariskiSite) [IsIso (S.projToOpen U)] :
    IsIso (S.relativeProj.hom ∣_ U.toOpens) := by
  have h₁ := S.projChart_isPullback U
  have h₂ := AlgebraicGeometry.isPullback_morphismRestrict S.relativeProj.hom U.toOpens
  have he : (h₁.isoIsPullback _ _ h₂).inv ≫ S.projToOpen U = S.relativeProj.hom ∣_ U.toOpens :=
    h₁.isoIsPullback_inv_fst _ _ h₂
  rw [← he]
  infer_instance

/-- Stacks 02OS(1): the blowup is an isomorphism over an open set `U` disjoint from the support of the
centre (the same as `Scheme.isIso_blowup_hom_restrict_of_disjoint_support` in
`BlowupIsoAwayFromCenter.lean`; private copy for the same reason as above). -/
private theorem isIso_blowup_hom_restrict_of_disjoint_support_aux {X : AlgebraicGeometry.Scheme.{u}}
    (I : X.IdealSheafData) (U : X.Opens) (hU : Disjoint (U : Set X) (I.support : Set X)) :
    IsIso ((AlgebraicGeometry.Scheme.blowup I).hom ∣_ U) := by
  rw [← MorphismProperty.isomorphisms.iff]
  refine AlgebraicGeometry.IsZariskiLocalAtTarget.of_iSup_eq_top
    (P := MorphismProperty.isomorphisms AlgebraicGeometry.Scheme)
    (fun V : U.toScheme.affineOpens => (V : U.toScheme.Opens))
    (AlgebraicGeometry.iSup_affineOpens_eq_top _) ?_
  intro V
  rw [(MorphismProperty.isomorphisms AlgebraicGeometry.Scheme).arrow_mk_iso_iff
    (AlgebraicGeometry.morphismRestrictRestrict (AlgebraicGeometry.Scheme.blowup I).hom U V.1),
    MorphismProperty.isomorphisms.iff]
  have hV : AlgebraicGeometry.IsAffineOpen (U.ι ''ᵁ V.1) := V.2.image_of_isOpenImmersion U.ι
  have hle : U.ι ''ᵁ V.1 ≤ U :=
    (U.ι.image_le_opensRange V.1).trans (le_of_eq (AlgebraicGeometry.Scheme.Opens.opensRange_ι U))
  have htop : I.ideal ⟨U.ι ''ᵁ V.1, hV⟩ = ⊤ :=
    I.ideal_eq_top_of_disjoint_support ⟨_, hV⟩ (hU.mono_left (fun _ h => hle h))
  have := I.isIso_reesAlgebra_projToOpen_of_ideal_eq_top ⟨U.ι ''ᵁ V.1, hV⟩ htop
  exact isIso_relativeProj_hom_restrict_aux I.reesAlgebra.toGradedAffineAlgebra ⟨U.ι ''ᵁ V.1, hV⟩

/-- `Bl_p S` is a regular scheme.

Proof (regularity is pointwise; two cases):

0. **Locally Noetherian**: `Bl_p S → S` is projective (Stacks 02NS), hence proper and locally of
   finite type (Stacks 01WC); `S` is locally Noetherian (a variety), so `Bl_p S` is locally Noetherian
   (`LocallyOfFiniteType.isLocallyNoetherian`).
1. **Over `S ∖ {p}`**: `𝓘_p` is the unit ideal sheaf on `S ∖ {p}` (`supp 𝓘_p = {p}`,
   `coe_support_vanishingIdeal`), and the blowup along the unit ideal is an isomorphism
   (Stacks 02OS(1), `isIso_reesAlgebra_projToOpen_of_ideal_eq_top`), so `π⁻¹(S ∖ {p}) ≅ S ∖ {p}`;
   `S` is smooth projective, hence regular (Stacks 056S), and the stalks are transported along the open
   immersion `π⁻¹(S∖{p}) ↪ Bl_p S`, the isomorphism `π|` and the open immersion `S∖{p} ↪ S`
   (`IsRegularLocalRing.of_ringEquiv`).
2. **On the exceptional fibre `π⁻¹(p)`**: `O_{S,p}` is a two-dimensional regular local ring
   (`SmoothProjectiveSurface.stalk_regular_dim_two`); Stacks 0805 (the blowup commutes with the flat
   base change `g = Spec O_{S,p} → S`, `g` flat by `fromSpecStalk_flat`) gives
   `Bl_{𝓘_p·O} Spec O_{S,p} ≅ Bl_p S ×_S Spec O_{S,p}` with centre `𝓘_p·O_{S,p} = 𝔪_p`
   (`vanishingIdeal_singleton_comap_fromSpecStalk`); a point `x ∈ π⁻¹(p)` lifts to a point `y` of the
   fibre product (`Scheme.Pullback.exists_preimage_pullback`, since `g(closed point) = p`), and the
   stalk map of the second projection at `y` is bijective
   (`stalkMap_pullback_snd_fromSpecStalk_bijective`), so `O_{Bl_p S, x} ≅ O_{Bl_𝔪 Spec O_{S,p}, y'}`
   with `y'` over the closed point; Stacks 0AGR says the latter is regular.

(The alternative "`A[y/x]` is a smooth `A`-algebra" is wrong as stated; one has to use the regularity
of Stacks 0AGR, not flatness.) -/
theorem AlgebraicGeometry.Scheme.blowupClosedPoint_isRegular {k : Type u} [Field k] [PerfectField k]
    (S : SmoothProjectiveSurface k) (p : S.toScheme) (hp : IsClosed ({p} : Set S.toScheme)) :
    AlgebraicGeometry.Scheme.IsRegular
      (AlgebraicGeometry.Scheme.blowup
        (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)).left := by
  set I := AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal
    (⟨{p}, hp⟩ : TopologicalSpace.Closeds S.toScheme) with hI
  have hS : AlgebraicGeometry.Scheme.IsRegular S.toScheme :=
    AlgebraicGeometry.isRegular_of_smoothOver S.toScheme S.toSmoothProjectiveVariety.smooth
  have : AlgebraicGeometry.IsNoetherian S.toScheme :=
    { toIsLocallyNoetherian := inferInstance, toCompactSpace := inferInstance }
  have : AlgebraicGeometry.IsProjectiveMorphism (AlgebraicGeometry.Scheme.blowup I).hom :=
    AlgebraicGeometry.Scheme.blowup_isProjectiveMorphism I
  have : AlgebraicGeometry.IsProper (AlgebraicGeometry.Scheme.blowup I).hom :=
    AlgebraicGeometry.IsProjectiveMorphism.isProper _
  have : AlgebraicGeometry.IsLocallyNoetherian (AlgebraicGeometry.Scheme.blowup I).left :=
    AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian (AlgebraicGeometry.Scheme.blowup I).hom
  refine { isRegularLocalRing_stalk := fun x => ?_ }
  by_cases hx : (AlgebraicGeometry.Scheme.blowup I).hom x = p
  · -- points on the exceptional fibre
    set g := S.toScheme.fromSpecStalk p with hg
    have : AlgebraicGeometry.Flat g := AlgebraicGeometry.Scheme.fromSpecStalk_flat S.toScheme p
    have hgp : g (IsLocalRing.closedPoint (S.toScheme.presheaf.stalk p)) =
        (AlgebraicGeometry.Scheme.blowup I).hom x := by
      rw [hx, hg]
      exact AlgebraicGeometry.Scheme.fromSpecStalk_closedPoint
    obtain ⟨y, hy1, hy2⟩ := AlgebraicGeometry.Scheme.Pullback.exists_preimage_pullback
      (f := g) (g := (AlgebraicGeometry.Scheme.blowup I).hom) _ x hgp
    obtain ⟨e, he⟩ := AlgebraicGeometry.Scheme.blowup_flatBaseChange g I
    obtain ⟨hreg, hdim⟩ := S.stalk_regular_dim_two p hp
    have key : ∀ (J : (AlgebraicGeometry.Spec (CommRingCat.of (S.toScheme.presheaf.stalk p))).IdealSheafData),
        J = AlgebraicGeometry.Scheme.IdealSheafData.ofIdealTop
          ((IsLocalRing.maximalIdeal (S.toScheme.presheaf.stalk p)).map
            (AlgebraicGeometry.Scheme.ΓSpecIso (S.toScheme.presheaf.stalk p)).inv.hom) →
        ∀ y' : ↑(AlgebraicGeometry.Scheme.blowup J).left,
          (AlgebraicGeometry.Scheme.blowup J).hom y' = IsLocalRing.closedPoint (S.toScheme.presheaf.stalk p) →
          IsRegularLocalRing ((AlgebraicGeometry.Scheme.blowup J).left.presheaf.stalk y') := by
      rintro J rfl y' hy'
      exact AlgebraicGeometry.blowup_regularLocalRing_dimTwo_isRegularLocalRing_stalk _ hdim y' hy'
    have h1 : IsRegularLocalRing
        ((AlgebraicGeometry.Scheme.blowup (I.comap g)).left.presheaf.stalk (e.inv y)) := by
      refine key _ (AlgebraicGeometry.Scheme.vanishingIdeal_singleton_comap_fromSpecStalk p hp) (e.inv y) ?_
      have hy' : e.hom (e.inv y) = y := by
        rw [← AlgebraicGeometry.Scheme.Hom.comp_apply, e.inv_hom_id]
        rfl
      rw [← he, AlgebraicGeometry.Scheme.Hom.comp_apply, hy', hy1]
    have h2 : IsRegularLocalRing
        ((CategoryTheory.Limits.pullback g (AlgebraicGeometry.Scheme.blowup I).hom).presheaf.stalk y) := by
      have := h1
      have : IsIso (e.inv.stalkMap y) :=
        ((AlgebraicGeometry.isIso_iff_isIso_stalkMap e.inv).mp inferInstance).2 y
      exact IsRegularLocalRing.of_ringEquiv (asIso (e.inv.stalkMap y)).commRingCatIsoToRingEquiv
    have h3 : IsRegularLocalRing ((AlgebraicGeometry.Scheme.blowup I).left.presheaf.stalk
        (CategoryTheory.Limits.pullback.snd g (AlgebraicGeometry.Scheme.blowup I).hom y)) := by
      have := h2
      exact IsRegularLocalRing.of_ringEquiv (RingEquiv.ofBijective _
        (AlgebraicGeometry.Scheme.Hom.stalkMap_pullback_snd_fromSpecStalk_bijective
          (AlgebraicGeometry.Scheme.blowup I).hom p y)).symm
    rwa [hy2] at h3
  · -- points over `S ∖ {p}`
    let V : S.toScheme.Opens := ⟨{p}ᶜ, hp.isOpen_compl⟩
    have hdisj : Disjoint (V : Set S.toScheme) (I.support : Set S.toScheme) := by
      have hsupp : (I.support : Set S.toScheme) = {p} :=
        AlgebraicGeometry.Scheme.IdealSheafData.coe_support_vanishingIdeal _
      rw [hsupp]
      exact disjoint_compl_left
    have : IsIso ((AlgebraicGeometry.Scheme.blowup I).hom ∣_ V) :=
      isIso_blowup_hom_restrict_of_disjoint_support_aux I V hdisj
    have hxV : x ∈ (AlgebraicGeometry.Scheme.blowup I).hom ⁻¹ᵁ V := hx
    let x₀ : ((AlgebraicGeometry.Scheme.blowup I).hom ⁻¹ᵁ V).toScheme := ⟨x, hxV⟩
    let φ : ((AlgebraicGeometry.Scheme.blowup I).hom ⁻¹ᵁ V).toScheme ⟶ S.toScheme :=
      ((AlgebraicGeometry.Scheme.blowup I).hom ∣_ V) ≫ V.ι
    have hφ : IsIso (φ.stalkMap x₀) := by
      have h1 : IsIso (((AlgebraicGeometry.Scheme.blowup I).hom ∣_ V).stalkMap x₀) :=
        ((AlgebraicGeometry.isIso_iff_isIso_stalkMap _).mp inferInstance).2 x₀
      have h2 : IsIso (V.ι.stalkMap (((AlgebraicGeometry.Scheme.blowup I).hom ∣_ V) x₀)) :=
        inferInstance
      rw [AlgebraicGeometry.Scheme.Hom.stalkMap_comp]
      exact IsIso.comp_isIso' h2 h1
    have h1 : IsRegularLocalRing (S.toScheme.presheaf.stalk (φ x₀)) := hS.isRegularLocalRing_stalk _
    have h2 : IsRegularLocalRing
        (((AlgebraicGeometry.Scheme.blowup I).hom ⁻¹ᵁ V).toScheme.presheaf.stalk x₀) :=
      IsRegularLocalRing.of_ringEquiv (asIso (φ.stalkMap x₀)).commRingCatIsoToRingEquiv
    exact IsRegularLocalRing.of_ringEquiv
      (asIso (((AlgebraicGeometry.Scheme.blowup I).hom ⁻¹ᵁ V).ι.stalkMap x₀)).commRingCatIsoToRingEquiv.symm

end
