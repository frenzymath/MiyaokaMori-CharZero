import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.ProjectiveLineIsSmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Surfaces.PointBlowupSurface
import MiyaokaMori.AlgebraicGeometry.Morphisms.SmoothProjectiveSurfaceIsoTransfer
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothRationalCurve
import MiyaokaMori.AlgebraicGeometry.Blowup.StrictTransform
import MiyaokaMori.AlgebraicGeometry.Blowup.Stacks0807
import MiyaokaMori.AlgebraicGeometry.Blowup.Stacks080e
import MiyaokaMori.AlgebraicGeometry.Varieties.Smooth.Stacks056s
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.Stacks0b8y

/-! # The strict transform of a smooth rational curve is smooth rational

The strict transform of a smooth rational curve under a point blowup is again a smooth rational curve:
`Γ' ≅ Γ ≅ P¹` (Lemma 5.1 of the paper, §5).

Route (the proof of Stacks 0BI7(1), but with no case split on `p ∈ Γ` at the top level):
1. The closure model `strictTransform p hp Γ` is the closed subscheme `V(ker ι)` of `Γ ×_S Bl_p S`,
   `ι := AlgebraicGeometry.Blowup.StrictTransformClosureModel.ι`; `ker ι` is *definitionally* the Stacks 080D ideal
   `strictTransformIdeal Γ.ι I_p` (`strictTransform.ker_ι`, by `IdealSheafData.ker_subschemeι`).
2. Stacks 080E (`strictTransform_eq_blowup`): `Bl_J Γ`, `J := I_p.comap Γ.ι`, also embeds in
   `Γ ×_S Bl_p S` with kernel `strictTransformIdeal`, over `Γ`. Two closed immersions with the same
   kernel differ by an isomorphism (`IsClosedImmersion.lift`, `IsClosedImmersion.isIso_of_ker_eq`),
   so the model's projection `q` to `Γ` is `(iso) ≫ (Bl_J Γ → Γ)` (`strictTransform.exists_iso_over`).
3. `J` is an effective Cartier divisor on `Γ` (`strictTransform.exists_effCartier_comap`):
   if `p = Γ.ι x` then `J = vanishingIdeal {x}` (`comap_vanishingIdeal_singleton`: for a closed
   immersion `comap ∘ map = id`, `comap_map_of_isClosedImmersion`, and
   `map (vanishingIdeal {x}) = vanishingIdeal {p}` by Mathlib's `map_vanishingIdeal`); `x` is a
   closed point whose local ring is regular (`Γ ≅ P¹_k` is smooth over `k`, hence regular by
   Stacks 056S), so Stacks 0B8Y gives the divisor. If `p ∉ Γ` then `J = ⊤` (empty support), generated
   by the nonzerodivisor `1` (`EffCartier.top`).
4. Stacks 0807: the blowup along an effective Cartier divisor is an isomorphism, so `q` is an
   isomorphism; compatibility with the `k`-structures is `i ≫ b = q ≫ j` in the fibre product
   (`StrictTransformClosureModel.i_comp_b`). Compose with `Γ ≅ P¹_k`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- For a closed immersion `f : X ⟶ Y` and an ideal sheaf `m` on `X`, `(m.map f).comap f = m`.
Proof: `g := m.subschemeι ≫ f` is a closed immersion, `(m.map f).subschemeι = g.imageι` and
`g = g.toImage ≫ g.imageι` with `g.toImage` an isomorphism; since `f` is a monomorphism the square
`m.subscheme → g.image`, `m.subscheme → X`, `X → Y`, `g.image → Y` is a pullback, so
`(pullback.fst f g.imageι).ker = m.subschemeι.ker = m`, and the left side is `(m.map f).comap f`
by `ker_fst_of_isClosedImmersion`. -/
theorem AlgebraicGeometry.Scheme.IdealSheafData.comap_map_of_isClosedImmersion
    {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) [AlgebraicGeometry.IsClosedImmersion f]
    (m : X.IdealSheafData) : (m.map f).comap f = m := by
  set g : m.subscheme ⟶ Y := m.subschemeι ≫ f with hg_def
  have hsq : IsPullback m.subschemeι g.toImage f g.imageι := by
    refine IsPullback.of_isLimit' ⟨by simp [hg_def]⟩ ?_
    refine PullbackCone.IsLimit.mk _ (fun s ↦ s.snd ≫ inv g.toImage) (fun s ↦ ?_) (fun s ↦ ?_)
      (fun s l h₁ h₂ ↦ ?_)
    · rw [← cancel_mono f]
      simp only [Category.assoc]
      rw [← hg_def, s.condition]
      congr 1
      rw [IsIso.inv_comp_eq]
      exact g.toImage_imageι.symm
    · simp
    · simp [← h₂]
  have h1 := AlgebraicGeometry.Scheme.IdealSheafData.ker_fst_of_isClosedImmersion g.imageι f
  rw [← hsq.isoPullback_inv_fst, AlgebraicGeometry.Scheme.Hom.ker_comp_of_isIso,
    AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι] at h1
  simp only [AlgebraicGeometry.Scheme.Hom.imageι,
    AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι] at h1
  exact h1.symm

/-- The pullback of the vanishing ideal of a closed point along a closed immersion is the
vanishing ideal of its (unique) preimage point. -/
theorem AlgebraicGeometry.Scheme.IdealSheafData.comap_vanishingIdeal_singleton
    {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) [AlgebraicGeometry.IsClosedImmersion f]
    (x : X) (hx : IsClosed ({x} : Set X)) (hp : IsClosed ({f.base x} : Set Y)) :
    (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{f.base x}, hp⟩).comap f
      = AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩ := by
  have h : (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩).map f
      = AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{f.base x}, hp⟩ := by
    rw [AlgebraicGeometry.Scheme.IdealSheafData.map_vanishingIdeal]
    congr 1
    ext1
    simp
  rw [← h, AlgebraicGeometry.Scheme.IdealSheafData.comap_map_of_isClosedImmersion]

/-- The unit ideal is an effective Cartier divisor (locally generated by the nonzerodivisor `1`). -/
def AlgebraicGeometry.Scheme.EffCartier.top (X : AlgebraicGeometry.Scheme.{u}) : X.EffCartier where
  ideal := ⊤
  isInvertible := fun x ↦ by
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    refine ⟨⟨U, hU⟩, hxU, 1, fun r h ↦ by simpa using h, ?_⟩
    simp [AlgebraicGeometry.Scheme.IdealSheafData.ideal_top]

/-- A smooth rational curve is smooth over `k` (transport along the isomorphism with `P¹_k`). -/
theorem IntegralCurve.isSmoothOver_of_isSmoothRational {k : Type u} [Field k]
    {X : AlgebraicGeometry.Scheme.{u}} [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (Γ : IntegralCurve k X) (hΓ : Γ.IsSmoothRational) : IsSmoothOver k Γ.carrier := by
  obtain ⟨e, he⟩ := hΓ
  refine MiyaokaMori.IsoOverBase.isSmoothOver_of_isoOver e.symm ?_
    (ProjectiveLine.asSmoothProjectiveCurve k).smooth
  rw [Iso.symm_hom, ← he, Iso.inv_hom_id_assoc]

/-- The kernel of the closure model's inclusion into `Γ ×_S Bl_p S` is exactly the Stacks 080D
strict-transform ideal: both are the kernel of the open immersion of the complement of the pulled
back exceptional locus (definitional). This is the content of `strictTransform_ker_eq_stacks`, whose
witness can be taken to be `ι` itself. -/
theorem strictTransform.ker_ι {k : Type u} [Field k] [PerfectField k]
    {S : SmoothProjectiveSurface k} (p : S.toScheme) (hp : IsClosed ({p} : Set S.toScheme))
    (Γ : IntegralCurve k S.toScheme) :
    (AlgebraicGeometry.Blowup.StrictTransformClosureModel.ι
      (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩) (pointBlowup.π S p hp) Γ.ι).ker
      = AlgebraicGeometry.Scheme.strictTransformIdeal Γ.ι
          (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩) :=
  AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι _

/-- The centre ideal pulled back to a smooth rational curve `Γ` is an effective Cartier divisor
on `Γ`: if `p ∈ Γ` it is the reduced closed point (Stacks 0B8Y, `Γ` regular by 056S); if `p ∉ Γ`
it is the unit ideal. -/
theorem strictTransform.exists_effCartier_comap {k : Type u} [Field k] [PerfectField k]
    {S : SmoothProjectiveSurface k} (p : S.toScheme) (hp : IsClosed ({p} : Set S.toScheme))
    (Γ : IntegralCurve k S.toScheme) (hΓ : Γ.IsSmoothRational) :
    ∃ D : Γ.carrier.EffCartier,
      D.ideal = (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩).comap Γ.ι := by
  by_cases hpΓ : p ∈ Set.range Γ.ι.base
  · obtain ⟨x, rfl⟩ := hpΓ
    have hx : IsClosed ({x} : Set Γ.carrier) := by
      have : ({x} : Set Γ.carrier) = Γ.ι.base ⁻¹' {Γ.ι.base x} := by
        ext y
        simp [Γ.ι.isEmbedding.injective.eq_iff]
      rw [this]
      exact hp.preimage Γ.ι.base.hom.continuous
    have : IsRegularLocalRing (Γ.carrier.presheaf.stalk x) :=
      (AlgebraicGeometry.isRegular_of_smoothOver Γ.carrier
        (Γ.isSmoothOver_of_isSmoothRational hΓ)).isRegularLocalRing_stalk x
    have hP : AlgebraicGeometry.IsProper (Γ.carrier ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      Γ.isProper
    obtain ⟨D, hD⟩ := AlgebraicGeometry.closedPoint_effectiveCartier_of_regular (k := k) Γ.carrier
      Γ.dim_eq_one x hx
    refine ⟨D, ?_⟩
    rw [AlgebraicGeometry.Scheme.IdealSheafData.comap_vanishingIdeal_singleton Γ.ι x hx hp]
    exact hD
  · refine ⟨AlgebraicGeometry.Scheme.EffCartier.top _, ?_⟩
    symm
    show (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩).comap Γ.ι = ⊤
    rw [← AlgebraicGeometry.Scheme.IdealSheafData.support_eq_bot_iff,
      AlgebraicGeometry.Scheme.IdealSheafData.support_comap]
    ext1
    simp only [Closeds.coe_preimage, AlgebraicGeometry.Scheme.IdealSheafData.coe_support_vanishingIdeal,
      Closeds.coe_bot]
    ext y
    simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
    intro h
    exact hpΓ ⟨y, h⟩

/-- The closure-model strict transform maps isomorphically onto `Γ`, compatibly with the
`k`-structures, as soon as the blowup of `Γ` along the pulled-back centre ideal is an isomorphism
(Stacks 080E identifies the strict transform with that blowup; two closed immersions with the same
kernel differ by an isomorphism; the compatibility is `i ≫ b = q ≫ j` in the fibre product). -/
theorem strictTransform.exists_iso_over {k : Type u} [Field k] [PerfectField k]
    {S : SmoothProjectiveSurface k} (p : S.toScheme) (hp : IsClosed ({p} : Set S.toScheme))
    (Γ : IntegralCurve k S.toScheme)
    (hblow : IsIso (AlgebraicGeometry.Scheme.blowup
      ((AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩).comap Γ.ι)).hom) :
    ∃ e : (strictTransform p hp Γ).carrier ≅ Γ.carrier,
      e.hom ≫ (Γ.carrier ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
        = (strictTransform p hp Γ).carrier ↘ AlgebraicGeometry.Spec (CommRingCat.of k) := by
  obtain ⟨i₀, hi₀, hker, hfst⟩ := AlgebraicGeometry.Scheme.strictTransform_eq_blowup Γ.ι
    (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)
  -- everything below lives in the world of `b := (blowup I).hom`; `pointBlowup.π S p hp` unfolds to it
  have hkerι : (AlgebraicGeometry.Blowup.StrictTransformClosureModel.ι
      (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)
      (AlgebraicGeometry.Scheme.blowup
        (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)).hom Γ.ι).ker
      = AlgebraicGeometry.Scheme.strictTransformIdeal Γ.ι
          (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩) :=
    AlgebraicGeometry.Scheme.IdealSheafData.ker_subschemeι _
  have hcl : AlgebraicGeometry.IsClosedImmersion (AlgebraicGeometry.Blowup.StrictTransformClosureModel.ι
      (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)
      (AlgebraicGeometry.Scheme.blowup
        (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)).hom Γ.ι) :=
    AlgebraicGeometry.Blowup.StrictTransformClosureModel.isClosedImmersion_ι _ _ _
  let φ := AlgebraicGeometry.IsClosedImmersion.lift (AlgebraicGeometry.Blowup.StrictTransformClosureModel.ι
      (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)
      (AlgebraicGeometry.Scheme.blowup
        (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)).hom Γ.ι)
      i₀ (hkerι.trans hker.symm).le
  have hφι : φ ≫ AlgebraicGeometry.Blowup.StrictTransformClosureModel.ι
      (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)
      (AlgebraicGeometry.Scheme.blowup
        (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)).hom Γ.ι
      = i₀ := AlgebraicGeometry.IsClosedImmersion.lift_fac _ _ _
  have : IsIso φ := AlgebraicGeometry.IsClosedImmersion.isIso_of_ker_eq i₀ _ φ hφι
    (hker.trans hkerι.symm)
  have hq : AlgebraicGeometry.Blowup.StrictTransformClosureModel.q
      (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)
      (AlgebraicGeometry.Scheme.blowup
        (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)).hom Γ.ι
      = inv φ ≫ (AlgebraicGeometry.Scheme.blowup
      ((AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩).comap Γ.ι)).hom := by
    rw [← hfst, ← hφι, AlgebraicGeometry.Blowup.StrictTransformClosureModel.q]
    simp
  have hiso : IsIso (AlgebraicGeometry.Blowup.StrictTransformClosureModel.q
      (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)
      (AlgebraicGeometry.Scheme.blowup
        (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)).hom Γ.ι) := by
    rw [hq]
    infer_instance
  refine ⟨@asIso _ _ _ _ _ hiso, ?_⟩
  change AlgebraicGeometry.Blowup.StrictTransformClosureModel.q
      (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)
      (AlgebraicGeometry.Scheme.blowup
        (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)).hom Γ.ι ≫
      Γ.ι ≫ (S.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
    = AlgebraicGeometry.Blowup.StrictTransformClosureModel.i
      (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)
      (AlgebraicGeometry.Scheme.blowup
        (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)).hom Γ.ι ≫
      (AlgebraicGeometry.Scheme.blowup
        (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩)).hom ≫
      (S.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
  rw [← Category.assoc, ← Category.assoc, AlgebraicGeometry.Blowup.StrictTransformClosureModel.i_comp_b]

/-- **The strict transform of a smooth rational curve is smooth rational** (Stacks 0BI7(1)). -/
theorem strictTransform_isSmoothRational {k : Type u} [Field k] [PerfectField k]
    {S : SmoothProjectiveSurface k} (p : S.toScheme) (hp : IsClosed ({p} : Set S.toScheme))
    (Γ : IntegralCurve k S.toScheme) (hΓ : Γ.IsSmoothRational) :
    (strictTransform p hp Γ).IsSmoothRational := by
  obtain ⟨eΓ, heΓ⟩ := hΓ
  obtain ⟨D, hD⟩ := strictTransform.exists_effCartier_comap p hp Γ ⟨eΓ, heΓ⟩
  have hblow : IsIso (AlgebraicGeometry.Scheme.blowup
      ((AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ⟨{p}, hp⟩).comap Γ.ι)).hom := by
    rw [← hD]
    exact AlgebraicGeometry.Scheme.blowup_isIso_of_effectiveCartier D
  obtain ⟨e, he⟩ := strictTransform.exists_iso_over p hp Γ hblow
  exact ⟨e ≪≫ eΓ, by rw [Iso.trans_hom, Category.assoc, heΓ, he]⟩

end
