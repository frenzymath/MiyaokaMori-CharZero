import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Surfaces.SurfaceClosedSubsetCodimTwoFinite
import MiyaokaMori.AlgebraicGeometry.Varieties.Smooth.RegularScheme
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.AlgebraicGeometry.Blowup.BlowupIsoAwayFromCenter
import MiyaokaMori.AlgebraicGeometry.Blowup.BlowupTower
import MiyaokaMori.AlgebraicGeometry.Blowup.BlowupTowerAvoiding
import MiyaokaMori.AlgebraicGeometry.Morphisms.EliminationResolvingTower
import MiyaokaMori.AlgebraicGeometry.Varieties.Surfaces.PointBlowupSurface
import MiyaokaMori.AlgebraicGeometry.Morphisms.RationalMapPrecomp
import MiyaokaMori.AlgebraicGeometry.Varieties.Surfaces.SmoothProjectiveSurface
import MiyaokaMori.RingTheory.OrderOfVanishing.RegularLocalRingDVR
import MiyaokaMori.RingTheory.RegularLocalRing.Stacks00np
import MiyaokaMori.AlgebraicGeometry.Morphisms.Stacks0bx7
import MiyaokaMori.AlgebraicGeometry.Varieties.Smooth.Stacks056s
import MiyaokaMori.AlgebraicGeometry.Blowup.PointBlowupFiniteSupport

/-! # Elimination of indeterminacy with centres avoiding the regular locus

Elimination of indeterminacy for rational maps from smooth projective surfaces, with centres avoiding
the domain of definition (Debarre, *Introduction to Mori theory*, Theorem 5.18 and its proof; the target
is a projective `k`-scheme): if a rational map `φ : W ⇢ Y` from a smooth projective surface `W` to a
projective `k`-scheme `Y` is regular on an open set `U`, there is a tower of point blowups `β : S → W`
all of whose centres lie outside the inverse images of `U`, such that `φ ∘ β` extends to a morphism `Ψ`.
This is the resolution step in the proof of Corollary 4.3 of the paper (§4).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

private lemma tower_dominant {k : Type u} [Field k] [PerfectField k]
    {S W : SmoothProjectiveSurface k} {β : S.toScheme ⟶ W.toScheme}
    (hβ : IsBlowupTower β) : AlgebraicGeometry.IsDominant β := by
  induction hβ with
  | id W => infer_instance
  | step g hg p hp ih => infer_instance

private lemma generic_pullback_hom_eq
    {X X' Y : Scheme.{u}}
    [PreirreducibleSpace X] [PreirreducibleSpace X'] [Nonempty X]
    (p : X' ⟶ X) [IsDominant p]
    (f : X.PartialMap Y) (f' : X' ⟶ Y)
    (hagree : (p ⁻¹ᵁ f.domain).ι ≫ f' = (p ∣_ f.domain) ≫ f.hom) :
    (p.toPartialMap.comp f).hom = (p.toPartialMap.comp f).domain.ι ≫ f' := by
  let c : X'.PartialMap Y := p.toPartialMap.comp f
  let d := (p.toPartialMap.domain.ι).isoImage (p.toPartialMap.hom ⁻¹ᵁ f.domain)
  apply (cancel_epi d.hom).mp
  dsimp [c, d]
  change _ = _ ≫ ((p.toPartialMap.domain.ι ''ᵁ
    (p.toPartialMap.hom ⁻¹ᵁ f.domain)).ι) ≫ f'
  rw [PartialMap.comp_hom]
  rw [Iso.hom_inv_id_assoc]
  rw [Hom.isoImage_hom_ι_assoc]
  let U : (⊤ : X'.Opens).toScheme.Opens :=
    X'.topIso.hom ⁻¹ᵁ (p ⁻¹ᵁ f.domain)
  have hU : p.toPartialMap.hom ⁻¹ᵁ f.domain = U := by
    dsimp [U]
    change (X'.topIso.hom ≫ p) ⁻¹ᵁ f.domain = _
    rw [Scheme.Hom.comp_preimage]
  cases hU
  let r : U.toScheme ⟶ (p ⁻¹ᵁ f.domain).toScheme :=
    X'.topIso.hom ∣_ (p ⁻¹ᵁ f.domain)
  have hr : r ≫ (p ⁻¹ᵁ f.domain).ι = U.ι ≫ X'.topIso.hom := by
    dsimp [r, U]
    exact morphismRestrict_ι _ _
  have H := congrArg (fun q => r ≫ q) hagree
  rw [← Category.assoc, hr] at H
  have H' :
      U.ι ≫ X'.topIso.hom ≫ f' =
        (X'.topIso.hom ∣_ (p ⁻¹ᵁ f.domain) ≫ p ∣_ f.domain) ≫ f.hom := by
    simpa [r, Category.assoc] using H
  rw [Hom.toPartialMap_hom]
  change (X'.topIso.hom ≫ p) ∣_ f.domain ≫ f.hom =
    ((X'.topIso.hom ≫ p) ⁻¹ᵁ f.domain).ι ≫ (⊤ : X'.Opens).ι ≫ f'
  rw [morphismRestrict_comp]
  simpa [Scheme.topIso_hom, Category.assoc] using H'.symm

private lemma composite_agreement
    {S W X Y : Scheme.{u}}
    (f : W.PartialMap Y) (g : S ⟶ X) (p : X ⟶ W) (f' : X ⟶ Y)
    (hagree : (p ⁻¹ᵁ f.domain).ι ≫ f' =
      (p ∣_ f.domain) ≫ f.hom) :
    ((g ≫ p) ⁻¹ᵁ f.domain).ι ≫ g ≫ f' =
      ((g ≫ p) ∣_ f.domain) ≫ f.hom := by
  let Q : X.Opens := p ⁻¹ᵁ f.domain
  let V : S.Opens := g ⁻¹ᵁ Q
  have H := congrArg (fun q => (g ∣_ Q) ≫ q) hagree
  rw [← Category.assoc] at H
  rw [morphismRestrict_ι] at H
  have H0 : V.ι ≫ g ≫ f' = (g ≫ p) ∣_ f.domain ≫ f.hom := by
    rw [morphismRestrict_comp]
    simpa [V, Q, Category.assoc] using H
  simpa [V, Q, Category.assoc] using H0

private lemma composite_rational_map_eq {k : Type u} [Field k] [PerfectField k]
    (W : SmoothProjectiveSurface k) (Y : AlgebraicGeometry.Scheme.{u})
    [Y.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.IsProper (Y ↘ AlgebraicGeometry.Spec (CommRingCat.of k))]
    [Y.IsSeparated]
    (φ : W.toScheme ⤏ Y) [φ.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (S : SmoothProjectiveSurface k) (β : S.toScheme ⟶ W.toScheme)
    (hβd : AlgebraicGeometry.IsDominant β)
    (X' : AlgebraicGeometry.Scheme.{u}) (p : X' ⟶ W.toScheme)
    (f' : X' ⟶ Y) (g : S.toScheme ⟶ X')
    (hfactor : g ≫ p = β)
    (hagree : (p ⁻¹ᵁ φ.domain).ι ≫ f' =
      (p ∣_ φ.domain) ≫ φ.toPartialMap.hom) :
    (g ≫ f').toRationalMap = (haveI := hβd; φ.precomp β) := by
  subst β
  let f : W.toScheme.PartialMap Y := φ.toPartialMap
  have hf_rmap : f.toRationalMap = φ :=
    AlgebraicGeometry.Scheme.RationalMap.toRationalMap_toPartialMap φ
  letI : AlgebraicGeometry.IsDominant (g ≫ p) := by infer_instance
  have hagree' : (p ⁻¹ᵁ f.domain).ι ≫ f' = (p ∣_ f.domain) ≫ f.hom := by
    change (p ⁻¹ᵁ φ.domain).ι ≫ f' = (p ∣_ φ.domain) ≫ φ.toPartialMap.hom
    exact hagree
  have hac := composite_agreement f g p f' hagree'
  have hc_hom : ((g ≫ p).toPartialMap.comp f).hom =
      ((g ≫ p).toPartialMap.comp f).domain.ι ≫ (g ≫ f') :=
    generic_pullback_hom_eq (g ≫ p) f (g ≫ f') hac
  let c : S.toScheme.PartialMap Y := (g ≫ p).toPartialMap.comp f
  let a : S.toScheme.PartialMap Y := (g ≫ f').toPartialMap
  have hle : c.domain ≤ a.domain := by simp [c, a]
  have hequiv : a.equiv c := by
    refine ⟨c.domain, c.dense_domain, hle, le_rfl, ?_⟩
    dsimp [PartialMap.restrict]
    simp only [Scheme.homOfLE_rfl, Category.id_comp]
    dsimp [a, c]
    simp only [PartialMap.comp_hom, Hom.toPartialMap_hom]
    have htop : S.toScheme.homOfLE hle ≫ a.domain.ι =
        ((g ≫ p).toPartialMap.comp f).domain.ι := by
      rw [← Scheme.homOfLE_ι S.toScheme hle]
    change S.toScheme.homOfLE hle ≫ a.domain.ι ≫ g ≫ f' = _
    rw [← Category.assoc, htop]
    exact hc_hom.symm
  have hrmap : a.toRationalMap = c.toRationalMap :=
    AlgebraicGeometry.Scheme.PartialMap.toRationalMap_eq_iff.mpr hequiv
  change a.toRationalMap = (haveI := hβd; φ.precomp (g ≫ p))
  rw [hrmap]
  change c.toRationalMap = (haveI := hβd; φ.precomp (g ≫ p))
  change c.toRationalMap = (g ≫ p).toRationalMap.comp φ
  calc
    c.toRationalMap = ((g ≫ p).toPartialMap.comp f).toRationalMap := by rfl
    _ = (g ≫ p).toPartialMap.toRationalMap.comp f.toRationalMap := by
      rw [AlgebraicGeometry.Scheme.RationalMap.toRationalMap_comp]
    _ = (g ≫ p).toRationalMap.comp φ := by rw [hf_rmap]

private lemma domain_complement_codim_two {k : Type u} [Field k] [PerfectField k]
    (W : SmoothProjectiveSurface k) (Y : AlgebraicGeometry.Scheme.{u})
    [Y.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.IsProper (Y ↘ AlgebraicGeometry.Spec (CommRingCat.of k))]
    (φ : W.toScheme ⤏ Y) [φ.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))] :
    ∀ z ∈ ((φ.domain : Set W.toScheme)ᶜ),
      2 ≤ ringKrullDim (W.toScheme.presheaf.stalk z) := by
  letI : AlgebraicGeometry.IsSeparated
      (Y ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    AlgebraicGeometry.IsProper.toIsSeparated
  letI : Y.IsSeparated := by
    constructor
    rw [← CategoryTheory.Limits.terminal.comp_from
      (Y ↘ AlgebraicGeometry.Spec (CommRingCat.of k))]
    infer_instance
  let f : W.toScheme.PartialMap Y := φ.toPartialMap
  have hf_rmap : f.toRationalMap = φ :=
    AlgebraicGeometry.Scheme.RationalMap.toRationalMap_toPartialMap φ
  haveI : AlgebraicGeometry.IsNoetherian W.toScheme := W.toVariety.isNoetherian
  haveI : AlgebraicGeometry.IsIntegral W.toScheme := by infer_instance
  haveI : AlgebraicGeometry.Scheme.IsRegular W.toScheme :=
    AlgebraicGeometry.isRegular_of_smoothOver W.toScheme W.toSmoothProjectiveVariety.smooth
  haveI : AlgebraicGeometry.Scheme.PartialMap.IsOver
      (AlgebraicGeometry.Spec (CommRingCat.of k)) f := by
    infer_instance
  intro z hz
  have hzdom : z ∉ f.domain := by
    change z ∉ φ.toPartialMap.domain
    exact hz
  have hgen : genericPoint W.toScheme ∈ f.domain := by
    obtain ⟨x, hx⟩ := f.dense_domain.nonempty
    exact (genericPoint_specializes x).mem_open f.domain.2 hx
  have hco0 : Order.coheight z ≠ 0 := by
    intro hzero
    have hmax : IsMax z := Order.coheight_eq_zero.mp hzero
    have hzg : genericPoint W.toScheme ≤ z :=
      hmax (AlgebraicGeometry.Scheme.le_iff_specializes.mpr (genericPoint_specializes z))
    have hgz : z ≤ genericPoint W.toScheme :=
      AlgebraicGeometry.Scheme.le_iff_specializes.mpr (genericPoint_specializes z)
    have hzgen : z = genericPoint W.toScheme :=
      Inseparable.eq ((genericPoint_specializes z).antisymm
        (AlgebraicGeometry.Scheme.le_iff_specializes.mp hzg)).symm
    exact hzdom (hzgen ▸ hgen)
  have hco1 : Order.coheight z ≠ 1 := by
    intro hone
    letI : IsRegularLocalRing (W.toScheme.presheaf.stalk z) :=
      AlgebraicGeometry.Scheme.IsRegular.isRegularLocalRing_stalk z
    have hdim1 : ringKrullDim (W.toScheme.presheaf.stalk z) = 1 := by
      rw [AlgebraicGeometry.ringKrullDim_stalk_eq_coheight, hone]
      norm_num
    -- Stacks 00PD: a 1-dimensional regular local ring is a DVR (`RegularLocalRingDVR`; the domain
    -- instance is `IsRegularLocalRing.isDomain` from `Stacks00np`).
    letI hdom : IsDomain (W.toScheme.presheaf.stalk z) := IsRegularLocalRing.isDomain _
    letI hdvr : IsDiscreteValuationRing (W.toScheme.presheaf.stalk z) :=
      MiyaokaMori.RingTheory.isDiscreteValuationRing_of_regularLocalRing_dimension_one _ hdim1
    letI hval : ValuationRing (W.toScheme.presheaf.stalk z) := inferInstance
    have hfbase : f.hom ≫ (Y ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
        f.domain.ι ≫ (W.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      AlgebraicGeometry.Scheme.PartialMap.isOver_iff.mp inferInstance
    have hzclosure : z ∈ closure (f.domain : Set W.toScheme) := by
      rw [f.dense_domain.closure_eq]
      trivial
    obtain ⟨U', hUU', f', hzU', hf'base, hrestrict⟩ :=
      AlgebraicGeometry.exists_extend_across_valuationRing_point
        (S := AlgebraicGeometry.Spec (CommRingCat.of k)) f.domain f.hom hfbase z hzclosure hval
    let g : W.toScheme.PartialMap Y :=
      { domain := U'
        dense_domain := Dense.mono (by exact hUU') f.dense_domain
        hom := f' }
    have hgequiv : g.equiv f := by
      refine ⟨f.domain, f.dense_domain, hUU', le_rfl, ?_⟩
      simp only [AlgebraicGeometry.Scheme.PartialMap.restrict_hom]
      dsimp [g]
      rw [hrestrict]
      simp
      rfl
    have hgrmap : g.toRationalMap = φ := by
      rw [AlgebraicGeometry.Scheme.PartialMap.toRationalMap_eq_iff.mpr hgequiv]
      exact hf_rmap
    have hzφ : z ∈ φ.domain :=
      AlgebraicGeometry.Scheme.RationalMap.mem_domain.mpr ⟨g, hzU', hgrmap⟩
    apply hzdom
    change z ∈ φ.domain
    exact hzφ
  have hdim : topologicalKrullDim W.toScheme = (2 : WithBot ℕ∞) := by
    have h := W.toVariety.dim_spec
    simpa [SmoothProjectiveSurface.toVariety, W.dim_eq_two] using h
  have hkrull : Order.krullDim W.toScheme = topologicalKrullDim W.toScheme :=
    (Order.krullDim_eq_of_orderIso
      (@irreducibleSetEquivPoints W.toScheme _ _ _ :
        TopologicalSpace.IrreducibleCloseds W.toScheme ≃o W.toScheme)).symm
  have hco' : (Order.coheight z : WithBot ℕ∞) ≤ 2 := by
    exact (Order.coheight_le_krullDim z).trans (by rw [hkrull, hdim])
  have hco : Order.coheight z ≤ (2 : ℕ∞) := WithBot.coe_le_coe.mp hco'
  have hco_top : Order.coheight z ≠ ⊤ := by
    intro ht
    rw [ht] at hco
    simp at hco
  lift Order.coheight z to ℕ using hco_top with c hc
  have hc_bound : c ≤ 2 := by exact_mod_cast hco
  have hc0 : c ≠ 0 := by
    intro hc0
    apply hco0
    simpa [hc0] using hc
  have hc1 : c ≠ 1 := by
    intro hc1
    apply hco1
    simpa [hc1] using hc
  rw [AlgebraicGeometry.ringKrullDim_stalk_eq_coheight z, ← hc]
  have hc_eq : c = 2 := by omega
  subst c
  simp

/-- Strengthened form of elimination of indeterminacy: besides the equality of rational maps, `Ψ` agrees
pointwise with `φ ∘ β` on all of `β⁻¹(dom φ)`. Assembled from `exists_resolving_tower_agree` (the base
ideal, Stacks 0AHH and Hartshorne II, Exercise 7.17.3); the set of indeterminacy points is a finite set of
closed points by `domain_complement_codim_two` and `closed_subset_codim_two_finite`. -/
theorem elimination_of_indeterminacy_agree {k : Type u} [Field k] [PerfectField k]
    (W : SmoothProjectiveSurface k) (Y : AlgebraicGeometry.Scheme.{u})
    [Y.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.IsProper (Y ↘ AlgebraicGeometry.Spec (CommRingCat.of k))]
    [Y.IsSeparated] (hY : IsProjectiveOver k Y)
    (φ : W.toScheme ⤏ Y) [φ.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (U : W.toScheme.Opens) (hU : IsRegularOn φ U) :
    ∃ (S : SmoothProjectiveSurface k) (β : S.toScheme ⟶ W.toScheme)
      (_ : IsBlowupTower β) (_ : IsBlowupTowerAvoiding β (U : Set W.toScheme))
      (hβd : AlgebraicGeometry.IsDominant β) (Ψ : S.toScheme ⟶ Y),
      Ψ.toRationalMap = (haveI := hβd; φ.precomp β) ∧
      (β ⁻¹ᵁ φ.domain).ι ≫ Ψ = (β ∣_ φ.domain) ≫ φ.toPartialMap.hom := by
  have hcodim := domain_complement_codim_two W Y φ
  have hclosed : IsClosed ((φ.domain : Set W.toScheme)ᶜ) := φ.domain.2.isClosed_compl
  have hfinite := closed_subset_codim_two_finite W ((φ.domain : Set W.toScheme)ᶜ)
    hclosed hcodim
  obtain ⟨S, β, hβ, havoidV, hβd, Ψ, hagree⟩ :=
    exists_resolving_tower_agree W Y hY φ hfinite.1 hfinite.2
  have havoidU : IsBlowupTowerAvoiding β (U : Set W.toScheme) := by
    unfold IsBlowupTowerAvoiding at *
    apply MiyaokaMori.Statement.IsPointBlowupSequenceOver.mono havoidV
    intro x hx hxU
    exact hx (hU hxU)
  refine ⟨S, β, hβ, havoidU, hβd, Ψ, ?_, hagree⟩
  have h := composite_rational_map_eq W Y φ S β hβd S.toScheme β Ψ (𝟙 S.toScheme)
    (Category.id_comp β) hagree
  rwa [Category.id_comp] at h

/-- **Elimination of indeterminacy** (Debarre, Theorem 5.18): a rational map `φ : W ⇢ Y` from a smooth
projective surface to a projective `k`-scheme, regular on `U`, becomes a morphism after a tower of point
blowups `β : S → W` whose centres avoid `U`. -/
theorem elimination_of_indeterminacy {k : Type u} [Field k] [PerfectField k]
    (W : SmoothProjectiveSurface k) (Y : AlgebraicGeometry.Scheme.{u})
    [Y.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.IsProper (Y ↘ AlgebraicGeometry.Spec (CommRingCat.of k))]
    (hY : IsProjectiveOver k Y)
    (φ : W.toScheme ⤏ Y) [φ.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (U : W.toScheme.Opens) (hU : IsRegularOn φ U) :
    ∃ (S : SmoothProjectiveSurface k) (β : S.toScheme ⟶ W.toScheme)
      (_ : IsBlowupTower β) (_ : IsBlowupTowerAvoiding β (U : Set W.toScheme))
      (hβd : AlgebraicGeometry.IsDominant β) (Ψ : S.toScheme ⟶ Y),
      Ψ.toRationalMap = (haveI := hβd; φ.precomp β) := by
  haveI : Y.IsSeparated := AlgebraicGeometry.Scheme.isSeparated_of_isProper_over_field (k := k) Y
  obtain ⟨S, β, hβ, havoid, hβd, Ψ, hΨ, -⟩ := elimination_of_indeterminacy_agree W Y hY φ U hU
  exact ⟨S, β, hβ, havoid, hβd, Ψ, hΨ⟩

end
