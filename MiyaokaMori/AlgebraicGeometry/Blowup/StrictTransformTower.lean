import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.CurveDimensionOne
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProjectiveOverField
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.VarietyDimension
import MiyaokaMori.AlgebraicGeometry.Blowup.BlowupIsoAwayFromCenter
import MiyaokaMori.AlgebraicGeometry.Blowup.BlowupTower
import MiyaokaMori.AlgebraicGeometry.Blowup.BlowupTowerIsOver
import MiyaokaMori.AlgebraicGeometry.Morphisms.DimensionLtOfProperClosedIntegral
import MiyaokaMori.AlgebraicGeometry.Varieties.Surfaces.PointBlowupSurface
import MiyaokaMori.AlgebraicGeometry.Varieties.Surfaces.SmoothProjectiveSurface
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.IntegralCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.SchemeDimensionFinite
import MiyaokaMori.AlgebraicGeometry.Varieties.Points.ReducedPointClosure

/-! # The strict transform of an integral curve under a tower of point blowups

The strict transform of an integral curve `Γ ⊆ W` under a tower of point blowups `β : S → W`
(iterating the single-step strict transform along the tower). Used for the exceptional curves and the
strict transform of the section in Proposition 6.1 of the paper (§6).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The exceptional locus of the tower `β`: the points of `S` contracted by `β`, defined intrinsically as
the preimage of the complement of the largest open set `V_β` over which `β` is an isomorphism (no
recursion on the `Prop`-valued `hβ`). -/
noncomputable def ExceptionalLocus {k : Type u} [Field k] [PerfectField k] {S W : SmoothProjectiveSurface k}
    (β : S.toScheme ⟶ W.toScheme) (hβ : IsBlowupTower β) : Set S.toScheme :=
  β.base ⁻¹' ((⨆ (V : W.toScheme.Opens) (_ : IsIso (β ∣_ V)), V : W.toScheme.Opens) : Set W.toScheme)ᶜ

/-- The centres of the tower: the images in `W` of the exceptional locus. -/
noncomputable def ExceptionalCenters {k : Type u} [Field k] [PerfectField k] {S W : SmoothProjectiveSurface k}
    (β : S.toScheme ⟶ W.toScheme) (hβ : IsBlowupTower β) : Set W.toScheme :=
  β.base '' (ExceptionalLocus β hβ)

/-- The ideal sheaf of the closure model: the vanishing ideal of `T := closure(β⁻¹Γ ∖ ExceptionalLocus)`. -/

noncomputable def strictTransformTower.ideal {k : Type u} [Field k] [PerfectField k] {S W : SmoothProjectiveSurface k}
    (β : S.toScheme ⟶ W.toScheme) (hβ : IsBlowupTower β)
    (Γ : IntegralCurve k W.toScheme) : S.toScheme.IdealSheafData :=
  AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal
    ⟨closure (β.base ⁻¹' (Set.range Γ.ι.base) \ ExceptionalLocus β hβ), isClosed_closure⟩

/-! ## Auxiliary lemmas for well-definedness

Route:
* `IsoLocus β`: the largest open set `V_β` over which `β` is an isomorphism (the `iSup` in the definition
  of `ExceptionalLocus`); `isIso_restrict_isoLocus`: being an isomorphism is Zariski-local on the target,
  so `β ∣_ V_β` is an isomorphism.
* `IsBlowupTower.exists_finite_closed_centers`: by induction along the tower there is a finite set of
  closed points `C ⊆ W` such that `β` is an isomorphism over every open set disjoint from `C` (a single
  step uses `pointBlowup_isIso_away`; the image of a centre is a closed point because the tower is proper,
  `IsBlowupTower.isProper_strictTransform`). Hence `(V_β)ᶜ ⊆ C`.
* The generic point of `Γ` is not closed (`dim Γ = 1`), so it lies in `V_β`; `β⁻¹Γ ∖ Exc = β⁻¹(Γ ∩ V_β)` is
  homeomorphic via `β ∣_ V_β` to `Γ ∩ V_β`, a nonempty open subset of the irreducible `Γ`, hence
  irreducible; so its closure `T` is irreducible.
-/

/-- The isomorphism locus `V_β` of `β`: the largest open set over which `β` is an isomorphism (the `iSup`
in the definition of `ExceptionalLocus`). -/
noncomputable def IsoLocus {k : Type u} [Field k] [PerfectField k] {S W : SmoothProjectiveSurface k}
    (β : S.toScheme ⟶ W.toScheme) : W.toScheme.Opens :=
  ⨆ (V : W.toScheme.Opens) (_ : IsIso (β ∣_ V)), V

theorem exceptionalLocus_eq {k : Type u} [Field k] [PerfectField k] {S W : SmoothProjectiveSurface k}
    (β : S.toScheme ⟶ W.toScheme) (hβ : IsBlowupTower β) :
    ExceptionalLocus β hβ = β.base ⁻¹' ((IsoLocus β : Set W.toScheme)ᶜ) := rfl

theorem le_isoLocus {k : Type u} [Field k] [PerfectField k] {S W : SmoothProjectiveSurface k}
    (β : S.toScheme ⟶ W.toScheme) {V : W.toScheme.Opens} (hV : IsIso (β ∣_ V)) :
    V ≤ IsoLocus β :=
  le_iSup₂ (f := fun (V : W.toScheme.Opens) (_ : IsIso (β ∣_ V)) => V) V hV

theorem mem_isoLocus_iff {k : Type u} [Field k] [PerfectField k] {S W : SmoothProjectiveSurface k}
    (β : S.toScheme ⟶ W.toScheme) {x : W.toScheme} :
    x ∈ IsoLocus β ↔ ∃ V : W.toScheme.Opens, IsIso (β ∣_ V) ∧ x ∈ V := by
  unfold IsoLocus
  simp only [TopologicalSpace.Opens.mem_iSup]
  exact ⟨fun ⟨V, h, hx⟩ => ⟨V, h, hx⟩, fun ⟨V, h, hx⟩ => ⟨V, h, hx⟩⟩

/-- Being an isomorphism is Zariski-local on the target: `β` is an isomorphism over `V_β`. -/
theorem isIso_restrict_isoLocus {k : Type u} [Field k] [PerfectField k] {S W : SmoothProjectiveSurface k}
    (β : S.toScheme ⟶ W.toScheme) : IsIso (β ∣_ IsoLocus β) := by
  rw [← MorphismProperty.isomorphisms.iff]
  apply AlgebraicGeometry.IsZariskiLocalAtTarget.of_forall_exists_morphismRestrict
  intro x
  obtain ⟨V, hV, hxV⟩ := (mem_isoLocus_iff β).mp x.2
  refine ⟨(IsoLocus β).ι ⁻¹ᵁ V, hxV, ?_⟩
  rw [MorphismProperty.arrow_mk_iso_iff (P := MorphismProperty.isomorphisms AlgebraicGeometry.Scheme)
    (AlgebraicGeometry.morphismRestrictRestrict β (IsoLocus β) ((IsoLocus β).ι ⁻¹ᵁ V))]
  have h : (IsoLocus β).ι ''ᵁ ((IsoLocus β).ι ⁻¹ᵁ V) = V := by
    rw [AlgebraicGeometry.Scheme.Hom.image_preimage_eq_opensRange_inf,
      AlgebraicGeometry.Scheme.Opens.opensRange_ι]
    exact inf_eq_right.mpr (le_isoLocus β hV)
  rw [h]
  exact hV

theorem isoLocus_homeomorph_apply {k : Type u} [Field k] [PerfectField k] {S W : SmoothProjectiveSurface k}
    (β : S.toScheme ⟶ W.toScheme) (u : (β ⁻¹ᵁ IsoLocus β).toScheme) :
    haveI := isIso_restrict_isoLocus β
    ((β ∣_ IsoLocus β).homeomorph u).1 = β.base u.1 := by
  have := isIso_restrict_isoLocus β
  rw [AlgebraicGeometry.Scheme.Hom.homeomorph_apply]
  exact AlgebraicGeometry.morphismRestrict_base_coe β _ u

/-- A tower of point blowups is proper: `β` is a `k`-morphism (`IsBlowupTower.isOver`), `S` is proper over
`k` and `W` is separated over `k`. -/
theorem IsBlowupTower.isProper_strictTransform {k : Type u} [Field k] [PerfectField k] {S W : SmoothProjectiveSurface k}
    {β : S.toScheme ⟶ W.toScheme} (hβ : IsBlowupTower β) : AlgebraicGeometry.IsProper β := by
  have := hβ.isOver
  have : AlgebraicGeometry.IsProper (S.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ((isProjectiveOver_iff_isProper_and_isAmple k _).mp S.toSmoothProjectiveVariety.projective).1
  have h : β ≫ (W.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      S.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k) := by
    exact (hβ.isOver).comp_over
  have : AlgebraicGeometry.IsProper (β ≫ (W.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) := by
    rw [h]; infer_instance
  exact AlgebraicGeometry.IsProper.of_comp (f := β) (g := W.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))

/-- The centres of the tower: there is a finite set of closed points `C ⊆ W` such that `β` is an isomorphism
over every open set disjoint from `C`. Induction along the tower: for the identity take `C = ∅`; for
`β = π_p ≫ g` take `C = C_g ∪ {g p}` (`g p` is closed since `g` is proper, hence a closed map); over an open
`V` disjoint from it, `β ∣_ V = (π_p ∣_ g⁻¹V) ≫ (g ∣_ V)`, whose factors are isomorphisms by
`pointBlowup_isIso_away` (`p ∉ g⁻¹V`) and the induction hypothesis. -/
theorem IsBlowupTower.exists_finite_closed_centers {k : Type u} [Field k] [PerfectField k]
    {S W : SmoothProjectiveSurface k} {β : S.toScheme ⟶ W.toScheme} (hβ : IsBlowupTower β) :
    ∃ C : Set W.toScheme, C.Finite ∧ (∀ c ∈ C, IsClosed ({c} : Set W.toScheme)) ∧
      ∀ V : W.toScheme.Opens, Disjoint (V : Set W.toScheme) C → IsIso (β ∣_ V) := by
  induction hβ with
  | id W =>
    refine ⟨∅, Set.finite_empty, by simp, fun V _ => ?_⟩
    have h : MorphismProperty.isomorphisms AlgebraicGeometry.Scheme (𝟙 W.toScheme ∣_ V) :=
      AlgebraicGeometry.IsZariskiLocalAtTarget.restrict
        (P := MorphismProperty.isomorphisms AlgebraicGeometry.Scheme)
        (inferInstance : IsIso (𝟙 W.toScheme)) V
    exact h
  | step g hg p hp ih =>
    obtain ⟨C, hCfin, hCcl, hC⟩ := ih
    refine ⟨insert (g.base p) C, hCfin.insert _, ?_, fun V hV => ?_⟩
    · intro c hc
      rcases Set.mem_insert_iff.mp hc with rfl | hc
      · have := hg.isProper_strictTransform
        have := g.isClosedMap _ hp
        rwa [Set.image_singleton] at this
      · exact hCcl c hc
    · rw [AlgebraicGeometry.morphismRestrict_comp]
      have : IsIso (g ∣_ V) := hC V (hV.mono_right (Set.subset_insert _ _))
      have : IsIso (pointBlowup.π _ p hp ∣_ (g ⁻¹ᵁ V)) := by
        apply pointBlowup_isIso_away
        intro hpV
        exact Set.disjoint_left.mp hV hpV (Set.mem_insert _ _)
      exact inferInstanceAs (IsIso (pointBlowup.π _ p hp ∣_ (g ⁻¹ᵁ V) ≫ g ∣_ V))

/-- `(V_β)ᶜ` is contained in a finite set of closed points. -/
theorem IsBlowupTower.compl_isoLocus_subset {k : Type u} [Field k] [PerfectField k]
    {S W : SmoothProjectiveSurface k} {β : S.toScheme ⟶ W.toScheme} (hβ : IsBlowupTower β) :
    ∃ C : Set W.toScheme, C.Finite ∧ (∀ c ∈ C, IsClosed ({c} : Set W.toScheme)) ∧
      ((IsoLocus β : Set W.toScheme))ᶜ ⊆ C := by
  obtain ⟨C, hfin, hcl, hC⟩ := hβ.exists_finite_closed_centers
  have hCcl : IsClosed C := by
    rw [← Set.biUnion_of_singleton C]
    exact hfin.isClosed_biUnion hcl
  have hiso : IsIso (β ∣_ ⟨Cᶜ, hCcl.isOpen_compl⟩) := hC _ disjoint_compl_left
  refine ⟨C, hfin, hcl, fun x hx => ?_⟩
  by_contra hxC
  exact hx (le_isoLocus β hiso hxC)

/-! Natural numbers in `WithBot ℕ∞`: three conversion lemmas (all reduce to `ℕ` via `WithBot.coe_injective`
/ `WithBot.coe_le_coe`). -/

theorem withBot_enat_natCast_le_iff {m n : ℕ} :
    ((m : ℕ∞) : WithBot ℕ∞) ≤ ((n : ℕ∞) : WithBot ℕ∞) ↔ m ≤ n := by
  rw [WithBot.coe_le_coe]; exact Nat.cast_le

theorem withBot_enat_natCast_inj {m n : ℕ}
    (h : ((m : ℕ∞) : WithBot ℕ∞) = ((n : ℕ∞) : WithBot ℕ∞)) : m = n :=
  Nat.cast_injective (WithBot.coe_injective h)

theorem withBot_enat_natCast_ne_top (n : ℕ) : ((n : ℕ∞) : WithBot ℕ∞) ≠ ⊤ := fun h =>
  ENat.natCast_ne_top n (WithBot.coe_injective h)

/-- A space with at most one point has topological Krull dimension `≤ 0`. -/
theorem topologicalKrullDim_nonpos_of_subsingleton (X : Type*) [TopologicalSpace X] [Subsingleton X] :
    topologicalKrullDim X ≤ 0 := by
  refine Order.krullDim_nonpos_iff_forall_isMax.mpr fun Z Y _ y _ => ?_
  obtain ⟨z, hz⟩ := Z.isIrreducible.nonempty
  exact (Subsingleton.elim y z) ▸ hz

/-- The generic point of a one-dimensional integral curve is not a closed point of `X`: if it were,
`Γ = closure{η} = {η}` would be a single point, of dimension `0 ≠ 1`. -/
theorem IntegralCurve.not_isClosed_genericPoint {k : Type u} [Field k] {X : AlgebraicGeometry.Scheme.{u}}
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (Γ : IntegralCurve k X) :
    ¬ IsClosed ({Γ.ι.base (genericPoint Γ.carrier)} : Set X) := by
  intro hcl
  have h1 : IsClosed ({genericPoint Γ.carrier} : Set Γ.carrier) := by
    have := hcl.preimage Γ.ι.base.hom.continuous
    rwa [← Set.image_singleton, Γ.ι.isClosedEmbedding.injective.preimage_image] at this
  have h2 : ({genericPoint Γ.carrier} : Set Γ.carrier) = Set.univ := by
    rw [← h1.closure_eq]
    exact genericPoint_closure _
  have : Subsingleton Γ.carrier := Set.subsingleton_univ_iff.mp (h2 ▸ Set.subsingleton_singleton)
  have h3 := topologicalKrullDim_nonpos_of_subsingleton Γ.carrier
  have h4 : topologicalKrullDim Γ.carrier = 1 := Γ.dim_eq_one
  rw [h4] at h3
  have h5 : (((1 : ℕ) : ℕ∞) : WithBot ℕ∞) ≤ (((0 : ℕ) : ℕ∞) : WithBot ℕ∞) := h3
  have h6 := withBot_enat_natCast_le_iff.mp h5
  omega

/-- The generic point of `Γ` lies in `V_β` (as `(V_β)ᶜ` consists of closed points). -/
theorem genericPoint_mem_isoLocus {k : Type u} [Field k] [PerfectField k] {S W : SmoothProjectiveSurface k}
    (β : S.toScheme ⟶ W.toScheme) (hβ : IsBlowupTower β) (Γ : IntegralCurve k W.toScheme) :
    Γ.ι.base (genericPoint Γ.carrier) ∈ IsoLocus β := by
  obtain ⟨C, _, hcl, hsub⟩ := hβ.compl_isoLocus_subset
  by_contra h
  exact Γ.not_isClosed_genericPoint (hcl _ (hsub h))

/-- `β⁻¹Γ ∖ Exc` is the image of `Γ ∩ V_β` under the homeomorphism induced by `β ∣_ V_β`. -/
theorem sdiff_exceptionalLocus_eq {k : Type u} [Field k] [PerfectField k] {S W : SmoothProjectiveSurface k}
    (β : S.toScheme ⟶ W.toScheme) (hβ : IsBlowupTower β) (Γ : IntegralCurve k W.toScheme) :
    haveI := isIso_restrict_isoLocus β
    β.base ⁻¹' (Set.range Γ.ι.base) \ ExceptionalLocus β hβ =
      (fun u : (β ⁻¹ᵁ IsoLocus β).toScheme => (u.1 : S.toScheme)) ''
        ((β ∣_ IsoLocus β).homeomorph.symm ''
          ((fun v : (IsoLocus β).toScheme => (v.1 : W.toScheme)) ⁻¹' Set.range Γ.ι.base)) := by
  have := isIso_restrict_isoLocus β
  ext x
  rw [exceptionalLocus_eq]
  constructor
  · rintro ⟨hx1, hx2⟩
    have hxV : β.base x ∈ IsoLocus β := not_not.mp hx2
    let u : (β ⁻¹ᵁ IsoLocus β).toScheme := ⟨x, hxV⟩
    refine ⟨u, ⟨(β ∣_ IsoLocus β).homeomorph u, ?_, Homeomorph.symm_apply_apply _ _⟩, rfl⟩
    show ((β ∣_ IsoLocus β).homeomorph u).1 ∈ Set.range Γ.ι.base
    rw [isoLocus_homeomorph_apply]
    exact hx1
  · rintro ⟨u, ⟨v, hv, rfl⟩, rfl⟩
    have h := isoLocus_homeomorph_apply β ((β ∣_ IsoLocus β).homeomorph.symm v)
    rw [Homeomorph.apply_symm_apply] at h
    refine ⟨?_, ?_⟩
    · show β.base _ ∈ Set.range Γ.ι.base
      rw [← h]; exact hv
    · show β.base _ ∉ (IsoLocus β : Set W.toScheme)ᶜ
      rw [← h]; exact not_not.mpr v.2

theorem isIrreducible_range_ι {k : Type u} [Field k] {X : AlgebraicGeometry.Scheme.{u}}
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (Γ : IntegralCurve k X) :
    IsIrreducible (Set.range Γ.ι.base) := by
  have := (IrreducibleSpace.isIrreducible_univ Γ.carrier).image Γ.ι.base
    Γ.ι.base.hom.continuous.continuousOn
  rwa [Set.image_univ] at this

/-- `β⁻¹Γ ∖ Exc` is irreducible. -/
theorem isIrreducible_sdiff_exceptionalLocus {k : Type u} [Field k] [PerfectField k]
    {S W : SmoothProjectiveSurface k} (β : S.toScheme ⟶ W.toScheme) (hβ : IsBlowupTower β)
    (Γ : IntegralCurve k W.toScheme) :
    IsIrreducible (β.base ⁻¹' (Set.range Γ.ι.base) \ ExceptionalLocus β hβ) := by
  have := isIso_restrict_isoLocus β
  rw [sdiff_exceptionalLocus_eq β hβ Γ]
  have hη := genericPoint_mem_isoLocus β hβ Γ
  have h1 : IsIrreducible ((fun v : (IsoLocus β).toScheme => (v.1 : W.toScheme)) ⁻¹'
      Set.range Γ.ι.base) :=
    (isIrreducible_range_ι Γ).preimage (IsoLocus β).isOpen.isOpenEmbedding_subtypeVal
      ⟨Γ.ι.base (genericPoint Γ.carrier), ⟨_, rfl⟩, ⟨⟨_, hη⟩, rfl⟩⟩
  exact (h1.image _ (β ∣_ IsoLocus β).homeomorph.symm.continuous.continuousOn).image _
    continuous_subtype_val.continuousOn

/-- There is a point `x₀ ∈ β⁻¹Γ ∖ Exc` with `β x₀` the generic point of `Γ`. -/
theorem exists_mem_sdiff_exceptionalLocus {k : Type u} [Field k] [PerfectField k]
    {S W : SmoothProjectiveSurface k} (β : S.toScheme ⟶ W.toScheme) (hβ : IsBlowupTower β)
    (Γ : IntegralCurve k W.toScheme) :
    ∃ x₀ ∈ β.base ⁻¹' (Set.range Γ.ι.base) \ ExceptionalLocus β hβ,
      β.base x₀ = Γ.ι.base (genericPoint Γ.carrier) := by
  have := isIso_restrict_isoLocus β
  have hη := genericPoint_mem_isoLocus β hβ Γ
  let v : (IsoLocus β).toScheme := ⟨_, hη⟩
  have h := isoLocus_homeomorph_apply β ((β ∣_ IsoLocus β).homeomorph.symm v)
  rw [Homeomorph.apply_symm_apply] at h
  refine ⟨((β ∣_ IsoLocus β).homeomorph.symm v).1, ⟨?_, ?_⟩, h.symm⟩
  · show β.base _ ∈ Set.range Γ.ι.base
    rw [← h]; exact ⟨_, rfl⟩
  · rw [exceptionalLocus_eq]
    show β.base _ ∉ (IsoLocus β : Set W.toScheme)ᶜ
    rw [← h]; exact not_not.mpr hη

/-- If the image of a closed embedding is irreducible, so is the source. -/
theorem irreducibleSpace_of_isClosedEmbedding_range {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : X → Y} (hf : Topology.IsClosedEmbedding f) (h : IsIrreducible (Set.range f)) :
    IrreducibleSpace X := by
  refine { toPreirreducibleSpace := ⟨?_⟩, toNonempty := ?_ }
  · rw [isPreirreducible_iff_isClosed_union_isClosed]
    intro Z₁ Z₂ h₁ h₂ hcov
    have hcov' : Set.range f ⊆ f '' Z₁ ∪ f '' Z₂ := by
      rintro _ ⟨x, rfl⟩
      rcases hcov (Set.mem_univ x) with hx | hx
      · exact Or.inl ⟨x, hx, rfl⟩
      · exact Or.inr ⟨x, hx, rfl⟩
    rcases (isPreirreducible_iff_isClosed_union_isClosed.mp h.isPreirreducible) _ _
      (hf.isClosedMap _ h₁) (hf.isClosedMap _ h₂) hcov' with hs | hs
    · left
      intro x _
      obtain ⟨x', hx', hxx'⟩ := hs ⟨x, rfl⟩
      exact hf.injective hxx' ▸ hx'
    · right
      intro x _
      obtain ⟨x', hx', hxx'⟩ := hs ⟨x, rfl⟩
      exact hf.injective hxx' ▸ hx'
  · obtain ⟨_, x, rfl⟩ := h.nonempty
    exact ⟨x⟩

theorem strictTransformTower.range_subschemeι {k : Type u} [Field k] [PerfectField k]
    {S W : SmoothProjectiveSurface k} (β : S.toScheme ⟶ W.toScheme) (hβ : IsBlowupTower β)
    (Γ : IntegralCurve k W.toScheme) :
    Set.range (strictTransformTower.ideal β hβ Γ).subschemeι.base
      = closure (β.base ⁻¹' (Set.range Γ.ι.base) \ ExceptionalLocus β hβ) :=
  (AlgebraicGeometry.Scheme.IdealSheafData.range_subschemeι _).trans
    (AlgebraicGeometry.Scheme.IdealSheafData.coe_support_vanishingIdeal _)

/-- `T ≠ S`: otherwise `V_β ⊆ Γ`, so the generic point of `W` lies in `Γ` or in the finite set of closed
points `C`; both cases give `Γ = W`, contradicting `dim Γ = 1 ≠ 2 = dim W`. -/
theorem closure_sdiff_exceptionalLocus_ne_univ {k : Type u} [Field k] [PerfectField k]
    {S W : SmoothProjectiveSurface k} (β : S.toScheme ⟶ W.toScheme) (hβ : IsBlowupTower β)
    (Γ : IntegralCurve k W.toScheme) :
    closure (β.base ⁻¹' (Set.range Γ.ι.base) \ ExceptionalLocus β hβ) ≠ Set.univ := by
  intro huniv
  have := isIso_restrict_isoLocus β
  have hsub : closure (β.base ⁻¹' (Set.range Γ.ι.base) \ ExceptionalLocus β hβ) ⊆
      β.base ⁻¹' (Set.range Γ.ι.base) :=
    closure_minimal Set.sdiff_subset (Γ.ι.isClosedEmbedding.isClosed_range.preimage β.base.hom.continuous)
  have hV : (IsoLocus β : Set W.toScheme) ⊆ Set.range Γ.ι.base := by
    intro w hw
    let v : (IsoLocus β).toScheme := ⟨w, hw⟩
    have h := isoLocus_homeomorph_apply β ((β ∣_ IsoLocus β).homeomorph.symm v)
    rw [Homeomorph.apply_symm_apply] at h
    have hu := hsub (huniv ▸ Set.mem_univ ((β ∣_ IsoLocus β).homeomorph.symm v).1)
    show w ∈ Set.range Γ.ι.base
    have h' : w = β.base ((β ∣_ IsoLocus β).homeomorph.symm v).1 := h
    rw [h']; exact hu
  obtain ⟨C, _, hcl, hC⟩ := hβ.compl_isoLocus_subset
  have hΓuniv : Set.range Γ.ι.base = Set.univ := by
    by_cases hη : genericPoint W.toScheme ∈ IsoLocus β
    · apply Set.eq_univ_of_univ_subset
      rw [← genericPoint_closure W.toScheme]
      exact closure_minimal (Set.singleton_subset_iff.mpr (hV hη)) Γ.ι.isClosedEmbedding.isClosed_range
    · have hcl' : IsClosed ({genericPoint W.toScheme} : Set W.toScheme) := hcl _ (hC hη)
      have hsing : ({genericPoint W.toScheme} : Set W.toScheme) = Set.univ := by
        rw [← hcl'.closure_eq]; exact genericPoint_closure _
      apply Set.eq_univ_of_univ_subset
      rw [← hsing]
      intro w hw
      obtain ⟨γ⟩ : Nonempty Γ.carrier := inferInstance
      have hγ : Γ.ι.base γ ∈ ({genericPoint W.toScheme} : Set W.toScheme) := hsing ▸ Set.mem_univ _
      rw [Set.mem_singleton_iff] at hγ hw
      rw [hw, ← hγ]; exact ⟨γ, rfl⟩
  have hhomeo : IsHomeomorph Γ.ι.base :=
    isHomeomorph_iff_isEmbedding_surjective.mpr
      ⟨Γ.ι.isClosedEmbedding.isEmbedding, Set.range_eq_univ.mp hΓuniv⟩
  have h1 := hhomeo.topologicalKrullDim_eq
  have hΓ : topologicalKrullDim Γ.carrier = 1 := Γ.dim_eq_one
  have hW : topologicalKrullDim W.toScheme = 2 := by
    have := Variety.dim_spec W.toSmoothProjectiveVariety.toVariety
    rw [W.dim_eq_two] at this
    exact this
  rw [hΓ, hW] at h1
  have h2 : (((1 : ℕ) : ℕ∞) : WithBot ℕ∞) = (((2 : ℕ) : ℕ∞) : WithBot ℕ∞) := h1
  have h3 := withBot_enat_natCast_inj h2
  omega

/- The two properties of the strict transform (integral, one-dimensional), stated as separate theorems. -/

/-- Integrality of the strict transform: `β` is an isomorphism away from the exceptional locus, so
`β⁻¹Γ ∖ Exc ≅ Γ ∖ (centres)` is irreducible, hence so is its closure; irreducibility is transported to the
subscheme along the closed embedding `subschemeι` (`irreducibleSpace_of_isClosedEmbedding_range`), and the
induced reduced structure gives reducedness
(`AlgebraicGeometry.Intersection.ReducedPointClosure.vanishingIdeal_subscheme_isReduced`). -/
theorem strictTransformTower.ideal_subscheme_isIntegral {k : Type u} [Field k] [PerfectField k] {S W : SmoothProjectiveSurface k}
    (β : S.toScheme ⟶ W.toScheme) (hβ : IsBlowupTower β)
    (Γ : IntegralCurve k W.toScheme) :
    AlgebraicGeometry.IsIntegral (strictTransformTower.ideal β hβ Γ).subscheme := by
  have : AlgebraicGeometry.IsReduced (strictTransformTower.ideal β hβ Γ).subscheme :=
    AlgebraicGeometry.Intersection.ReducedPointClosure.vanishingIdeal_subscheme_isReduced _
  have : IrreducibleSpace (strictTransformTower.ideal β hβ Γ).subscheme := by
    refine irreducibleSpace_of_isClosedEmbedding_range
      (strictTransformTower.ideal β hβ Γ).subschemeι.isClosedEmbedding ?_
    have h := (isIrreducible_sdiff_exceptionalLocus β hβ Γ).closure
    rwa [← strictTransformTower.range_subschemeι β hβ Γ] at h
  exact AlgebraicGeometry.isIntegral_of_irreducibleSpace_of_isReduced _

/-- The strict transform is one-dimensional (it is birational to the curve `Γ`).
Lower bound: `T` is a nonempty closed subset of the proper surface `S`, so it contains a closed point `x`
(`IsClosed.exists_closed_singleton`); it also contains a point `x₀` with `β x₀` the generic point of `Γ`
(`exists_mem_sdiff_exceptionalLocus`), and `x₀ ≠ x` (otherwise the closed map `β` would send the closed
point `x` to the generic point of `Γ`, contradicting `IntegralCurve.not_isClosed_genericPoint`); so
`{x} ⊊ T` is a chain of irreducible closed sets of length `1`.
Upper bound: `T ≠ S` (`closure_sdiff_exceptionalLocus_ne_univ`), and
`dimension_lt_of_isClosedImmersion_of_range_ne_univ` gives `dim T < dim S = 2`. -/
theorem strictTransformTower.ideal_subscheme_dim_eq_one {k : Type u} [Field k] [PerfectField k] {S W : SmoothProjectiveSurface k}
    (β : S.toScheme ⟶ W.toScheme) (hβ : IsBlowupTower β)
    (Γ : IntegralCurve k W.toScheme) :
    SchemeIsOneDimensional (strictTransformTower.ideal β hβ Γ).subscheme := by
  set I := strictTransformTower.ideal β hβ Γ with hI
  have hrange := strictTransformTower.range_subschemeι β hβ Γ
  have hint : AlgebraicGeometry.IsIntegral I.subscheme := strictTransformTower.ideal_subscheme_isIntegral β hβ Γ
  obtain ⟨x₀, hx₀A, hx₀β⟩ := exists_mem_sdiff_exceptionalLocus β hβ Γ
  have hx₀T : x₀ ∈ closure (β.base ⁻¹' (Set.range Γ.ι.base) \ ExceptionalLocus β hβ) := subset_closure hx₀A
  have hSproper : AlgebraicGeometry.IsProper (S.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ((isProjectiveOver_iff_isProper_and_isAmple k _).mp S.toSmoothProjectiveVariety.projective).1
  have : CompactSpace S.toScheme :=
    AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace
      (S.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
  obtain ⟨x, hxT, hxcl⟩ := (isClosed_closure (s := β.base ⁻¹' (Set.range Γ.ι.base) \ ExceptionalLocus β hβ)).exists_closed_singleton ⟨x₀, hx₀T⟩
  have hx_ne : x ≠ x₀ := by
    rintro rfl
    apply Γ.not_isClosed_genericPoint
    rw [← hx₀β, ← Set.image_singleton]
    have := hβ.isProper_strictTransform
    exact β.isClosedMap _ hxcl
  obtain ⟨x', hx'⟩ : x ∈ Set.range I.subschemeι.base := hrange ▸ hxT
  obtain ⟨x₀', hx₀'⟩ : x₀ ∈ Set.range I.subschemeι.base := hrange ▸ hx₀T
  have hx'cl : IsClosed ({x'} : Set I.subscheme) := by
    have := hxcl.preimage I.subschemeι.base.hom.continuous
    rwa [← hx', ← Set.image_singleton, I.subschemeι.isClosedEmbedding.injective.preimage_image] at this
  -- lower bound
  have hlow : (1 : WithBot ℕ∞) ≤ topologicalKrullDim I.subscheme := by
    refine Order.one_le_krullDim_iff.mpr
      ⟨⟨{x'}, isIrreducible_singleton, hx'cl⟩, ⟨Set.univ, IrreducibleSpace.isIrreducible_univ _, isClosed_univ⟩, ?_⟩
    refine lt_of_le_of_ne (fun _ _ => Set.mem_univ _) ?_
    intro heq
    have h := congrArg (fun Z : IrreducibleCloseds I.subscheme => (Z : Set I.subscheme)) heq
    simp only [IrreducibleCloseds.coe_mk] at h
    have hmem : x₀' ∈ ({x'} : Set I.subscheme) := by rw [h]; trivial
    exact hx_ne (by rw [← hx', ← hx₀', Set.mem_singleton_iff.mp hmem])
  -- upper bound
  have hS2 : S.toScheme.dimension = 2 := S.dim_eq_two
  have hne : Set.range I.subschemeι.base ≠ Set.univ := by
    rw [hrange]; exact closure_sdiff_exceptionalLocus_ne_univ β hβ Γ
  have hlt := AlgebraicGeometry.Scheme.dimension_lt_of_isClosedImmersion_of_range_ne_univ (K := k)
    hSproper I.subschemeι hne
  rw [hS2] at hlt
  have : Nonempty I.subscheme := ⟨x'⟩
  have hSdim : topologicalKrullDim S.toScheme = 2 := by
    have := Variety.dim_spec S.toSmoothProjectiveVariety.toVariety
    rw [S.dim_eq_two] at this
    exact this
  have hfin : topologicalKrullDim I.subscheme ≠ ⊤ := by
    intro h
    have := I.subschemeι.isClosedEmbedding.isInducing.topologicalKrullDim_le
    rw [h, hSdim] at this
    exact withBot_enat_natCast_ne_top 2 (top_le_iff.mp this)
  have hspec := AlgebraicGeometry.Scheme.topologicalKrullDim_eq_dimension I.subscheme hfin
  rw [hspec] at hlow
  have hlow' : (((1 : ℕ) : ℕ∞) : WithBot ℕ∞) ≤ ((I.subscheme.dimension : ℕ∞) : WithBot ℕ∞) := hlow
  have h1 : 1 ≤ I.subscheme.dimension := withBot_enat_natCast_le_iff.mp hlow'
  have hd : I.subscheme.dimension = 1 := by omega
  show topologicalKrullDim I.subscheme = 1
  rw [hspec, hd]
  rfl

/-- The strict transform of the integral curve `Γ ⊆ W` under the tower of point blowups `β : S → W`: the
closure of `β⁻¹Γ ∖ ExceptionalLocus` with its induced reduced structure (the same closure-model
construction as for a single point blowup). -/
noncomputable def strictTransformTower {k : Type u} [Field k] [PerfectField k] {S W : SmoothProjectiveSurface k}
    (β : S.toScheme ⟶ W.toScheme) (hβ : IsBlowupTower β)
    (Γ : IntegralCurve k W.toScheme) :
    IntegralCurve k S.toScheme where
  carrier := (strictTransformTower.ideal β hβ Γ).subscheme
  ι := (strictTransformTower.ideal β hβ Γ).subschemeι
  isIntegral := strictTransformTower.ideal_subscheme_isIntegral β hβ Γ
  isProper := by
    show AlgebraicGeometry.IsProper ((AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal
      ⟨closure (β.base ⁻¹' (Set.range Γ.ι.base) \ ExceptionalLocus β hβ), isClosed_closure⟩).subschemeι ≫ _)
    infer_instance
  dim_eq_one := strictTransformTower.ideal_subscheme_dim_eq_one β hβ Γ

theorem strictTransformTower_range {k : Type u} [Field k] [PerfectField k] {S W : SmoothProjectiveSurface k}
    (β : S.toScheme ⟶ W.toScheme) (hβ : IsBlowupTower β)
    (Γ : IntegralCurve k W.toScheme) :
    Set.range (strictTransformTower β hβ Γ).ι.base
      = closure (β.base ⁻¹' (Set.range Γ.ι.base) \ ExceptionalLocus β hβ) := by
  exact (AlgebraicGeometry.Scheme.IdealSheafData.range_subschemeι _).trans
    (AlgebraicGeometry.Scheme.IdealSheafData.coe_support_vanishingIdeal _)

end
