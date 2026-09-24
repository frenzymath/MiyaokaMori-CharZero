import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S3PositiveLine.Realization.FiberDegreeBetween
import MiyaokaMori.AlgebraicGeometry.Varieties.Surfaces.GeneralFiberAvoidsFiniteSet
import MiyaokaMori.AlgebraicGeometry.Morphisms.RationalMapPrecomp
import MiyaokaMori.AlgebraicGeometry.Morphisms.BlowupSequenceIsoOverOpen
import MiyaokaMori.AlgebraicGeometry.Morphisms.EliminationResolvingTower
import MiyaokaMori.AlgebraicGeometry.Morphisms.ResolvedSurfaceGeneralFiberDegree
import MiyaokaMori.AlgebraicGeometry.Varieties.Smooth.SmoothVarietyRegularInCodimOne

/-! # General fibres of the resolved ruled surface

After eliminating the indeterminacy of `Φ₀` by a tower `β : S → W` of point blowups, a general
closed fibre of `S → C̃` is still `P¹`, and the degree of `Φ^*O_X(1)` on it still lies in `[1, r₀]`:
the tower has finitely many centres, a general fibre avoids them, and `β` is an isomorphism near it
(Corollary 4.3 of the paper: "a general fibre avoids the finitely many centres
and remains the original `P¹`; the same observation preserves the degree bound").

The main theorem is `resolved_surface_general_fiber`. Its step (11), the comparison of the fibre
degree with the degree on `P¹`, is `fiberDegree_eq_degree_of_fiber_iso`
(`ResolvedSurfaceGeneralFiberDegree`). The fact that the images of the centres are closed points is
obtained by induction on `IsBlowupTower β` (each `pointBlowup.π` is proper, hence a closed map), and
`blowup_isBlowup` translates the tower into a point-blowup sequence over a finite set of closed
points (`IsBlowupTower.exists_finset_closed_centres`); the hypothesis `havoid` is therefore not
used in the proof. The fibre isomorphism lemma `exists_fiber_comp_iso_of_isIso_morphismRestrict`
provides an explicit isomorphism compatible with the fibre inclusions.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open AlgebraicGeometry

/-- If `g` is an isomorphism over the open `U` and the whole `π`-fibre over `y` lies in `U`, then
the fibre of `g ≫ π` over `y` is isomorphic to the fibre of `π` over `y`, compatibly with the two
fibre inclusions: `φ.hom ≫ π.fiberι y = (g ≫ π).fiberι y ≫ g` and
`φ.inv ≫ (g ≫ π).fiberι y = i' ≫ inv (g ∣_ U) ≫ (g ⁻¹ᵁ U).ι`, where `i'` is the lift of the
`π`-fibre into `U`.
Proof: construct both directions by the universal property of the pullback (`pullback.lift`) and
check they are mutually inverse with `pullback.hom_ext`; that the `(g ≫ π)`-fibre lies in `g⁻¹U`
uses `range_fiberι` and `IsOpenImmersion.lift`. -/
theorem AlgebraicGeometry.Scheme.Hom.exists_fiber_comp_iso_of_isIso_morphismRestrict
    {S' S C : Scheme.{u}} (g : S' ⟶ S) (π : S ⟶ C) (U : S.Opens)
    (hg : IsIso (g ∣_ U)) (y : C) (hy : (π.base ⁻¹' {y}) ⊆ (U : Set S)) :
    ∃ (φ : (g ≫ π).fiber y ≅ π.fiber y) (i' : π.fiber y ⟶ U.toScheme),
      i' ≫ U.ι = π.fiberι y ∧
      φ.hom ≫ π.fiberι y = (g ≫ π).fiberι y ≫ g ∧
      φ.inv ≫ (g ≫ π).fiberι y = i' ≫ inv (g ∣_ U) ≫ (g ⁻¹ᵁ U).ι := by
  have hrange : Set.range (π.fiberι y).base ⊆ Set.range U.ι.base := by
    rw [Scheme.Hom.range_fiberι, Scheme.Opens.range_ι]
    exact hy
  let i' : π.fiber y ⟶ U.toScheme := IsOpenImmersion.lift U.ι (π.fiberι y) hrange
  have hi' : i' ≫ U.ι = π.fiberι y := IsOpenImmersion.lift_fac _ _ _
  let s : π.fiber y ⟶ S' := i' ≫ inv (g ∣_ U) ≫ (g ⁻¹ᵁ U).ι
  have hs : s ≫ g = π.fiberι y := by
    simp only [s, Category.assoc]
    rw [← morphismRestrict_ι, IsIso.inv_hom_id_assoc, hi']
  let ψ : π.fiber y ⟶ (g ≫ π).fiber y :=
    pullback.lift s (π.fiberToSpecResidueField y) (by
      rw [← Category.assoc, hs]
      exact π.fiber_fac y)
  let φ : (g ≫ π).fiber y ⟶ π.fiber y :=
    pullback.lift ((g ≫ π).fiberι y ≫ g) ((g ≫ π).fiberToSpecResidueField y) (by
      rw [Category.assoc]
      exact (g ≫ π).fiber_fac y)
  have hψfst : ψ ≫ (g ≫ π).fiberι y = s := pullback.lift_fst _ _ _
  have hψsnd : ψ ≫ (g ≫ π).fiberToSpecResidueField y = π.fiberToSpecResidueField y :=
    pullback.lift_snd _ _ _
  have hφfst : φ ≫ π.fiberι y = (g ≫ π).fiberι y ≫ g := pullback.lift_fst _ _ _
  have hφsnd : φ ≫ π.fiberToSpecResidueField y = (g ≫ π).fiberToSpecResidueField y :=
    pullback.lift_snd _ _ _
  have hrange' : Set.range ((g ≫ π).fiberι y).base ⊆ Set.range (g ⁻¹ᵁ U).ι.base := by
    rw [Scheme.Hom.range_fiberι, Scheme.Opens.range_ι]
    intro x hx
    have hx' : (g ≫ π).base x = y := hx
    apply hy
    show π.base (g.base x) = y
    rw [← hx']
    rfl
  let j' : (g ≫ π).fiber y ⟶ (g ⁻¹ᵁ U).toScheme :=
    IsOpenImmersion.lift (g ⁻¹ᵁ U).ι ((g ≫ π).fiberι y) hrange'
  have hj' : j' ≫ (g ⁻¹ᵁ U).ι = (g ≫ π).fiberι y := IsOpenImmersion.lift_fac _ _ _
  have hkey : j' ≫ (g ∣_ U) = φ ≫ i' := by
    rw [← cancel_mono U.ι]
    simp only [Category.assoc]
    rw [morphismRestrict_ι, hi', hφfst, ← Category.assoc, hj']
  have h1 : ψ ≫ φ = 𝟙 _ := by
    apply pullback.hom_ext
    · change (ψ ≫ φ) ≫ π.fiberι y = 𝟙 _ ≫ π.fiberι y
      rw [Category.assoc, hφfst, ← Category.assoc, hψfst, hs, Category.id_comp]
    · change (ψ ≫ φ) ≫ π.fiberToSpecResidueField y = 𝟙 _ ≫ π.fiberToSpecResidueField y
      rw [Category.assoc, hφsnd, hψsnd, Category.id_comp]
  have h2 : φ ≫ ψ = 𝟙 _ := by
    apply pullback.hom_ext
    · change (φ ≫ ψ) ≫ (g ≫ π).fiberι y = 𝟙 _ ≫ (g ≫ π).fiberι y
      rw [Category.assoc, hψfst, Category.id_comp]
      simp only [s]
      rw [← Category.assoc, ← hkey, Category.assoc, IsIso.hom_inv_id_assoc, hj']
    · change (φ ≫ ψ) ≫ (g ≫ π).fiberToSpecResidueField y =
        𝟙 _ ≫ (g ≫ π).fiberToSpecResidueField y
      rw [Category.assoc, hψsnd, hφsnd, Category.id_comp]
  refine ⟨⟨φ, ψ, h2, h1⟩, i', hi', hφfst, ?_⟩
  change ψ ≫ (g ≫ π).fiberι y = _
  rw [hψfst]

/-- A single point blowup `pointBlowup.π` is proper (projective over `k` implies proper;
`IsProper.of_comp`). -/
theorem pointBlowup.π_isProper {k : Type u} [Field k] [PerfectField k]
    (S : SmoothProjectiveSurface k) (p : S.toScheme) (hp : IsClosed ({p} : Set S.toScheme)) :
    IsProper (pointBlowup.π S p hp) := by
  have hproperSource : IsProper
      ((pointBlowup S p hp).toScheme ↘ Spec (CommRingCat.of k)) :=
    ((isProjectiveOver_iff_isProper_and_isAmple k _).mp
      (pointBlowup S p hp).toSmoothProjectiveVariety.projective).1
  have hcomp : pointBlowup.π S p hp ≫ (S.toScheme ↘ Spec (CommRingCat.of k)) =
      ((pointBlowup S p hp).toScheme ↘ Spec (CommRingCat.of k)) := rfl
  have hproperComp : IsProper
      (pointBlowup.π S p hp ≫ (S.toScheme ↘ Spec (CommRingCat.of k))) := by
    rw [hcomp]
    exact hproperSource
  exact IsProper.of_comp (pointBlowup.π S p hp) (S.toScheme ↘ Spec (CommRingCat.of k))

/-- A tower of point blowups is proper (each step is proper, and properness is closed under
composition). -/
theorem IsBlowupTower.isProper {k : Type u} [Field k] [PerfectField k]
    {S W : SmoothProjectiveSurface k} {β : S.toScheme ⟶ W.toScheme}
    (hβ : IsBlowupTower β) : IsProper β := by
  induction hβ with
  | id W => infer_instance
  | step g hg p hp ih =>
    have h1 := pointBlowup.π_isProper _ p hp
    have h2 := ih
    infer_instance

/-- A single `pointBlowup.π` satisfies the universal-property predicate `IsBlowup` for the ideal of
the point (`blowup_isBlowup` and `vanishingIdeal_singleton_eq_pointIdeal`). -/
theorem pointBlowup.π_isBlowup_pointIdeal {k : Type u} [Field k] [PerfectField k]
    (S : SmoothProjectiveSurface k) (p : S.toScheme) (hp : IsClosed ({p} : Set S.toScheme)) :
    MiyaokaMori.Statement.IsBlowup (MiyaokaMori.Statement.pointIdeal S.toScheme p)
      (pointBlowup.π S p hp) := by
  rw [← AlgebraicGeometry.Scheme.vanishingIdeal_singleton_eq_pointIdeal p hp]
  exact AlgebraicGeometry.Scheme.blowup_isBlowup _

/-- The images in `W` of the centres of a tower of point blowups form a finite set of **closed
points**, and the tower is a point-blowup sequence over this finite set
(`IsPointBlowupSequenceOver`). By induction on `IsBlowupTower`: each centre `p` is closed and the
tower `g` below it is proper, hence a closed map, so `g p` is closed. (The predicate
`IsPointBlowupSequenceOver` alone does not give this, since its intermediate schemes are arbitrary
and the images of its centres need not be closed.) -/
theorem IsBlowupTower.exists_finset_closed_centres {k : Type u} [Field k] [PerfectField k]
    {S W : SmoothProjectiveSurface k} {β : S.toScheme ⟶ W.toScheme}
    (hβ : IsBlowupTower β) :
    ∃ K : Finset W.toScheme, (∀ z ∈ K, IsClosed ({z} : Set W.toScheme)) ∧
      MiyaokaMori.Statement.IsPointBlowupSequenceOver W.toScheme (K : Set W.toScheme) β := by
  classical
  induction hβ with
  | id W => exact ⟨∅, fun z hz => (Finset.notMem_empty z hz).elim, .id⟩
  | step g hg p hp ih =>
    obtain ⟨K, hK, hseq⟩ := ih
    have hgproper : IsProper g := hg.isProper
    have hclosedmap : IsClosedMap g.base := g.isClosedMap
    have hgp : IsClosed ({g.base p} : Set _) := by
      have := hclosedmap _ hp
      rwa [Set.image_singleton] at this
    refine ⟨insert (g.base p) K, ?_, ?_⟩
    · intro z hz
      rcases Finset.mem_insert.mp hz with hz | hz
      · rw [hz]; exact hgp
      · exact hK z hz
    · refine .cons g (pointBlowup.π _ p hp) (hseq.mono ?_) p hp ?_
        (pointBlowup.π_isBlowup_pointIdeal _ p hp)
      · intro x hx
        exact Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_coe.mp hx))
      · exact Finset.mem_coe.mpr (Finset.mem_insert_self _ _)

/-- General fibres of the resolved surface (Corollary 4.3 of the paper).
(8) The centres are finitely many closed points (`IsBlowupTower.exists_finset_closed_centres`);
`exists_open_avoiding` gives a nonempty open `V₁ ⊆ C̃` with no centre above it;
`V := V₁ ∩ V_deg` (nonempty since `C̃` is irreducible).
(9) For a closed point `y ∈ V`, `β` is an isomorphism over `U₁ := π_W⁻¹(V₁)`
(`IsPointBlowupSequenceOver.mono` and `isIso_morphismRestrict`), hence
`(β ≫ π_W).fiber y ≅ (π_W).fiber y` (`exists_fiber_comp_iso_of_isIso_morphismRestrict`) `≅ P¹`
(the `e` from `hdeg`).
(10) Under this isomorphism `Ψ|_{S_y}` and `Φ_y` agree on the nonempty open `O` of `AgreesOnOpen`
(`hagree`); since `P¹` is reduced, `X` is separated and `O → P¹` is dominant, they agree everywhere
(Mathlib's `ext_of_isDominant_of_isSeparated`).
(11) `fiberDegree = deg((e.inv ≫ Φ_y)^*O_X(1))`: `fiberDegree_eq_degree_of_fiber_iso`, functoriality
of pullback (`Modules.pullbackComp`, `pullbackCongr`) and `LineBundle.degree_congr`. -/
theorem resolved_surface_general_fiber {k : Type u} [Field k] [IsAlgClosed k]
    {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}
    {ρ : FiniteCover k C}
    {L : LineBundle ρ.source.toVariety} {r₀ : ℕ}
    (Φ₀ : (ruledSurface L).toScheme ⤏ X.toScheme)
    [Φ₀.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (U : (ruledSurface L).toScheme.Opens) (hU : IsRegularOn Φ₀ U)
    (hdeg : ∃ V : Set ρ.source.toScheme, IsOpen V ∧ V.Nonempty ∧
      ∀ y ∈ V, IsClosed ({y} : Set ρ.source.toScheme) →
        ∃ (e : ((ruledSurface.π L).fiber y)
              ≅ (ProjectiveLine.asSmoothProjectiveCurve k).toScheme)
          (Φy : ((ruledSurface.π L).fiber y) ⟶ X.toScheme),
          AgreesOnOpen Φy ((ruledSurface L).toScheme.homOfLE hU ≫ Φ₀.toPartialMap.hom)
            ((ruledSurface.π L).fiberι y) (CategoryTheory.CategoryStruct.id _) ∧
          1 ≤ (LineBundle.pullback (X := (ProjectiveLine.asSmoothProjectiveCurve k).toVariety) (e.inv ≫ Φy) (X.OX 1)).degree ∧
          (LineBundle.pullback (X := (ProjectiveLine.asSmoothProjectiveCurve k).toVariety) (e.inv ≫ Φy) (X.OX 1)).degree ≤ (r₀ : ℤ))
    (S : SmoothProjectiveSurface k) (β : S.toScheme ⟶ (ruledSurface L).toScheme)
    (hβ : IsBlowupTower β)
    (havoid : IsBlowupTowerAvoiding β (U : Set (ruledSurface L).toScheme))
    (Ψ : S.toScheme ⟶ X.toScheme)
    (hagree : (β ⁻¹ᵁ U).ι ≫ Ψ =
      (β ∣_ U) ≫ (ruledSurface L).toScheme.homOfLE hU ≫ Φ₀.toPartialMap.hom)
    (hπS : AlgebraicGeometry.Surjective (β ≫ ruledSurface.π L)) :
    ∃ V : Set ρ.source.toScheme, IsOpen V ∧ V.Nonempty ∧
      ∀ y ∈ V, IsClosed ({y} : Set ρ.source.toScheme) →
        Nonempty (((β ≫ ruledSurface.π L).fiber y) ≅
          (ProjectiveLine.asSmoothProjectiveCurve k).toScheme) ∧
        1 ≤ fiberDegree (β ≫ ruledSurface.π L) hπS (LineBundle.pullback Ψ (X.OX 1)) y ∧
        fiberDegree (β ≫ ruledSurface.π L) hπS (LineBundle.pullback Ψ (X.OX 1)) y ≤ (r₀ : ℤ) := by
  classical
  obtain ⟨Vd, hVdopen, hVdne, hVd⟩ := hdeg
  -- (8) the centres of the tower: finitely many closed points of W
  obtain ⟨K, hK, hseq⟩ := hβ.exists_finset_closed_centres
  have hπW : (ruledSurface.π L).IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) := by
    rw [AlgebraicGeometry.Scheme.Hom.isOver_iff]
    rfl
  have := hπW
  obtain ⟨V₁, hV₁open, hV₁ne, hV₁⟩ := exists_open_avoiding (ruledSurface.π L) K hK
  have hVne : (V₁ ∩ Vd).Nonempty :=
    nonempty_preirreducible_inter hV₁open hVdopen hV₁ne hVdne
  refine ⟨V₁ ∩ Vd, hV₁open.inter hVdopen, hVne, ?_⟩
  intro y hy hyclosed
  obtain ⟨hyV₁, hyVd⟩ := hy
  -- (9) β is an isomorphism over U₁ := π⁻¹(V₁), which contains the whole fibre over y
  let U₁ : (ruledSurface L).toScheme.Opens := (ruledSurface.π L) ⁻¹ᵁ ⟨V₁, hV₁open⟩
  have hseq' : MiyaokaMori.Statement.IsPointBlowupSequenceOver (ruledSurface L).toScheme
      ((U₁ : Set (ruledSurface L).toScheme)ᶜ) β := by
    refine hseq.mono ?_
    intro z hz
    rw [Set.mem_compl_iff]
    intro hzU
    have hzV : (ruledSurface.π L).base z ∈ V₁ := hzU
    exact hV₁ _ hzV z (Finset.mem_coe.mp hz) rfl
  have hiso : IsIso (β ∣_ U₁) :=
    MiyaokaMori.Statement.IsPointBlowupSequenceOver.isIso_morphismRestrict U₁ β hseq'
  have hy₁ : ((ruledSurface.π L).base ⁻¹' {y}) ⊆ (U₁ : Set (ruledSurface L).toScheme) := by
    intro w hw
    have hw' : (ruledSurface.π L).base w = y := hw
    show (ruledSurface.π L).base w ∈ V₁
    rw [hw']
    exact hyV₁
  obtain ⟨φ, i', hi', hφhom, hφinv⟩ :=
    AlgebraicGeometry.Scheme.Hom.exists_fiber_comp_iso_of_isIso_morphismRestrict β
      (ruledSurface.π L) U₁ hiso y hy₁
  obtain ⟨e, Φy, hagreeO, hlow, hupp⟩ := hVd y hyVd hyclosed
  refine ⟨⟨φ ≪≫ e⟩, ?_⟩
  -- (10) Ψ restricted to the fibre agrees with Φy
  obtain ⟨O, hO, jO, hjO1, hjO2⟩ := hagreeO
  rw [Category.comp_id] at hjO1
  let t : O.toScheme ⟶ S.toScheme := O.ι ≫ φ.inv ≫ (β ≫ ruledSurface.π L).fiberι y
  have ht : t = O.ι ≫ i' ≫ inv (β ∣_ U₁) ≫ (β ⁻¹ᵁ U₁).ι := by
    simp only [t]
    rw [hφinv]
  have htβ : t ≫ β = jO ≫ U.ι := by
    rw [ht]
    simp only [Category.assoc]
    rw [← AlgebraicGeometry.morphismRestrict_ι, IsIso.inv_hom_id_assoc, hi', hjO1]
  have hrange_t : Set.range t.base ⊆ Set.range (β ⁻¹ᵁ U).ι.base := by
    rw [AlgebraicGeometry.Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    show β.base (t.base x) ∈ U
    have h1 : (t ≫ β).base x = (jO ≫ U.ι).base x := by rw [htβ]
    simp only [AlgebraicGeometry.Scheme.Hom.comp_apply] at h1
    rw [h1]
    have hmem : U.ι.base (jO.base x) ∈ Set.range U.ι.base := Set.mem_range_self _
    rwa [AlgebraicGeometry.Scheme.Opens.range_ι] at hmem
  let t' : O.toScheme ⟶ (β ⁻¹ᵁ U).toScheme :=
    AlgebraicGeometry.IsOpenImmersion.lift (β ⁻¹ᵁ U).ι t hrange_t
  have ht' : t' ≫ (β ⁻¹ᵁ U).ι = t := AlgebraicGeometry.IsOpenImmersion.lift_fac _ _ _
  have ht'β : t' ≫ (β ∣_ U) = jO := by
    rw [← cancel_mono U.ι, Category.assoc, AlgebraicGeometry.morphismRestrict_ι,
      ← Category.assoc, ht', htβ]
  have hOeq : O.ι ≫ φ.inv ≫ (β ≫ ruledSurface.π L).fiberι y ≫ Ψ = O.ι ≫ Φy := by
    calc O.ι ≫ φ.inv ≫ (β ≫ ruledSurface.π L).fiberι y ≫ Ψ = t ≫ Ψ := by
          simp only [t, Category.assoc]
      _ = (t' ≫ (β ⁻¹ᵁ U).ι) ≫ Ψ := by rw [ht']
      _ = t' ≫ (β ∣_ U) ≫ (ruledSurface L).toScheme.homOfLE hU ≫ Φ₀.toPartialMap.hom := by
          rw [Category.assoc, hagree]
      _ = jO ≫ (ruledSurface L).toScheme.homOfLE hU ≫ Φ₀.toPartialMap.hom := by
          rw [← Category.assoc, ht'β]
      _ = O.ι ≫ Φy := hjO2
  have hsep : X.toScheme.IsSeparated :=
    AlgebraicGeometry.Scheme.isSeparated_of_isProper_over_field (k := k) X.toScheme
  have : IsIntegral (ProjectiveLine.asSmoothProjectiveCurve k).toScheme :=
    SmoothProjectiveCurve.isIntegral _
  have hdom : AlgebraicGeometry.IsDominant (O.ι ≫ e.hom) := by
    constructor
    have hOne : (O : Set ((ruledSurface.π L).fiber y)).Nonempty :=
      (TopologicalSpace.Opens.ne_bot_iff_nonempty O).mp hO
    have hr : Set.range (O.ι ≫ e.hom).base = e.hom.base '' (O : Set _) := by
      rw [AlgebraicGeometry.Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
        AlgebraicGeometry.Scheme.Opens.range_ι]
    show Dense (Set.range (O.ι ≫ e.hom).base)
    rw [hr]
    exact (e.hom.isOpenEmbedding.isOpenMap _ O.2).dense (hOne.image _)
  have hmaps : e.inv ≫ φ.inv ≫ (β ≫ ruledSurface.π L).fiberι y ≫ Ψ = e.inv ≫ Φy := by
    refine AlgebraicGeometry.ext_of_isDominant_of_isSeparated (terminal.from X.toScheme)
      (terminal.hom_ext _ _) (O.ι ≫ e.hom) ?_
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    exact hOeq
  -- (11) the fibre degree equals the degree on P¹
  have hdeg_eq := fiberDegree_eq_degree_of_fiber_iso (β ≫ ruledSurface.π L) hπS
    (LineBundle.pullback Ψ (X.OX 1)) y hyclosed (φ ≪≫ e)
  have hdeg_eq' : fiberDegree (β ≫ ruledSurface.π L) hπS (LineBundle.pullback Ψ (X.OX 1)) y =
      (LineBundle.pullback (X := (ProjectiveLine.asSmoothProjectiveCurve k).toVariety)
        (e.inv ≫ Φy) (X.OX 1)).degree := by
    rw [hdeg_eq]
    apply LineBundle.degree_congr
    exact ((AlgebraicGeometry.Scheme.Modules.pullbackComp
        ((φ ≪≫ e).inv ≫ (β ≫ ruledSurface.π L).fiberι y) Ψ).app (X.OX 1).toModules) ≪≫
      (AlgebraicGeometry.Scheme.Modules.pullbackCongr (by
        simp only [Iso.trans_inv, Category.assoc]
        exact hmaps)).app (X.OX 1).toModules
  rw [hdeg_eq']
  exact ⟨hlow, hupp⟩

end
