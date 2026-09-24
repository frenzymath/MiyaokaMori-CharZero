import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.ClosedSubvariety
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.FundamentalClass
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.VarietyLineBundle
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Divisors.Weil.CartierToWeil
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.Paper.S3PositiveLine.Realization.RuledSurface
import MiyaokaMori.AlgebraicGeometry.Blowup.BlowupIsoAwayFromCenter
import MiyaokaMori.AlgebraicGeometry.Blowup.BlowupTowerAvoiding
import MiyaokaMori.AlgebraicGeometry.Varieties.Surfaces.PointBlowupSurface
import MiyaokaMori.AlgebraicGeometry.Varieties.Surfaces.SmoothProjectiveSurface
import MiyaokaMori.AlgebraicGeometry.Blowup.BlowupExceptionalP1
import MiyaokaMori.AlgebraicGeometry.Blowup.BlowupFiberDecomposition
import MiyaokaMori.AlgebraicGeometry.Blowup.BlowupPreservesConnected
import MiyaokaMori.AlgebraicGeometry.Varieties.Surfaces.FiberDivisorDecomposition
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.FiberDivisorPullback
import MiyaokaMori.Paper.S4Completion.FiberOneCycle
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.IntegralCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.IntegralCurveEqOfRangeSubset
import MiyaokaMori.Paper.S4Completion.RuledSurfaceFiberP1
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothRationalCurve
import MiyaokaMori.AlgebraicGeometry.Blowup.StrictTransform
import MiyaokaMori.AlgebraicGeometry.Blowup.StrictTransformSmoothRational

/-! # Fibres of the resolved ruled surface

Let `S → W = P(O_C̃ ⊕ L)` be a tower of point blowups avoiding an open set `U`, and `π : S → C̃` the
composite with the ruling. For a closed point `y`, the fibre cycle `π^*(y) = ∑ mᵢ Γᵢ` has connected
reduced support and every component `Γᵢ` is a smooth rational curve: this holds for the fibre `P¹` of
the ruled surface, and under a point blowup the strict transforms stay smooth rational while the new
exceptional curve is a `P¹` meeting the rest of the fibre (Lemma 5.1 of the paper,
§5).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
open AlgebraicGeometry

noncomputable section

/-- Induction along the blowup tower: the fibre of `S → C̃` over `y` is a connected finite union of
smooth rational integral curves. -/
private theorem tower_cover_probe {k : Type u} [Field k] [IsAlgClosed k]
    {C : SmoothProjectiveCurve k} (L : LineBundle C.toVariety)
    (y : C.toScheme) (hy : IsClosed ({y} : Set C.toScheme))
    {S : SmoothProjectiveSurface k}
    (bl : S.toScheme ⟶ (ruledSurface L).toScheme) (hβ : IsBlowupTower bl)
    (hblπ : AlgebraicGeometry.Surjective (bl ≫ ruledSurface.π L)) :
    ∃ (ι : Type) (_ : Fintype ι) (T : ι → IntegralCurve k S.toScheme),
      (∀ i, (T i).IsSmoothRational) ∧
      (⋃ i, Set.range (T i).ι.base) = bl.base ⁻¹' ((ruledSurface.π L).base ⁻¹' {y}) ∧
      _root_.IsConnected (bl.base ⁻¹' ((ruledSurface.π L).base ⁻¹' {y})) := by
  let P : ∀ {S W : SmoothProjectiveSurface k} (bl : S.toScheme ⟶ W.toScheme),
    IsBlowupTower bl → Prop := fun {S} {W} bl _ =>
    ∀ (hW : W = ruledSurface L) (q : W.toScheme ⟶ C.toScheme),
      q = (eqToHom (by rw [hW]) ≫ ruledSurface.π L) →
      AlgebraicGeometry.Surjective (bl ≫ q) →
      ∃ (ι : Type) (_ : Fintype ι) (T : ι → IntegralCurve k S.toScheme),
        (∀ i, (T i).IsSmoothRational) ∧
        (⋃ i, Set.range (T i).ι.base) = (bl ≫ q).base ⁻¹' {y} ∧
        _root_.IsConnected ((bl ≫ q).base ⁻¹' {y})
  have hP : P bl hβ := by
    exact IsBlowupTower.rec (motive := P)
      (id := by
        intro W hW q hq hqsurj
        subst hW
        obtain ⟨_, F, hFrange, hFrat⟩ := ruled_fiber_iso_p1 L y hy
        have hq' : q = ruledSurface.π L := by simpa using hq
        let ι : Type := PUnit
        let T : ι → IntegralCurve k (ruledSurface L).toScheme := fun _ => F
        have hirr : IsIrreducible (Set.univ : Set F.carrier) :=
          (AlgebraicGeometry.irreducibleSpace_of_isIntegral F.carrier).isIrreducible_univ
        have hconn : _root_.IsConnected (Set.range F.ι.base) := by
          convert (hirr.image F.ι.base F.ι.continuous.continuousOn).isConnected using 1
          ext z
          simp
        refine ⟨ι, inferInstance, T, ?_, ?_, ?_⟩
        · intro i
          exact hFrat
        · rw [hq']
          change (⋃ _ : ι, Set.range F.ι.base) = _
          rw [Set.iUnion_const]
          simpa using hFrange
        · rw [hq']
          simpa only [CategoryTheory.Category.id_comp, hFrange] using hconn
      )
      (step := by
        intro S W g hg p hp ih hW q hq hqsurj
        have hcomp : AlgebraicGeometry.Surjective
            (pointBlowup.π S p hp ≫ (g ≫ q)) := by
          simpa [Category.assoc] using hqsurj
        have hqold : AlgebraicGeometry.Surjective (g ≫ q) :=
          AlgebraicGeometry.Surjective.of_comp (pointBlowup.π S p hp) (g ≫ q)
        obtain ⟨ι, hι, T, hTrat, hTcov, hTconn⟩ := ih hW q hq hqold
        by_cases hpy : (g ≫ q).base p = y
        · have hdec := blowup_fiber_support (π := g ≫ q) hqold p hp y hpy hTcov
          have hconn := blowup_fiber_connected (π := g ≫ q) p hp y (by simpa using hy) hTconn
          let ι' : Type := Sum Unit ι
          let T' : ι' → IntegralCurve k (pointBlowup S p hp).toScheme :=
            Sum.elim (fun _ => pointBlowup.exceptional S p hp)
              (fun i => strictTransform p hp (T i))
          refine ⟨ι', inferInstance, T', ?_, ?_, ?_⟩
          · intro i
            cases i with
            | inl u => exact exceptional_isSmoothRational S p hp
            | inr i => exact strictTransform_isSmoothRational p hp (T i) (hTrat i)
          · rw [Set.iUnion_sum]
            change (⋃ _ : Unit, Set.range (pointBlowup.exceptional S p hp).ι.base) ∪
              ⋃ i, Set.range (strictTransform p hp (T i)).ι.base = _
            rw [Set.iUnion_const]
            simpa [Category.assoc] using hdec.1.symm
          · simpa [Category.assoc] using hconn
        · have hpnot (i : ι) : p ∉ Set.range (T i).ι.base := by
            intro hpi
            obtain ⟨z, hz⟩ := hpi
            have hz' : (g ≫ q).base ((T i).ι.base z) = y := by
              have hzfib : (T i).ι.base z ∈ (g ≫ q).base ⁻¹' {y} := by
                rw [← hTcov]
                exact Set.mem_iUnion.mpr ⟨i, ⟨z, rfl⟩⟩
              exact hzfib
            exact hpy (by simpa [hz] using hz')
          have hstrict (i : ι) :
              Set.range (strictTransform p hp (T i)).ι.base =
                (pointBlowup.π S p hp).base ⁻¹' Set.range (T i).ι.base := by
            rw [strictTransform_range]
            have hclosed : IsClosed
                ((pointBlowup.π S p hp).base ⁻¹' Set.range (T i).ι.base) :=
              (T i).ι.isClosedEmbedding.isClosed_range.preimage
                (pointBlowup.π S p hp).continuous
            rw [Set.diff_singleton_eq_self (hpnot i)]
            exact hclosed.closure_eq
          refine ⟨ι, hι, (fun i => strictTransform p hp (T i)), ?_, ?_, ?_⟩
          · intro i
            exact strictTransform_isSmoothRational p hp (T i) (hTrat i)
          · calc
              ⋃ i, Set.range (strictTransform p hp (T i)).ι.base =
                  ⋃ i, (pointBlowup.π S p hp).base ⁻¹' Set.range (T i).ι.base := by
                    apply Set.iUnion_congr
                    intro i
                    exact hstrict i
              _ = (pointBlowup.π S p hp).base ⁻¹' (⋃ i, Set.range (T i).ι.base) := by
                    rw [Set.preimage_iUnion]
              _ = (pointBlowup.π S p hp).base ⁻¹' ((g ≫ q).base ⁻¹' {y}) := by rw [hTcov]
              _ = ((pointBlowup.π S p hp ≫ g) ≫ q).base ⁻¹' {y} := by
                    rfl
          · simpa [Category.assoc] using
              (show _root_.IsConnected ((pointBlowup.π S p hp ≫ (g ≫ q)).base ⁻¹' {y})
                from blowup_fiber_connected (π := g ≫ q) p hp y (by simpa using hy) hTconn)
      ) hβ
  exact hP rfl (ruledSurface.π L) (by simp) hblπ

/-- Every irreducible component of the fibre over `y` is one of the smooth rational curves covering it,
hence smooth rational itself. -/
private theorem component_rat_probe {k : Type u} [Field k] [IsAlgClosed k]
    {S : SmoothProjectiveSurface k} {ι₀ ι : Type} [Fintype ι₀] [Fintype ι]
    (T : ι₀ → IntegralCurve k S.toScheme) (Γ : ι → IntegralCurve k S.toScheme)
    (hT : ∀ j, (T j).IsSmoothRational)
    (hcover : (⋃ j, Set.range (T j).ι.base) = ⋃ i, Set.range (Γ i).ι.base) :
    ∀ i, (Γ i).IsSmoothRational := by
  intro i
  have hirr : IsIrreducible (Set.range (Γ i).ι.base) := by
    have h0 : IsIrreducible (Set.univ : Set (Γ i).carrier) :=
      (AlgebraicGeometry.irreducibleSpace_of_isIntegral (Γ i).carrier).isIrreducible_univ
    convert h0.image (Γ i).ι.base (Γ i).ι.continuous.continuousOn using 1
    ext z
    simp
  have hsub : Set.range (Γ i).ι.base ⊆ ⋃ j, Set.range (T j).ι.base := by
    intro z hz
    exact hcover.symm ▸ Set.mem_iUnion_of_mem i hz
  let s : Finset (Set S.toScheme) := Finset.univ.image (fun j => Set.range (T j).ι.base)
  have hsclosed : ∀ z ∈ s, IsClosed z := by
    intro z hz
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hz
    exact (T j).ι.isClosedEmbedding.isClosed_range
  have hscover : Set.range (Γ i).ι.base ⊆ ⋃₀ (s : Set (Set S.toScheme)) := by
    intro z hz
    obtain ⟨j, hjz⟩ := Set.mem_iUnion.mp (hsub hz)
    apply Set.mem_sUnion_of_mem hjz
    exact (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩ :
      Set.range (T j).ι.base ∈ s)
  obtain ⟨z, hz, hzsub⟩ := (isIrreducible_iff_sUnion_isClosed.mp hirr) s hsclosed hscover
  obtain ⟨j, hj, hjEq⟩ := Finset.mem_image.mp hz
  have hZj : Set.range (Γ i).ι.base ⊆ Set.range (T j).ι.base := by simpa [← hjEq] using hzsub
  obtain ⟨e, he⟩ := IntegralCurve.iso_of_range_subset (Γ i) (T j) hZj
  obtain ⟨e', he'⟩ := hT j
  refine ⟨e ≪≫ e', ?_⟩
  have hebase := congrArg (fun f => f ≫ (S.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) he
  change (e.hom ≫ e'.hom) ≫ (ProjectiveLine k ↘
      AlgebraicGeometry.Spec (CommRingCat.of k)) =
    (Γ i).carrier ↘ AlgebraicGeometry.Spec (CommRingCat.of k)
  simp only [Category.assoc]
  rw [he']
  change e.hom ≫ ((T j).ι ≫
      (S.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) =
    (Γ i).ι ≫ (S.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
  simpa [Category.assoc] using hebase

/-- Assembly: the fibre cycle over `y` decomposes with positive multiplicities into its irreducible
components, which cover the fibre, are smooth rational, and have connected union. -/
private theorem special_fiber_probe {k : Type u} [Field k] [IsAlgClosed k]
    {S : SmoothProjectiveSurface k} {C : SmoothProjectiveCurve k}
    (L : LineBundle C.toVariety) (bl : S.toScheme ⟶ (ruledSurface L).toScheme)
    (hβ : IsBlowupTower bl) {U : Set (ruledSurface L).toScheme}
    (hbl : IsBlowupTowerAvoiding bl U) (π : S.toScheme ⟶ C.toScheme)
    (hπfac : π = bl ≫ ruledSurface.π L)
    (hπ : AlgebraicGeometry.Surjective π) (y : C.toScheme)
    (hy : IsClosed ({y} : Set C.toScheme)) :
    ∃ (ι : Type) (_ : Fintype ι) (m : ι → ℕ)
      (Γ : ι → IntegralCurve k S.toScheme),
      (∀ i, 0 < m i) ∧
      fiberCycle π hπ y = ∑ i, (m i : ℤ) • (Γ i).fundamentalClass ∧
      (⋃ i, Set.range (Γ i).ι.base) = π.base ⁻¹' {y} ∧
      _root_.IsConnected (π.base ⁻¹' {y}) ∧
      (∀ i, (Γ i).IsSmoothRational) := by
  have hblπ : AlgebraicGeometry.Surjective (bl ≫ ruledSurface.π L) := by
    rw [← hπfac]
    exact hπ
  obtain ⟨ι₀, hι₀, T, hTrat, hTcov, hTconn⟩ := tower_cover_probe L y hy bl hβ hblπ
  obtain ⟨ι, hι, m, Γ, hm, hΓinj, hΓcov, hΓdec⟩ := fiberDivisor_eq_sum π hπ y hy
  letI : Fintype ι₀ := hι₀
  letI : Fintype ι := hι
  have hΓrat : ∀ i, (Γ i).IsSmoothRational := by
    apply component_rat_probe T Γ hTrat
    calc
      (⋃ j, Set.range (T j).ι.base) = bl.base ⁻¹' ((ruledSurface.π L).base ⁻¹' {y}) := hTcov
      _ = π.base ⁻¹' {y} := by
        ext z
        have hbasefac := congrArg (fun f => f.base) hπfac
        have hzfac := congrArg (fun f => f z) hbasefac.symm
        change (bl ≫ ruledSurface.π L).base z = y ↔ π.base z = y
        rw [hzfac]
      _ = ⋃ i, Set.range (Γ i).ι.base := hΓcov.symm
  refine ⟨ι, hι, m, Γ, hm, hΓdec, hΓcov, ?_, hΓrat⟩
  have hconn' : _root_.IsConnected (bl.base ⁻¹' ((ruledSurface.π L).base ⁻¹' {y})) := hTconn
  have hset : bl.base ⁻¹' ((ruledSurface.π L).base ⁻¹' {y}) = π.base ⁻¹' {y} := by
    ext z
    have hbasefac := congrArg (fun f => f.base) hπfac
    have hzfac := congrArg (fun f => f z) hbasefac.symm
    change (bl ≫ ruledSurface.π L).base z = y ↔ π.base z = y
    rw [hzfac]
  exact hset ▸ hconn'

/-- **Special fibres of the resolved ruled surface.** For a tower of point blowups `bl : S → P(O ⊕ L)`
and `π = bl ≫ π_W`, the fibre cycle over a closed point `y` is `∑ mᵢ [Γᵢ]` with `mᵢ > 0`, the `Γᵢ` cover
`π⁻¹(y)`, the fibre is connected, and each `Γᵢ` is a smooth rational curve. -/
theorem special_fiber_rational_connected {k : Type u} [Field k] [IsAlgClosed k]
    {S : SmoothProjectiveSurface k} {C : SmoothProjectiveCurve k}
    (L : LineBundle C.toVariety)
    (bl : S.toScheme ⟶ (ruledSurface L).toScheme)
    (hβ : IsBlowupTower bl) {U : Set (ruledSurface L).toScheme}
    (hbl : IsBlowupTowerAvoiding bl U)
    (π : S.toScheme ⟶ C.toScheme) (hπfac : π = bl ≫ ruledSurface.π L) (hπ : AlgebraicGeometry.Surjective π)
    (y : C.toScheme) (hy : IsClosed ({y} : Set C.toScheme)) :
    ∃ (ι : Type) (_ : Fintype ι) (m : ι → ℕ)
      (Γ : ι → IntegralCurve k S.toScheme),
      (∀ i, 0 < m i) ∧
      fiberCycle π hπ y = ∑ i, (m i : ℤ) • (Γ i).fundamentalClass ∧
      (⋃ i, Set.range (Γ i).ι.base) = π.base ⁻¹' {y} ∧
      _root_.IsConnected (π.base ⁻¹' {y}) ∧
      (∀ i, (Γ i).IsSmoothRational) := by
  exact special_fiber_probe L bl hβ hbl π hπfac hπ y hy

end
