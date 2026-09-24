import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Morphisms.ConstantMorphism
import MiyaokaMori.AlgebraicGeometry.Morphisms.FiberRestriction
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.GenericallyScalar
import MiyaokaMori.Paper.S3PositiveLine.Realization.ScalarJetFromConstantFiber
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.SectionPullbackNotZeroAt
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotalSpaceIsIntegral
import MiyaokaMori.Paper.S3PositiveLine.Realization.ProjectivizationOfNowhereZeroTuple
import MiyaokaMori.Paper.S3PositiveLine.Realization.SeedMinorPullbackEqZeroOfCompEq
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpaceHomUniversallyOpen
import MiyaokaMori.AlgebraicGeometry.Morphisms.ClosedPointResidueUnique
import MiyaokaMori.Paper.S3PositiveLine.Realization.ProjectivizationOnZeroSection
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleNonvanishingLocus
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.UnitNonvanishingSection
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleSectionGenericGermZero

/-! # Nonconstancy on a general ruled fiber

The projective map is nonconstant on a general ruled fiber: on the general fiber `Φ₀ ≠ f∘ρ∘p_L`, and there is a
nonempty open `V ⊆ C̃` such that for every closed point `y ∈ V` the restriction `Φ₀|_{U_y}` is nonconstant
(by contradiction: otherwise the `k`-jet would be generically scalar). Proof of Theorem 4.2 of the paper.

Proof (the passage from the generic point to general closed fibers uses universal openness rather than the
`ξ^q`-coefficients):
1. First conjunct: relatively constant ⇒ generically scalar, contradicting `hns`.
2. `hns` ⇒ some seed minor `m = M_{ab} ≠ 0` (contrapositive of `generically_scalar_of_minors_eq_zero`).
3. `Tot(L)` is integral, so `m` does not vanish at the generic point; `W := U ∩ {m ≠ 0}` is a nonempty open
   containing the generic point; `V := p_L(W)` is open (`p_L` is universally open) and nonempty.
4. Take a closed point `y ∈ V` and `p ∈ W` above `y`. Suppose `Φ₀|_{U_y}` is constant with value `x₀`. The
   zero-section point `0_y ∈ U_y` has `Φ₀(0_y) = f(ρ(y))`, so `x₀ = f(ρ(y)) =: x`, a closed point.
5. On `Spec κ(p)`, `Φ₀` and `f∘ρ∘p_L` are both `k`-morphisms constant with value `x`, hence equal
   (`κ(x) = k`); so `m` pulls back to zero along `Spec κ(p) → U → Tot(L)`, i.e. `m` vanishes at `p`,
   contradicting `p ∈ W`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The line bundle `p_L^*A_ρ ⊗ p_L^*ρ^*O(1)|_f` containing the seed minors `seedMinor` (a transparent abbreviation). -/
abbrev seedMinorBundle {k : Type u} [Field k]
    {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}
    (f : C.toScheme ⟶ X.toScheme) (ρ : FiniteCover k C) (L : LineBundle ρ.source.toVariety) :
    (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.Modules :=
  AlgebraicGeometry.Scheme.Modules.tensor
    ((AlgebraicGeometry.Scheme.Modules.pullback
      (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
      (seedBundlePullback f ρ).toModules)
    ((AlgebraicGeometry.Scheme.Modules.pullback
      (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
      ((AlgebraicGeometry.Scheme.Modules.pullback ρ.hom).obj
        (seedLineBundle X.embedding f)))

theorem nonconstant_on_general_fiber {k : Type u} [Field k] [IsAlgClosed k]
    {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}
    {f : C.toScheme ⟶ X.toScheme} [D : MMSetup f] {ρ : FiniteCover k C}
    {L : LineBundle ρ.source.toVariety} {κ : ℕ} (jet : BasedJet f ρ L κ)
    (hns : ¬ jet.IsGenericallyScalar)
    (P : Fin (X.embDim + 1) →
      (((AlgebraicGeometry.Scheme.Modules.pullback
          (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
          (seedBundlePullback f ρ).toModules).val.obj
          (Opposite.op ⊤) : Type u))
    (hjet : ∀ ℓ, BasedJet.coneCoordinate jet ℓ
      = restrictToThickening L (seedBundlePullback f ρ) κ (P ℓ))
    (hzero : ∀ ℓ, AlgebraicGeometry.Scheme.restrictToZeroSection L.toModules (P ℓ)
      = seedCoordPullback f ρ (D.coord ℓ))
    (U : (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.Opens)
    (Φ₀ : U.toScheme ⟶ X.toScheme) (hΦ : IsTupleProjectivization _ P U Φ₀)
    (hU0 : Set.range (AlgebraicGeometry.Scheme.zeroSection L.toModules).base
      ⊆ (U : Set (AlgebraicGeometry.Scheme.totalSpace L.toModules).left)) :
    ¬ IsSeedConstantOnGenericRuling f ρ L U Φ₀ ∧
      ∃ V : Set ρ.source.toScheme, IsOpen V ∧ V.Nonempty ∧
        ∀ y ∈ V, IsClosed ({y} : Set ρ.source.toScheme) →
          ¬ IsConstantMorphism
            (fiberRestrict Φ₀ (U.ι ≫ (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom) y) := by
  have hint : AlgebraicGeometry.IsIntegral ρ.source.toScheme := ρ.source.isIntegral
  have hTint : AlgebraicGeometry.IsIntegral (AlgebraicGeometry.Scheme.totalSpace L.toModules).left :=
    AlgebraicGeometry.Scheme.totalSpace_isIntegral L.toModules
  -- first conjunct: relatively constant ⇒ generically scalar, contradicting hns
  refine ⟨fun hconst => hns
    (generically_scalar_of_constant_on_generic_fiber jet P hjet hzero U Φ₀ hΦ hU0 hconst).2, ?_⟩
  -- step 2: there is a nonzero seed minor m := M_{ab}
  obtain ⟨a, b, hm⟩ : ∃ a b, seedMinor f ρ L D.coord P a b ≠ 0 := by
    by_contra h
    exact hns (generically_scalar_of_minors_eq_zero jet P hjet hzero
      (fun i j => by by_contra h'; exact h ⟨i, j, h'⟩))
  -- step 3: m does not vanish at the generic point of Tot(L) (the maximal ideal at the generic point is zero, so a section of a line bundle with zero germ is zero)
  have hgen : genericPoint (AlgebraicGeometry.Scheme.totalSpace L.toModules).left ∈
      AlgebraicGeometry.Scheme.Modules.nonvanishingLocus (seedMinorBundle f ρ L) (seedMinor f ρ L D.coord P a b) := by
    apply AlgebraicGeometry.Scheme.Modules.mem_nonvanishingLocus_of_maximalIdeal_eq_bot
    · exact IsLocalRing.maximalIdeal_eq_bot
    · intro h0
      exact hm (lineBundle_section_eq_zero_of_germ_genericPoint_eq_zero _ _ h0)
  have hne : (U : Set (AlgebraicGeometry.Scheme.totalSpace L.toModules).left).Nonempty := by
    obtain ⟨c⟩ : Nonempty ρ.source.toScheme := inferInstance
    exact ⟨_, hU0 ⟨c, rfl⟩⟩
  have hUη : genericPoint (AlgebraicGeometry.Scheme.totalSpace L.toModules).left ∈
      (U : Set (AlgebraicGeometry.Scheme.totalSpace L.toModules).left) := by
    rw [(genericPoint_spec _).mem_open_set_iff U.isOpen]
    simpa using hne
  -- V := p_L(U ∩ {m ≠ 0}): p_L is universally open, so V is open; the generic point lies in U ∩ {m ≠ 0}, so V is nonempty
  refine ⟨(AlgebraicGeometry.Scheme.totalSpace L.toModules).hom.base ''
      ((U : Set (AlgebraicGeometry.Scheme.totalSpace L.toModules).left) ∩
        (AlgebraicGeometry.Scheme.Modules.nonvanishingLocus (seedMinorBundle f ρ L) (seedMinor f ρ L D.coord P a b) :
          Set (AlgebraicGeometry.Scheme.totalSpace L.toModules).left)),
    AlgebraicGeometry.Scheme.totalSpace_hom_isOpenMap L.toModules _
      (U.isOpen.inter (AlgebraicGeometry.Scheme.Modules.nonvanishingLocus (seedMinorBundle f ρ L) _).isOpen),
    ⟨_, ⟨_, ⟨hUη, hgen⟩, rfl⟩⟩, ?_⟩
  rintro y ⟨p, ⟨hpU, hpnv⟩, hpy⟩ hy hconst
  obtain ⟨x₀, hx₀⟩ := hconst
  -- p as a point p' of U (no anonymous constructor, to avoid instance unification failures)
  obtain ⟨p', hp'⟩ : ∃ p' : U.toScheme, U.ι.base p' = p := ⟨⟨p, hpU⟩, rfl⟩
  have hp'y : (U.ι ≫ (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).base p' = y := by
    change (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom.base (U.ι.base p') = y
    rw [hp']
    exact hpy
  -- the lift z of the zero section to U, and Φ₀ equals ρ ≫ f on the zero section
  have hrange : Set.range (AlgebraicGeometry.Scheme.zeroSection L.toModules).base ⊆ Set.range U.ι.base := by
    rw [AlgebraicGeometry.Scheme.Opens.range_ι]
    exact hU0
  have hz : AlgebraicGeometry.IsOpenImmersion.lift U.ι (AlgebraicGeometry.Scheme.zeroSection L.toModules) hrange
      ≫ U.ι = AlgebraicGeometry.Scheme.zeroSection L.toModules :=
    AlgebraicGeometry.IsOpenImmersion.lift_fac _ _ _
  have hzΦ := zeroSectionLift_comp_eq_of_isTupleProjectivization P hzero U Φ₀ hΦ _ hz
  -- all points of the fiber U_y map to x₀
  have hfib : ∀ u : U.toScheme,
      (U.ι ≫ (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).base u = y → Φ₀.base u = x₀ := by
    intro u hu
    have hmem : u ∈ Set.range ((U.ι ≫ (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).fiberι y).base := by
      rw [AlgebraicGeometry.Scheme.Hom.range_fiberι]
      exact hu
    obtain ⟨q, hq⟩ := hmem
    have := hx₀ q
    rw [fiberRestrict_eq] at this
    rw [← hq]
    exact this
  -- the zero-section point z y lies in U_y, so x₀ = f(ρ(y))
  have hzy : (U.ι ≫ (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).base
      ((AlgebraicGeometry.IsOpenImmersion.lift U.ι (AlgebraicGeometry.Scheme.zeroSection L.toModules) hrange).base y)
      = y := by
    change (AlgebraicGeometry.IsOpenImmersion.lift U.ι (AlgebraicGeometry.Scheme.zeroSection L.toModules) hrange
      ≫ U.ι ≫ (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).base y = y
    rw [← Category.assoc, hz, AlgebraicGeometry.Scheme.zeroSection_comp]
    rfl
  have hx₀y : x₀ = f.base (ρ.hom.base y) := by
    rw [← hfib _ hzy]
    change (AlgebraicGeometry.IsOpenImmersion.lift U.ι (AlgebraicGeometry.Scheme.zeroSection L.toModules) hrange
      ≫ Φ₀).base y = _
    rw [hzΦ]
    rfl
  -- p' := p as a point of U; Φ₀ p' = f(ρ(y))
  have hp'Φ : Φ₀.base p' = f.base (ρ.hom.base y) := (hfib p' hp'y).trans hx₀y
  -- f, Φ₀, ρ are k-morphisms
  obtain ⟨hc, hcEq⟩ := id D.hcoord
  obtain ⟨hU', hEq⟩ := id hΦ
  have hfk : f ≫ (X.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
      = C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k) := by
    rw [← X.embedding.over, ← Category.assoc, ← hcEq, projectivizationMorphism_comp_over]
  have hΦk : Φ₀ ≫ (X.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
      = U.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k) := by
    rw [← X.embedding.over, ← Category.assoc, hEq, projectivizationMorphism_comp_over]
  have hρk : ρ.hom ≫ (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
      = ρ.source.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k) := ρ.isOver
  -- x := f(ρ(y)) is a closed point of X
  have hxcl : IsClosed ({f.base (ρ.hom.base y)} : Set X.toScheme) := by
    have := AlgebraicGeometry.isClosed_singleton_image_of_isClosed_singleton
      (ρ.source.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
      (X.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) (ρ.hom ≫ f)
      (by rw [Category.assoc, hfk, hρk]) y hy
    exact this
  -- on Spec κ(p'): Φ₀ and the seed map f∘ρ∘p_L are both constant with value x and both k-morphisms, hence equal
  let : (AlgebraicGeometry.Spec (U.toScheme.residueField p')).Over
      (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨U.toScheme.fromSpecResidueField p' ≫ (U.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  have hiO : (U.toScheme.fromSpecResidueField p').IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨rfl⟩
  have hi_apply : ∀ s, (U.toScheme.fromSpecResidueField p').base s = p' :=
    fun s => AlgebraicGeometry.Scheme.fromSpecResidueField_apply _ s
  have hred : AlgebraicGeometry.IsReduced (AlgebraicGeometry.Spec (U.toScheme.residueField p')) :=
    inferInstance
  have heq : U.toScheme.fromSpecResidueField p' ≫ Φ₀
      = U.toScheme.fromSpecResidueField p' ≫ U.ι ≫
          (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ≫ ρ.hom ≫ f := by
    apply AlgebraicGeometry.eq_of_constant_at_closedPoint
      (X.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) _ hxcl
    · intro s
      change Φ₀.base ((U.toScheme.fromSpecResidueField p').base s) = _
      rw [hi_apply, hp'Φ]
    · intro s
      change f.base (ρ.hom.base ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom.base
        (U.ι.base ((U.toScheme.fromSpecResidueField p').base s)))) = _
      rw [hi_apply, hp', hpy]
    · simp only [Category.assoc, hΦk, hfk, hρk]
      rfl
  -- hence the seed minor pulls back to zero along U.ι and Spec κ(p') → U, so m vanishes at p: contradiction
  have hpull := seedMinor_pullback_eq_zero_of_comp_eq P U Φ₀ hΦ
    (U.toScheme.fromSpecResidueField p') heq a b
  have hz1 := isZeroAt_of_sectionPullbackAlong_eq_zero (U.toScheme.fromSpecResidueField p') _
    (sectionPullbackAlong U.ι (seedMinor f ρ L D.coord P a b)) default hpull
  rw [hi_apply] at hz1
  have hz2 := isZeroAt_of_isZeroAt_sectionPullbackAlong U.ι _ (seedMinor f ρ L D.coord P a b) p' hz1
  rw [hp'] at hz2
  exact (AlgebraicGeometry.Scheme.Modules.mem_nonvanishingLocus (seedMinorBundle f ρ L) _ _).mp hpnv hz2

end
