import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Morphisms.FiberRestriction
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.GenericallyScalar
import MiyaokaMori.Paper.S3PositiveLine.Realization.MorphismNearZeroSection
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.SectionPullbackNotZeroAt
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleSectionZeroOfGenericFiberZero
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotalSpaceIsIntegral
import MiyaokaMori.Paper.S3PositiveLine.Realization.ScalarRatioOfSeedMinorsZero
import MiyaokaMori.AlgebraicGeometry.Morphisms.ConeMorphismScaleOfCoordinates
import MiyaokaMori.Paper.S3PositiveLine.Realization.ProjectivizationMinors

/-! # A constant projective map on the general fiber gives a scalar jet

The core of the contradiction in the proof of Theorem 4.2 of the paper: if over `k(C̃)` (on the
general ruled fiber) the projective map is constant (equal to the seed point `f∘ρ`), then all `2×2` minors of the
affine tuple `P` against the seed tuple vanish, hence `P = λ·(seed)` with `λ = 1` on the zero section, and after
truncation `ȷ` is a scalar jet. Two parts: all minors zero ⇒ generically scalar; constant on the general fiber ⇒
all minors zero.

`sectionPullbackAlong` is the one definition (its body is the adjunction unit) and
`AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback` its `Γ`-typed reducible abbrev: `unfold sectionPullbackAlong` does not produce
the `Γ`-typed spelling, so the proofs below use `simp only [sectionPullbackAlong_eq_pullback]` (to reach it) or
plain `unfold sectionPullbackAlong` (to reach the unit).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The `2×2` minors `s_i ξ_j − s_j ξ_i` of the seed tuple: the coordinates are global sections of
    `seedLineBundle X.embedding f` (the type of `D.coord` of `MMSetup`), and `ξ` is the tuple `P` of sections of
    `A_ρ = seedBundlePullback f ρ` on `Tot(L)`. Both are pulled back along `p_L ≫ ρ` and then tensored. -/

noncomputable def seedMinor {k : Type u} [Field k]
    {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}
    (f : C.toScheme ⟶ X.toScheme) (ρ : FiniteCover k C) (L : LineBundle ρ.source.toVariety)
    (coord : Fin (X.embDim + 1) →
      ((seedLineBundle X.embedding f).val.obj (Opposite.op ⊤) : Type u))
    (P : Fin (X.embDim + 1) →
      (((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        (seedBundlePullback f ρ).toModules).val.obj (Opposite.op ⊤) : Type u))
    (i j : Fin (X.embDim + 1)) :
    ((AlgebraicGeometry.Scheme.Modules.tensor
        ((AlgebraicGeometry.Scheme.Modules.pullback
          (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
          (seedBundlePullback f ρ).toModules)
        ((AlgebraicGeometry.Scheme.Modules.pullback
          (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
          ((AlgebraicGeometry.Scheme.Modules.pullback ρ.hom).obj
            (seedLineBundle X.embedding f)))).val.obj
        (Opposite.op ⊤) : Type u) :=
  sectionTensor (P i)
      (sectionPullbackAlong (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom
        (sectionPullbackAlong ρ.hom (coord j)))
    - sectionTensor (P j)
      (sectionPullbackAlong (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom
        (sectionPullbackAlong ρ.hom (coord i)))

def IsSeedConstantOnGenericRuling {k : Type u} [Field k]
    {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}
    (f : C.toScheme ⟶ X.toScheme) (ρ : FiniteCover k C) (L : LineBundle ρ.source.toVariety)
    (U : (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.Opens)
    (Φ₀ : U.toScheme ⟶ X.toScheme) : Prop :=
  haveI : AlgebraicGeometry.IsIntegral ρ.source.carrier := ρ.source.isIntegral
  fiberRestrict Φ₀ (U.ι ≫ (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom)
      (genericPoint ρ.source.toScheme)
    = fiberRestrict (U.ι ≫ (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ≫ ρ.hom ≫ f)
      (U.ι ≫ (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom)
      (genericPoint ρ.source.toScheme)

/- The following private lemmas are used only in the proofs of this file: pullback of sections is natural in
   module maps and preserves subtraction; the formula for sections of a tensor product under two pullbacks;
   a module isomorphism is injective on global sections; projectivization commutes with pullback (together with
   the transport of "nowhere all zero"); the generic point of `Tot(L)` lies over the generic point of `C̃`. -/

theorem sectionPullbackAlong_map {X Y : AlgebraicGeometry.Scheme.{u}} (g : X ⟶ Y) {M M' : Y.Modules}
    (φ : M ⟶ M') (s : (M.val.obj (Opposite.op ⊤) : Type u)) :
    sectionPullbackAlong g (φ.app ⊤ s)
      = ((AlgebraicGeometry.Scheme.Modules.pullback g).map φ).app ⊤ (sectionPullbackAlong g s) := by
  have h := (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction g).unit.naturality φ
  have h2 := congrArg (fun ψ => (AlgebraicGeometry.Scheme.Modules.Hom.app ψ ⊤) s) h
  exact h2

theorem sectionPullbackAlong_sub {X Y : AlgebraicGeometry.Scheme.{u}} (g : X ⟶ Y) {M : Y.Modules}
    (s t : (M.val.obj (Opposite.op ⊤) : Type u)) :
    sectionPullbackAlong g (s - t) = sectionPullbackAlong g s - sectionPullbackAlong g t := by
  unfold sectionPullbackAlong
  exact map_sub _ s t

/-- Sections of a tensor product under two pullbacks. -/
theorem sectionPullbackAlong₂_sectionTensor {X Y Z : AlgebraicGeometry.Scheme.{u}} (i : X ⟶ Y) (g : Y ⟶ Z)
    {M N : Z.Modules} (s : (M.val.obj (Opposite.op ⊤) : Type u)) (t : (N.val.obj (Opposite.op ⊤) : Type u)) :
    (AlgebraicGeometry.Scheme.Modules.pullbackTensorIso i _ _).hom.app ⊤
      (((AlgebraicGeometry.Scheme.Modules.pullback i).map
        (AlgebraicGeometry.Scheme.Modules.pullbackTensorIso g M N).hom).app ⊤
        (sectionPullbackAlong i (sectionPullbackAlong g (sectionTensor s t))))
      = sectionTensor (sectionPullbackAlong i (sectionPullbackAlong g s))
          (sectionPullbackAlong i (sectionPullbackAlong g t)) := by
  rw [← sectionPullbackAlong_map, AlgebraicGeometry.Scheme.Modules.pullbackTensorIso_sectionTensor,
    AlgebraicGeometry.Scheme.Modules.pullbackTensorIso_sectionTensor]
theorem modules_iso_app_top_injective {X : AlgebraicGeometry.Scheme.{u}} {A B : X.Modules} (e : A ≅ B) :
    Function.Injective (fun s : (A.val.obj (Opposite.op ⊤) : Type u) => e.hom.app ⊤ s) := by
  intro s t h
  have h' := congrArg (fun x => e.inv.app ⊤ x) h
  have hc : ∀ x : (A.val.obj (Opposite.op ⊤) : Type u), e.inv.app ⊤ (e.hom.app ⊤ x) = x := by
    intro x
    have := congrArg (fun ψ => (AlgebraicGeometry.Scheme.Modules.Hom.app ψ ⊤) x) e.hom_inv_id
    exact this
  exact (hc s).symm.trans (h'.trans (hc t))

private theorem totalSpace_hom_genericPoint {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L : LineBundle C.toVariety)
    [AlgebraicGeometry.IsIntegral (AlgebraicGeometry.Scheme.totalSpace L.toModules).left]
    [AlgebraicGeometry.IsIntegral C.toScheme] :
    (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom.base
        (genericPoint (AlgebraicGeometry.Scheme.totalSpace L.toModules).left)
      = genericPoint C.toScheme := by
  have hcomp := AlgebraicGeometry.Scheme.zeroSection_comp L.toModules
  have hsurj : Function.Surjective (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom.base := by
    intro x
    refine ⟨(AlgebraicGeometry.Scheme.zeroSection L.toModules).base x, ?_⟩
    have := congrArg (fun g => g.base x) hcomp
    simpa using this
  have h1 := (genericPoint_spec (AlgebraicGeometry.Scheme.totalSpace L.toModules).left).image
    (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom.continuous
  rw [Set.image_univ, hsurj.range_eq, closure_univ] at h1
  exact h1.eq (genericPoint_spec C.toScheme)

theorem exists_projectivizationMorphism_pullback {k : Type u} [Field k]
    {V V' : AlgebraicGeometry.Scheme.{u}}
    [V.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [V'.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (g : V' ⟶ V) [g.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (M : V.Modules) [M.IsLineBundle] {N : ℕ}
    (P : Fin (N + 1) → (M.val.obj (Opposite.op ⊤) : Type u))
    (hP : ∀ v : V, ∃ ℓ, ¬ IsZeroAt (P ℓ) v) :
    ∃ hP' : ∀ v : V', ∃ ℓ, ¬ IsZeroAt (sectionPullbackAlong g (P ℓ)) v,
      g ≫ projectivizationMorphism (k := k) M P hP
        = projectivizationMorphism (k := k) ((AlgebraicGeometry.Scheme.Modules.pullback g).obj M)
            (fun ℓ => sectionPullbackAlong g (P ℓ)) hP' := by
  have hP' : ∀ v : V', ∃ ℓ, ¬ IsZeroAt (sectionPullbackAlong g (P ℓ)) v := by
    intro v
    obtain ⟨ℓ, hℓ⟩ := hP (g.base v)
    exact ⟨ℓ, not_isZeroAt_sectionPullbackAlong g M (P ℓ) v hℓ⟩
  exact ⟨hP', projectivizationMorphism_pullback (k := k) g M P hP hP'⟩

/- The seed coordinates are the `D.coord` of `MMSetup` (the homogeneous coordinate sections of `f`; `D.hcoord` gives
   `IsHomogeneousCoordinateTuple`); the bundle on `Tot(L)` is `A_ρ = seedBundlePullback f ρ = ρ^* f^* O_X(1)`. -/

theorem generically_scalar_of_minors_eq_zero {k : Type u} [Field k]
    {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}
    {f : C.toScheme ⟶ X.toScheme} [D : MMSetup f] {ρ : FiniteCover k C}
    {L : LineBundle ρ.source.toVariety} {κ : ℕ} (jet : BasedJet f ρ L κ)
    (P : Fin (X.embDim + 1) →
      (((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        (seedBundlePullback f ρ).toModules).val.obj
          (Opposite.op ⊤) : Type u))
    (hjet : ∀ ℓ, BasedJet.coneCoordinate jet ℓ
        = restrictToThickening L (seedBundlePullback f ρ) κ (P ℓ))
    (hzero : ∀ ℓ, AlgebraicGeometry.Scheme.restrictToZeroSection L.toModules (P ℓ)
      = seedCoordPullback f ρ (D.coord ℓ))
    (hminor : ∀ i j, seedMinor f ρ L D.coord P i j = 0) :
    jet.IsGenericallyScalar := by
  obtain ⟨V, hV, u, hu1, hP⟩ := exists_scalar_ratio_of_seed_minors_eq_zero (f := f) κ P hzero
    (fun i j => sub_eq_zero.mp (hminor i j))
  refine ⟨V, hV, u, hu1, BasedJet.restrict_eq_scale_of_coneCoordinate jet V u (fun ℓ => ?_)⟩
  rw [hjet ℓ]
  exact hP ℓ

theorem generically_scalar_of_constant_on_generic_fiber {k : Type u} [Field k]
    {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}
    {f : C.toScheme ⟶ X.toScheme} [D : MMSetup f] {ρ : FiniteCover k C}
    {L : LineBundle ρ.source.toVariety} {κ : ℕ} (jet : BasedJet f ρ L κ)
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
    (Φ₀ : U.toScheme ⟶ X.toScheme)
    (hΦ : IsTupleProjectivization _ P U Φ₀)
    (hU0 : Set.range (AlgebraicGeometry.Scheme.zeroSection L.toModules).base
      ⊆ (U : Set (AlgebraicGeometry.Scheme.totalSpace L.toModules).left))
    (hconst : IsSeedConstantOnGenericRuling f ρ L U Φ₀) :
    (∀ i j, seedMinor f ρ L D.coord P i j = 0) ∧ jet.IsGenericallyScalar := by
  have hminor : ∀ a b, seedMinor f ρ L D.coord P a b = 0 := by
    intro a b
    have : AlgebraicGeometry.IsIntegral ρ.source.toScheme := ρ.source.isIntegral
    have : AlgebraicGeometry.IsIntegral (AlgebraicGeometry.Scheme.totalSpace L.toModules).left :=
      AlgebraicGeometry.Scheme.totalSpace_isIntegral L.toModules
    obtain ⟨hU, hEq⟩ := hΦ
    obtain ⟨hc, hcEq⟩ := D.hcoord
    -- notation
    let T := AlgebraicGeometry.Scheme.totalSpace L.toModules
    let η := genericPoint ρ.source.toScheme
    let i := (U.ι ≫ T.hom).fiberι η
    have : i.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) := ⟨rfl⟩
    have : U.ι.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) := ⟨rfl⟩
    have : T.hom.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) := ⟨rfl⟩
    have : ρ.hom.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) := ⟨ρ.isOver⟩
    have hconst' : i ≫ Φ₀ = i ≫ U.ι ≫ T.hom ≫ ρ.hom ≫ f := by
      have h := hconst
      unfold IsSeedConstantOnGenericRuling fiberRestrict at h
      simpa [Category.assoc] using h
    -- seed side: four pullbacks
    obtain ⟨h1, e1⟩ := exists_projectivizationMorphism_pullback (k := k) ρ.hom
      (seedLineBundle X.embedding f) D.coord hc
    obtain ⟨h2, e2⟩ := exists_projectivizationMorphism_pullback (k := k) T.hom _ _ h1
    obtain ⟨h3, e3⟩ := exists_projectivizationMorphism_pullback (k := k) U.ι _ _ h2
    obtain ⟨h4, e4⟩ := exists_projectivizationMorphism_pullback (k := k) i _ _ h3
    -- P side: one pullback
    obtain ⟨h5, e5⟩ := exists_projectivizationMorphism_pullback (k := k) i _ _ hU
    have hR : i ≫ Φ₀ ≫ X.embedding.emb = projectivizationMorphism (k := k) _ _ h4 := by
      rw [← Category.assoc, hconst', ← e4, ← e3, ← e2, ← e1, hcEq]
      simp only [Category.assoc]
    have hproj : projectivizationMorphism (k := k) _ _ h5 = projectivizationMorphism (k := k) _ _ h4 := by
      rw [← e5, ← hEq]
      exact hR
    have hmin := minors_eq_zero_of_projectivizationMorphism_eq (k := k) _ _ _ _ h5 h4 hproj a b
    -- unfold
    have hne : (U : Set (AlgebraicGeometry.Scheme.totalSpace L.toModules).left).Nonempty := by
      obtain ⟨c⟩ : Nonempty ρ.source.toScheme := inferInstance
      exact ⟨_, hU0 ⟨c, rfl⟩⟩
    apply lineBundle_section_eq_zero_of_generic_fiber_eq_zero T.hom
      (totalSpace_hom_genericPoint L) _ U hne
    show sectionPullbackAlong i (sectionPullbackAlong U.ι (seedMinor f ρ L D.coord P a b)) = 0
    unfold seedMinor
    rw [sectionPullbackAlong_sub, sectionPullbackAlong_sub, sub_eq_zero]
    apply modules_iso_app_top_injective ((AlgebraicGeometry.Scheme.Modules.pullback i).mapIso
      (AlgebraicGeometry.Scheme.Modules.pullbackTensorIso U.ι _ _))
    apply modules_iso_app_top_injective (AlgebraicGeometry.Scheme.Modules.pullbackTensorIso i _ _)
    dsimp only [Functor.mapIso_hom]
    have key := fun (s : _) (t : _) => sectionPullbackAlong₂_sectionTensor i U.ι
      (M := (AlgebraicGeometry.Scheme.Modules.pullback T.hom).obj (seedBundlePullback f ρ).toModules)
      (N := (AlgebraicGeometry.Scheme.Modules.pullback T.hom).obj
        ((AlgebraicGeometry.Scheme.Modules.pullback ρ.hom).obj (seedLineBundle X.embedding f))) s t
    rw [key, key]
    exact hmin

  exact ⟨hminor, generically_scalar_of_minors_eq_zero jet P hjet hzero hminor⟩

end
