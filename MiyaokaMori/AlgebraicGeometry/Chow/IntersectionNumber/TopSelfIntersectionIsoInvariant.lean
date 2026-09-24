import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.Pushforward.ChowPushforwardScheme
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ChowDegreeRatPushforward
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.FirstChernCapPointGeneric
import MiyaokaMori.AlgebraicGeometry.Chow.CapTrivialBundleZero
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.ProjectionFormula
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.TopSelfIntersection
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ZeroCycleDegreeScheme

/-! # Invariance of the top self-intersection under isomorphisms

The top self-intersection is invariant under isomorphisms: if `X ≅ X'` (compatibly with an
isomorphism of base fields `k ≅ k'`) and `L₀ ≅ e^*L`, then `(L₀^d)_X = (L^d)_{X'}`. Used to replace a
fiber (over `κ(t)`) by a scheme over `k` and to exchange isomorphic line bundles (proof of
Proposition 2.4 of the paper). -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry

theorem Scheme.Hom.residueDegree_of_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] (x : X) :
    f.residueDegree x = 1 := by
  unfold Scheme.Hom.residueDegree
  let _ := (f.residueFieldMap x).hom.toAlgebra
  exact Algebra.finrank_eq_one_iff_bijective_algebraMap.mpr
    (ConcreteCategory.bijective_of_isIso (f.residueFieldMap x))

theorem Scheme.Hom.residueDegree_comp_isIso {k k' : Type u} [Field k] [Field k'] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (τ : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of k'))
    [IsIso τ] (x : X) :
    (p ≫ τ).residueDegree x = p.residueDegree x := by
  rw [← Scheme.Hom.residueFieldDegree_eq_residueDegree,
    AlgebraicGeometry.Intersection.residueFieldDegree_comp τ p x,
    Scheme.Hom.residueFieldDegree_eq_residueDegree, Scheme.Hom.residueDegree_of_isIso, one_mul]

theorem Scheme.dimension_eq_of_iso {X Y : Scheme.{u}} (e : X ≅ Y) :
    X.dimension = Y.dimension := by
  unfold Scheme.dimension
  rw [IsHomeomorph.topologicalKrullDim_eq _ e.hom.homeomorph.isHomeomorph]

theorem pointClosureDimension_eq_of_iso {X Y : Scheme.{u}} (e : X ≅ Y) (x : X) :
    AlgebraicGeometry.Intersection.pointClosureDimension X x =
      AlgebraicGeometry.Intersection.pointClosureDimension Y (e.hom x) := by
  simp only [AlgebraicGeometry.Intersection.pointClosureDimension_eq_topologicalKrullDim_closure]
  have h : e.hom.homeomorph '' closure ({x} : Set X) = closure {e.hom x} := by
    rw [Homeomorph.image_closure, Set.image_singleton]; rfl
  exact IsHomeomorph.topologicalKrullDim_eq _
    ((e.hom.homeomorph.image (closure {x})).trans (Homeomorph.setCongr h)).isHomeomorph

theorem mem_genericPoints_iff_of_iso {X Y : Scheme.{u}} (e : X ≅ Y) (x : X) :
    e.hom x ∈ genericPoints Y ↔ x ∈ genericPoints X := by
  let h := e.hom.homeomorph
  constructor
  · intro hy
    have := preimage_mem_irreducibleComponents hy h.isOpenEmbedding
      ⟨e.hom x, subset_closure rfl, ⟨x, rfl⟩⟩
    have hpre : h ⁻¹' closure ({e.hom x} : Set Y) = closure {x} := by
      rw [Homeomorph.preimage_closure]
      congr 1
      ext y
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact h.injective.eq_iff
    rwa [hpre] at this
  · intro hx
    have := preimage_mem_irreducibleComponents hx h.symm.isOpenEmbedding
      ⟨x, subset_closure rfl, ⟨e.hom x, h.symm_apply_apply x⟩⟩
    have hpre : h.symm ⁻¹' closure ({x} : Set X) = closure {e.hom x} := by
      rw [Homeomorph.preimage_closure]
      congr 1
      ext y
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact h.symm_apply_eq
    rwa [hpre] at this

theorem stalkLength_eq_of_iso {X Y : Scheme.{u}} (e : X ≅ Y) (x : X) :
    AlgebraicGeometry.Intersection.stalkLength X x = AlgebraicGeometry.Intersection.stalkLength Y (e.hom x) := by
  unfold AlgebraicGeometry.Intersection.stalkLength
  let φ : Y.presheaf.stalk (e.hom x) ≃+* X.presheaf.stalk x :=
    (asIso (e.hom.stalkMap x)).commRingCatIsoToRingEquiv
  let _ : Algebra (Y.presheaf.stalk (e.hom x)) (X.presheaf.stalk x) := φ.toRingHom.toAlgebra
  let ψ : Y.presheaf.stalk (e.hom x) ≃ₗ[Y.presheaf.stalk (e.hom x)] X.presheaf.stalk x :=
    { φ with map_smul' := fun r s => map_mul φ r s }
  rw [ψ.length_eq]
  exact (Module.length_eq_of_surjective φ.surjective).symm

theorem integralFundamentalMultiplicity_eq_of_iso {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    [IsLocallyNoetherian Y] (e : X ≅ Y) (x : X) :
    AlgebraicGeometry.Intersection.integralFundamentalMultiplicity X x =
      AlgebraicGeometry.Intersection.integralFundamentalMultiplicity Y (e.hom x) := by
  have h : AlgebraicGeometry.Intersection.fundamentalMultiplicity X x =
      AlgebraicGeometry.Intersection.fundamentalMultiplicity Y (e.hom x) := by
    unfold AlgebraicGeometry.Intersection.fundamentalMultiplicity
    rw [mem_genericPoints_iff_of_iso e x, stalkLength_eq_of_iso e x]
  unfold AlgebraicGeometry.Intersection.integralFundamentalMultiplicity
  congr 1
  exact Nat.cast_injective (R := ℕ∞) (by rw [ENat.natCast_lift, ENat.natCast_lift, h])

theorem Scheme.fundamentalCycle_properPushforward_of_iso {X Y : Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (e : X ≅ Y) (d : ℕ) :
    AlgebraicGeometry.AlgebraicCycle.properPushforward e.hom (X.fundamentalCycle d) = Y.fundamentalCycle d := by
  ext y
  obtain ⟨x, rfl⟩ : ∃ x, e.hom x = y := ⟨e.inv y, by rw [← Scheme.Hom.comp_apply]; simp⟩
  rw [MiyaokaMori.FirstChernCapPointGeneric.properPushforward_closedImmersion_apply e.hom _ x]
  show (if AlgebraicGeometry.Intersection.pointClosureDimension X x = d
      then AlgebraicGeometry.Intersection.integralFundamentalMultiplicity X x else 0) =
    (if AlgebraicGeometry.Intersection.pointClosureDimension Y (e.hom x) = d
      then AlgebraicGeometry.Intersection.integralFundamentalMultiplicity Y (e.hom x) else 0)
  rw [pointClosureDimension_eq_of_iso e x, integralFundamentalMultiplicity_eq_of_iso e x]

theorem chowPushforward_fundamentalChowClass_of_iso {k : Type u} [Field k] {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k))] [Y.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k))]
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    (e : X ≅ Y) [e.hom.IsOver (Spec (CommRingCat.of k))] (d : ℕ) :
    chowPushforward e.hom d (X.fundamentalChowClass d) = Y.fundamentalChowClass d := by
  have hdesc : PushforwardDescends e.hom d := fun β γ hβγ =>
    AlgebraicCycle.properPushforward_rationallyEquivalent (k := k) e.hom d β γ hβγ
  have hp : chowPushforward e.hom d = QuotientAddGroup.map _ _
      (cyclePushforwardHom e.hom d hdesc) (cyclePushforwardHom_rel e.hom d hdesc) := by
    unfold chowPushforward
    exact dif_pos hdesc
  rw [hp]
  unfold Scheme.fundamentalChowClass
  change ChowGroup.mk (cyclePushforwardHom e.hom d hdesc ⟨X.fundamentalCycle d, _⟩) =
    ChowGroup.mk ⟨Y.fundamentalCycle d, _⟩
  congr 1
  exact Subtype.ext (Scheme.fundamentalCycle_properPushforward_of_iso e d)

/-- Iterated projection formula: `f_*(c₁(L₀)^e ∩ α) = c₁(L)^e ∩ f_*α` when `L₀ ≅ f^*L`. -/
theorem chowPushforward_capPow_of_pullbackIso {k : Type u} [Field k] {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k))] [Y.Over (Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))]
    [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (CommRingCat.of k))] [IsProper p]
    (L : Y.Modules) [L.IsLineBundle] (L₀ : X.Modules) [L₀.IsLineBundle]
    (hL : Nonempty (L₀ ≅ (Scheme.Modules.pullback p).obj L)) (n d : ℕ)
    (α : ChowGroup X (d + n)) :
    chowPushforward p d (firstChernClass.capPow L₀ n d α) =
      firstChernClass.capPow L n d (chowPushforward p (d + n) α) := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih =>
    obtain ⟨f⟩ := hL
    show chowPushforward p d (firstChernClass.capPow L₀ n d (firstChernClass L₀ (d + n + 1) α)) =
      firstChernClass.capPow L n d (firstChernClass L (d + n + 1) (chowPushforward p (d + n + 1) α))
    rw [ih d (firstChernClass L₀ (d + n + 1) α)]
    congr 1
    rw [firstChernClass_congr L₀ _ f (d + n)]
    exact chowPushforward_firstChernClass_pullback (k := k) p L (d + n) α

private theorem rawZeroCycleDegree_congr_hom {k : Type u} [Field k] {X : Scheme.{u}}
    (f g : X ⟶ Spec (CommRingCat.of k)) [IsProper f] [IsProper g] (h : f = g)
    (β : AlgebraicGeometry.Intersection.DimensionCycle X 0) :
    AlgebraicGeometry.Intersection.rawZeroCycleDegree f β = AlgebraicGeometry.Intersection.rawZeroCycleDegree g β := by
  subst h
  rfl

theorem ChowGroup.degreeOver_chowPushforward_of_iso {k : Type u} [Field k] {X Y : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k))] [Y.Over (Spec (CommRingCat.of k))]
    (hX : IsProperOver k X) (hY : IsProperOver k Y)
    (e : X ≅ Y) [e.hom.IsOver (Spec (CommRingCat.of k))] (α : ChowGroup X 0) :
    ChowGroup.degreeOver k Y hY (chowPushforward e.hom 0 α) = ChowGroup.degreeOver k X hX α := by
  have : IsProper (X ↘ Spec (CommRingCat.of k)) := hX
  have : IsProper (Y ↘ Spec (CommRingCat.of k)) := hY
  obtain ⟨c, rfl⟩ := QuotientAddGroup.mk_surjective α
  have hdesc : PushforwardDescends e.hom 0 := fun β γ hβγ =>
    AlgebraicCycle.properPushforward_rationallyEquivalent (k := k) e.hom 0 β γ hβγ
  have hp : chowPushforward e.hom 0 = QuotientAddGroup.map _ _
      (cyclePushforwardHom e.hom 0 hdesc) (cyclePushforwardHom_rel e.hom 0 hdesc) := by
    unfold chowPushforward
    exact dif_pos hdesc
  rw [hp]
  change AlgebraicCycle.degree (k := k)
      ((cyclePushforwardHom e.hom 0 hdesc c : ↥(cycleSubgroup Y 0)) : AlgebraicCycle Y ℤ) =
    AlgebraicCycle.degree (k := k) (c : AlgebraicCycle X ℤ)
  -- `rawZeroCycleDegree` is an abbrev of `AlgebraicCycle.degree`: equal by definition
  change AlgebraicGeometry.Intersection.rawZeroCycleDegree (Y ↘ Spec (CommRingCat.of k))
      (cyclePushforwardHom e.hom 0 hdesc c) =
    AlgebraicGeometry.Intersection.rawZeroCycleDegree (X ↘ Spec (CommRingCat.of k)) c
  have heq : cyclePushforwardHom e.hom 0 hdesc c =
      AlgebraicGeometry.Intersection.dimensionProperPushforward e.hom 0 c :=
    Subtype.ext rfl
  rw [heq, AlgebraicGeometry.Intersection.rawZeroCycleDegree_properPushforward
    (Y ↘ Spec (CommRingCat.of k)) e.hom c]
  exact rawZeroCycleDegree_congr_hom _ _ (comp_over e.hom (Spec (CommRingCat.of k))) _

theorem ChowGroup.degreeOver_eq_of_eq_comp {k k' : Type u} [Field k] [Field k'] {X : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k))] [X.Over (Spec (CommRingCat.of k'))]
    (hX : IsProperOver k X) (hX' : IsProperOver k' X)
    (τ : Spec (CommRingCat.of k) ⟶ Spec (CommRingCat.of k')) [IsIso τ]
    (h : (X ↘ Spec (CommRingCat.of k')) = (X ↘ Spec (CommRingCat.of k)) ≫ τ)
    (α : ChowGroup X 0) :
    ChowGroup.degreeOver k' X hX' α = ChowGroup.degreeOver k X hX α := by
  obtain ⟨c, rfl⟩ := QuotientAddGroup.mk_surjective α
  change AlgebraicCycle.degree (k := k') (c : AlgebraicCycle X ℤ) =
    AlgebraicCycle.degree (k := k) (c : AlgebraicCycle X ℤ)
  unfold AlgebraicCycle.degree
  rw [h]
  simp only [Scheme.Hom.residueDegree_comp_isIso]

theorem topSelfIntersection_eq_of_iso_over {k : Type u} [Field k] {X X' : Scheme.{u}}
    [X.Over (Spec (CommRingCat.of k))] [X'.Over (Spec (CommRingCat.of k))]
    (e : X ≅ X') [e.hom.IsOver (Spec (CommRingCat.of k))]
    (hX : IsProperOver k X) (hX' : IsProperOver k X') (L : X'.Modules) [L.IsLineBundle]
    (L₀ : X.Modules) [L₀.IsLineBundle]
    (hL : Nonempty (L₀ ≅ (Scheme.Modules.pullback e.hom).obj L)) :
    topSelfIntersection X hX L₀ = topSelfIntersection X' hX' L := by
  have : IsProper (X ↘ Spec (CommRingCat.of k)) := hX
  have : IsProper (X' ↘ Spec (CommRingCat.of k)) := hX'
  have : IsLocallyNoetherian X :=
    LocallyOfFiniteType.isLocallyNoetherian (X ↘ Spec (CommRingCat.of k))
  have : IsLocallyNoetherian X' :=
    LocallyOfFiniteType.isLocallyNoetherian (X' ↘ Spec (CommRingCat.of k))
  have key : ∀ d d' : ℕ, d = d' →
      ChowGroup.degreeOver k X hX (firstChernClass.capPow L₀ d 0
        (cast (congrArg (ChowGroup X) (zero_add d).symm) (X.fundamentalChowClass d))) =
      ChowGroup.degreeOver k X' hX' (firstChernClass.capPow L d' 0
        (cast (congrArg (ChowGroup X') (zero_add d').symm) (X'.fundamentalChowClass d'))) := by
    intro d d' hdd
    subst hdd
    rw [← ChowGroup.degreeOver_chowPushforward_of_iso hX hX' e, chowPushforward_capPow_of_pullbackIso (k := k) e.hom L L₀ hL d 0]
    congr 2
    have key2 : ∀ (m : ℕ) (hm : d = m),
        chowPushforward e.hom m (cast (congrArg (ChowGroup X) hm) (X.fundamentalChowClass d)) =
          cast (congrArg (ChowGroup X') hm) (chowPushforward e.hom d (X.fundamentalChowClass d)) := by
      intro m hm
      subst hm
      rfl
    rw [key2 (0 + d) (zero_add d).symm, chowPushforward_fundamentalChowClass_of_iso (k := k) e d]
  exact key _ _ (Scheme.dimension_eq_of_iso e)

end AlgebraicGeometry

theorem topSelfIntersection_eq_of_iso {k k' : Type u} [Field k] [Field k']
    {X X' : AlgebraicGeometry.Scheme.{u}}
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [X'.Over (AlgebraicGeometry.Spec (CommRingCat.of k'))] (σ : k ≃+* k') (e : X ≅ X')
    (he : e.hom ≫ (X' ↘ AlgebraicGeometry.Spec (CommRingCat.of k')) =
      (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) ≫
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom (σ.symm : k' →+* k)))
    (hX : IsProperOver k X) (hX' : IsProperOver k' X') (L : X'.Modules) [L.IsLineBundle]
    (L₀ : X.Modules) [L₀.IsLineBundle]
    (hL : Nonempty (L₀ ≅ (AlgebraicGeometry.Scheme.Modules.pullback e.hom).obj L)) :
    AlgebraicGeometry.topSelfIntersection X hX L₀ = AlgebraicGeometry.topSelfIntersection X' hX' L := by
  have : AlgebraicGeometry.IsProper (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := hX
  have : AlgebraicGeometry.IsProper (X' ↘ AlgebraicGeometry.Spec (CommRingCat.of k')) := hX'
  let _ : X.Over (AlgebraicGeometry.Spec (CommRingCat.of k')) :=
    ⟨e.hom ≫ (X' ↘ AlgebraicGeometry.Spec (CommRingCat.of k'))⟩
  have : e.hom.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k')) := ⟨rfl⟩
  have hX₂ : IsProperOver k' X :=
    inferInstanceAs (AlgebraicGeometry.IsProper
      (e.hom ≫ (X' ↘ AlgebraicGeometry.Spec (CommRingCat.of k'))))
  have : IsIso (CommRingCat.ofHom (σ.symm : k' →+* k)) :=
    (σ.symm.toCommRingCatIso).isIso_hom
  have h1 : AlgebraicGeometry.topSelfIntersection X hX L₀ =
      AlgebraicGeometry.topSelfIntersection X hX₂ L₀ := by
    unfold AlgebraicGeometry.topSelfIntersection
    exact (AlgebraicGeometry.ChowGroup.degreeOver_eq_of_eq_comp hX hX₂
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (σ.symm : k' →+* k))) he _).symm
  rw [h1]
  exact AlgebraicGeometry.topSelfIntersection_eq_of_iso_over e hX₂ hX' L L₀ hL

end
