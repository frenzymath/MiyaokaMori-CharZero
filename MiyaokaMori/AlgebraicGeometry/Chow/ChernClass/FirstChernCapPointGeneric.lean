import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.RationalSections.RationalSectionOrdRestrict
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.FirstChernCapCycle
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.PointClosureKrullDim
import MiyaokaMori.AlgebraicGeometry.Morphisms.ClosedImmersionCycles
import MiyaokaMori.AlgebraicGeometry.Divisors.RationalSections.RationalSectionDivisor
import MiyaokaMori.AlgebraicGeometry.Varieties.Points.ReducedInducedSubschemeIntegral
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # The cap with the first Chern class at the generic point

Let `X` be integral and locally Noetherian, `L` a line bundle on `X` and `η` the generic point. Then there
is a nonzero element `s′` of the stalk of `L` at `η` such that the cycle-level `c₁(L) ∩ [X]` —
`firstChernCapPoint L η`, which by definition is `ι_{η*} div_{ι_η^*L}(s₀)` for `ι_η : X.pointClosure η → X`
and a chosen `s₀` — equals `div_L(s′)` (`L.rationalSectionDivisor s′`). Accompanying facts: (a) the
coefficient of the pushforward along a closed immersion `i` at an image point is the original coefficient,
`(i_* c)(i x) = c x`; (b) an isomorphism of module sheaves on the same scheme does not change
`rationalSectionOrd`; (c) for `X` integral, `ι_η` is an isomorphism (a surjective closed immersion into a
reduced scheme).

Proof:
1. (c): the image of `ι_η` is `closure{η}`, the whole space (Mathlib's `range_subschemeι` +
   `coe_support_vanishingIdeal`); Mathlib's `isIso_of_isClosedImmersion_of_surjective`.
2. (a): a closed immersion is injective on points, so the fiber is a single point (`finsum_mem_singleton`);
   heights are preserved (`Scheme.Hom.height_of_isClosedImmersion`); the residue degree is `1`
   (`closedImmersion_residueDegree_eq_one`).
3. (b): take a generator `t` of `M_z` and `g` with `g • j t = s`; `e` is linear and invertible on stalks, sends
   `t` to a generator of `N_z`, and `g • j(e t) = e_η s` (`moduleStalkToGenericFiber_naturality`); apply the
   generator formula for `rationalSectionOrd` on both sides.
4. Main statement: `ι_η` is an isomorphism, hence an open immersion, and `ι_η^*L ≅ L.restrict ι_η`
   (Mathlib's `restrictFunctorIsoPullback`). Let `s₁ := e_η s₀`, `s′ := Φ s₁` (`genericStalkMap`). Compare
   pointwise: for any `z = ι z′` (surjectivity from step 1),
   `(ι_* div_{ι^*L}(s₀))(ι z′) = ord_{z′,ι^*L}(s₀)` (step 2) `= ord_{z′,L|}(s₁)` (step 3)
   `= ord_{ι z′,L}(s′)` (restriction of `ord` along open immersions).

Source: Stacks 02SJ (for `X` integral, `c₁(L) ∩ [X] = [div_L(s)]`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
universe u
open CategoryTheory AlgebraicGeometry Opposite
noncomputable section
namespace MiyaokaMori.FirstChernCapPointGeneric
open AlgebraicGeometry.Scheme.Modules MiyaokaMori.RationalSectionOrdRestrict

/-- The coefficient of the pushforward along a closed immersion at an image point is the original
coefficient (heights preserved, residue degree `1`, single-point fibers). -/
theorem properPushforward_closedImmersion_apply {W X : Scheme.{u}} (i : W ⟶ X)
    [IsClosedImmersion i] (c : AlgebraicCycle W ℤ) (x : W) :
    AlgebraicGeometry.AlgebraicCycle.properPushforward i c (i x) = c x := by
  have happ : AlgebraicGeometry.AlgebraicCycle.properPushforward i c (i x) =
      ∑ᶠ z ∈ i.base ⁻¹' {i x}, c z *
        ((AlgebraicCycle.mapCoeff i (Order.height (α := W)) (Order.height (α := X)) z : ℕ) : ℤ) :=
    rfl
  have hinj : Function.Injective i.base := i.isClosedEmbedding.injective
  have hset : i.base ⁻¹' {i x} = {x} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact ⟨fun h => hinj h, fun h => h ▸ rfl⟩
  rw [happ, hset, finsum_mem_singleton]
  unfold AlgebraicCycle.mapCoeff
  rw [if_pos (Scheme.Hom.height_of_isClosedImmersion i x).symm,
    Intersection.closedImmersion_residueDegree_eq_one]
  simp

/-- An isomorphism of module sheaves on the same scheme does not change the order of a rational section. -/
theorem rationalSectionOrd_iso {W : Scheme.{u}} [IsIntegral W] [IsLocallyNoetherian W]
    {M N : W.Modules} [M.IsLineBundle] [N.IsLineBundle] (e : M ≅ N)
    (s : M.stalk (genericPoint W)) (hs : s ≠ 0) (z : W) :
    M.rationalSectionOrd s z =
      N.rationalSectionOrd (moduleStalkMap W (genericPoint W) e.hom s) z := by
  obtain ⟨t, ht⟩ := Scheme.Modules.exists_stalk_generator M z
  have hinvhom : ∀ (x : W) (n : N.presheaf.stalk x),
      moduleStalkMap W x e.hom (moduleStalkMap W x e.inv n) = n := fun x n =>
    congrArg (fun F => (ModuleCat.Hom.hom F) n) ((moduleStalkFunctor W x).mapIso e).inv_hom_id
  have hhominv : ∀ (x : W) (m : M.presheaf.stalk x),
      moduleStalkMap W x e.inv (moduleStalkMap W x e.hom m) = m := fun x m =>
    congrArg (fun F => (ModuleCat.Hom.hom F) m) ((moduleStalkFunctor W x).mapIso e).hom_inv_id
  obtain ⟨g, hg⟩ := Scheme.Modules.exists_smul_toGenericFiber_eq M z t ht s
  have ht' : Submodule.span (W.presheaf.stalk z) {moduleStalkMap W z e.hom t} = ⊤ := by
    rw [eq_top_iff]
    intro n _
    have hmem : moduleStalkMap W z e.inv n ∈ Submodule.span (W.presheaf.stalk z) {t} := by
      rw [ht]; trivial
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmem
    refine Submodule.mem_span_singleton.mpr ⟨a, ?_⟩
    rw [← (moduleStalkMap W z e.hom).map_smul, ha, hinvhom]
  have hg' : g • moduleStalkToGenericFiber W N z (moduleStalkMap W z e.hom t) =
      moduleStalkMap W (genericPoint W) e.hom s := by
    rw [← moduleStalkToGenericFiber_naturality, ← (moduleStalkMap W (genericPoint W) e.hom).map_smul]
    exact congrArg _ hg
  have hs' : moduleStalkMap W (genericPoint W) e.hom s ≠ 0 := by
    intro h
    apply hs
    have h2 := congrArg (moduleStalkMap W (genericPoint W) e.inv) h
    rw [map_zero] at h2
    exact (hhominv _ s).symm.trans h2
  rw [Scheme.Modules.rationalSectionOrd_eq_ord_of_generator M z t ht g s hs hg,
    Scheme.Modules.rationalSectionOrd_eq_ord_of_generator N z _ ht' g _ hs' hg']

/-- An isomorphism of module sheaves is injective on stalks: the image of a nonzero element is nonzero. -/
theorem moduleStalkMap_iso_ne_zero {W : Scheme.{u}} {M N : W.Modules} (e : M ≅ N) (x : W)
    (s : M.presheaf.stalk x) (hs : s ≠ 0) : moduleStalkMap W x e.hom s ≠ 0 := by
  intro h
  apply hs
  have hhominv : moduleStalkMap W x e.inv (moduleStalkMap W x e.hom s) = s :=
    congrArg (fun F => (ModuleCat.Hom.hom F) s) ((moduleStalkFunctor W x).mapIso e).hom_inv_id
  have h2 := congrArg (moduleStalkMap W x e.inv) h
  rw [map_zero] at h2
  exact hhominv.symm.trans h2

theorem pointClosureι_genericPoint_surjective {X : Scheme.{u}} [IsIntegral X] :
    Function.Surjective (X.pointClosureι (genericPoint X)) := by
  intro x
  have hr := Scheme.IdealSheafData.range_subschemeι
    (Scheme.IdealSheafData.vanishingIdeal ⟨closure {genericPoint X}, isClosed_closure⟩)
  rw [Scheme.IdealSheafData.coe_support_vanishingIdeal] at hr
  have hx : x ∈ closure ({genericPoint X} : Set X) := by
    rw [genericPoint_spec X |>.def]; trivial
  exact (hr ▸ hx : x ∈ Set.range (Scheme.IdealSheafData.vanishingIdeal
      ⟨closure {genericPoint X}, isClosed_closure⟩).subschemeι)

instance isClosedImmersion_pointClosureι {X : Scheme.{u}} (w : X) :
    IsClosedImmersion (X.pointClosureι w) := by
  unfold Scheme.pointClosureι; exact IsClosedImmersion.instSubschemeι _

/-- For `X` integral, the closure of the generic point (with reduced induced structure) is `X` itself:
`ι_η` is an isomorphism. -/
instance isIso_pointClosureι_genericPoint {X : Scheme.{u}} [IsIntegral X] :
    IsIso (X.pointClosureι (genericPoint X)) := by
  have : Surjective (X.pointClosureι (genericPoint X)) :=
    ⟨pointClosureι_genericPoint_surjective⟩
  exact isIso_of_isClosedImmersion_of_surjective _

/-- **General section form**: `X` integral and locally Noetherian, `L` a line bundle, `ι = ι_η`. For **any**
nonzero rational section `s` of `ι^*L`, `ι_* div_{ι^*L}(s) = div_L(s′)` with `s′` nonzero. -/
theorem properPushforward_pointClosure_rationalSectionDivisor {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [IsLocallyNoetherian (X.pointClosure (genericPoint X))]
    (L : X.Modules) [L.IsLineBundle]
    (s : ((Scheme.Modules.pullback (X.pointClosureι (genericPoint X))).obj L).stalk
      (genericPoint (X.pointClosure (genericPoint X)))) (hs : s ≠ 0) :
    ∃ s' : L.stalk (genericPoint X), s' ≠ 0 ∧
      AlgebraicGeometry.AlgebraicCycle.properPushforward (X.pointClosureι (genericPoint X))
        (((Scheme.Modules.pullback (X.pointClosureι (genericPoint X))).obj L).rationalSectionDivisor s)
        = L.rationalSectionDivisor s' := by
  let ι := X.pointClosureι (genericPoint X)
  let Lw := (Scheme.Modules.pullback ι).obj L
  let e : Lw ≅ L.restrict ι := ((Scheme.Modules.restrictFunctorIsoPullback ι).app L).symm
  have hs₁ := moduleStalkMap_iso_ne_zero e _ s hs
  refine ⟨genericStalkMap ι L (moduleStalkMap _ _ e.hom s), ?_, ?_⟩
  · intro h0
    exact hs₁ (genericStalkMap_injective ι L (h0.trans (genericStalkMap_zero ι L).symm))
  · ext z
    obtain ⟨z', rfl⟩ := pointClosureι_genericPoint_surjective z
    refine (properPushforward_closedImmersion_apply ι _ z').trans ?_
    show Lw.rationalSectionOrd s z' = L.rationalSectionOrd _ (ι z')
    rw [rationalSectionOrd_iso e s hs z']
    exact rationalSectionOrd_restrict ι L _ hs₁ z'

/-- The cycle-level `c₁(L) ∩ [X]` (`firstChernCapPoint L η`) is the divisor of some nonzero rational
section of `L`. -/
theorem firstChernCapPoint_genericPoint {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (L : X.Modules) [L.IsLineBundle] :
    ∃ s : L.stalk (genericPoint X), s ≠ 0 ∧
      firstChernCapPoint L (genericPoint X) = L.rationalSectionDivisor s := by
  have : IsLocallyNoetherian (X.pointClosure (genericPoint X)) :=
    Scheme.isLocallyNoetherian_pointClosure _
  exact properPushforward_pointClosure_rationalSectionDivisor L
    (Classical.epsilon fun t => t ≠ 0)
    (Classical.epsilon_spec (Scheme.Modules.exists_stalk_genericPoint_ne_zero
      ((Scheme.Modules.pullback (X.pointClosureι (genericPoint X))).obj L)))

end MiyaokaMori.FirstChernCapPointGeneric
end
