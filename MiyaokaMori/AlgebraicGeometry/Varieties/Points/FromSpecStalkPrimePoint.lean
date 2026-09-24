import MiyaokaMori.Prelude
import Mathlib.AlgebraicGeometry.Stalk
import Mathlib.AlgebraicGeometry.Properties

/-! # Points of `Spec` of a stalk

A prime `𝔭` of the stalk `O_{X,q}` at a point `q` of a scheme `X` corresponds to a generization
`η := fromSpecStalk q 𝔭` of `q` (Stacks 01J7: the image of `Spec O_{X,q} → X` is the set of
generizations of `q`). Three facts:
1. `η ⤳ q`;
2. `coheight η = ht 𝔭` (`fromSpecStalk` is a topological embedding whose image is closed under
   generization, so it preserves coheight; on `Spec`, coheight equals the height of the prime,
   `idealHeight_eq_coheight`);
3. for `c ∈ O_{X,q}`, its image in `O_{X,η}` lies in the maximal ideal iff `c ∈ 𝔭` (the composite
   `Spec O_{X,η} → Spec O_{X,q} → X` is `fromSpecStalk η`, sending the closed point to `η`; by
   injectivity of the embedding, the image of the closed point in `Spec O_{X,q}` is `𝔭`, i.e.
   `comap (m_η) = 𝔭`).

Sources: Stacks 01J7; Hartshorne II, Exercise 2.7 (the image of `Spec O_{X,q} → X`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory TopologicalSpace Topology
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} (q : X)

/-- The point `η = fromSpecStalk q 𝔭` given by a prime of the stalk is a generization of `q`:
`η ⤳ q` (`range_fromSpecStalk`). -/
theorem fromSpecStalk_apply_specializes (𝔭 : Spec (X.presheaf.stalk q)) :
    X.fromSpecStalk q 𝔭 ⤳ q := by
  have hmem : X.fromSpecStalk q 𝔭 ∈ Set.range (X.fromSpecStalk q) := ⟨𝔭, rfl⟩
  rw [range_fromSpecStalk] at hmem
  exact hmem

/-- `fromSpecStalk q` is a topological embedding whose image is closed under generization, so it
preserves coheight: `coheight (fromSpecStalk q 𝔭) = coheight 𝔭 = ht 𝔭`. -/
theorem coheight_fromSpecStalk_apply (𝔭 : Spec (X.presheaf.stalk q)) :
    Order.coheight (X.fromSpecStalk q 𝔭) = 𝔭.asIdeal.height := by
  rw [idealHeight_eq_coheight]
  have hemb : IsEmbedding (X.fromSpecStalk q).base := (X.fromSpecStalk q).isEmbedding
  have hspec : ∀ a b : Spec (X.presheaf.stalk q),
      X.fromSpecStalk q a ⤳ X.fromSpecStalk q b ↔ a ⤳ b := fun a b =>
    hemb.isInducing.specializes_iff
  have hmono : StrictMono (fun p : Spec (X.presheaf.stalk q) => X.fromSpecStalk q p) := by
    intro a b hab
    rw [lt_iff_le_not_ge] at hab ⊢
    simp only [le_iff_specializes, hspec] at hab ⊢
    exact hab
  symm
  apply Order.coheight_eq_of_strictMono _ hmono
  intro a b hab
  rw [lt_iff_le_not_ge] at hab
  simp only [le_iff_specializes] at hab
  have hbq : b ⤳ q := hab.1.trans (fromSpecStalk_apply_specializes q a)
  have hb : b ∈ Set.range (X.fromSpecStalk q) := by
    rw [range_fromSpecStalk]
    exact hbq
  obtain ⟨a', rfl⟩ := hb
  refine ⟨a', ?_, rfl⟩
  rw [lt_iff_le_not_ge]
  simp only [le_iff_specializes]
  rw [← hspec, ← hspec]
  exact hab

/-- `Spec O_{X,η} → Spec O_{X,q}` sends the closed point to `𝔭`: by
`SpecMap_stalkSpecializes_fromSpecStalk`, `fromSpecStalk_closedPoint` and injectivity of
`fromSpecStalk q`. -/
theorem SpecMap_stalkSpecializes_closedPoint (𝔭 : Spec (X.presheaf.stalk q)) :
    Spec.map (X.presheaf.stalkSpecializes (fromSpecStalk_apply_specializes q 𝔭))
        (IsLocalRing.closedPoint (X.presheaf.stalk (X.fromSpecStalk q 𝔭))) = 𝔭 := by
  have hemb : IsEmbedding (X.fromSpecStalk q).base := (X.fromSpecStalk q).isEmbedding
  apply hemb.injective
  have h := SpecMap_stalkSpecializes_fromSpecStalk (X := X) (fromSpecStalk_apply_specializes q 𝔭)
  have h' := congrArg (fun f : Spec (X.presheaf.stalk (X.fromSpecStalk q 𝔭)) ⟶ X =>
    f (IsLocalRing.closedPoint (X.presheaf.stalk (X.fromSpecStalk q 𝔭)))) h
  simp only [fromSpecStalk_closedPoint] at h'
  exact h'

/-- The image of `c ∈ O_{X,q}` in `O_{X,η}` lies in the maximal ideal iff `c ∈ 𝔭`
(`η = fromSpecStalk q 𝔭`). -/
theorem stalkSpecializes_mem_maximalIdeal_iff (𝔭 : Spec (X.presheaf.stalk q))
    (c : X.presheaf.stalk q) :
    X.presheaf.stalkSpecializes (fromSpecStalk_apply_specializes q 𝔭) c ∈
        IsLocalRing.maximalIdeal (X.presheaf.stalk (X.fromSpecStalk q 𝔭)) ↔
      c ∈ 𝔭.asIdeal := by
  have h : PrimeSpectrum.comap
      (X.presheaf.stalkSpecializes (fromSpecStalk_apply_specializes q 𝔭)).hom
      (IsLocalRing.closedPoint (X.presheaf.stalk (X.fromSpecStalk q 𝔭))) = 𝔭 :=
    SpecMap_stalkSpecializes_closedPoint q 𝔭
  have h2 := congrArg PrimeSpectrum.asIdeal h
  rw [PrimeSpectrum.comap_asIdeal] at h2
  rw [← h2, Ideal.mem_comap]
  rfl

end AlgebraicGeometry.Scheme

end
