import MiyaokaMori.Prelude

/-! # `Proj.fromOfGlobalSections` is natural in the source

Used for `zeroSection_comp_toProjBundle`: to compare `zeroSection L ≫ toProjBundle L` with `oSection L` chart by
chart (`projBundle.lift_restrict`), both sides have to be written as `Proj.fromOfGlobalSections` of a ring
homomorphism out of the same graded ring `A(W)`, which requires moving `zeroSection` (restricted) through
`fromOfGlobalSections`.

References: Stacks 01O4 / 01M9 (the morphism `X → Proj A` attached to `A → Γ(X, O)` is functorial in `X`: it is glued
from `D(f r) → D₊(r)`, `Spec` of the degree-0 localization map, and `Spec`/`toSpecΓ` are natural); Mathlib
`AlgebraicGeometry.Proj.fromOfGlobalSections` (Mathlib has `fromOfGlobalSections_preimage_basicOpen /
_morphismRestrict / _resLE / _toSpecZero`, but no naturality in `X`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
-- Mathlib's own proofs about `toBasicOpenOfGlobalSections` / `basicOpenIsoSpecAway` need this
-- (`(Spec S).Opens` vs `Opens (PrimeSpectrum S)`, `Hom.hom` vs `ConcreteCategory.hom`).
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Proj

variable {σ : Type*} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- The hypothesis of `fromOfGlobalSections` is stable under postcomposition with `g^♯`
(`Ideal.map_map`, `Ideal.map_top`). -/
theorem map_irrelevant_comp_eq_top {X Y : AlgebraicGeometry.Scheme.{u}} (g : Y ⟶ X) (f : A →+* Γ(X, ⊤))
    (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤) :
    (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map (g.appTop.hom.comp f) = ⊤ := by
  rw [← Ideal.map_map, hf, Ideal.map_top]

/-- `resLE` respects equality of the morphism (the proof argument is transported). -/
theorem resLE_eq_of_hom_eq {X Y : AlgebraicGeometry.Scheme.{u}}
    {f f' : X ⟶ Y} (h : f = f') {U : Y.Opens} {V : X.Opens} (e : V ≤ f ⁻¹ᵁ U) :
    f.resLE U V e = f'.resLE U V (h ▸ e) := by
  subst h
  rfl

/-- `Spec.map g^♯` restricted to basic opens is `Spec` of the induced map of localizations, transported
along `basicOpenIsoSpecAway` (`basicOpenIsoSpecAway_hom_SpecMap`, `IsLocalization.map_comp`). -/
@[reassoc]
theorem SpecMap_resLE_basicOpenIsoSpecAway_hom {R S : CommRingCat.{u}} (φ : R ⟶ S) (x : R) :
    (Spec.map φ).resLE (PrimeSpectrum.basicOpen x) (PrimeSpectrum.basicOpen (φ x))
        (AlgebraicGeometry.SpecMap_preimage_basicOpen φ x).ge ≫ (basicOpenIsoSpecAway x).hom =
      (basicOpenIsoSpecAway (φ x)).hom ≫
        Spec.map (CommRingCat.ofHom (IsLocalization.map (M := .powers x) (T := .powers (φ x))
          (Localization.Away (φ x)) φ.hom (Submonoid.powers_le.mpr (Submonoid.mem_powers _)))) := by
  rw [← cancel_mono (Spec.map (CommRingCat.ofHom (algebraMap R (Localization.Away x))))]
  simp only [Category.assoc, basicOpenIsoSpecAway_hom_SpecMap,
    ← Spec.map_comp, ← CommRingCat.ofHom_comp, IsLocalization.map_comp]
  rw [CommRingCat.ofHom_comp, Spec.map_comp, basicOpenIsoSpecAway_hom_SpecMap_assoc, CommRingCat.ofHom_hom]
  exact Scheme.Hom.resLE_comp_ι _ _

/-- `g.resLE` moves through `toBasicOpenOfGlobalSections`: the piece `D(g^♯(f t)) → D₊(t)` of `g^♯ ∘ f`
is `g` restricted followed by the piece `D(f t) → D₊(t)` of `f`. -/
theorem resLE_toBasicOpenOfGlobalSections {X Y : AlgebraicGeometry.Scheme.{u}} (g : Y ⟶ X)
    (f : A →+* Γ(X, ⊤)) {t : A} {d : ℕ} (h0d : 0 < d) (hd : t ∈ 𝒜 d)
    (hle : Y.basicOpen (g.appTop (f t)) ≤ g ⁻¹ᵁ X.basicOpen (f t)) :
    g.resLE _ _ hle ≫ toBasicOpenOfGlobalSections 𝒜 f rfl h0d hd =
      toBasicOpenOfGlobalSections 𝒜 (g.appTop.hom.comp f) (x := g.appTop (f t)) rfl h0d hd := by
  simp only [toBasicOpenOfGlobalSections, Scheme.isoOfEq_inv, CommRingCat.ofHom_comp, Spec.map_comp,
    Category.assoc]
  rw [← Scheme.Hom.resLE_eq_morphismRestrict X.toSpecΓ, ← Scheme.Hom.resLE_eq_morphismRestrict Y.toSpecΓ,
    Scheme.Hom.map_resLE_assoc, Scheme.Hom.map_resLE_assoc]
  rw [Scheme.Hom.resLE_comp_resLE_assoc, resLE_eq_of_hom_eq (Scheme.toSpecΓ_naturality g),
    ← Scheme.Hom.resLE_comp_resLE_assoc (e := (Y.toSpecΓ_preimage_basicOpen _).ge)
      (e' := (AlgebraicGeometry.SpecMap_preimage_basicOpen g.appTop (f t)).ge),
    SpecMap_resLE_basicOpenIsoSpecAway_hom_assoc]
  congr 2
  simp only [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
  rw [← RingHom.comp_assoc, IsLocalization.map_comp_map]

/-- **`fromOfGlobalSections` is natural in the scheme**: for `g : Y ⟶ X`,
`g ≫ fromOfGlobalSections 𝒜 f hf = fromOfGlobalSections 𝒜 (g^♯ ∘ f) _`.

## Proof (Stacks 01O4/01M9, Mathlib's construction)
Both sides are morphisms `Y ⟶ Proj 𝒜`; check them on the open cover `{D(g^♯(f r))}` of `Y` given by
`openCoverOfMapIrrelevantEqTop 𝒜 (g^♯ ∘ f) _` (`Scheme.Cover.hom_ext`).
1. On the piece `D(g^♯(f r)) = g⁻¹ᵁ D(f r)` (`Scheme.preimage_basicOpen`), the right-hand side is
   `toBasicOpenOfGlobalSections 𝒜 (g^♯ ∘ f) rfl hd hr ≫ (basicOpen 𝒜 r).ι` (`Cover.ι_glueMorphisms`).
2. The left-hand side is `g.resLE (D(f r)) (D(g^♯(f r))) _ ≫ D(f r).ι ≫ fromOfGlobalSections 𝒜 f hf`
   (`Scheme.Hom.resLE_comp_ι`) `= g.resLE … ≫ toBasicOpenOfGlobalSections 𝒜 f rfl hd hr ≫ (basicOpen 𝒜 r).ι`
   (`fromOfGlobalSections_resLE` + `resLE_comp_ι`).
3. Unfold `toBasicOpenOfGlobalSections` (`isoOfEq.inv ≫ toSpecΓ ∣_ D(x) ≫ basicOpenIsoSpecAway.hom ≫
   Spec.map (IsLocalization.map f ∘ algebraMap) ≫ basicOpenIsoSpec.inv`) on both sides and cancel the
   monomorphism `basicOpenIsoSpec.inv ≫ ι`. `g.resLE` commutes with `toSpecΓ ∣_ D(x)` by
   `Scheme.toSpecΓ_naturality` (`g ≫ X.toSpecΓ = Y.toSpecΓ ≫ Spec.map g.appTop`) restricted to basic opens
   (`Scheme.Hom.resLE_comp_resLE`, `Scheme.Hom.map_resLE`), and `(Spec.map g.appTop).resLE` commutes with
   `basicOpenIsoSpecAway` up to `Spec.map (IsLocalization.Away.map g^♯)` (`basicOpenIsoSpecAway` is
   `Spec.map (algebraMap)` composed with the range isomorphism; `IsOpenImmersion.isoOfRangeEq_hom_fac`).
4. The remaining identity is `Spec.map` of `IsLocalization.map (g^♯ ∘ f) = IsLocalization.Away.map g^♯ ∘
   IsLocalization.map f` on `Localization.Away r` (`IsLocalization.map_comp_map` / `IsLocalization.ringHom_ext`
   on `powers r`), and `Spec.map_comp`.
Edge cases: `Y = ∅` (both sides are the unique morphism), `A` with no positive-degree elements (`hf` forces
`Γ(X, ⊤) = 0`, so `X = ∅` and `Y = ∅`).

`resLE_toBasicOpenOfGlobalSections` is step 3 (with `SpecMap_resLE_basicOpenIsoSpecAway_hom` for the
`basicOpenIsoSpecAway` part and `IsLocalization.map_comp_map` for step 4); the cover argument is steps 1–2. -/
theorem comp_fromOfGlobalSections {X Y : AlgebraicGeometry.Scheme.{u}} (g : Y ⟶ X) (f : A →+* Γ(X, ⊤))
    (hf : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map f = ⊤) :
    g ≫ AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 f hf =
      AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 (g.appTop.hom.comp f) (map_irrelevant_comp_eq_top 𝒜 g f hf) := by
  refine (openCoverOfMapIrrelevantEqTop 𝒜 (g.appTop.hom.comp f)
    (map_irrelevant_comp_eq_top 𝒜 g f hf)).hom_ext _ _ fun ir ↦ ?_
  obtain ⟨i, r, hi, hr⟩ := ir
  -- the right-hand side on the piece `D(g^♯(f r))`
  have hR : (openCoverOfMapIrrelevantEqTop 𝒜 (g.appTop.hom.comp f)
      (map_irrelevant_comp_eq_top 𝒜 g f hf)).f ⟨i, r, hi, hr⟩ ≫
        fromOfGlobalSections 𝒜 (g.appTop.hom.comp f) (map_irrelevant_comp_eq_top 𝒜 g f hf) =
      toBasicOpenOfGlobalSections 𝒜 (g.appTop.hom.comp f) rfl hi hr ≫ (basicOpen 𝒜 r).ι := by
    unfold fromOfGlobalSections
    exact (openCoverOfMapIrrelevantEqTop 𝒜 _ _).ι_glueMorphisms _ _ ⟨i, r, hi, hr⟩
  -- the left-hand side: move through `g` with `resLE`
  have hle : Y.basicOpen (g.appTop (f r)) ≤ g ⁻¹ᵁ X.basicOpen (f r) :=
    (Scheme.preimage_basicOpen_top g (f r)).ge
  have hL : (openCoverOfMapIrrelevantEqTop 𝒜 (g.appTop.hom.comp f)
      (map_irrelevant_comp_eq_top 𝒜 g f hf)).f ⟨i, r, hi, hr⟩ ≫ g ≫ fromOfGlobalSections 𝒜 f hf =
      g.resLE _ _ hle ≫ toBasicOpenOfGlobalSections 𝒜 f rfl hi hr ≫ (basicOpen 𝒜 r).ι := by
    change (Y.basicOpen (g.appTop (f r))).ι ≫ g ≫ fromOfGlobalSections 𝒜 f hf = _
    rw [← Category.assoc, ← Scheme.Hom.resLE_comp_ι g hle, Category.assoc,
      ← fromOfGlobalSections_resLE 𝒜 f hf hi hr, Scheme.Hom.resLE_comp_ι]
  rw [hR, hL]
  change g.resLE (X.basicOpen (f r)) (Y.basicOpen (g.appTop (f r))) hle ≫
      toBasicOpenOfGlobalSections 𝒜 f rfl hi hr ≫ (basicOpen 𝒜 r).ι =
    toBasicOpenOfGlobalSections 𝒜 (g.appTop.hom.comp f) (x := g.appTop (f r)) rfl hi hr ≫ (basicOpen 𝒜 r).ι
  rw [← Category.assoc, resLE_toBasicOpenOfGlobalSections]

end AlgebraicGeometry.Proj

end
