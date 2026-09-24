import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjBaseChangeUnit
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjBaseChangeAlgebra
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.ProjCongrGrading
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.Stacks01n2
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.ProjTwistPullbackHomComp
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.ProjMapTwistComparison
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.RelativeProjTwistLocalIso
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProj

/-! # Base change of a relative Proj on a chart

Statement: the **local comparison map** of Stacks 01O3. For `g : S' ⟶ S`, `𝒜 : S.GradedQCAlgebra`,
affine opens `U ∈ S.AffineZariskiSite`, `V ∈ S'.AffineZariskiSite` with `V ≤ g⁻¹U`,
`baseChangeProjMap g 𝒜 U V hV : Proj((g^*𝒜)(V)) ⟶ Proj(𝒜(U))` is `Proj.map` of the unit graded
hom `𝒜(U) → (g^*𝒜)(V)` (`RelativeProjBaseChangeUnit.lean`). Three properties:
1. `baseChangeProjMap_isPullback` (Stacks 01N2): the square
   `Proj((g^*𝒜)(V)) → Proj(𝒜(U))` over `V → U` (`g.resLE`) is a pullback square, from
   `Proj.isPullback_of_isBaseChange` (`Stacks01n2.lean`), the base-change witness of
   `RelativeProjBaseChangeAlgebra.lean` (Stacks 01I9) and the `Proj` transport of
   `ProjCongrGrading.lean`;
2. `baseChangeProjMap_compat`: compatibility with the transition maps `projFunctor.map` of the
   two relative-Proj gluing data (for `U' ≤ U`, `V' ≤ V`, `V' ≤ g⁻¹U'`);
3. `isIso_baseChangeProjMap_twistPullbackHom` (Stacks 01N2, last sentence, via 01MX): the
   canonical comparison `(baseChangeProjMap)^* O_{Proj 𝒜(U)}(d) ⟶ O_{Proj (g^*𝒜)(V)}(d)`
   (`Proj.twistPullbackHom`) is an isomorphism, from 1's ingredients,
   `Proj.isIso_twistPullbackHom` (`Stacks01n2.lean`) and the compatibility of `θ` with composition
   (`Proj.twistPullbackHom_comp`).

These are the chart-level inputs glued in `RelativeProjBaseChangeGlue.lean` and the twisting-sheaf
comparison.

Source: Stacks 01O3, 01N2, 01I9; the base change of `P(O ⊕ L)` in Corollary 4.3 of
the paper.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.GradedQCAlgebra

variable {S S' : AlgebraicGeometry.Scheme.{u}} (g : S' ⟶ S) (𝒜 : S.GradedQCAlgebra)
  (U : S.AffineZariskiSite) (V : S'.AffineZariskiSite) (hV : V.toOpens ≤ g ⁻¹ᵁ U.toOpens)

/-- The local comparison map `Proj((g^*𝒜)(V)) ⟶ Proj(𝒜(U))`: `Proj.map` of the unit graded hom. -/
def baseChangeProjMap :
    AlgebraicGeometry.Proj ((𝒜.pullback g).toGradedAffineAlgebra.grading V) ⟶
      AlgebraicGeometry.Proj (𝒜.toGradedAffineAlgebra.grading U) :=
  AlgebraicGeometry.Proj.map (baseChangeUnitGraded g 𝒜 U.toOpens V.toOpens hV)
    (baseChangeUnitGraded_irrelevant_le g 𝒜 U.toOpens V.toOpens hV U.2 V.2)

/-- The `AddSubgroup`- and `Submodule`-valued gradings of the section ring have the same members. -/
theorem mem_sectionsGrading_iff_mem_sectionsSubmodule {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) (U : X.Opens) :
    letI := S.sectionsAlgebraBC U
    ∀ (i : ℕ) (x : S.sectionsRing U), x ∈ S.sectionsGrading U i ↔ x ∈ S.sectionsSubmodule U i :=
  letI := S.sectionsAlgebraBC U
  fun i x => (S.mem_sectionsSubmodule U (m := i) (x := x)).symm

/-- Variable-level diagram chase for `congr_toSpecZero_projToOpen` (concrete schemes enter through
`exact`): from `e ≫ t = t' ≫ sγ` and `sα = sγ ≫ sν`,
`(t' ≫ sα) ≫ i = e ≫ t ≫ sν ≫ i`. -/
private theorem transport_aux {P P' Z Z' Y W : AlgebraicGeometry.Scheme.{u}} (e : P' ⟶ P)
    (t : P ⟶ Z) (t' : P' ⟶ Z') (sγ : Z' ⟶ Z) (sν : Z ⟶ Y) (sα : Z' ⟶ Y) (i : Y ⟶ W)
    (h1 : e ≫ t = t' ≫ sγ) (h2 : sα = sγ ≫ sν) : (t' ≫ sα) ≫ i = e ≫ t ≫ sν ≫ i := by
  rw [h2, ← Category.assoc t', ← h1]
  simp only [Category.assoc]

/-- Variable-level lemma for the `snd` compatibility in `baseChangeProjMap_isPullback`. -/
private theorem snd_aux {P Q R T : AlgebraicGeometry.Scheme.{u}} (a : P ⟶ Q) (b : Q ⟶ R)
    (c : R ⟶ T) (d : T ⟶ R) (h : c ≫ d = 𝟙 R) : (a ≫ b ≫ c) ≫ d = a ≫ b := by
  rw [Category.assoc, Category.assoc, h, Category.comp_id]

/-- Transport of the structure map to the degree-zero spectrum from the `Submodule`-valued grading
`S.sectionsSubmodule U` (Stacks 01N2 shape) to `projToOpen U` (`RelativeProj.lean` shape):
`(toSpecZero ≫ Spec.map (algebraMap Γ(X,U) 𝒜(U)_0)) ≫ isoSpec.inv = Proj.map (id) ≫ projToOpen U`.
The two `Spec.map`s agree because `algebraMap Γ(X,U) 𝒜(U) = sectionsUnitHom` (`algebraMap_eq_sectionsUnitHom`). -/
theorem congr_toSpecZero_projToOpen {X : AlgebraicGeometry.Scheme.{u}} (S : X.GradedQCAlgebra)
    (U : X.AffineZariskiSite) :
    letI := S.sectionsAlgebraBC U.toOpens
    letI := S.gradedAlgebraSectionsSubmodule U.toOpens
    (AlgebraicGeometry.Proj.toSpecZero (S.sectionsSubmodule U.toOpens) ≫
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom
          (algebraMap Γ(X, U.toOpens) (S.sectionsSubmodule U.toOpens 0)))) ≫ U.2.isoSpec.inv =
      AlgebraicGeometry.Proj.map
        (AlgebraicGeometry.Proj.congrGradingHom (S.sectionsGrading U.toOpens)
          (S.sectionsSubmodule U.toOpens) (mem_sectionsGrading_iff_mem_sectionsSubmodule S U.toOpens))
        (AlgebraicGeometry.Proj.irrelevant_le_map_congrGradingHom _ _ _) ≫
        S.toGradedAffineAlgebra.projToOpen U := by
  letI := S.sectionsAlgebraBC U.toOpens
  letI := S.gradedAlgebraSectionsSubmodule U.toOpens
  have e : CommRingCat.ofHom (S.toGradedAffineAlgebra.unitZero U) ≫
      CommRingCat.ofHom (AlgebraicGeometry.Proj.congrGradingHom (S.sectionsGrading U.toOpens)
        (S.sectionsSubmodule U.toOpens)
        (mem_sectionsGrading_iff_mem_sectionsSubmodule S U.toOpens)).gradedZeroRingHom =
      CommRingCat.ofHom (algebraMap Γ(X, U.toOpens) (S.sectionsSubmodule U.toOpens 0)) := by
    ext r
    exact (S.algebraMap_eq_sectionsUnitHom U.toOpens r).symm
  exact transport_aux _ _ _ _ _ _ _
    (AlgebraicGeometry.Proj.map_congrGradingHom_toSpecZero (S.sectionsGrading U.toOpens)
      (S.sectionsSubmodule U.toOpens) (mem_sectionsGrading_iff_mem_sectionsSubmodule S U.toOpens))
    ((congrArg AlgebraicGeometry.Spec.map e.symm).trans (AlgebraicGeometry.Spec.map_comp _ _))

/-- **Stacks 01N2 on a chart**: the local comparison square is a pullback square,
```
Proj((g^*𝒜)(V)) --baseChangeProjMap--> Proj(𝒜(U))
      | projToOpen V                        | projToOpen U
      v                                     v
      V ---------- g.resLE U V hV --------> U
```

Source: Stacks 01N2 (`constructions-lemma-proj-base-change`), 01I9.

Proof. Write `R = Γ(S,U)`, `R' = Γ(S',V)`, `A = 𝒜(U)`, `B = (g^*𝒜)(V)`.
(a) `RelativeProjBaseChangeAlgebra.lean`: `A`, `B` are `R`- resp. `R'`-algebras with
`algebraMap = sectionsUnitHom` (`sectionsAlgebraBC`), `B` is an `R`-algebra through `g^♯`
(`baseChangeAlgebra`), the gradings are `Submodule`-valued `GradedAlgebra`s (`sectionsSubmodule`), the
unit is an `R`-algebra hom `fR` (`baseChangeUnitAlgHom`) and, for affine `U`, `V`, a base change
`R' ⊗_R A ≅ B` (`isBaseChange_baseChangeUnit`: Stacks 01I9 piecewise,
`Modules.isIso_transpose_pullbackSectionsNative`, plus Mathlib `IsBaseChange.directSum`).
(b) `Proj.isPullback_of_isBaseChange` (`Stacks01n2.lean`) gives the pullback square
`Proj.map fₛ / toSpecZero B ≫ Spec.map (R' → B_0) / toSpecZero A ≫ Spec.map (R → A_0) / Spec.map g^♯`
for the unit `fₛ` between the `Submodule`-valued gradings.
(c) Transport (`ProjCongrGrading.lean`): `Proj.map` of the identity graded homs identifies
`Proj` of the `Submodule`-valued gradings with `Proj` of the `AddSubgroup`-valued ones
(`congrGradingIso`), compatibly with `toSpecZero` (`map_congrGradingHom_toSpecZero`), so
`toSpecZero ≫ Spec.map (algebraMap) ≫ isoSpec.inv` becomes `projToOpen` (`congr_toSpecZero_projToOpen`);
`Spec.map g^♯ ≫ U.isoSpec.inv = V.isoSpec.inv ≫ g.resLE` is `Scheme.Opens.toSpecΓ_SpecMap_appLE`
(`isoSpec.hom = toSpecΓ`). `IsPullback.of_iso` along these isomorphisms gives the statement. -/
theorem baseChangeProjMap_isPullback :
    CategoryTheory.IsPullback ((𝒜.pullback g).toGradedAffineAlgebra.projToOpen V)
      (baseChangeProjMap g 𝒜 U V hV) (g.resLE U.toOpens V.toOpens hV)
      (𝒜.toGradedAffineAlgebra.projToOpen U) := by
  letI := baseAlgebra g U.toOpens V.toOpens hV
  letI := 𝒜.sectionsAlgebraBC U.toOpens
  letI := (𝒜.pullback g).sectionsAlgebraBC V.toOpens
  letI := baseChangeAlgebra g 𝒜 U.toOpens V.toOpens hV
  letI := baseChangeTower g 𝒜 U.toOpens V.toOpens hV
  letI := 𝒜.gradedAlgebraSectionsSubmodule U.toOpens
  letI := (𝒜.pullback g).gradedAlgebraSectionsSubmodule V.toOpens
  have hA := mem_sectionsGrading_iff_mem_sectionsSubmodule 𝒜 U.toOpens
  have hB := mem_sectionsGrading_iff_mem_sectionsSubmodule (𝒜.pullback g) V.toOpens
  -- (a)+(b): the 01N2 square for the `Submodule`-valued gradings
  have hcA' := AlgebraicGeometry.Proj.irrelevant_le_map_congrGradingHom
    (𝒜.sectionsSubmodule U.toOpens) (𝒜.sectionsGrading U.toOpens)
    (AlgebraicGeometry.Proj.congr_symm _ _ hA)
  have hcB := AlgebraicGeometry.Proj.irrelevant_le_map_congrGradingHom
    ((𝒜.pullback g).sectionsGrading V.toOpens) ((𝒜.pullback g).sectionsSubmodule V.toOpens) hB
  have hf := baseChangeUnitGraded_irrelevant_le g 𝒜 U.toOpens V.toOpens hV U.2 V.2
  have h01n2 := AlgebraicGeometry.Proj.isPullback_of_isBaseChange (𝒜.sectionsSubmodule U.toOpens)
    ((𝒜.pullback g).sectionsSubmodule V.toOpens)
    ((AlgebraicGeometry.Proj.congrGradingHom _ _ hB).comp
      ((baseChangeUnitGraded g 𝒜 U.toOpens V.toOpens hV).comp
        (AlgebraicGeometry.Proj.congrGradingHom _ _ (AlgebraicGeometry.Proj.congr_symm _ _ hA))))
    (HomogeneousIdeal.irrelevant_le_map_comp (HomogeneousIdeal.irrelevant_le_map_comp hcA' hf) hcB)
    (baseChangeUnitAlgHom g 𝒜 U.toOpens V.toOpens hV) (fun _ => rfl)
    (isBaseChange_baseChangeUnit g 𝒜 U.toOpens V.toOpens hV U.2 V.2)
  rw [AlgebraicGeometry.Proj.map_comp (hf := HomogeneousIdeal.irrelevant_le_map_comp hcA' hf)
    (hg := hcB), AlgebraicGeometry.Proj.map_comp (hf := hcA') (hg := hf)] at h01n2
  -- (c): transport along the identifications of the four corners
  refine h01n2.flip.of_iso
    (AlgebraicGeometry.Proj.congrGradingIso ((𝒜.pullback g).sectionsGrading V.toOpens)
      ((𝒜.pullback g).sectionsSubmodule V.toOpens) hB) V.2.isoSpec.symm
    (AlgebraicGeometry.Proj.congrGradingIso (𝒜.sectionsGrading U.toOpens)
      (𝒜.sectionsSubmodule U.toOpens) hA) U.2.isoSpec.symm ?_ ?_ ?_ ?_
  · exact congr_toSpecZero_projToOpen (𝒜.pullback g) V
  · exact snd_aux _ _ _ _ (AlgebraicGeometry.Proj.congrGradingIso (𝒜.sectionsGrading U.toOpens)
      (𝒜.sectionsSubmodule U.toOpens) hA).inv_hom_id
  · show AlgebraicGeometry.Spec.map (g.appLE U.toOpens V.toOpens hV) ≫ U.2.isoSpec.inv =
      V.2.isoSpec.inv ≫ g.resLE U.toOpens V.toOpens hV
    have h := AlgebraicGeometry.Scheme.Opens.toSpecΓ_SpecMap_appLE g U.toOpens V.toOpens hV
    rw [← AlgebraicGeometry.IsAffineOpen.isoSpec_hom V.2,
      ← AlgebraicGeometry.IsAffineOpen.isoSpec_hom U.2] at h
    rw [Iso.comp_inv_eq, Category.assoc, ← h, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  · exact congr_toSpecZero_projToOpen 𝒜 U

private theorem proj_map_congr {A B : Type u} [CommRing A] [CommRing B]
    {𝒜 : ℕ → AddSubgroup A} {ℬ : ℕ → AddSubgroup B} [GradedRing 𝒜] [GradedRing ℬ]
    {f g : 𝒜 →+*ᵍ ℬ} (e : f = g)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    (hg : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map g) :
    AlgebraicGeometry.Proj.map f hf = AlgebraicGeometry.Proj.map g hg := by
  subst e; rfl

/-- Variable-level form of `Proj.map_comp` for a commuting square of graded ring homs
(`f₂ ∘ f₁ = f₄ ∘ f₃`); the concrete rings enter only through `exact`, so the two spellings of the
section rings (`sectionsRing` vs `GradedAffineAlgebra.ring.obj`) never have to be matched by `rw`. -/
private theorem proj_map_comp_eq {A B C D : Type u} [CommRing A] [CommRing B] [CommRing C]
    [CommRing D] {𝒜 : ℕ → AddSubgroup A} {ℬ : ℕ → AddSubgroup B} {𝒞 : ℕ → AddSubgroup C}
    {𝒟 : ℕ → AddSubgroup D} [GradedRing 𝒜] [GradedRing ℬ] [GradedRing 𝒞] [GradedRing 𝒟]
    (f₁ : 𝒜 →+*ᵍ ℬ) (f₂ : ℬ →+*ᵍ 𝒞) (f₃ : 𝒜 →+*ᵍ 𝒟) (f₄ : 𝒟 →+*ᵍ 𝒞)
    (h₁ : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f₁)
    (h₂ : HomogeneousIdeal.irrelevant 𝒞 ≤ (HomogeneousIdeal.irrelevant ℬ).map f₂)
    (h₃ : HomogeneousIdeal.irrelevant 𝒟 ≤ (HomogeneousIdeal.irrelevant 𝒜).map f₃)
    (h₄ : HomogeneousIdeal.irrelevant 𝒞 ≤ (HomogeneousIdeal.irrelevant 𝒟).map f₄)
    (h : f₂.comp f₁ = f₄.comp f₃) :
    AlgebraicGeometry.Proj.map f₂ h₂ ≫ AlgebraicGeometry.Proj.map f₁ h₁ =
      AlgebraicGeometry.Proj.map f₄ h₄ ≫ AlgebraicGeometry.Proj.map f₃ h₃ := by
  rw [← AlgebraicGeometry.Proj.map_comp, ← AlgebraicGeometry.Proj.map_comp]
  exact proj_map_congr h _ _

/-- The unit graded homs commute with the graded restriction maps of the two gluing data. -/
theorem restrictGraded_comp_baseChangeUnitGraded {U' : S.AffineZariskiSite}
    {V' : S'.AffineZariskiSite} (hU' : U' ≤ U) (hV'V : V' ≤ V)
    (hV' : V'.toOpens ≤ g ⁻¹ᵁ U'.toOpens) :
    ((𝒜.pullback g).toGradedAffineAlgebra.restrictGraded hV'V).comp
        (baseChangeUnitGraded g 𝒜 U.toOpens V.toOpens hV) =
      (baseChangeUnitGraded g 𝒜 U'.toOpens V'.toOpens hV').comp
        (𝒜.toGradedAffineAlgebra.restrictGraded hU') :=
  GradedRingHom.ext fun x =>
    baseChangeUnitRingHom_restrict g 𝒜 U.toOpens V.toOpens hV
      (AffineZariskiSite.toOpens_mono hU') (AffineZariskiSite.toOpens_mono hV'V) hV' x

/-- **Compatibility with the transition maps**: for `U' ≤ U`, `V' ≤ V`, `V' ≤ g⁻¹U'`,
```
Proj((g^*𝒜)(V')) --> Proj(𝒜(U'))
      |                   |
Proj((g^*𝒜)(V))  --> Proj(𝒜(U))
```
commutes (`Proj.map_comp` + the unit commutes with restriction). -/
theorem baseChangeProjMap_compat {U' : S.AffineZariskiSite} {V' : S'.AffineZariskiSite}
    (hU' : U' ≤ U) (hV'V : V' ≤ V) (hV' : V'.toOpens ≤ g ⁻¹ᵁ U'.toOpens) :
    (𝒜.pullback g).toGradedAffineAlgebra.projFunctor.map (homOfLE hV'V) ≫
        baseChangeProjMap g 𝒜 U V hV =
      baseChangeProjMap g 𝒜 U' V' hV' ≫ 𝒜.toGradedAffineAlgebra.projFunctor.map (homOfLE hU') :=
  proj_map_comp_eq (baseChangeUnitGraded g 𝒜 U.toOpens V.toOpens hV)
    ((𝒜.pullback g).toGradedAffineAlgebra.restrictGraded hV'V)
    (𝒜.toGradedAffineAlgebra.restrictGraded hU')
    (baseChangeUnitGraded g 𝒜 U'.toOpens V'.toOpens hV')
    (baseChangeUnitGraded_irrelevant_le g 𝒜 U.toOpens V.toOpens hV U.2 V.2)
    ((𝒜.pullback g).toGradedAffineAlgebra.restrict_irrelevant_le hV'V)
    (𝒜.toGradedAffineAlgebra.restrict_irrelevant_le hU')
    (baseChangeUnitGraded_irrelevant_le g 𝒜 U'.toOpens V'.toOpens hV' U'.2 V'.2)
    (restrictGraded_comp_baseChangeUnitGraded g 𝒜 U V hV hU' hV'V hV')

/-- `θ` for the identity graded hom between two encodings of one grading is an isomorphism
(`isIso_twistPullbackHom_of_isLocalizationAway` with `f = 1`: the identity is the localization away
from `1`, and `Proj.map` of the identity transport is an isomorphism, hence an open immersion). -/
theorem isIso_twistPullbackHom_congrGradingHom {A : Type u} [CommRing A] {σ τ : Type u}
    [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ A] [AddSubgroupClass τ A] (𝒜 : ℕ → σ)
    (𝒜' : ℕ → τ) [GradedRing 𝒜] [GradedRing 𝒜'] (h : ∀ (i : ℕ) (x : A), x ∈ 𝒜 i ↔ x ∈ 𝒜' i)
    (n : ℤ) :
    IsIso (AlgebraicGeometry.Proj.twistPullbackHom (AlgebraicGeometry.Proj.congrGradingHom 𝒜 𝒜' h)
      (AlgebraicGeometry.Proj.irrelevant_le_map_congrGradingHom 𝒜 𝒜' h) n) := by
  haveI := AlgebraicGeometry.Proj.isIso_map_congrGradingHom 𝒜 𝒜' h
  exact MiyaokaMori.RelativeProjTwistLocalIso.isIso_twistPullbackHom_of_isLocalizationAway
    (AlgebraicGeometry.Proj.congrGradingHom 𝒜 𝒜' h)
    (AlgebraicGeometry.Proj.irrelevant_le_map_congrGradingHom 𝒜 𝒜' h)
    (SetLike.one_mem_graded 𝒜)
    (IsLocalization.away_of_isUnit_of_bijective A isUnit_one Function.bijective_id) n

/-- **Stacks 01N2, twisting sheaves, for the `Submodule`-valued gradings**: `θ` for the unit
`fₛ = cB ∘ f ∘ cA'` between `sectionsSubmodule U` and `sectionsSubmodule V` is an isomorphism
(`Proj.isIso_twistPullbackHom` with the base-change witness of
`RelativeProjBaseChangeAlgebra.lean`). -/
theorem isIso_twistPullbackHom_sectionsSubmodule (d : ℤ) :
    letI := baseAlgebra g U.toOpens V.toOpens hV
    letI := 𝒜.sectionsAlgebraBC U.toOpens
    letI := (𝒜.pullback g).sectionsAlgebraBC V.toOpens
    letI := baseChangeAlgebra g 𝒜 U.toOpens V.toOpens hV
    letI := baseChangeTower g 𝒜 U.toOpens V.toOpens hV
    letI := 𝒜.gradedAlgebraSectionsSubmodule U.toOpens
    letI := (𝒜.pullback g).gradedAlgebraSectionsSubmodule V.toOpens
    IsIso (AlgebraicGeometry.Proj.twistPullbackHom
      ((AlgebraicGeometry.Proj.congrGradingHom _ _
          (mem_sectionsGrading_iff_mem_sectionsSubmodule (𝒜.pullback g) V.toOpens)).comp
        ((baseChangeUnitGraded g 𝒜 U.toOpens V.toOpens hV).comp
          (AlgebraicGeometry.Proj.congrGradingHom _ _ (AlgebraicGeometry.Proj.congr_symm _ _
            (mem_sectionsGrading_iff_mem_sectionsSubmodule 𝒜 U.toOpens)))))
      (HomogeneousIdeal.irrelevant_le_map_comp (HomogeneousIdeal.irrelevant_le_map_comp
        (AlgebraicGeometry.Proj.irrelevant_le_map_congrGradingHom _ _
          (AlgebraicGeometry.Proj.congr_symm _ _
            (mem_sectionsGrading_iff_mem_sectionsSubmodule 𝒜 U.toOpens)))
        (baseChangeUnitGraded_irrelevant_le g 𝒜 U.toOpens V.toOpens hV U.2 V.2))
        (AlgebraicGeometry.Proj.irrelevant_le_map_congrGradingHom _ _
          (mem_sectionsGrading_iff_mem_sectionsSubmodule (𝒜.pullback g) V.toOpens))) d) := by
  letI := baseAlgebra g U.toOpens V.toOpens hV
  letI := 𝒜.sectionsAlgebraBC U.toOpens
  letI := (𝒜.pullback g).sectionsAlgebraBC V.toOpens
  letI := baseChangeAlgebra g 𝒜 U.toOpens V.toOpens hV
  letI := baseChangeTower g 𝒜 U.toOpens V.toOpens hV
  letI := 𝒜.gradedAlgebraSectionsSubmodule U.toOpens
  letI := (𝒜.pullback g).gradedAlgebraSectionsSubmodule V.toOpens
  exact AlgebraicGeometry.Proj.isIso_twistPullbackHom (𝒜.sectionsSubmodule U.toOpens)
    ((𝒜.pullback g).sectionsSubmodule V.toOpens) _ _
    (baseChangeUnitAlgHom g 𝒜 U.toOpens V.toOpens hV) (fun _ => rfl)
    (isBaseChange_baseChangeUnit g 𝒜 U.toOpens V.toOpens hV U.2 V.2) d

/-- **Stacks 01N2, twisting sheaves**: the canonical comparison
`θ : (baseChangeProjMap)^* O_{Proj 𝒜(U)}(d) ⟶ O_{Proj (g^*𝒜)(V)}(d)` (`Proj.twistPullbackHom`)
is an isomorphism.

Source: Stacks 01N2 (last sentence) via 01MX; 01I9.

Proof. Write `f = unit : 𝒜(U) →+*ᵍ (g^*𝒜)(V)` (`AddSubgroup`-valued
gradings), `cA`, `cA'`, `cB`, `cB'` the identity graded homs between the `AddSubgroup`- and
`Submodule`-valued encodings (`Proj.congrGradingHom`, `ProjCongrGrading.lean`) and
`fₛ = cB ∘ f ∘ cA'` the unit between the `Submodule`-valued gradings `sectionsSubmodule`, as in
`baseChangeProjMap_isPullback`. Then `f = cB' ∘ (fₛ ∘ cA)` as graded ring homs (all `c`'s are the identity
of the ring).
(1) `θ^{fₛ}` is an isomorphism: `Proj.isIso_twistPullbackHom` (`Stacks01n2.lean`) with the base-change
witness of `RelativeProjBaseChangeAlgebra.lean` (`isIso_twistPullbackHom_sectionsSubmodule`).
(2) `θ^{cA}`, `θ^{cB'}` are isomorphisms: `isIso_twistPullbackHom_of_isLocalizationAway` with `f = 1`
(`isIso_twistPullbackHom_congrGradingHom`).
(3) `θ` is compatible with composition (`Proj.twistPullbackHom_comp`):
`isIso_twistPullbackHom_comp` gives `θ^{fₛ ∘ cA}`, and `isIso_twistPullbackHom_of_eq_comp` transports along
`f = cB' ∘ (fₛ ∘ cA)`. -/
theorem isIso_baseChangeProjMap_twistPullbackHom (d : ℤ) :
    CategoryTheory.IsIso (AlgebraicGeometry.Proj.twistPullbackHom
      (baseChangeUnitGraded g 𝒜 U.toOpens V.toOpens hV)
      (baseChangeUnitGraded_irrelevant_le g 𝒜 U.toOpens V.toOpens hV U.2 V.2) d) := by
  letI := baseAlgebra g U.toOpens V.toOpens hV
  letI := 𝒜.sectionsAlgebraBC U.toOpens
  letI := (𝒜.pullback g).sectionsAlgebraBC V.toOpens
  letI := baseChangeAlgebra g 𝒜 U.toOpens V.toOpens hV
  letI := baseChangeTower g 𝒜 U.toOpens V.toOpens hV
  letI := 𝒜.gradedAlgebraSectionsSubmodule U.toOpens
  letI := (𝒜.pullback g).gradedAlgebraSectionsSubmodule V.toOpens
  have hA := mem_sectionsGrading_iff_mem_sectionsSubmodule 𝒜 U.toOpens
  have hB := mem_sectionsGrading_iff_mem_sectionsSubmodule (𝒜.pullback g) V.toOpens
  -- the four identity transports and the `Submodule`-side unit
  set cA := AlgebraicGeometry.Proj.congrGradingHom (𝒜.sectionsGrading U.toOpens)
    (𝒜.sectionsSubmodule U.toOpens) hA with hcA_def
  set cA' := AlgebraicGeometry.Proj.congrGradingHom (𝒜.sectionsSubmodule U.toOpens)
    (𝒜.sectionsGrading U.toOpens) (AlgebraicGeometry.Proj.congr_symm _ _ hA) with hcA'_def
  set cB := AlgebraicGeometry.Proj.congrGradingHom ((𝒜.pullback g).sectionsGrading V.toOpens)
    ((𝒜.pullback g).sectionsSubmodule V.toOpens) hB with hcB_def
  set cB' := AlgebraicGeometry.Proj.congrGradingHom ((𝒜.pullback g).sectionsSubmodule V.toOpens)
    ((𝒜.pullback g).sectionsGrading V.toOpens) (AlgebraicGeometry.Proj.congr_symm _ _ hB) with hcB'_def
  have hcA := AlgebraicGeometry.Proj.irrelevant_le_map_congrGradingHom (𝒜.sectionsGrading U.toOpens)
    (𝒜.sectionsSubmodule U.toOpens) hA
  have hcA' := AlgebraicGeometry.Proj.irrelevant_le_map_congrGradingHom (𝒜.sectionsSubmodule U.toOpens)
    (𝒜.sectionsGrading U.toOpens) (AlgebraicGeometry.Proj.congr_symm _ _ hA)
  have hcB := AlgebraicGeometry.Proj.irrelevant_le_map_congrGradingHom
    ((𝒜.pullback g).sectionsGrading V.toOpens) ((𝒜.pullback g).sectionsSubmodule V.toOpens) hB
  have hcB' := AlgebraicGeometry.Proj.irrelevant_le_map_congrGradingHom
    ((𝒜.pullback g).sectionsSubmodule V.toOpens) ((𝒜.pullback g).sectionsGrading V.toOpens)
    (AlgebraicGeometry.Proj.congr_symm _ _ hB)
  have hf := baseChangeUnitGraded_irrelevant_le g 𝒜 U.toOpens V.toOpens hV U.2 V.2
  have hfs : HomogeneousIdeal.irrelevant ((𝒜.pullback g).sectionsSubmodule V.toOpens) ≤
      (HomogeneousIdeal.irrelevant (𝒜.sectionsSubmodule U.toOpens)).map
        (cB.comp ((baseChangeUnitGraded g 𝒜 U.toOpens V.toOpens hV).comp cA')) :=
    HomogeneousIdeal.irrelevant_le_map_comp (HomogeneousIdeal.irrelevant_le_map_comp hcA' hf) hcB
  -- (1), (2)
  haveI h1 : CategoryTheory.IsIso (AlgebraicGeometry.Proj.twistPullbackHom
      (cB.comp ((baseChangeUnitGraded g 𝒜 U.toOpens V.toOpens hV).comp cA')) hfs d) :=
    isIso_twistPullbackHom_sectionsSubmodule g 𝒜 U V hV d
  haveI h2 : CategoryTheory.IsIso (AlgebraicGeometry.Proj.twistPullbackHom cA hcA d) :=
    isIso_twistPullbackHom_congrGradingHom _ _ hA d
  haveI h3 : CategoryTheory.IsIso (AlgebraicGeometry.Proj.twistPullbackHom cB' hcB' d) :=
    isIso_twistPullbackHom_congrGradingHom _ _ (AlgebraicGeometry.Proj.congr_symm _ _ hB) d
  -- (3)
  haveI h4 := AlgebraicGeometry.Proj.isIso_twistPullbackHom_comp cA
    (cB.comp ((baseChangeUnitGraded g 𝒜 U.toOpens V.toOpens hV).comp cA')) hcA hfs d
  exact AlgebraicGeometry.Proj.isIso_twistPullbackHom_of_eq_comp
    ((cB.comp ((baseChangeUnitGraded g 𝒜 U.toOpens V.toOpens hV).comp cA')).comp cA) cB'
    (HomogeneousIdeal.irrelevant_le_map_comp hcA hfs) hcB' d
    (baseChangeUnitGraded g 𝒜 U.toOpens V.toOpens hV) hf (GradedRingHom.ext fun _ => rfl)

end AlgebraicGeometry.Scheme.GradedQCAlgebra

end
