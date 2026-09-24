import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.Stacks01nq
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProj

/-! # Scalar bookkeeping for the evaluation map of a relative Proj

Scalar bookkeeping for the `O_X`-linearity of the local evaluation `evaluationLocal` of
`RelativeProjEvaluation`, Stacks 01MN (`A_m → Γ(Proj A, O(m))` is `A_0`-linear) together with 01NQ/01NR.

Contents:

* `Proj.zeroToGlobal 𝒜 : A₀ → Γ(Proj A, ⊤)`, `u ↦ u/1`, with `Proj.toSpecZero = toSpecΓ ≫ Spec.map zeroToGlobal`
  (`toSpecZero_eq_toSpecΓ`), so that `toSpecZero^♯ (ΓSpecIso⁻¹ u) = u/1` (`toSpecZero_appTop_ΓSpecIso_inv`),
  and the pointwise value `(u/1)(x) = Localization.mk u 1` (`zeroToGlobal_apply_val`).
* Generic `appLE` bookkeeping: `Scheme.Hom.appLE_of_eq`, `appLE_top_top`, `comp_appLE_top`,
  `IsAffineOpen.fromSpec_appLE_top`, `Scheme.SpecMap_appTop_ΓSpecIso_inv`.
* Generic module bookkeeping: `Modules.pushforward_smul_def'` (the `Γ(X, W)`-action on `h_*N` is through `h^♯`, rfl),
  `Modules.restrict_appLE_smul` (the action of `f.appLE U W e c` on `Γ(M|_f, W) = Γ(M, f ''ᵁ W)` is the action of
  `c|_{f ''ᵁ W}`), `Scheme.presheaf_map_map_of_le_le`.
* For the relative Proj `π : Proj_X S → X`, an affine open `V`, `ι : π⁻¹V ↪ Proj_X S`, `φ = affineIso V : π⁻¹V ≅ Proj A(V)`:
  the typed charts `chart`, `chartToOpen` (`chart_hom`, `affineIso_hom_chart`, `ι_comp_hom`,
  `chartToOpen_comp_ι : chartToOpen ≫ V.ι = (toSpecZero ≫ Spec.map (sectionsUnit V)) ≫ fromSpec`), and the
  **structure section** `structureSection S V r ∈ Γ(Proj A(V), ⊤)` of `r ∈ Γ(X, V)`, which is `(sectionsUnit V r)/1`
  (`structureSection_eq`, `structureSection_apply_val`) and satisfies
  `φ^♯ (structureSection r) = ι^♯ (π^♯ r)` (`affineIso_hom_app_structureSection`).

Source: Stacks 01MN, 01NQ; Mathlib `Proj.toSpecZero`, `Proj.awayToSection`; Proposition 3.2 of the
paper.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Proj

variable {σ A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- The ring map `A₀ → Γ(Proj A, ⊤)`, `u ↦ u/1` (through `D₊(1) = Proj A`). -/
noncomputable def zeroToGlobal : CommRingCat.of (𝒜 0) ⟶ Γ(Proj 𝒜, ⊤) :=
  CommRingCat.ofHom (HomogeneousLocalization.fromZeroRingHom 𝒜 (Submonoid.powers (1 : A))) ≫
    Proj.awayToSection 𝒜 1 ≫
    (Proj 𝒜).presheaf.map (homOfLE (le_of_eq (Proj.basicOpen_one 𝒜).symm)).op

theorem toSpecZero_eq_toSpecΓ :
    Proj.toSpecZero 𝒜 = (Proj 𝒜).toSpecΓ ≫ Spec.map (zeroToGlobal 𝒜) := by
  unfold Proj.toSpecZero Proj.basicOpenToSpec zeroToGlobal
  rw [Spec.map_comp, Spec.map_comp]
  rw [Scheme.isoOfEq_inv]
  have h1 := Scheme.Opens.toSpecΓ_SpecMap_presheaf_map (X := Proj 𝒜) ⊤ (Proj.basicOpen 𝒜 1)
    (le_of_eq (Proj.basicOpen_one 𝒜).symm)
  rw [Scheme.Opens.toSpecΓ_top] at h1
  have h1' := reassoc_of% h1
  simp only [Category.assoc]
  rw [← h1', ← Category.assoc (Proj 𝒜).topIso.inv, Scheme.toIso_inv_ι, Category.id_comp]

theorem toSpecZero_appTop_ΓSpecIso_inv (u : 𝒜 0) :
    (Proj.toSpecZero 𝒜).appTop ((Scheme.ΓSpecIso (CommRingCat.of (𝒜 0))).inv u) =
      zeroToGlobal 𝒜 u := by
  rw [toSpecZero_eq_toSpecΓ, Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop]
  rw [Scheme.ΓSpecIso_naturality, CommRingCat.comp_apply, Iso.inv_hom_id_apply]

/-- Pointwise value of `u/1`: at every point it is the fraction `u/1`. -/
theorem zeroToGlobal_apply_val (u : 𝒜 0) (x : (⊤ : (Proj 𝒜).Opens)) :
    HomogeneousLocalization.val ((zeroToGlobal 𝒜 u).1 x) = Localization.mk (u : A) 1 := by
  unfold zeroToGlobal
  rw [CommRingCat.comp_apply, CommRingCat.comp_apply]
  erw [AlgebraicGeometry.Proj.res_apply]
  erw [ProjectiveSpectrum.Proj.awayToSection_apply]
  change (IsLocalization.map _ (RingHom.id A) _) (Localization.mk (u : A) 1) = _
  rw [Localization.mk_eq_mk', IsLocalization.map_mk', Localization.mk_eq_mk']
  simp only [RingHom.id_apply]
  rfl

end AlgebraicGeometry.Proj

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y Z : AlgebraicGeometry.Scheme.{u}}

theorem appLE_of_eq {f f' : X ⟶ Y} (h : f = f') (U : Y.Opens) (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U) :
    f.appLE U V e = f'.appLE U V (h ▸ e) := by
  subst h; rfl

theorem appLE_top_top (f : X ⟶ Y) (e : (⊤ : X.Opens) ≤ f ⁻¹ᵁ ⊤) :
    f.appLE ⊤ ⊤ e = f.appTop := by
  show f.app ⊤ ≫ X.presheaf.map (CategoryTheory.homOfLE e).op = f.app ⊤
  have h : X.presheaf.map (CategoryTheory.homOfLE e).op = 𝟙 Γ(X, ⊤) :=
    X.presheaf.map_id (op (⊤ : X.Opens))
  exact (congrArg _ h).trans (CategoryTheory.Category.comp_id _)

/-- `(f ≫ g).appLE U ⊤ = g.appLE U ⊤ ≫ f.appTop` when `g` lands in `U`. -/
theorem comp_appLE_top (f : X ⟶ Y) (g : Y ⟶ Z) (U : Z.Opens) (hg : (⊤ : Y.Opens) ≤ g ⁻¹ᵁ U)
    (e : (⊤ : X.Opens) ≤ (f ≫ g) ⁻¹ᵁ U) :
    (f ≫ g).appLE U ⊤ e = g.appLE U ⊤ hg ≫ f.appTop := by
  rw [← appLE_top_top f (le_of_eq (AlgebraicGeometry.Scheme.Hom.preimage_top f).symm),
    AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE]

end AlgebraicGeometry.Scheme.Hom

theorem AlgebraicGeometry.IsAffineOpen.fromSpec_appLE_top {X : AlgebraicGeometry.Scheme.{u}}
    {U : X.Opens} (hU : AlgebraicGeometry.IsAffineOpen U) (e : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U) :
    hU.fromSpec.appLE U ⊤ e = (AlgebraicGeometry.Scheme.ΓSpecIso Γ(X, U)).inv := by
  rw [AlgebraicGeometry.Scheme.Hom.appLE, hU.fromSpec_app_self, CategoryTheory.Category.assoc,
    ← CategoryTheory.Functor.map_comp]
  have : ((CategoryTheory.eqToHom hU.fromSpec_preimage_self).op ≫ (CategoryTheory.homOfLE e).op) =
      𝟙 (op (⊤ : (Spec Γ(X, U)).Opens)) := Subsingleton.elim _ _
  rw [this, CategoryTheory.Functor.map_id, CategoryTheory.Category.comp_id]

/-- `(Spec.map f).appTop` on `ΓSpecIso.inv x` is `ΓSpecIso.inv (f x)` (`ΓSpecIso_naturality`, elementwise). -/
theorem AlgebraicGeometry.Scheme.SpecMap_appTop_ΓSpecIso_inv {R S : CommRingCat.{u}} (f : R ⟶ S) (x : R) :
    (Spec.map f).appTop ((AlgebraicGeometry.Scheme.ΓSpecIso R).inv x) =
      (AlgebraicGeometry.Scheme.ΓSpecIso S).inv (f x) := by
  have h := AlgebraicGeometry.Scheme.ΓSpecIso_naturality f
  rw [(CategoryTheory.Iso.eq_comp_inv _).mpr h, CommRingCat.comp_apply, CommRingCat.comp_apply,
    CategoryTheory.Iso.inv_hom_id_apply]

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : AlgebraicGeometry.Scheme.{u}}

/-- The `Γ(X, W)`-action on the pushforward `h_*N` over `W ⊆ X` goes through `h^♯` by definition:
`r • x = h^♯(r) • x` (a definitional equality). -/
theorem pushforward_smul_def' (h : Y ⟶ X) (N : Y.Modules) (W : X.Opens) (r : Γ(X, W))
    (x : Γ((AlgebraicGeometry.Scheme.Modules.pushforward h).obj N, W)) :
    r • x = (show Γ(N, h ⁻¹ᵁ W) from h.app W r • (show Γ(N, h ⁻¹ᵁ W) from x)) := rfl

/-- Scalar multiplication on the restricted sheaf `M|_f` over `W`: the element `f.appLE U W e c` of `Γ(Y, W)`
(`c ∈ Γ(X, U)`) acts on `Γ(M|_f, W) = Γ(M, f ''ᵁ W)` as the restriction of `c` to `f ''ᵁ W`. -/
theorem restrict_appLE_smul (f : Y ⟶ X) [AlgebraicGeometry.IsOpenImmersion f] (M : X.Modules)
    {U : X.Opens} {W : Y.Opens} (e : W ≤ f ⁻¹ᵁ U) (h : f ''ᵁ W ≤ U) (c : Γ(X, U))
    (t : Γ(M.restrict f, W)) :
    f.appLE U W e c • t =
      (show Γ(M.restrict f, W) from
        (X.presheaf.map (CategoryTheory.homOfLE h).op c • (show Γ(M, f ''ᵁ W) from t))) := by
  have h2 : (f.appIso W).inv (f.appLE U W e c) = X.presheaf.map (CategoryTheory.homOfLE h).op c := by
    rw [← CommRingCat.comp_apply, AlgebraicGeometry.Scheme.Hom.appLE_appIso_inv]
  rw [← h2]
  exact AlgebraicGeometry.Scheme.Modules.smul_restrictAppIso_hom_apply f M W _ t

/-- Restricting back and forth between two equal opens is the identity. -/
theorem _root_.AlgebraicGeometry.Scheme.presheaf_map_map_of_le_le (X : AlgebraicGeometry.Scheme.{u})
    {U V : X.Opens} (h1 : U ≤ V) (h2 : V ≤ U) (c : Γ(X, U)) :
    X.presheaf.map (CategoryTheory.homOfLE h1).op (X.presheaf.map (CategoryTheory.homOfLE h2).op c) = c := by
  rw [← CommRingCat.comp_apply, ← CategoryTheory.Functor.map_comp]
  have : (CategoryTheory.homOfLE h2).op ≫ (CategoryTheory.homOfLE h1).op = 𝟙 (op U) :=
    Subsingleton.elim _ _
  rw [this, CategoryTheory.Functor.map_id]
  rfl

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.relativeProj

variable {X : AlgebraicGeometry.Scheme.{u}} (S : X.GradedQCAlgebra) (V : X.affineOpens)

/-- The chart `Proj A(V) ⟶ Proj_X S`, with source spelled `Proj (S.sectionsGrading V.1)` (aligned with `affineIso`). -/
def chart : AlgebraicGeometry.Proj (S.sectionsGrading V.1) ⟶ (AlgebraicGeometry.Scheme.relativeProj S).left :=
  S.toGradedAffineAlgebra.projChart (affineSite V)

/-- The structure map of the chart, `Proj A(V) ⟶ V`, with source spelled `Proj (S.sectionsGrading V.1)`. -/
def chartToOpen : AlgebraicGeometry.Proj (S.sectionsGrading V.1) ⟶ V.1.toScheme :=
  S.toGradedAffineAlgebra.projToOpen (affineSite V)

theorem chart_hom :
    chart S V ≫ (AlgebraicGeometry.Scheme.relativeProj S).hom = chartToOpen S V ≫ V.1.ι :=
  S.toGradedAffineAlgebra.projChart_hom (affineSite V)

theorem affineIso_inv_ι' :
    (AlgebraicGeometry.Scheme.relativeProj.affineIso S V).inv ≫
      ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1).ι = chart S V :=
  AlgebraicGeometry.Scheme.relativeProj.affineIso_inv_ι S V

theorem affineIso_hom_chart :
    (AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ≫ chart S V =
      ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1).ι := by
  rw [← affineIso_inv_ι' S V, ← CategoryTheory.Category.assoc, CategoryTheory.Iso.hom_inv_id,
    CategoryTheory.Category.id_comp]

/-- The structure map of the chart followed by the open immersion:
`chartToOpen ≫ V.ι = (toSpecZero ≫ Spec.map unitZero) ≫ fromSpec`. -/
theorem chartToOpen_comp_ι :
    chartToOpen S V ≫ V.1.ι =
      (AlgebraicGeometry.Proj.toSpecZero (S.sectionsGrading V.1) ≫
        Spec.map (CommRingCat.ofHom (S.sectionsUnit V.1))) ≫
        V.2.fromSpec := by
  rw [← V.2.isoSpec_inv_ι]
  simp only [chartToOpen, AlgebraicGeometry.Scheme.GradedAffineAlgebra.projToOpen]
  rfl

/-- `ι ≫ π = φ ≫ (chartToOpen ≫ V.ι)` (`affineIso_inv_ι` and `projChart_hom`). -/
theorem ι_comp_hom :
    ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1).ι ≫ (AlgebraicGeometry.Scheme.relativeProj S).hom =
      (AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ≫ (chartToOpen S V ≫ V.1.ι) := by
  rw [← affineIso_hom_chart S V, CategoryTheory.Category.assoc, chart_hom]

theorem chartToOpen_comp_ι_preimage :
    (⊤ : (AlgebraicGeometry.Proj (S.sectionsGrading V.1)).Opens) ≤ (chartToOpen S V ≫ V.1.ι) ⁻¹ᵁ V.1 := by
  rw [AlgebraicGeometry.Scheme.Hom.comp_preimage, AlgebraicGeometry.Scheme.Opens.ι_preimage_self,
    AlgebraicGeometry.Scheme.Hom.preimage_top]

/-- The global section `(sectionsUnit V r)/1` of `Proj A(V)` that `π^♯ r` becomes on the chart. -/
def structureSection (r : Γ(X, V.1)) : Γ(AlgebraicGeometry.Proj (S.sectionsGrading V.1), ⊤) :=
  (AlgebraicGeometry.Proj.toSpecZero (S.sectionsGrading V.1) ≫
    Spec.map (CommRingCat.ofHom (S.sectionsUnit V.1))).appTop
      ((AlgebraicGeometry.Scheme.ΓSpecIso Γ(X, V.1)).inv r)

theorem structureSection_eq (r : Γ(X, V.1)) :
    structureSection S V r =
      AlgebraicGeometry.Proj.zeroToGlobal (S.sectionsGrading V.1) (S.sectionsUnit V.1 r) := by
  unfold structureSection
  rw [AlgebraicGeometry.Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  erw [AlgebraicGeometry.Scheme.SpecMap_appTop_ΓSpecIso_inv]
  rw [AlgebraicGeometry.Proj.toSpecZero_appTop_ΓSpecIso_inv]
  rfl

/-- Pointwise, the value of `structureSection r` at every point is the fraction `(sectionsUnit V r)/1`. -/
theorem structureSection_apply_val (r : Γ(X, V.1))
    (x : (⊤ : (AlgebraicGeometry.Proj (S.sectionsGrading V.1)).Opens)) :
    HomogeneousLocalization.val ((structureSection S V r).1 x) =
      Localization.mk ((S.sectionsUnit V.1 r : S.sectionsGrading V.1 0) : S.sectionsRing V.1) 1 := by
  rw [structureSection_eq]
  exact AlgebraicGeometry.Proj.zeroToGlobal_apply_val (S.sectionsGrading V.1) (S.sectionsUnit V.1 r) x

theorem unitZero_val (r : Γ(X, V.1)) :
    (S.toGradedAffineAlgebra.unitZero (affineSite V) r).1 = (S.sectionsUnit V.1 r).1 := rfl

/-- The key compatibility: `φ^♯(structureSection r)` is `ι^♯(π^♯ r)`. -/
theorem affineIso_hom_app_structureSection (r : Γ(X, V.1)) :
    (AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom.app ⊤ (structureSection S V r) =
      ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1).ι.appLE
        ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1)
        ((AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ⁻¹ᵁ ⊤)
        (by rw [AlgebraicGeometry.Scheme.Hom.preimage_top, AlgebraicGeometry.Scheme.Opens.ι_preimage_self])
        ((AlgebraicGeometry.Scheme.relativeProj S).hom.app V.1 r) := by
  have e' : (AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ⁻¹ᵁ ⊤ ≤
      (((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1).ι ≫
        (AlgebraicGeometry.Scheme.relativeProj S).hom) ⁻¹ᵁ V.1 := by
    rw [AlgebraicGeometry.Scheme.Hom.comp_preimage, AlgebraicGeometry.Scheme.Hom.preimage_top,
      AlgebraicGeometry.Scheme.Opens.ι_preimage_self]
  have h1 : ((((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1).ι ≫
      (AlgebraicGeometry.Scheme.relativeProj S).hom).appLE V.1
        ((AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ⁻¹ᵁ ⊤) e') r =
      ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1).ι.appLE
        ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1)
        ((AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom ⁻¹ᵁ ⊤)
        (by rw [AlgebraicGeometry.Scheme.Hom.preimage_top, AlgebraicGeometry.Scheme.Opens.ι_preimage_self])
        ((AlgebraicGeometry.Scheme.relativeProj S).hom.app V.1 r) := by
    rw [AlgebraicGeometry.Scheme.Hom.comp_appLE]; rfl
  have e'' : (⊤ : ((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1).toScheme.Opens) ≤
      (((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1).ι ≫
        (AlgebraicGeometry.Scheme.relativeProj S).hom) ⁻¹ᵁ V.1 := by
    rw [AlgebraicGeometry.Scheme.Hom.comp_preimage, AlgebraicGeometry.Scheme.Opens.ι_preimage_self]
  rw [← h1]
  change (AlgebraicGeometry.Scheme.Hom.appTop (AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom)
      (structureSection S V r) =
    ((((AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1).ι ≫
      (AlgebraicGeometry.Scheme.relativeProj S).hom).appLE V.1 ⊤ e'') r
  rw [AlgebraicGeometry.Scheme.Hom.appLE_of_eq (ι_comp_hom S V),
    AlgebraicGeometry.Scheme.Hom.comp_appLE_top _ _ _ (chartToOpen_comp_ι_preimage S V),
    CommRingCat.comp_apply]
  congr 1
  rw [AlgebraicGeometry.Scheme.Hom.appLE_of_eq (chartToOpen_comp_ι S V),
    AlgebraicGeometry.Scheme.Hom.comp_appLE_top _ _ _ (le_of_eq V.2.fromSpec_preimage_self.symm),
    CommRingCat.comp_apply]
  erw [AlgebraicGeometry.IsAffineOpen.fromSpec_appLE_top]
  rfl

end AlgebraicGeometry.Scheme.relativeProj

end
