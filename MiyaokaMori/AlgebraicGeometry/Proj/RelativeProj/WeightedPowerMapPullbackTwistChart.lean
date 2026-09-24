import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.Stacks01my

/-! # The chart map of a graded ring homomorphism under the weighted power map

Variable-level material (no polynomial ring appears). For a graded ring homomorphism
`ψ : 𝒜 →+*ᵍ ℬ` and `f ∈ 𝒜 d`, `d > 0`:

* `Proj.awayChartMap ψ f : D_+(ψ f) ⟶ D_+(f)` is `Spec (Away.map ψ f)` transported through the two
  chart isomorphisms `basicOpenIsoSpec`;
* `Proj.awayChartMap_appTop`: on global sections it sends `awayToSection 𝒜 f a` to
  `awayToSection ℬ (ψ f) (Away.map ψ f a)` (Stacks 01MY, the local description of `r_ψ`), a pure
  computation from `basicOpenToSpec_app_top` and `ΓSpecIso_inv_naturality`;
* `Proj.ι_comp_mapOfGradedHom_eq_awayChartMap`: when `U(ψ) = ⊤`, the morphism
  `r_ψ : Proj ℬ ⟶ Proj 𝒜` of Stacks 01MY (`Stacks01my.lean`) restricted to `D_+(ψ f)` is `awayChartMap ψ f`.
  This is the only place where `Proj.mapOfGradedHom_basicOpen` (`Stacks01my.lean`)
  enters; it is exactly the `key` step of `weightedPowerMap_functionFieldDegree_eq_chart`
  (`WeightedPowerMapDegree.lean`) with `m = 1` replaced by general `d`.

Also two bookkeeping lemmas on restriction of sections of the structure sheaf to opens
(`Scheme.homOfLE_appTop_topIso_inv`, `Scheme.Opens.appIso_top_hom_map`), used in step (d).

Source: Stacks 01MY; the finite map from ordinary to weighted projective space in Lemma 3.1
of the paper.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry

/-! ## Restriction of sections to opens: two spellings -/

/-- Two successive restriction maps of the structure sheaf are one restriction map. -/
theorem Scheme.presheaf_map_map_op (X : Scheme.{u}) {a b c : X.Opens} (f : op a ⟶ op b)
    (g : op b ⟶ op c) (x : Γ(X, a)) :
    X.presheaf.map g (X.presheaf.map f x) =
      X.presheaf.map (homOfLE ((leOfHom g.unop).trans (leOfHom f.unop))).op x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- Restrict a section over `W` to the global sections of the open subscheme `V ≤ W`. -/
def Scheme.resTop (X : Scheme.{u}) {V W : X.Opens} (h : V ≤ W) (x : Γ(X, W)) : Γ(V, ⊤) :=
  V.topIso.inv (X.presheaf.map (homOfLE h).op x)

theorem Scheme.homOfLE_appTop_topIso_inv (X : Scheme.{u}) {V W : X.Opens} (h : V ≤ W)
    (x : Γ(X, W)) :
    (X.homOfLE h).appTop (W.topIso.inv x) = X.resTop h x := by
  unfold Scheme.resTop
  rw [Scheme.Hom.appTop, Scheme.homOfLE_app]
  simp only [Scheme.Opens.topIso_inv]
  erw [Scheme.presheaf_map_map_op, Scheme.presheaf_map_map_op]
  rfl

theorem Scheme.Opens.appIso_top_hom_map (X : Scheme.{u}) {V W : X.Opens} (h : V ≤ W)
    (hVW : V.ι ''ᵁ ⊤ ≤ W) (x : Γ(X, W)) :
    (V.ι.appIso ⊤).hom (X.presheaf.map (homOfLE hVW).op x) = X.resTop h x := by
  unfold Scheme.resTop
  rw [Scheme.Opens.ι_appIso]
  simp only [Iso.refl_hom, Scheme.Opens.topIso_inv]
  erw [ConcreteCategory.id_apply, Scheme.presheaf_map_map_op]

namespace Proj

variable {A B σ τ : Type u} [CommRing A] [CommRing B]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ] (ψ : 𝒜 →+*ᵍ ℬ)
  (f : A) {d : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d)

/-- The chart map `D_+(ψ f) ⟶ D_+(f)`: `Spec (Away.map ψ f)` through the chart isomorphisms. -/
def awayChartMap :
    (Proj.basicOpen ℬ (ψ f)).toScheme ⟶ (Proj.basicOpen 𝒜 f).toScheme :=
  (Proj.basicOpenIsoSpec ℬ (ψ f) (ψ.2 hf) hd).hom ≫
    Spec.map (CommRingCat.ofHom (HomogeneousLocalization.Away.map ψ f)) ≫
    (Proj.basicOpenIsoSpec 𝒜 f hf hd).inv

theorem awayChartMap_ι :
    awayChartMap ψ f hf hd ≫ (Proj.basicOpen 𝒜 f).ι =
      (Proj.basicOpenIsoSpec ℬ (ψ f) (ψ.2 hf) hd).hom ≫
        Spec.map (CommRingCat.ofHom (HomogeneousLocalization.Away.map ψ f)) ≫
        Proj.awayι 𝒜 f hf hd := by
  simp only [awayChartMap, Category.assoc, Proj.basicOpenIsoSpec_inv_ι]

omit [AddSubgroupClass σ A] [GradedRing 𝒜] in
/-- `D_+(ψ f).ι = (basicOpenIsoSpec).hom ≫ awayι`. -/
theorem basicOpenIsoSpec_hom_awayι :
    (Proj.basicOpenIsoSpec ℬ (ψ f) (ψ.2 hf) hd).hom ≫ Proj.awayι ℬ (ψ f) (ψ.2 hf) hd =
      (Proj.basicOpen ℬ (ψ f)).ι := by
  rw [← Proj.basicOpenIsoSpec_inv_ι, Iso.hom_inv_id_assoc]

/-- **Stacks 01MY on a chart.** If `U(ψ) = ⊤`, the morphism `r_ψ` (`Proj.mapOfGradedHom`, composed
with the identifications `Proj ℬ = ⊤ = U(ψ)`) restricted to `D_+(ψ f)` is `awayChartMap ψ f`.
Depends on `Proj.mapOfGradedHom_basicOpen` (`Stacks01my.lean`). -/
theorem ι_comp_mapOfGradedHom_eq_awayChartMap (h : Proj.mapDomain ψ = ⊤) :
    (Proj.basicOpen ℬ (ψ f)).ι ≫
        ((Scheme.topIso (Proj ℬ)).inv ≫ ((Proj ℬ).isoOfEq h.symm).hom ≫ Proj.mapOfGradedHom ψ) =
      awayChartMap ψ f hf hd ≫ (Proj.basicOpen 𝒜 f).ι := by
  have hle : Proj.basicOpen ℬ (ψ f) ≤ Proj.mapDomain ψ :=
    le_iSup_of_le f (le_iSup_of_le d (le_iSup_of_le hd (le_iSup_of_le hf le_rfl)))
  have hfac : (Proj.basicOpen ℬ (ψ f)).ι ≫ (Scheme.topIso (Proj ℬ)).inv ≫
      ((Proj ℬ).isoOfEq h.symm).hom = (Proj ℬ).homOfLE hle := by
    rw [← cancel_mono (Proj.mapDomain ψ).ι]
    simp only [Category.assoc, Scheme.isoOfEq_hom_ι, Scheme.toIso_inv_ι, Category.comp_id,
      Scheme.homOfLE_ι]
  rw [awayChartMap_ι, ← Proj.mapOfGradedHom_basicOpen ψ f d hd hf, ← Category.assoc, ← hfac,
    Iso.hom_inv_id_assoc]
  simp only [Category.assoc]

/-- The chart map on global sections: `awayToSection 𝒜 f a ↦ awayToSection ℬ (ψ f) (Away.map ψ f a)`. -/
theorem awayChartMap_appTop (a : HomogeneousLocalization.Away 𝒜 f) :
    (awayChartMap ψ f hf hd).appTop ((Proj.basicOpen 𝒜 f).topIso.inv (Proj.awayToSection 𝒜 f a)) =
      (Proj.basicOpen ℬ (ψ f)).topIso.inv
        (Proj.awayToSection ℬ (ψ f) (HomogeneousLocalization.Away.map ψ f a)) := by
  -- `basicOpenIsoSpec.hom` on global sections
  have hA : ∀ (𝒞 : ℕ → σ) [GradedRing 𝒞] (c : A) {e : ℕ} (hc : c ∈ 𝒞 e) (he : 0 < e)
      (z : HomogeneousLocalization.Away 𝒞 c),
      (Proj.basicOpenIsoSpec 𝒞 c hc he).hom.appTop ((Scheme.ΓSpecIso _).inv z) =
        (Proj.basicOpen 𝒞 c).topIso.inv (Proj.awayToSection 𝒞 c z) := by
    intro 𝒞 _ c e hc he z
    rw [Scheme.Hom.appTop, Proj.basicOpenIsoSpec_hom, Proj.basicOpenToSpec_app_top]
    simp only [ConcreteCategory.comp_apply, Iso.inv_hom_id_apply]
  have hB : ∀ (𝒞 : ℕ → τ) [GradedRing 𝒞] (c : B) {e : ℕ} (hc : c ∈ 𝒞 e) (he : 0 < e)
      (z : HomogeneousLocalization.Away 𝒞 c),
      (Proj.basicOpenIsoSpec 𝒞 c hc he).hom.appTop ((Scheme.ΓSpecIso _).inv z) =
        (Proj.basicOpen 𝒞 c).topIso.inv (Proj.awayToSection 𝒞 c z) := by
    intro 𝒞 _ c e hc he z
    rw [Scheme.Hom.appTop, Proj.basicOpenIsoSpec_hom, Proj.basicOpenToSpec_app_top]
    simp only [ConcreteCategory.comp_apply, Iso.inv_hom_id_apply]
  -- the inverse chart iso on global sections
  have hAinv : (Proj.basicOpenIsoSpec 𝒜 f hf hd).inv.appTop
      ((Proj.basicOpen 𝒜 f).topIso.inv (Proj.awayToSection 𝒜 f a)) =
      (Scheme.ΓSpecIso _).inv a := by
    rw [← hA 𝒜 f hf hd a]
    change ((Proj.basicOpenIsoSpec 𝒜 f hf hd).inv ≫ (Proj.basicOpenIsoSpec 𝒜 f hf hd).hom).appTop
      ((Scheme.ΓSpecIso (CommRingCat.of (HomogeneousLocalization.Away 𝒜 f))).inv a) = _
    rw [Iso.inv_hom_id]
    rfl
  -- `Spec.map φ` on global sections
  have hnat : (Spec.map (CommRingCat.ofHom (HomogeneousLocalization.Away.map ψ f))).appTop
      ((Scheme.ΓSpecIso _).inv a) =
      (Scheme.ΓSpecIso _).inv (HomogeneousLocalization.Away.map ψ f a) := by
    have := congrArg (fun h => h a)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (HomogeneousLocalization.Away.map ψ f)))
    simp only [ConcreteCategory.comp_apply, CommRingCat.hom_ofHom] at this
    exact this.symm
  unfold awayChartMap
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop]
  simp only [ConcreteCategory.comp_apply]
  rw [hAinv, hnat, hB ℬ (ψ f) (ψ.2 hf) hd]

end Proj

end AlgebraicGeometry

end
