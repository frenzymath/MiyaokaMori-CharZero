import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.WeightedPowerMapPullbackTwistChart
import MiyaokaMori.AlgebraicGeometry.Modules.Glue.WeightedPowerMapPullbackTwistGlue
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.WeightedProjCoordinateFormula

/-! # Pullback of `O(m)` along a graded homomorphism (the weighted power map, variable level)

Variable-level version of the whole argument (Stacks 01MS + 01MY + gluing), for two graded rings
`𝒜`, `ℬ`, a graded ring hom `ψ : 𝒜 →+*ᵍ ℬ`, and a morphism `g : Proj ℬ ⟶ Proj 𝒜` which on each chart
`D_+(ψ f)` is the chart map `awayChartMap ψ f` (hypothesis `hg`; for `r_ψ` this is
`Proj.ι_comp_mapOfGradedHom_eq_awayChartMap`).

For one chart `f ∈ 𝒜 d` and `n * d = m`:
* `O_{Proj 𝒜}(m)|_{D_+(f)}` is framed by `f ^ n` (`homogeneousCoordinateFrameIso`, Stacks 01MS);
* `O_{Proj ℬ}(m)|_V` is framed by `ψ f ^ n` for every `V ≤ D_+(ψ f)`;
* the pullback frame (`pullbackFrameIso`) and the source frame give
  `comparisonIsoOn V : (g^* O(m))|_V ≅ O(m)|_V`;
* `comparisonIsoOn_section`: it sends the pullback of the global section `a ∈ 𝒜 m` to the global
  section `ψ a`. Both sides are computed as the restriction to `V` of
  `awayToSection ℬ (ψ f) (a / f^n ↦ ψ a / (ψ f)^n)`; on the pullback side this is exactly the
  formula `awayChartMap_appTop` (01MY), on the source side it is division by the frame.
* Hence (`hom_ext_of_frame`) the comparisons agree on common opens and are compatible with
  restriction, and `Scheme.Modules.exists_iso_of_local_isos` glues them:
  `pullback_twist_iso_of_charts`.

All declarations are stated for variable graded rings; the concrete weighted polynomial case is a
pure instantiation (`WeightedPowerMapPullbackTwist`). Modelled on
`HomogeneousTupleTwistPullback` (the same argument for a homogeneous
tuple `P^1 → P^N`), whose performance notes apply.

Source: Lemma 2.2 of the paper; Stacks 01MS, 01MY, 04TN.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Proj.TwistPullback

open MiyaokaMori.WeightedJets.ProjTwisting
open AlgebraicGeometry.Scheme.Modules.HomogeneousTupleTwistPullback (restrictedGlobalSection chartPullbackIso
  pullbackFrameIso pullbackFrameIso_section hom_ext_of_frame)
open AlgebraicGeometry.Scheme.Modules.HomogeneousTupleTwistRestriction (restrictIsoOfLE restrictIsoOfLE_section)

-- `SheafOfModules.unit` is an object of `SheafOfModules X.ringCatSheaf`, while `X.Modules` is a plain
-- `def` around it; the frame API needs this (elaborator-only option).
set_option backward.isDefEq.respectTransparency false

local instance twistPullbackUnitSectionOfNat (X : Scheme.{u}) (U : X.Opens) :
    OfNat (Γ(SheafOfModules.unit (R := X.ringCatSheaf), U)) 1 where
  ofNat := show Γ(X, U) from 1

variable {A B σ τ : Type u} [CommRing A] [CommRing B]
  [SetLike σ A] [AddSubgroupClass σ A] [SetLike τ B] [AddSubgroupClass τ B]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ] (ψ : 𝒜 →+*ᵍ ℬ)

/-! ## Frame elements -/

section FrameElem

variable {𝒜}

theorem pow_mem_of_mul_eq (f : A) {d : ℕ} (hf : f ∈ 𝒜 d) (m n : ℕ) (hn : n * d = m) :
    f ^ n ∈ 𝒜 m := by
  have h := SetLike.pow_mem_graded n hf
  rwa [smul_eq_mul, hn] at h

omit [CommRing A] [AddSubgroupClass σ A] [GradedRing 𝒜] in
theorem mem_smul_of_mem {d m n : ℕ} (hn : n * d = m) {a : A} (ha : a ∈ 𝒜 m) : a ∈ 𝒜 (n • d) := by
  rwa [smul_eq_mul, hn]

/-- On an open contained in `D_+(f)`, the power `f ^ n` does not vanish. -/
theorem pow_not_mem_of_le (f : A) (n : ℕ) {V : (Proj 𝒜).Opens} (hV : V ≤ Proj.basicOpen 𝒜 f)
    (x : V) : f ^ n ∉ x.1.asHomogeneousIdeal := by
  intro h
  have hx : x.1 ∈ Proj.basicOpen 𝒜 f := hV x.2
  exact hx (x.1.isPrime.mem_of_pow_mem n h)

/-- The degree-zero fraction `a / f ^ n` for `a ∈ 𝒜 m`. -/
def ratio (f : A) {d : ℕ} (hf : f ∈ 𝒜 d) (m n : ℕ) (hn : n * d = m) {a : A} (ha : a ∈ 𝒜 m) :
    HomogeneousLocalization.Away 𝒜 f :=
  HomogeneousLocalization.Away.mk 𝒜 hf n a (mem_smul_of_mem hn ha)

/-- Dividing the homogeneous section `a` by the frame `f ^ n` on an open `V ≤ D_+(f)` gives the
restriction of the chart function `a / f ^ n`. -/
theorem divideSection_homogeneousSection_eq (f : A) {d : ℕ} (hf : f ∈ 𝒜 d) (m n : ℕ)
    (hn : n * d = m) {V : (Proj 𝒜).Opens} (hV : V ≤ Proj.basicOpen 𝒜 f) {a : A} (ha : a ∈ 𝒜 m) :
    divideSection 𝒜 m (f ^ n) (pow_mem_of_mul_eq f hf m n hn) (pow_not_mem_of_le f n hV)
        (homogeneousSection 𝒜 m a ha V) =
      (Proj 𝒜).presheaf.map (homOfLE hV).op (Proj.awayToSection 𝒜 f (ratio f hf m n hn ha)) := by
  apply Subtype.ext
  funext x
  apply HomogeneousLocalization.val_injective
  rw [divideSection_val]
  change Localization.mk a 1 * Localization.mk 1 ⟨f ^ n, _⟩ =
    ((Proj.awayToSection 𝒜 f (ratio f hf m n hn ha)).1 ⟨x.1, hV x.2⟩).val
  rw [Localization.mk_mul, mul_one, one_mul]
  erw [ProjectiveSpectrum.Proj.awayToSection_apply]
  simp only [ratio, HomogeneousLocalization.Away.val_mk, Localization.mk_eq_mk',
    IsLocalization.map_mk', RingHom.id_apply]

/-- `f ^ n / f ^ n = 1`. -/
theorem ratio_self (f : A) {d : ℕ} (hf : f ∈ 𝒜 d) (m n : ℕ) (hn : n * d = m) :
    ratio f hf m n hn (pow_mem_of_mul_eq f hf m n hn) = 1 := by
  apply HomogeneousLocalization.val_injective
  rw [HomogeneousLocalization.val_one]
  simp only [ratio, HomogeneousLocalization.Away.val_mk]
  exact Localization.mk_self (⟨f ^ n, ⟨n, rfl⟩⟩ : Submonoid.powers f)

end FrameElem

/-! ## One chart: the local comparison -/

section Chart

variable (g : Proj ℬ ⟶ Proj 𝒜) (f : A) {d : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d)
  (hg : (Proj.basicOpen ℬ (ψ f)).ι ≫ g =
    Proj.awayChartMap ψ f hf hd ≫ (Proj.basicOpen 𝒜 f).ι)
  (m n : ℕ) (hn : n * d = m)

/-- The frame `f ^ n` of `O(m)` on the target chart `D_+(f)`. -/
def targetFrameIso :
    (sheaf 𝒜 (m : ℤ)).restrict (Proj.basicOpen 𝒜 f).ι ≅
      SheafOfModules.unit (R := (Proj.basicOpen 𝒜 f).toScheme.ringCatSheaf) :=
  homogeneousCoordinateFrameIso 𝒜 m (f ^ n) (pow_mem_of_mul_eq f hf m n hn)
    (Proj.basicOpen 𝒜 f) (pow_not_mem_of_le f n le_rfl)

/-- The chart map restricted to an open `V ≤ D_+(ψ f)`. -/
def chartMapOn (V : (Proj ℬ).Opens) (hV : V ≤ Proj.basicOpen ℬ (ψ f)) :
    V.toScheme ⟶ (Proj.basicOpen 𝒜 f).toScheme :=
  (Proj ℬ).homOfLE hV ≫ Proj.awayChartMap ψ f hf hd

include hg in
theorem chartMapOn_comp_ι (V : (Proj ℬ).Opens) (hV : V ≤ Proj.basicOpen ℬ (ψ f)) :
    chartMapOn 𝒜 ℬ ψ f hf hd V hV ≫ (Proj.basicOpen 𝒜 f).ι = V.ι ≫ g := by
  rw [chartMapOn, Category.assoc, ← hg, ← Category.assoc, Scheme.homOfLE_ι]

/-- The pullback frame of `g^* O(m)` on `V ≤ D_+(ψ f)`, induced from `f ^ n`. -/
def pullbackFrameIsoOn (V : (Proj ℬ).Opens) (hV : V ≤ Proj.basicOpen ℬ (ψ f)) :
    ((Scheme.Modules.pullback g).obj (sheaf 𝒜 (m : ℤ))).restrict V.ι ≅
      SheafOfModules.unit (R := V.toScheme.ringCatSheaf) :=
  pullbackFrameIso g V (Proj.basicOpen 𝒜 f) (chartMapOn 𝒜 ℬ ψ f hf hd V hV)
    (chartMapOn_comp_ι 𝒜 ℬ ψ g f hf hd hg V hV) (sheaf 𝒜 (m : ℤ)) (targetFrameIso 𝒜 f hf m n hn)

/-- The frame `(ψ f) ^ n` of `O(m)` on `V ≤ D_+(ψ f)`. -/
def sourceFrameIsoOn (V : (Proj ℬ).Opens) (hV : V ≤ Proj.basicOpen ℬ (ψ f)) :
    (sheaf ℬ (m : ℤ)).restrict V.ι ≅ SheafOfModules.unit (R := V.toScheme.ringCatSheaf) :=
  homogeneousCoordinateFrameIso ℬ m (ψ f ^ n) (pow_mem_of_mul_eq (ψ f) (ψ.2 hf) m n hn) V
    (pow_not_mem_of_le (ψ f) n hV)

/-- The local comparison `(g^* O(m))|_V ≅ O(m)|_V`, `V ≤ D_+(ψ f)`. -/
def comparisonIsoOn (V : (Proj ℬ).Opens) (hV : V ≤ Proj.basicOpen ℬ (ψ f)) :
    ((Scheme.Modules.pullback g).obj (sheaf 𝒜 (m : ℤ))).restrict V.ι ≅
      (sheaf ℬ (m : ℤ)).restrict V.ι :=
  pullbackFrameIsoOn 𝒜 ℬ ψ g f hf hd hg m n hn V hV ≪≫
    (sourceFrameIsoOn 𝒜 ℬ ψ f hf m n hn V hV).symm

/-! ### Coordinate formulas -/

/-- The target frame sends the global section `a` to the chart function `a / f ^ n`. -/
theorem targetFrameIso_section {a : A} (ha : a ∈ 𝒜 m) :
    (targetFrameIso 𝒜 f hf m n hn).hom.app ⊤
        (restrictedGlobalSection (sheaf 𝒜 (m : ℤ)) (Proj.basicOpen 𝒜 f)
          (homogeneousSection 𝒜 m a ha ⊤)) =
      (Proj.basicOpen 𝒜 f).topIso.inv (Proj.awayToSection 𝒜 f (ratio f hf m n hn ha)) := by
  unfold targetFrameIso restrictedGlobalSection
  rw [homogeneousCoordinateFrameIso_hom_app_top_homogeneousSection 𝒜 m (f ^ n)
    (pow_mem_of_mul_eq f hf m n hn) (Proj.basicOpen 𝒜 f) (pow_not_mem_of_le f n le_rfl) a ha
    (V' := Proj.basicOpen 𝒜 f) (pow_not_mem_of_le f n le_rfl)
    (Proj.basicOpen 𝒜 f).ι_image_top.le]
  rw [divideSection_homogeneousSection_eq f hf m n hn le_rfl ha,
    Scheme.Opens.appIso_top_hom_map (Proj 𝒜) le_rfl]
  unfold Scheme.resTop
  rw [Scheme.presheaf_map_map_op]
  rfl

/-- The pullback frame sends the pullback of the global section `a` to the restriction of the chart
function `ψ a / (ψ f) ^ n` (Stacks 01MY: `g` acts on chart functions by `Away.map ψ f`). -/
theorem pullbackFrameIsoOn_section (V : (Proj ℬ).Opens) (hV : V ≤ Proj.basicOpen ℬ (ψ f))
    {a : A} (ha : a ∈ 𝒜 m) :
    (pullbackFrameIsoOn 𝒜 ℬ ψ g f hf hd hg m n hn V hV).hom.app ⊤
        (restrictedGlobalSection ((Scheme.Modules.pullback g).obj (sheaf 𝒜 (m : ℤ))) V
          (AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback g (homogeneousSection 𝒜 m a ha ⊤))) =
      (Proj ℬ).resTop hV (Proj.awayToSection ℬ (ψ f)
        (HomogeneousLocalization.Away.map ψ f (ratio f hf m n hn ha))) := by
  unfold pullbackFrameIsoOn
  rw [pullbackFrameIso_section, targetFrameIso_section, chartMapOn, Scheme.Hom.comp_appTop,
    ConcreteCategory.comp_apply, Proj.awayChartMap_appTop, Scheme.homOfLE_appTop_topIso_inv]

/-- The source frame sends the global section `ψ a` to the same restricted chart function. -/
theorem sourceFrameIsoOn_section (V : (Proj ℬ).Opens) (hV : V ≤ Proj.basicOpen ℬ (ψ f))
    {a : A} (ha : a ∈ 𝒜 m) :
    (sourceFrameIsoOn 𝒜 ℬ ψ f hf m n hn V hV).hom.app ⊤
        (restrictedGlobalSection (sheaf ℬ (m : ℤ)) V (homogeneousSection ℬ m (ψ a) (ψ.2 ha) ⊤)) =
      (Proj ℬ).resTop hV (Proj.awayToSection ℬ (ψ f)
        (HomogeneousLocalization.Away.map ψ f (ratio f hf m n hn ha))) := by
  unfold sourceFrameIsoOn restrictedGlobalSection
  rw [homogeneousCoordinateFrameIso_hom_app_top_homogeneousSection ℬ m (ψ f ^ n)
    (pow_mem_of_mul_eq (ψ f) (ψ.2 hf) m n hn) V (pow_not_mem_of_le (ψ f) n hV) (ψ a) (ψ.2 ha)
    (V' := Proj.basicOpen ℬ (ψ f)) (pow_not_mem_of_le (ψ f) n le_rfl)
    (V.ι_image_top.le.trans hV)]
  erw [divideSection_homogeneousSection_eq (ψ f) (ψ.2 hf) m n hn le_rfl (ψ.2 ha)]
  rw [Scheme.Opens.appIso_top_hom_map (Proj ℬ) hV]
  unfold Scheme.resTop
  rw [Scheme.presheaf_map_map_op]
  congr 3
  simp only [ratio, HomogeneousLocalization.Away.map_mk]
  rfl

/-- The local comparison sends the pullback of the global section `a` to the global section `ψ a`. -/
theorem comparisonIsoOn_section (V : (Proj ℬ).Opens) (hV : V ≤ Proj.basicOpen ℬ (ψ f))
    {a : A} (ha : a ∈ 𝒜 m) :
    (comparisonIsoOn 𝒜 ℬ ψ g f hf hd hg m n hn V hV).hom.app ⊤
        (restrictedGlobalSection ((Scheme.Modules.pullback g).obj (sheaf 𝒜 (m : ℤ))) V
          (AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback g (homogeneousSection 𝒜 m a ha ⊤))) =
      restrictedGlobalSection (sheaf ℬ (m : ℤ)) V (homogeneousSection ℬ m (ψ a) (ψ.2 ha) ⊤) := by
  unfold comparisonIsoOn
  simp only [Iso.trans_hom, Iso.symm_hom, Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply]
  rw [pullbackFrameIsoOn_section, ← sourceFrameIsoOn_section 𝒜 ℬ ψ f hf m n hn V hV ha]
  change ((sourceFrameIsoOn 𝒜 ℬ ψ f hf m n hn V hV).hom ≫
    (sourceFrameIsoOn 𝒜 ℬ ψ f hf m n hn V hV).inv).app ⊤ _ = _
  rw [Iso.hom_inv_id]
  rfl

/-- The pullback of `f ^ n` is the unit vector of the pullback frame. -/
theorem pullbackFrameIsoOn_self (V : (Proj ℬ).Opens) (hV : V ≤ Proj.basicOpen ℬ (ψ f)) :
    (pullbackFrameIsoOn 𝒜 ℬ ψ g f hf hd hg m n hn V hV).hom.app ⊤
        (restrictedGlobalSection ((Scheme.Modules.pullback g).obj (sheaf 𝒜 (m : ℤ))) V
          (AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback g
            (homogeneousSection 𝒜 m (f ^ n) (pow_mem_of_mul_eq f hf m n hn) ⊤))) = 1 := by
  rw [pullbackFrameIsoOn_section, ratio_self, map_one, map_one]
  unfold Scheme.resTop
  rw [map_one, map_one]

end Chart

/-! ## Two charts agree; restriction compatibility -/

section Compat

variable (g : Proj ℬ ⟶ Proj 𝒜) (m : ℕ)

/-- The comparisons of two charts agree on a common open. -/
theorem comparisonIsoOn_eq (f : A) {d : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d)
    (hg : (Proj.basicOpen ℬ (ψ f)).ι ≫ g = Proj.awayChartMap ψ f hf hd ≫ (Proj.basicOpen 𝒜 f).ι)
    (n : ℕ) (hn : n * d = m)
    (f' : A) {d' : ℕ} (hf' : f' ∈ 𝒜 d') (hd' : 0 < d')
    (hg' : (Proj.basicOpen ℬ (ψ f')).ι ≫ g =
      Proj.awayChartMap ψ f' hf' hd' ≫ (Proj.basicOpen 𝒜 f').ι)
    (n' : ℕ) (hn' : n' * d' = m)
    (V : (Proj ℬ).Opens) (hV : V ≤ Proj.basicOpen ℬ (ψ f)) (hV' : V ≤ Proj.basicOpen ℬ (ψ f')) :
    comparisonIsoOn 𝒜 ℬ ψ g f hf hd hg m n hn V hV =
      comparisonIsoOn 𝒜 ℬ ψ g f' hf' hd' hg' m n' hn' V hV' := by
  apply Iso.ext
  exact hom_ext_of_frame (pullbackFrameIsoOn 𝒜 ℬ ψ g f hf hd hg m n hn V hV)
    (restrictedGlobalSection ((Scheme.Modules.pullback g).obj (sheaf 𝒜 (m : ℤ))) V
      (AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback g
        (homogeneousSection 𝒜 m (f ^ n) (pow_mem_of_mul_eq f hf m n hn) ⊤)))
    (pullbackFrameIsoOn_self 𝒜 ℬ ψ g f hf hd hg m n hn V hV) _ _
    ((comparisonIsoOn_section 𝒜 ℬ ψ g f hf hd hg m n hn V hV (pow_mem_of_mul_eq f hf m n hn)).trans
      (comparisonIsoOn_section 𝒜 ℬ ψ g f' hf' hd' hg' m n' hn' V hV'
        (pow_mem_of_mul_eq f hf m n hn)).symm)

/-- The comparison restricted from a larger open is the comparison on the smaller open. -/
theorem comparisonIsoOn_restrict (f : A) {d : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d)
    (hg : (Proj.basicOpen ℬ (ψ f)).ι ≫ g = Proj.awayChartMap ψ f hf hd ≫ (Proj.basicOpen 𝒜 f).ι)
    (n : ℕ) (hn : n * d = m)
    {V V' : (Proj ℬ).Opens} (hVV' : V ≤ V') (hV' : V' ≤ Proj.basicOpen ℬ (ψ f)) :
    restrictIsoOfLE hVV' (comparisonIsoOn 𝒜 ℬ ψ g f hf hd hg m n hn V' hV') =
      comparisonIsoOn 𝒜 ℬ ψ g f hf hd hg m n hn V (hVV'.trans hV') := by
  apply Iso.ext
  apply hom_ext_of_frame (pullbackFrameIsoOn 𝒜 ℬ ψ g f hf hd hg m n hn V (hVV'.trans hV'))
    (restrictedGlobalSection ((Scheme.Modules.pullback g).obj (sheaf 𝒜 (m : ℤ))) V
      (AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback g
        (homogeneousSection 𝒜 m (f ^ n) (pow_mem_of_mul_eq f hf m n hn) ⊤)))
    (pullbackFrameIsoOn_self 𝒜 ℬ ψ g f hf hd hg m n hn V (hVV'.trans hV'))
  rw [comparisonIsoOn_section]
  exact restrictIsoOfLE_section hVV' (comparisonIsoOn 𝒜 ℬ ψ g f hf hd hg m n hn V' hV') _ _
    (comparisonIsoOn_section 𝒜 ℬ ψ g f hf hd hg m n hn V' hV' (pow_mem_of_mul_eq f hf m n hn))

end Compat

/-! ## Gluing -/

/-- **Pullback of `O(m)` along a morphism given chart-wise by a graded ring hom.**
Let `ψ : 𝒜 →+*ᵍ ℬ`, `g : Proj ℬ ⟶ Proj 𝒜`, and `f j ∈ 𝒜 (d j)` (`d j > 0`) such that the opens
`D_+(ψ (f j))` cover `Proj ℬ` and `g` restricted to `D_+(ψ (f j))` is `awayChartMap ψ (f j)`
(Stacks 01MY). If `d j ∣ m` for all `j` (`n j * d j = m`), then `g^* O_{Proj 𝒜}(m) ≅ O_{Proj ℬ}(m)`. -/
theorem pullback_twist_iso_of_charts (g : Proj ℬ ⟶ Proj 𝒜) {ι : Type u} (f : ι → A) (d : ι → ℕ)
    (hf : ∀ j, f j ∈ 𝒜 (d j)) (hd : ∀ j, 0 < d j)
    (hcov : ∀ x : Proj ℬ, ∃ j, x ∈ Proj.basicOpen ℬ (ψ (f j)))
    (hg : ∀ j, (Proj.basicOpen ℬ (ψ (f j))).ι ≫ g =
      Proj.awayChartMap ψ (f j) (hf j) (hd j) ≫ (Proj.basicOpen 𝒜 (f j)).ι)
    (m : ℕ) (n : ι → ℕ) (hn : ∀ j, n j * d j = m) :
    Nonempty ((Scheme.Modules.pullback g).obj (sheaf 𝒜 (m : ℤ)) ≅ sheaf ℬ (m : ℤ)) :=
  Scheme.Modules.exists_iso_of_local_isos (fun j => Proj.basicOpen ℬ (ψ (f j))) hcov _ _
    (fun j V hV => comparisonIsoOn 𝒜 ℬ ψ g (f j) (hf j) (hd j) (hg j) m (n j) (hn j) V hV)
    (fun j _V _V' hVV' hV' =>
      comparisonIsoOn_restrict 𝒜 ℬ ψ g m (f j) (hf j) (hd j) (hg j) (n j) (hn j) hVV' hV')
    (fun j j' V hj hj' =>
      comparisonIsoOn_eq 𝒜 ℬ ψ g m (f j) (hf j) (hd j) (hg j) (n j) (hn j)
        (f j') (hf j') (hd j') (hg j') (n j') (hn j') V hj hj')

end AlgebraicGeometry.Proj.TwistPullback

end
