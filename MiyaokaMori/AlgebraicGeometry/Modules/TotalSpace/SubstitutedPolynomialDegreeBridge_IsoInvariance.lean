import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotSectionsPolynomial
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.SubstitutedPolynomialDegreeBridge_XiDegreePullbackMap
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.SubstitutedPolynomialDegreeBridge_UnitDegree
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.SubstitutedPolynomialDegreeBridge_IsoInvariance_HomSection
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleSectionGenericGermZero
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.UnitNonvanishingSection
import MiyaokaMori.AlgebraicGeometry.Modules.NonvanishingLocusTensorSection

/-! # Isomorphisms of pullback line bundles preserve the ξ-degree

An arbitrary isomorphism `α : p^*A ≅ p^*B` of pullback line bundles on `Tot(L)` does not raise the ξ-degree of
global sections. This is exactly what is needed to pass from the canonical identification
`(p^*M)^{⊗d} ≅ p^*(M^d)` (for which the paper's bound is proved in `SubstitutedPolynomialDegreeBridge_Canonical`)
to the *arbitrary* `θ` quantified in `xiDegree_evalHomogeneousAtSections_le`.

Argument (not in the paper, which uses the canonical identification): any two such isomorphisms differ by a
unit of `Γ(Tot(L), O) = ⊕_{q≥0} H^0(C, L^{-q})`, an ℕ-graded domain, whose units have degree `0`.

**Structure.** The top-level theorem `xiDegree_pullbackIso_hom_app_le` is assembled from:
* `exists_xiSections_of_pullbackIso` (the Hom–section calculus `Hom(p^*A, p^*B) = Γ(Tot, p^*(A^∨⊗B))`,
  packaged as: `α.hom` is "multiplication by a section `s`" followed by the pullback of a base evaluation map, and
  the product of the sections of `α.hom` and `α.inv` is (a base isomorphism away from) the unit section `1`).
  Proved in `SubstitutedPolynomialDegreeBridge_IsoInvariance_HomSection` (`exists_xiSections_of_pullbackIso_of_evalCalculus`)
  from two facts about line bundles — the evaluation `A^∨ ⊗ A ⟶ O` is an isomorphism (Stacks 01CT) and
  `β_{A,A} = 𝟙` (Stacks 01CR) — and the abstract monoidal calculus `InvertibleEvalHomSectionCalculus`.
* `sectionTensor_ne_zero_of_isIntegral`: on an integral scheme the tensor product of two non-zero global
  sections of line bundles is non-zero (the generic point lies in `X_s ⊓ X_t = X_{s ⊗ t}`).
* proved here: `tensorCoefficients_ne_zero` (the coefficient pairing is an isomorphism on sections),
  `xiDegree_xiSectionMul` (**ξ-degrees add under multiplication**, from `xiCoefficient_mul` + the above),
  `eq_zero_of_xiDegree_eq_bot`, `pullbackUnitIso_inv_one_ne_zero`, `xiDegree_pullbackIso_hom_app_le`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- **Non-zero sections of line bundles on an integral scheme have non-zero tensor product**
(`sectionTensor s t = moduleTensorSection s t ∈ Γ(X, Modules.tensor M M')`).

Reference: Hartshorne II.6.15 (proof) / Stacks 0AXX-type argument; a generic-point argument.

Proof. Let `η` be the generic point of the integral scheme `X`; its local ring
is the function field, so `𝔪_η = ⊥` (`maximalIdeal_stalk_genericPoint_eq_bot`). A global section of a line bundle
is zero as soon as its germ at `η` is zero (`lineBundle_section_eq_zero_of_germ_genericPoint_eq_zero`), so
`s ≠ 0`, `t ≠ 0` give non-zero germs at `η`, i.e. (since `𝔪_η = ⊥`) `η ∈ X_s ∩ X_t`
(`mem_nonvanishingLocus_of_maximalIdeal_eq_bot`). The non-vanishing locus of `s ⊗ t` is `X_s ⊓ X_t`
(`mem_nonvanishingLocus_sectionTensor`, Stacks 01CB stalk computation), so `η ∈ X_{s ⊗ t}`, and the germ of
`s ⊗ t` at `η` is not in `𝔪_η (M ⊗ M')_η ∋ 0`; hence `s ⊗ t ≠ 0`.
Edge cases: `X` empty is excluded by `IsIntegral`; `s = 0` or `t = 0` are excluded by hypothesis. -/
theorem sectionTensor_ne_zero_of_isIntegral {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsIntegral X]
    (M M' : X.Modules) [M.IsLineBundle] [M'.IsLineBundle]
    (s : (M.val.obj (Opposite.op ⊤) : Type u)) (t : (M'.val.obj (Opposite.op ⊤) : Type u))
    (hs : s ≠ 0) (ht : t ≠ 0) : sectionTensor s t ≠ 0 := by
  intro h0
  have hη := AlgebraicGeometry.maximalIdeal_stalk_genericPoint_eq_bot X
  have hs' : M.presheaf.germ ⊤ (genericPoint X) trivial s ≠ 0 := fun h =>
    hs (lineBundle_section_eq_zero_of_germ_genericPoint_eq_zero M s h)
  have ht' : M'.presheaf.germ ⊤ (genericPoint X) trivial t ≠ 0 := fun h =>
    ht (lineBundle_section_eq_zero_of_germ_genericPoint_eq_zero M' t h)
  have h1 : genericPoint X ∈ M.nonvanishingLocus s :=
    AlgebraicGeometry.Scheme.Modules.mem_nonvanishingLocus_of_maximalIdeal_eq_bot M s _ hη hs'
  have h2 : genericPoint X ∈ M'.nonvanishingLocus t :=
    AlgebraicGeometry.Scheme.Modules.mem_nonvanishingLocus_of_maximalIdeal_eq_bot M' t _ hη ht'
  have h3 : genericPoint X ∈
      (AlgebraicGeometry.Scheme.Modules.tensor M M').nonvanishingLocus (sectionTensor s t) :=
    (AlgebraicGeometry.Scheme.Modules.mem_nonvanishingLocus_sectionTensor M M' s t _).mpr ⟨h1, h2⟩
  have h4 := (AlgebraicGeometry.Scheme.Modules.mem_nonvanishingLocus _ _ _).mp h3
  apply h4
  have h5 : TopCat.Presheaf.germ (AlgebraicGeometry.Scheme.Modules.tensor M M').presheaf ⊤ (genericPoint X)
      trivial (sectionTensor s t) = 0 := by
    rw [h0]
    exact map_zero _
  rw [h5]
  exact Submodule.zero_mem _

/-- The coefficient pairing `tensorCoefficientsHom` packaged as an isomorphism (the same composite, factor by
factor: `tensorIsoTensorObj`, `tensorIso`, `tensorμ` with inverse `tensorδ`, `monoidalPowCat`,
`monoidalPowIsoTensorPower`, `eqToIso`, `coefficientModuleIso`); `tensorCoefficientsIso_hom` is `rfl`. -/
noncomputable def tensorCoefficientsIso {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L M M' : LineBundle C.toVariety) {a b q : ℕ} (hab : a + b = q) :
    AlgebraicGeometry.Scheme.Modules.tensor ((M.zpow 1).tensor (L.zpow (-(a : ℤ)))).toModules
        ((M'.zpow 1).tensor (L.zpow (-(b : ℤ)))).toModules ≅
      (((M.tensor M').zpow 1).tensor (L.zpow (-(q : ℤ)))).toModules :=
  let D := AlgebraicGeometry.Scheme.Modules.dual L.toModules
  let pw := AlgebraicGeometry.Scheme.Modules.monoidalPowIsoTensorPower D
  AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _ ≪≫
    CategoryTheory.MonoidalCategory.tensorIso
      ((L.coefficientModuleIso M a).symm ≪≫ AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _)
      ((L.coefficientModuleIso M' b).symm ≪≫ AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _) ≪≫
    ⟨CategoryTheory.MonoidalCategory.tensorμ M.toModules (AlgebraicGeometry.Scheme.Modules.moduleTensorPower D a)
        M'.toModules (AlgebraicGeometry.Scheme.Modules.moduleTensorPower D b),
      CategoryTheory.MonoidalCategory.tensorδ _ _ _ _,
      CategoryTheory.MonoidalCategory.tensorμ_tensorδ _ _ _ _,
      CategoryTheory.MonoidalCategory.tensorδ_tensorμ _ _ _ _⟩ ≪≫
    CategoryTheory.MonoidalCategory.tensorIso
      (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj M.toModules M'.toModules).symm
      (CategoryTheory.MonoidalCategory.tensorIso (pw a).symm (pw b).symm ≪≫
        AlgebraicGeometry.Scheme.Modules.monoidalPowCat D a b ≪≫ pw (a + b) ≪≫
        CategoryTheory.eqToIso (congrArg (AlgebraicGeometry.Scheme.Modules.moduleTensorPower D) hab)) ≪≫
    (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj (M.tensor M').toModules
      (AlgebraicGeometry.Scheme.Modules.moduleTensorPower D q)).symm ≪≫
    L.coefficientModuleIso (M.tensor M') q

theorem tensorCoefficientsIso_hom {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L M M' : LineBundle C.toVariety) {a b q : ℕ} (hab : a + b = q) :
    (tensorCoefficientsIso L M M' hab).hom = tensorCoefficientsHom L M M' hab := rfl

/-- **The coefficient pairing of two non-zero coefficients is non-zero** (`C` is integral):
`tensorCoefficients c c' = tensorCoefficientsHom (sectionTensor c c')`, `sectionTensor c c' ≠ 0` by
`sectionTensor_ne_zero_of_isIntegral`, and the section map of an isomorphism of sheaves of modules is injective. -/
theorem tensorCoefficients_ne_zero {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L M M' : LineBundle C.toVariety) {a b q : ℕ} (hab : a + b = q)
    (c : ((((M.zpow 1).tensor (L.zpow (-(a : ℤ)))).toModules.val.obj (Opposite.op ⊤)) : Type u))
    (c' : ((((M'.zpow 1).tensor (L.zpow (-(b : ℤ)))).toModules.val.obj (Opposite.op ⊤)) : Type u))
    (hc : c ≠ 0) (hc' : c' ≠ 0) : tensorCoefficients L M M' hab c c' ≠ 0 := by
  have : AlgebraicGeometry.IsIntegral C.toScheme := SmoothProjectiveCurve.isIntegral C
  intro h0
  apply sectionTensor_ne_zero_of_isIntegral _ _ c c' hc hc'
  have h1 := AlgebraicGeometry.Scheme.Modules.app_top_hom_inv (tensorCoefficientsIso L M M' hab) (sectionTensor c c')
  rw [tensorCoefficientsIso_hom] at h1
  unfold tensorCoefficients at h0
  rw [h0, map_zero] at h1
  exact h1.symm

/-- If all ξ-coefficients vanish, the section is zero (`eq_sum_xiMonomial` with an empty support). -/
theorem eq_zero_of_xiDegree_eq_bot {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L M : LineBundle C.toVariety)
    (P : (((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        M.toModules).val.obj (Opposite.op ⊤) : Type u))
    (h : xiDegree L M P = ⊥) : P = 0 := by
  unfold xiDegree at h
  rw [Finset.max_eq_bot] at h
  rw [eq_sum_xiMonomial L M P, h, Finset.sum_empty]

/-- **ξ-degrees add under multiplication** (`C` integral): `xiDegree (P·P') = xiDegree P + xiDegree P'`
(ξ-expansion; `Γ(Tot(L), O)` is a graded domain).

Proof. `≤` is `xiDegree_mul_le`. For `≥`: if either degree is `⊥` the right side is `⊥`. Otherwise let
`a = xiDegree P`, `b = xiDegree P'` (in `ℕ`), so `c_a(P) ≠ 0`, `c_b(P') ≠ 0` (`Finset.mem_of_max`). By the convolution
formula `xiCoefficient_mul`, the `(a+b)`-th coefficient of `P·P'` is `Σ_{i+j=a+b} c_i(P) ⊗ c_j(P')`; every term with
`(i, j) ≠ (a, b)` has `i > a` or `j > b`, hence vanishes (`xiCoefficient_eq_zero_of_xiDegree_lt`,
`tensorCoefficients_zero_left/right`), so the sum is `c_a(P) ⊗ c_b(P') ≠ 0` (`tensorCoefficients_ne_zero`). Hence
`a + b ≤ xiDegree (P·P')` (`Finset.le_max`). -/
theorem xiDegree_xiSectionMul {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L M M' : LineBundle C.toVariety)
    (P : (((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        M.toModules).val.obj (Opposite.op ⊤) : Type u))
    (P' : (((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        M'.toModules).val.obj (Opposite.op ⊤) : Type u)) :
    xiDegree L (M.tensor M') (xiSectionMul L M M' P P') = xiDegree L M P + xiDegree L M' P' := by
  refine le_antisymm (xiDegree_mul_le L M M' P P') ?_
  by_cases hPbot : xiDegree L M P = ⊥
  · rw [hPbot, WithBot.bot_add]; exact bot_le
  by_cases hP'bot : xiDegree L M' P' = ⊥
  · rw [hP'bot, WithBot.add_bot]; exact bot_le
  obtain ⟨a, hP⟩ := WithBot.ne_bot_iff_exists.mp hPbot
  obtain ⟨b, hP'⟩ := WithBot.ne_bot_iff_exists.mp hP'bot
  rw [← hP, ← hP']
  -- `a`, `b` are the top indices
  have ha : xiCoefficient L M P a ≠ 0 :=
    (xiCoefficient_finite_support L M P).mem_toFinset.mp (Finset.mem_of_max hP.symm)
  have hb : xiCoefficient L M' P' b ≠ 0 :=
    (xiCoefficient_finite_support L M' P').mem_toFinset.mp (Finset.mem_of_max hP'.symm)
  have hcoef : xiCoefficient L (M.tensor M') (xiSectionMul L M M' P P') (a + b) ≠ 0 := by
    rw [xiCoefficient_mul]
    have hmem : ((a, b) : ℕ × ℕ) ∈ Finset.HasAntidiagonal.antidiagonal (a + b) :=
      Finset.HasAntidiagonal.mem_antidiagonal.mpr rfl
    rw [Finset.sum_eq_single_of_mem (⟨(a, b), hmem⟩ : {x // x ∈ Finset.HasAntidiagonal.antidiagonal (a + b)})
      (Finset.mem_attach _ _)]
    · exact tensorCoefficients_ne_zero L M M' _ _ _ ha hb
    · rintro ⟨⟨i, j⟩, hij'⟩ _ hne
      have hij : i + j = a + b := Finset.HasAntidiagonal.mem_antidiagonal.mp hij'
      have hne' : ¬ (i = a ∧ j = b) := fun h => hne (by
        obtain ⟨rfl, rfl⟩ := h
        rfl)
      by_cases hi : a < i
      · rw [xiCoefficient_eq_zero_of_xiDegree_lt L M P (by rw [← hP]; exact WithBot.coe_lt_coe.mpr hi)]
        exact tensorCoefficients_zero_left L M M' _ _
      · have hj : b < j := by omega
        rw [xiCoefficient_eq_zero_of_xiDegree_lt L M' P' (by rw [← hP']; exact WithBot.coe_lt_coe.mpr hj)]
        exact tensorCoefficients_zero_right L M M' _ _
  have hmem : a + b ∈ (xiCoefficient_finite_support L (M.tensor M') (xiSectionMul L M M' P P')).toFinset :=
    (xiCoefficient_finite_support L (M.tensor M') (xiSectionMul L M M' P P')).mem_toFinset.mpr hcoef
  have := Finset.le_max hmem
  unfold xiDegree
  exact_mod_cast this

/-- The unit section `1 ∈ Γ(Tot(L), p^*O_C)` is non-zero (`Tot(L)` is non-empty: it contains the zero section
over the non-empty integral curve `C`, so `Γ(Tot(L), O)` is a non-trivial ring). -/
theorem pullbackUnitIso_inv_one_ne_zero {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L M : LineBundle C.toVariety) :
    ((AlgebraicGeometry.Scheme.Modules.pullbackUnitIso
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).inv.app ⊤
        (1 : (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.ringCatSheaf.obj.obj
          (Opposite.op ⊤)) : (((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        (M.zpow ((0 : ℕ) : ℤ)).toModules).val.obj (Opposite.op ⊤) : Type u)) ≠ 0 := by
  have : AlgebraicGeometry.IsIntegral C.toScheme := SmoothProjectiveCurve.isIntegral C
  have hne : Nonempty (AlgebraicGeometry.Scheme.totalSpace L.toModules).left :=
    ⟨(AlgebraicGeometry.Scheme.zeroSection L.toModules).base (Nonempty.some inferInstance)⟩
  have : Nonempty ((⊤ : (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.Opens) : Type u) :=
    ⟨⟨hne.some, trivial⟩⟩
  intro h0
  have h2 := AlgebraicGeometry.Scheme.Modules.app_top_inv_hom
    (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom)
    (1 : (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.ringCatSheaf.obj.obj (Opposite.op ⊤))
  have h0' : ((AlgebraicGeometry.Scheme.Modules.pullbackUnitIso
      (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).inv.val.app (Opposite.op ⊤)).hom
      (1 : (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.ringCatSheaf.obj.obj (Opposite.op ⊤)) = 0 := h0
  rw [h0', map_zero] at h2
  have : Nontrivial ((AlgebraicGeometry.Scheme.totalSpace L.toModules).left.ringCatSheaf.obj.obj (Opposite.op ⊤)) :=
    inferInstanceAs (Nontrivial Γ((AlgebraicGeometry.Scheme.totalSpace L.toModules).left, ⊤))
  exact (one_ne_zero (α := (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.ringCatSheaf.obj.obj
    (Opposite.op ⊤))) h2.symm

/-- **The Hom–section calculus for pullback line bundles on `Tot(L)`.**

Statement. Write `p : Tot(L) → C`, `pb := Modules.pullback p`, `A^∨ := A.zpow (-1)`, `H := A^∨ ⊗ B`, `H' := B^∨ ⊗ A`.
For an isomorphism `α : p^*A ≅ p^*B` there are global sections `s ∈ Γ(Tot, p^*H)`, `s' ∈ Γ(Tot, p^*H')`, a base
morphism `ev : A ⊗ H ⟶ B` on `C` and a base *isomorphism* `μ : H ⊗ H' ≅ O_C` (written `(A.zpow 0).toModules`, which
is `O_C` by definition) such that
(i) `α.hom.app ⊤ Q = (pb ev).app ⊤ (Q · s)` for every `Q ∈ Γ(Tot, p^*A)` (`·` is `xiSectionMul`), and
(ii) `(pb μ.hom).app ⊤ (s · s') = 1`, the unit section `(pullbackUnitIso p).inv.app ⊤ 1 ∈ Γ(Tot, p^*O_C)`.

References: Stacks 01CM/01CN (Hom and tensor commute with pullback for locally free sheaves; `Hom(A, B) ≅ A^∨ ⊗ B`),
01CT (the evaluation of an invertible sheaf is an isomorphism), 01CR (`β_{L,L} = 𝟙` for an invertible sheaf);
Hartshorne II Ex. 5.1.

Proof: `exists_xiSections_of_pullbackIso_of_evalCalculus`
(`SubstitutedPolynomialDegreeBridge_IsoInvariance_HomSection`). With `D := dual A` and the evaluation isomorphism
`ev₀ : D ⊗ A ≅ O_C`, put `c := ε ≫ pb(ev₀⁻¹) ≫ δ`, `e := μ ≫ pb(ev₀) ≫ η` on `Tot(L)` (so `c ≫ e = 𝟙`, and
`β_{p^*A,p^*A} = 𝟙`); `s := (c ≫ pb D ◁ α.hom ≫ μ)(1)` (moved to `p^*(A^∨ ⊗ B)` by `zpowNegOneIso` and
`tensorIsoTensorObj`), `s'` likewise from `α.inv`; `ev` and `μ` are the evident pairings built from `ev₀`. Then (i)
and (ii) are the abstract identities `EvalCalculus.hom_eq_secHom_transport` / `EvalCalculus.pair_secHom_transport`
(pure monoidal algebra), transported to sections by `homOfTopSection_xiSectionMul`, `homOfTopSection_sectionTensor`
and `unitHomEquivTop`. -/
theorem exists_xiSections_of_pullbackIso {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L A B : LineBundle C.toVariety)
    (α : (AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj A.toModules ≅
      (AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj B.toModules) :
    ∃ (s : (((AlgebraicGeometry.Scheme.Modules.pullback
          (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
          ((A.zpow (-1)).tensor B).toModules).val.obj (Opposite.op ⊤) : Type u))
      (s' : (((AlgebraicGeometry.Scheme.Modules.pullback
          (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
          ((B.zpow (-1)).tensor A).toModules).val.obj (Opposite.op ⊤) : Type u))
      (ev : (A.tensor ((A.zpow (-1)).tensor B)).toModules ⟶ B.toModules)
      (μ : (((A.zpow (-1)).tensor B).tensor ((B.zpow (-1)).tensor A)).toModules ≅
        (A.zpow ((0 : ℕ) : ℤ)).toModules),
      (∀ Q : (((AlgebraicGeometry.Scheme.Modules.pullback
          (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
          A.toModules).val.obj (Opposite.op ⊤) : Type u),
        α.hom.app ⊤ Q = ((AlgebraicGeometry.Scheme.Modules.pullback
          (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).map ev).app ⊤
            (xiSectionMul L A ((A.zpow (-1)).tensor B) Q s)) ∧
      ((AlgebraicGeometry.Scheme.Modules.pullback
          (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).map μ.hom).app ⊤
          (xiSectionMul L ((A.zpow (-1)).tensor B) ((B.zpow (-1)).tensor A) s s') =
        (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso
          (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).inv.app ⊤
          (1 : (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.ringCatSheaf.obj.obj
            (Opposite.op ⊤)) := by
  exact exists_xiSections_of_pullbackIso_of_evalCalculus L A B α

/-- **Isomorphisms between pullback line bundles preserve ξ-degree.**

Assembly. Take `s, s', ev, μ` from `exists_xiSections_of_pullbackIso`.
1. `xiDegree (α Q) = xiDegree (pb ev (Q·s)) ≤ xiDegree (Q·s) ≤ xiDegree Q + xiDegree s`
   (`xiDegree_pullback_map_le`, `xiDegree_mul_le`).
2. `xiDegree s + xiDegree s' = xiDegree (s·s')` (`xiDegree_xiSectionMul`) `= xiDegree (pb μ (s·s'))`
   (`xiDegree_pullback_map_le` for `μ.hom` and `μ.inv`) `= xiDegree 1 ≤ 0`
   (`xiDegree_pullbackUnitIso_inv_one_le_zero`), and `xiDegree 1 ≠ ⊥` since `1 ≠ 0`
   (`pullbackUnitIso_inv_one_ne_zero`, `eq_zero_of_xiDegree_eq_bot`).
3. Hence `xiDegree s = a ∈ ℕ`, `xiDegree s' = b ∈ ℕ` with `a + b ≤ 0`, so `a = 0`, and step 1 gives the claim. -/
theorem xiDegree_pullbackIso_hom_app_le {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L A B : LineBundle C.toVariety)
    (α : (AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj A.toModules ≅
      (AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj B.toModules)
    (Q : (((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        A.toModules).val.obj (Opposite.op ⊤) : Type u)) :
    xiDegree L B (α.hom.app ⊤ Q) ≤ xiDegree L A Q := by
  obtain ⟨s, s', ev, μ, hα, hunit⟩ := exists_xiSections_of_pullbackIso L A B α
  -- step 1
  have h1 : xiDegree L B (α.hom.app ⊤ Q) ≤ xiDegree L A Q + xiDegree L ((A.zpow (-1)).tensor B) s := by
    rw [hα Q]
    exact le_trans (xiDegree_pullback_map_le L _ B ev _) (xiDegree_mul_le L A _ Q s)
  -- step 2
  set t := xiSectionMul L ((A.zpow (-1)).tensor B) ((B.zpow (-1)).tensor A) s s' with ht
  have h2 : xiDegree L ((A.zpow (-1)).tensor B) s + xiDegree L ((B.zpow (-1)).tensor A) s' =
      xiDegree L _ t := (xiDegree_xiSectionMul L _ _ s s').symm
  have h3 : xiDegree L _ t = xiDegree L (A.zpow ((0 : ℕ) : ℤ))
      (((AlgebraicGeometry.Scheme.Modules.pullback
          (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).map μ.hom).app ⊤ t) := by
    refine le_antisymm ?_ (xiDegree_pullback_map_le L _ _ μ.hom t)
    have := xiDegree_pullback_map_le L _ _ μ.inv
      (((AlgebraicGeometry.Scheme.Modules.pullback
          (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).map μ.hom).app ⊤ t)
    have hback : ((AlgebraicGeometry.Scheme.Modules.pullback
          (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).map μ.inv).app ⊤
        (((AlgebraicGeometry.Scheme.Modules.pullback
          (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).map μ.hom).app ⊤ t) = t :=
      AlgebraicGeometry.Scheme.Modules.app_top_hom_inv
        ((AlgebraicGeometry.Scheme.Modules.pullback
          (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).mapIso μ) t
    rw [hback] at this
    exact this
  rw [hunit] at h3
  have h4 := xiDegree_pullbackUnitIso_inv_one_le_zero L A
  have h5 : xiDegree L (A.zpow ((0 : ℕ) : ℤ))
      ((AlgebraicGeometry.Scheme.Modules.pullbackUnitIso
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).inv.app ⊤
        (1 : (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.ringCatSheaf.obj.obj
          (Opposite.op ⊤))) ≠ ⊥ := by
    intro hbot
    exact pullbackUnitIso_inv_one_ne_zero L A (eq_zero_of_xiDegree_eq_bot L _ _ hbot)
  -- step 3: WithBot arithmetic
  rw [← h3, ← h2] at h4 h5
  by_cases hsbot : xiDegree L ((A.zpow (-1)).tensor B) s = ⊥
  · rw [hsbot, WithBot.add_bot] at h1
    exact le_trans h1 bot_le
  by_cases hs'bot : xiDegree L ((B.zpow (-1)).tensor A) s' = ⊥
  · exfalso
    apply h5
    rw [hs'bot, WithBot.add_bot]
  obtain ⟨a, hs⟩ := WithBot.ne_bot_iff_exists.mp hsbot
  obtain ⟨b, hs'⟩ := WithBot.ne_bot_iff_exists.mp hs'bot
  rw [← hs, ← hs'] at h4
  have hab' : ((a + b : ℕ) : WithBot ℕ) ≤ ((0 : ℕ) : WithBot ℕ) := by
    rw [Nat.cast_add]; exact h4
  have hab : a + b ≤ 0 := WithBot.coe_le_coe.mp hab'
  have ha0 : a = 0 := by omega
  rw [← hs, ha0] at h1
  simpa using h1

end
