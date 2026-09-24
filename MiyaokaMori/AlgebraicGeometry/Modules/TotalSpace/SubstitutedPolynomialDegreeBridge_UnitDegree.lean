import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotSectionsPolynomial

/-! # The unit section has ξ-degree `≤ 0`

The unit section `1 ∈ Γ(Tot(L), O)`, viewed in `Γ(Tot(L), p^*O_C)` through `pullbackUnitIso`, has ξ-degree
`≤ 0`: it is the pullback of the base section `1 ∈ Γ(C, O_C)`, and pullbacks of base sections live in the
`ξ^0` component of `Γ(Tot(L), p^*M) = ⊕_q H^0(C, M ⊗ L^{-q})` (a base section is `c·ξ^0` in the ξ-expansion).
This is the base case `e = 0` of the monomial bound in `SubstitutedPolynomialDegreeBridge_Canonical`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
open scoped CategoryTheory.MonoidalCategory

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : AlgebraicGeometry.Scheme.{u}}

/-- `pullbackUnitIso⁻¹` sends the unit section of `O_X` to the pullback `η(1)` of the unit section of
`O_Y` (`ModuleSections.pullback_unit_one` read backwards through `asIso`). -/
theorem pullbackUnitIso_inv_app_top_one (f : X ⟶ Y) :
    (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso f).inv.app ⊤
        (1 : X.ringCatSheaf.obj.obj (Opposite.op (⊤ : X.Opens))) =
      ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
        (SheafOfModules.unit Y.ringCatSheaf)).app ⊤
        (1 : Y.ringCatSheaf.obj.obj (Opposite.op (⊤ : Y.Opens))) := by
  have : (SheafOfModules.pushforward.{u} f.toRingCatSheafHom).IsRightAdjoint :=
    (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f).isRightAdjoint
  have h : (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso f).hom.app ⊤
      (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
        (SheafOfModules.unit Y.ringCatSheaf)).app ⊤
        (1 : Y.ringCatSheaf.obj.obj (Opposite.op (⊤ : Y.Opens)))) =
      (1 : X.ringCatSheaf.obj.obj (Opposite.op (⊤ : X.Opens))) :=
    AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback_unit_one f
  rw [← h]
  exact AlgebraicGeometry.Scheme.Modules.app_top_hom_inv
    (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso f) _

set_option backward.isDefEq.respectTransparency false in
/-- The inverse right unitor on a global section: `ρ⁻¹(a) = a ⊗ 1`. -/
theorem rightUnitor_inv_app_top (A : X.Modules) (a : (A.val.obj (Opposite.op ⊤) : Type u)) :
    (ρ_ A).inv.app ⊤ a =
      AlgebraicGeometry.Scheme.Modules.tensorSections A (𝟙_ X.Modules) ⊤ a (1 : Γ(X, ⊤)) := by
  have h := AlgebraicGeometry.Scheme.Modules.rightUnitor_app_tensorSections A ⊤ a (1 : Γ(X, ⊤))
  rw [show (1 : Γ(X, ⊤)) • a = a from one_smul _ a] at h
  conv_lhs => rw [← h]
  exact AlgebraicGeometry.Scheme.Modules.app_top_hom_inv (ρ_ A) _

/-- The counit–unit triangle on global sections: `ε(η(s)) = s` for `s ∈ Γ(Y, f_*N) = Γ(X, N)`. -/
theorem counit_app_unit_app_top (f : X ⟶ Y) (N : X.Modules)
    (s : (((AlgebraicGeometry.Scheme.Modules.pushforward f).obj N).val.obj (Opposite.op ⊤) : Type u)) :
    ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f).counit.app N).app (f ⁻¹ᵁ ⊤)
        (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
          ((AlgebraicGeometry.Scheme.Modules.pushforward f).obj N)).app ⊤ s) = s := by
  have h := congrArg (fun φ : (AlgebraicGeometry.Scheme.Modules.pushforward f).obj N ⟶
      (AlgebraicGeometry.Scheme.Modules.pushforward f).obj N =>
        AlgebraicGeometry.Scheme.Modules.Hom.app φ ⊤ s)
    ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f).right_triangle_components N)
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- **The projection-formula comparison map on a pure tensor of global sections**:
`θ(m ⊗ s) = η(m) ⊗ s` in `Γ(Y, f_*(f^*M ⊗ N)) = Γ(X, f^*M ⊗ N)`. Unfold `projectionFormulaHom`
(`homEquiv_unit`: `η ≫ f_*(δ ≫ (f^*M ◁ ε))`), evaluate `δ` on `η(m ⊗ s)` with
`pullbackTensorObjHom_app_unit_tensorSections`, the whiskering with `tensorHom_tensorSections`, and cancel
`ε ∘ η` with `counit_app_unit_app_top`. -/
theorem projectionFormulaHom_app_top_tensorSections (f : X ⟶ Y) (M : Y.Modules) (N : X.Modules)
    (m : (M.val.obj (Opposite.op ⊤) : Type u))
    (s : (((AlgebraicGeometry.Scheme.Modules.pushforward f).obj N).val.obj (Opposite.op ⊤) : Type u)) :
    (AlgebraicGeometry.Scheme.Modules.projectionFormulaHom f M N).app ⊤
        (AlgebraicGeometry.Scheme.Modules.tensorSections M
          ((AlgebraicGeometry.Scheme.Modules.pushforward f).obj N) ⊤ m s) =
      AlgebraicGeometry.Scheme.Modules.tensorSections
        ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M) N (f ⁻¹ᵁ ⊤)
        (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app ⊤ m) s := by
  unfold AlgebraicGeometry.Scheme.Modules.projectionFormulaHom
  rw [CategoryTheory.Adjunction.homEquiv_unit]
  change ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M ◁
      (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f).counit.app N).app (f ⁻¹ᵁ ⊤)
    ((AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom f M
        ((AlgebraicGeometry.Scheme.Modules.pushforward f).obj N)).app (f ⁻¹ᵁ ⊤)
      (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f).unit.app
          (CategoryTheory.MonoidalCategoryStruct.tensorObj M
            ((AlgebraicGeometry.Scheme.Modules.pushforward f).obj N))).app ⊤
        (AlgebraicGeometry.Scheme.Modules.tensorSections M
          ((AlgebraicGeometry.Scheme.Modules.pushforward f).obj N) ⊤ m s))) = _
  rw [AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom_app_unit_tensorSections]
  rw [← CategoryTheory.MonoidalCategory.id_tensorHom]
  change (CategoryTheory.MonoidalCategoryStruct.tensorHom (C := X.Modules)
      (𝟙 ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M))
      ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f).counit.app N)).val.app
      (Opposite.op (f ⁻¹ᵁ ⊤))
    (AlgebraicGeometry.Scheme.Modules.tensorSections _ _ (f ⁻¹ᵁ ⊤) _ _) = _
  erw [AlgebraicGeometry.Scheme.Modules.tensorHom_tensorSections]
  exact congrArg (fun z => AlgebraicGeometry.Scheme.Modules.tensorSections
    ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M) N (f ⁻¹ᵁ ⊤)
    (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f).unit.app M).app ⊤ m) z)
    (AlgebraicGeometry.Scheme.Modules.counit_app_unit_app_top f N s)

set_option backward.isDefEq.respectTransparency false in
/-- `Γ(T, g^*M) → Γ(X, M ⊗ g_*O_T)` on a pulled-back global section: `P = η(m)` goes to `m ⊗ 1`.
Combine `rightUnitor_inv_app_top` (`ρ⁻¹(η m) = η m ⊗ 1`), `projectionFormulaHom_app_top_tensorSections`
(`θ(m ⊗ 1) = η m ⊗ 1`) and `θIso.inv ∘ θ = id`. -/
theorem pullbackSectionToPushforward_unit_app (g : X ⟶ Y) (M : Y.Modules) [M.IsLineBundle]
    (m : (M.val.obj (Opposite.op ⊤) : Type u)) :
    AlgebraicGeometry.Scheme.Modules.pullbackSectionToPushforward g M
        (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M).app ⊤ m) =
      AlgebraicGeometry.Scheme.Modules.tensorSections M
        ((AlgebraicGeometry.Scheme.Modules.pushforward g).obj (SheafOfModules.unit X.ringCatSheaf)) ⊤ m
        (1 : Γ(X, g ⁻¹ᵁ ⊤)) := by
  have h1 := AlgebraicGeometry.Scheme.Modules.rightUnitor_inv_app_top
    ((AlgebraicGeometry.Scheme.Modules.pullback g).obj M)
    (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M).app ⊤ m)
  have h2 := AlgebraicGeometry.Scheme.Modules.projectionFormulaHom_app_top_tensorSections g M
    (SheafOfModules.unit X.ringCatSheaf) m (1 : Γ(X, g ⁻¹ᵁ ⊤))
  unfold AlgebraicGeometry.Scheme.Modules.pullbackSectionToPushforward
  change ((AlgebraicGeometry.Scheme.Modules.projectionFormulaIso g M
      (SheafOfModules.unit X.ringCatSheaf)).inv.val.app (Opposite.op ⊤)).hom
    ((ρ_ ((AlgebraicGeometry.Scheme.Modules.pullback g).obj M)).inv.app ⊤
      (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M).app ⊤ m)) = _
  rw [h1]
  have h3 : AlgebraicGeometry.Scheme.Modules.tensorSections
      ((AlgebraicGeometry.Scheme.Modules.pullback g).obj M) (𝟙_ X.Modules) ⊤
      (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M).app ⊤ m)
      (1 : Γ(X, ⊤)) =
      (AlgebraicGeometry.Scheme.Modules.projectionFormulaIso g M
        (SheafOfModules.unit X.ringCatSheaf)).hom.app ⊤
        (AlgebraicGeometry.Scheme.Modules.tensorSections M
          ((AlgebraicGeometry.Scheme.Modules.pushforward g).obj (SheafOfModules.unit X.ringCatSheaf)) ⊤ m
          (1 : Γ(X, g ⁻¹ᵁ ⊤))) := by
    exact h2.symm
  rw [h3]
  exact AlgebraicGeometry.Scheme.Modules.app_top_hom_inv
    (AlgebraicGeometry.Scheme.Modules.projectionFormulaIso g M (SheafOfModules.unit X.ringCatSheaf)) _

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- `ι_q ≫ π_{q'} = 0` for `q ≠ q'` (`Sigma.ι_desc` and the `dif_neg` branch of `totalProj`). -/
theorem GradedQCAlgebra.totalIncl_totalProj_of_ne (S : X.GradedQCAlgebra) {q q' : ℕ} (h : q ≠ q') :
    S.totalIncl q ≫ S.totalProj q' = 0 :=
  (CategoryTheory.Limits.Sigma.ι_desc _ _).trans (dif_neg h)

/-- The structure map `A → π_*O_{Spec_X A}` sends the unit of the sections ring to `1`
(`structureHom_app_apply` + `map_one` of the ring-presheaf map). -/
theorem relativeSpec.structureHom_app_top_one (A : X.QCAlgebra) :
    (AlgebraicGeometry.Scheme.relativeSpec.structureHom A).app ⊤ (1 : A.sectionsRing ⊤) =
      (1 : (AlgebraicGeometry.Scheme.relativeSpec A).left.ringCatSheaf.obj.obj
        (Opposite.op ((AlgebraicGeometry.Scheme.relativeSpec A).hom ⁻¹ᵁ ⊤))) := by
  have h := AlgebraicGeometry.Scheme.relativeSpec.structureHom_app_apply A ⊤ (1 : A.sectionsRing ⊤)
  refine h.trans ?_
  exact map_one ((AlgebraicGeometry.Scheme.relativeSpec.structureRingMap A).app (Opposite.op ⊤)).hom

/-- `structureIso⁻¹` sends `1 ∈ Γ(Spec_X A, ⊤)` to the unit of the sections ring `A(⊤)`. -/
theorem relativeSpec.structureIso_inv_app_top_one (A : X.QCAlgebra) :
    (AlgebraicGeometry.Scheme.relativeSpec.structureIso A).inv.app ⊤
        (1 : (AlgebraicGeometry.Scheme.relativeSpec A).left.ringCatSheaf.obj.obj
          (Opposite.op ((AlgebraicGeometry.Scheme.relativeSpec A).hom ⁻¹ᵁ ⊤))) =
      (1 : A.sectionsRing ⊤) := by
  rw [← AlgebraicGeometry.Scheme.relativeSpec.structureHom_app_top_one]
  exact AlgebraicGeometry.Scheme.Modules.app_top_hom_inv
    (AlgebraicGeometry.Scheme.relativeSpec.structureIso A) _

/-- The unit of the sections ring of `S.total` is `ι_0(1_{S_0})` (definitional: `total.one = S.one ≫ ι_0`). -/
theorem GradedQCAlgebra.total_sectionsRing_one (S : X.GradedQCAlgebra) :
    (1 : S.total.sectionsRing ⊤) = (S.totalIncl 0).app ⊤ (S.one.app ⊤ (1 : Γ(X, ⊤))) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- **The `q`-th coefficient map kills `m ⊗ 1` for `q ≠ 0`**: `1 ∈ Γ(Tot, O)` is `σ(ι_0 1)`, and
`ι_0 ≫ π_q = 0`. -/
theorem totalSpace.coefficientHom_app_top_tensorSections_one (L M : X.Modules) [L.IsLineBundle]
    {q : ℕ} (hq : q ≠ 0) (m : (M.val.obj (Opposite.op ⊤) : Type u)) :
    (AlgebraicGeometry.Scheme.totalSpace.coefficientHom L M q).app ⊤
        (AlgebraicGeometry.Scheme.Modules.tensorSections M
          ((AlgebraicGeometry.Scheme.Modules.pushforward (AlgebraicGeometry.Scheme.totalSpace L).hom).obj
            (SheafOfModules.unit (AlgebraicGeometry.Scheme.totalSpace L).left.ringCatSheaf)) ⊤ m
          (1 : (AlgebraicGeometry.Scheme.totalSpace L).left.ringCatSheaf.obj.obj
            (Opposite.op ((AlgebraicGeometry.Scheme.totalSpace L).hom ⁻¹ᵁ ⊤)))) = 0 := by
  -- the second tensor factor: `(σIso.inv ≫ π_q ≫ Θ'_q)(1) = 0`
  have hg : (((AlgebraicGeometry.Scheme.relativeSpec.structureIso
        (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual L)).total).inv ≫
      (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual L)).totalProj q ≫
      AlgebraicGeometry.Scheme.totalSpace.symPartToTensorPower L q).app ⊤
        (1 : (AlgebraicGeometry.Scheme.totalSpace L).left.ringCatSheaf.obj.obj
          (Opposite.op ((AlgebraicGeometry.Scheme.totalSpace L).hom ⁻¹ᵁ ⊤)))) = 0 := by
    rw [AlgebraicGeometry.Scheme.Modules.Hom.comp_app, AlgebraicGeometry.Scheme.Modules.Hom.comp_app]
    change (AlgebraicGeometry.Scheme.totalSpace.symPartToTensorPower L q).app ⊤
      (((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
        (AlgebraicGeometry.Scheme.Modules.dual L)).totalProj q).app ⊤
        ((AlgebraicGeometry.Scheme.relativeSpec.structureIso
          (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
            (AlgebraicGeometry.Scheme.Modules.dual L)).total).inv.app ⊤
          (1 : (AlgebraicGeometry.Scheme.totalSpace L).left.ringCatSheaf.obj.obj
            (Opposite.op ((AlgebraicGeometry.Scheme.totalSpace L).hom ⁻¹ᵁ ⊤))))) = 0
    rw [AlgebraicGeometry.Scheme.relativeSpec.structureIso_inv_app_top_one,
      AlgebraicGeometry.Scheme.GradedQCAlgebra.total_sectionsRing_one]
    change (AlgebraicGeometry.Scheme.totalSpace.symPartToTensorPower L q).app ⊤
      ((((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
        (AlgebraicGeometry.Scheme.Modules.dual L)).totalIncl 0 ≫
        (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
          (AlgebraicGeometry.Scheme.Modules.dual L)).totalProj q).app ⊤)
        ((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
          (AlgebraicGeometry.Scheme.Modules.dual L)).one.app ⊤
          (1 : X.ringCatSheaf.obj.obj (Opposite.op (⊤ : X.Opens))))) = 0
    rw [AlgebraicGeometry.Scheme.GradedQCAlgebra.totalIncl_totalProj_of_ne _ (Ne.symm hq),
      AlgebraicGeometry.Scheme.Modules.Hom.zero_app]
    change (AlgebraicGeometry.Scheme.totalSpace.symPartToTensorPower L q).app ⊤ 0 = 0
    exact map_zero _
  unfold AlgebraicGeometry.Scheme.totalSpace.coefficientHom
  rw [AlgebraicGeometry.Scheme.Modules.Hom.comp_app]
  change ((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj M
      (AlgebraicGeometry.Scheme.Modules.moduleTensorPower (AlgebraicGeometry.Scheme.Modules.dual L) q)).inv).app ⊤
    ((M ◁ ((AlgebraicGeometry.Scheme.relativeSpec.structureIso
        (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual L)).total).inv ≫
      (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual L)).totalProj q ≫
      AlgebraicGeometry.Scheme.totalSpace.symPartToTensorPower L q)).app ⊤
      (AlgebraicGeometry.Scheme.Modules.tensorSections _ _ ⊤ m
        (1 : (AlgebraicGeometry.Scheme.totalSpace L).left.ringCatSheaf.obj.obj
        (Opposite.op ((AlgebraicGeometry.Scheme.totalSpace L).hom ⁻¹ᵁ ⊤))))) = 0
  rw [← CategoryTheory.MonoidalCategory.id_tensorHom]
  change ((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj M
      (AlgebraicGeometry.Scheme.Modules.moduleTensorPower (AlgebraicGeometry.Scheme.Modules.dual L) q)).inv).app ⊤
    ((CategoryTheory.MonoidalCategoryStruct.tensorHom (C := X.Modules) (𝟙 M)
      ((AlgebraicGeometry.Scheme.relativeSpec.structureIso
        (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual L)).total).inv ≫
      (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual L)).totalProj q ≫
      AlgebraicGeometry.Scheme.totalSpace.symPartToTensorPower L q)).val.app (Opposite.op ⊤)
      (AlgebraicGeometry.Scheme.Modules.tensorSections _ _ ⊤ m
        (1 : (AlgebraicGeometry.Scheme.totalSpace L).left.ringCatSheaf.obj.obj
        (Opposite.op ((AlgebraicGeometry.Scheme.totalSpace L).hom ⁻¹ᵁ ⊤))))) = 0
  rw [AlgebraicGeometry.Scheme.Modules.tensorHom_tensorSections]
  change ((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj M
      (AlgebraicGeometry.Scheme.Modules.moduleTensorPower (AlgebraicGeometry.Scheme.Modules.dual L) q)).inv).app ⊤
    (AlgebraicGeometry.Scheme.Modules.tensorSections _ _ ⊤ ((𝟙 M : M ⟶ M).app ⊤ m)
      ((((AlgebraicGeometry.Scheme.relativeSpec.structureIso
        (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual L)).total).inv ≫
      (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual L)).totalProj q ≫
      AlgebraicGeometry.Scheme.totalSpace.symPartToTensorPower L q).app ⊤)
        (1 : (AlgebraicGeometry.Scheme.totalSpace L).left.ringCatSheaf.obj.obj
        (Opposite.op ((AlgebraicGeometry.Scheme.totalSpace L).hom ⁻¹ᵁ ⊤))))) = 0
  rw [hg, AlgebraicGeometry.Scheme.Modules.tensorSections_zero_right]
  exact map_zero _

end AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
/-- **The unit section has ξ-degree `≤ 0`.**

Proof. Write `p : Tot(L) → C`, `pb := Modules.pullback p`,
`u := (pullbackUnitIso p).inv.app ⊤ 1 ∈ Γ(Tot, p^*O_C)`. By `xiDegree_lt_iff` it suffices that
`xiCoefficient L (M.zpow 0) u q = 0` for all `q > 0` (here `(M.zpow 0).toModules = O_C` definitionally).
1. `u = η(1)` (the adjunction unit on the section `1 ∈ Γ(C, O_C)`): `pullbackUnitIso p = asIso (pullbackObjUnitToUnit p)`
   and `ModuleSections.pullback_unit_one` says `(pullbackObjUnitToUnit p).app ⊤ (η 1) = 1`; apply the
   inverse (`pullbackUnitIso_inv_app_top_one`).
2. `(ρ_ (pb O_C))⁻¹ (η 1) = tensorSections (η 1) 1` (`rightUnitor_app_tensorSections`, `rightUnitor_inv_app_top`).
3. `projectionFormulaIso⁻¹` of that element (read in `Γ(C, p_*(pb O_C ⊗ O_Tot))`) is `tensorSections 1 1`
   in `Γ(C, O_C ⊗ p_*O_Tot)`: `projectionFormulaHom p O_C O_Tot (tensorSections m s) = tensorSections (η m) s`
   (`projectionFormulaHom_app_top_tensorSections`, from `homEquiv_unit`, `pullbackTensorObjHom_app_unit_tensorSections`,
   `tensorHom_tensorSections` and the adjunction triangle `ε ∘ η = id`); together: `pullbackSectionToPushforward_unit_app`.
4. `coefficientHom_q (tensorSections 1 s) = tensorIsoTensorObj.inv (tensorSections 1 (Θ'_q (π_q (structureIso⁻¹ s))))`
   (`whiskerLeft = tensorHom 𝟙 _`, `tensorHom_tensorSections`).
5. `structureIso⁻¹ 1 = totalIncl 0 (S.one 1)`: `structureHom` is the ring-presheaf map `structureRingMap` on sections
   (`structureHom_app_apply`), so it preserves `1`, and `1 ∈ Γ(C, ⊕ Sym^m)` is `ι_0(1_{Sym^0})` by definition of `total.one`
   (`structureIso_inv_app_top_one`, `total_sectionsRing_one`).
6. `totalIncl 0 ≫ totalProj q = 0` for `q ≠ 0` (`Sigma.ι_desc` + `dif_neg`: `totalIncl_totalProj_of_ne`), so the
   coefficient is `tensorSections 1 0 = 0` (`tensorSections_zero_right`) and the remaining module maps send
   `0` to `0` (`map_zero`); together: `coefficientHom_app_top_tensorSections_one`. -/
theorem xiDegree_pullbackUnitIso_inv_one_le_zero {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L M : LineBundle C.toVariety) :
    xiDegree L (M.zpow ((0 : ℕ) : ℤ))
      ((AlgebraicGeometry.Scheme.Modules.pullbackUnitIso
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).inv.app ⊤
        (1 : (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.ringCatSheaf.obj.obj
          (Opposite.op ⊤))) ≤ ((0 : ℕ) : WithBot ℕ) := by
  rw [xiDegree_lt_iff]
  intro q hq
  have hq0 : q ≠ 0 := Nat.pos_iff_ne_zero.mp hq
  unfold xiCoefficient
  rw [AlgebraicGeometry.Scheme.Modules.pullbackUnitIso_inv_app_top_one]
  unfold AlgebraicGeometry.Scheme.totalSpace.coefficient
  have h1 := AlgebraicGeometry.Scheme.Modules.pullbackSectionToPushforward_unit_app
    (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom (M.zpow ((0 : ℕ) : ℤ)).toModules
    (1 : C.toScheme.ringCatSheaf.obj.obj (Opposite.op (⊤ : C.toScheme.Opens)))
  erw [h1]
  have h2 := AlgebraicGeometry.Scheme.totalSpace.coefficientHom_app_top_tensorSections_one L.toModules
    (M.zpow ((0 : ℕ) : ℤ)).toModules hq0
    (1 : C.toScheme.ringCatSheaf.obj.obj (Opposite.op (⊤ : C.toScheme.Opens)))
  erw [h2]
  exact map_zero _

end
