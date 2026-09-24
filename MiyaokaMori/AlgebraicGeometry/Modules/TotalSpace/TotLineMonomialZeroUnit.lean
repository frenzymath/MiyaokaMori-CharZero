import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesProjectionFormulaHom
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.SectionPullbackAlong
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.JetNeighborhoodToTotalSpaceLemmas
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotLineCoefficientMap

/-! # The degree-0 monomial map is the unit of the pullback adjunction

**The degree-0 monomial map is the unit of `p^* ⊣ p_*`**: for a line bundle `L` on `X`, `p : Tot(L) → X`,
`S := Sym(L^∨)`, the composite `Θ_0 ≫ ι_0 ≫ σ : T_0 = 𝟙_ ⟶ p_*O_Tot` (`tensorPowerToSymPart`, `totalIncl`,
`relativeSpec.structureHom`) is the adjoint transpose `T(η)` of the oplax unit `η : p^*𝟙_ ⟶ 𝟙_`, and
`(M ◁ (Θ_0 ≫ ι_0 ≫ σ)) ≫ θ_{M,O_Tot} ≫ p_*(ρ_{p^*M}) = (ρ_ M).hom ≫ unit_M`
(`totalSpace.whiskerLeft_monomialUnit_zero_projectionFormulaHom_map_rightUnitor`). Consequently the 0-th
monomial `c·ξ^0` is the pullback `p^*c` (assembled in `TotSectionsPolynomial`,
`xiMonomial_zero_eq_sectionPullbackAlong`). (In the paper: the constant term `π_L^*(ρ^*f_ℓ)` of the ξ-expansion.)

These are the helper lemmas of `ConeCoordinateFiniteXiExpansionConstantMonomial` (which proves the equivalent
statement `sectionPullbackAlong_totalSpace_eq_xiMonomial_zero` but imports `TotSectionsPolynomial`, so
`TotSectionsPolynomial` cannot use it), placed here upstream of `TotSectionsPolynomial` under new names:

| here | in `ConeCoordinateFiniteXiExpansionConstantMonomial` |
|---|---|
| `Adjunction.whiskerLeft_homEquiv_η_projFormulaHom_map_rightUnitor` | `Adjunction.whiskerLeft_homEquiv_η_projFormulaHom_unit` |
| `totalSpace.tensorPowerToSymPart_zero_eq_one` | `totalSpace.tensorPowerToSymPart_zero` |
| `relativeSpec.one_comp_structureHom_eq_unitToPushforwardObjUnit` | `relativeSpec.one_comp_structureHom` |
| `totalSpace.monomialUnit_zero_eq_homEquiv_η` | `totalSpace.tensorPowerToSymPart_totalIncl_structureHom_zero` |
| `Modules.monomialZero_iso_cancel_bridge` | `Modules.monomial_zero_bridge` |
| `Modules.whiskerLeft_homEquiv_η_projectionFormulaHom_map_rightUnitor` | `Modules.whiskerLeft_homEquiv_η_projectionFormulaHom_unit` |
| `totalSpace.whiskerLeft_monomialUnit_zero_projectionFormulaHom_map_rightUnitor` | `totalSpace.whiskerLeft_monomialUnit_projectionFormulaHom` |

Proof route (all at the level of morphisms, no section-level unfolding):
1. Abstract lemma for any adjunction `F ⊣ G` with `F` oplax monoidal: `(M ◁ T(η)) ≫ θ_{M,𝟙} ≫ G(ρ_{FM}) = ρ_M ≫ unit_M`
   (transpose both sides; `δ_natural_right`, `homEquiv_counit`, oplax right unitality).
2. `Θ_0 = powIso_0⁻¹ ≫ S.one` (quasi-coherent branch of `symGradedAlgebra`, `generalize … subst`).
3. `S.total.one ≫ σ = unitToPushforwardObjUnit p` (the structure map is an algebra map; compare on the section `1`
   via `unitHomEquiv`).
4. Hence `Θ_0 ≫ ι_0 ≫ σ = T(η)` (`pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit`, `pullback_η`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v₁ v₂ u₁ u₂

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry CategoryTheory.MonoidalCategory

noncomputable section

namespace CategoryTheory.Adjunction

open CategoryTheory.Category CategoryTheory.MonoidalCategory CategoryTheory.Functor.OplaxMonoidal

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
variable [MonoidalCategory C] [MonoidalCategory D]
variable {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [instF : F.OplaxMonoidal]

/-- The projection-formula map on `M ⊗ 𝟙`: with `e := T(η) : 𝟙 ⟶ G 𝟙` the adjoint transpose of the
oplax unit `η : F 𝟙 ⟶ 𝟙`, one has `(M ◁ e) ≫ θ_{M,𝟙} ≫ G(ρ_{F M}) = ρ_M ≫ unit_M`.
Proof: transpose both sides (`homEquiv.symm` is injective); the left side becomes
`F(M ◁ e) ≫ δ_{M,G𝟙} ≫ (F M ◁ counit_𝟙) ≫ ρ = δ_{M,𝟙} ≫ (F M ◁ (F e ≫ counit_𝟙)) ≫ ρ`
(`δ_natural_right`), and `F e ≫ counit_𝟙 = η` (`homEquiv_counit`), so it is `F(ρ_M)` by the oplax
right unitality `right_unitality_hom`; the right side transposes to `F(ρ_M) ≫ 𝟙`. -/
theorem whiskerLeft_homEquiv_η_projFormulaHom_map_rightUnitor (M : C) :
    (M ◁ adj.homEquiv _ _ (η F)) ≫ adj.projFormulaHom M (𝟙_ D) ≫ G.map (ρ_ (F.obj M)).hom =
      (ρ_ M).hom ≫ adj.unit.app M := by
  apply (adj.homEquiv _ _).symm.injective
  rw [homEquiv_naturality_left_symm, homEquiv_naturality_right_symm, homEquiv_symm_projFormulaHom,
    homEquiv_naturality_left_symm, ← homEquiv_id, Equiv.symm_apply_apply, comp_id, assoc,
    ← δ_natural_right_assoc, ← whiskerLeft_comp_assoc]
  have h : F.map (adj.homEquiv _ _ (η F)) ≫ adj.counit.app (𝟙_ D) = η F :=
    (adj.homEquiv_counit (g := adj.homEquiv _ _ (η F))).symm.trans (Equiv.symm_apply_apply _ _)
  rw [h]
  exact right_unitality_hom F M

end CategoryTheory.Adjunction

namespace AlgebraicGeometry.Scheme

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- `Θ_0 = powIso_0⁻¹ ≫ S.one`: the second factor of `tensorPowerToSymPart L 0` is `symPowπ (dual L) 0` in the
quasi-coherent branch, i.e. the unit of `symGradedAlgebraOfQC`; `symGradedAlgebra_eq_ofQC_of_isLineBundle` moves
`symGradedAlgebra (dual L)` to that branch, after which both sides are literally equal. -/
theorem totalSpace.tensorPowerToSymPart_zero_eq_one (L : X.Modules) [L.IsLineBundle] :
    totalSpace.tensorPowerToSymPart L 0 = (Modules.symGradedAlgebra (Modules.dual L)).one := by
  have hS := Modules.symGradedAlgebra_eq_ofQC_of_isLineBundle (Modules.dual L)
  unfold totalSpace.tensorPowerToSymPart
  change 𝟙 (Modules.monoidalPow (Modules.dual L) 0) ≫ _ = _
  rw [Category.id_comp, GradedQCAlgebra.one_eq_of_eq hS]
  generalize_proofs _ _ hq pfT pfP
  change (pfT hq).mpr (Modules.symPowπ (Modules.dual L) 0) =
    (Modules.symGradedAlgebraOfQC (Modules.dual L) hq).one ≫ eqToHom pfP
  generalize Modules.symGradedAlgebra (Modules.dual L) = S at hS pfT pfP ⊢
  subst hS
  exact (Category.comp_id _).symm

/-- The structure map of a relative Spec preserves the unit: `A.one ≫ structureHom A = unitToPushforwardObjUnit π`
(`π : Spec_X A → X`). Both sides are morphisms out of `𝟙_ = O_X`, so by `unitHomEquiv` it suffices to compare the
values on the section `1`: the left one is `1` by the unit clause of the universal property
(`relativeSpecHomEquiv … (𝟙 _)`), the right one is the ring map `π^♯` on `1`. -/
theorem relativeSpec.one_comp_structureHom_eq_unitToPushforwardObjUnit (A : X.QCAlgebra) :
    A.one ≫ relativeSpec.structureHom A =
      SheafOfModules.unitToPushforwardObjUnit (relativeSpec A).hom.toRingCatSheafHom := by
  have h := (relativeSpecHomEquiv A (relativeSpec A) (CategoryTheory.CategoryStruct.id _)).2.2
  apply ((Modules.pushforward (relativeSpec A).hom).obj
    (SheafOfModules.unit (relativeSpec A).left.ringCatSheaf)).unitHomEquiv.injective
  apply PresheafOfModules.sections_ext
  intro U
  refine (SheafOfModules.unitHomEquiv_apply_coe _ _ _).trans
    (Eq.trans ?_ (SheafOfModules.unitHomEquiv_apply_coe _ _ _).symm)
  refine Eq.trans ?_ (SheafOfModules.unitToPushforwardObjUnit_val_app_apply
    (relativeSpec A).hom.toRingCatSheafHom (X := U) 1).symm
  exact (h U.unop).trans (map_one ((relativeSpec A).hom.toRingCatSheafHom.hom.app U).hom).symm

/-- The `𝟙_ ⟶ π_*O_Tot` factor `Θ_0 ≫ ι_0 ≫ σ` of the degree-0 monomial map is the adjoint transpose `T(η)` of the
oplax unit `η : π^*O_X ⟶ O_Tot`. -/
theorem totalSpace.monomialUnit_zero_eq_homEquiv_η (L : X.Modules) [L.IsLineBundle] :
    totalSpace.tensorPowerToSymPart L 0 ≫
        (Modules.symGradedAlgebra (Modules.dual L)).totalIncl 0 ≫
        relativeSpec.structureHom (Modules.symGradedAlgebra (Modules.dual L)).total =
      (Modules.pullbackPushforwardAdjunction (totalSpace L).hom).homEquiv _ _
        (CategoryTheory.Functor.OplaxMonoidal.η (Modules.pullback (totalSpace L).hom)
          (self := Modules.pullbackOplaxMonoidal (totalSpace L).hom)) := by
  have e2 : totalSpace.tensorPowerToSymPart L 0 ≫
        (Modules.symGradedAlgebra (Modules.dual L)).totalIncl 0 ≫
        relativeSpec.structureHom (Modules.symGradedAlgebra (Modules.dual L)).total =
      (Modules.symGradedAlgebra (Modules.dual L)).one ≫
        (Modules.symGradedAlgebra (Modules.dual L)).totalIncl 0 ≫
        relativeSpec.structureHom (Modules.symGradedAlgebra (Modules.dual L)).total := by
    rw [totalSpace.tensorPowerToSymPart_zero_eq_one]; exact rfl
  have e3 : (Modules.symGradedAlgebra (Modules.dual L)).one ≫
        (Modules.symGradedAlgebra (Modules.dual L)).totalIncl 0 ≫
        relativeSpec.structureHom (Modules.symGradedAlgebra (Modules.dual L)).total =
      (Modules.symGradedAlgebra (Modules.dual L)).total.one ≫
        relativeSpec.structureHom (Modules.symGradedAlgebra (Modules.dual L)).total :=
    (Category.assoc _ _ _).symm
  have : (SheafOfModules.pushforward (totalSpace L).hom.toRingCatSheafHom).IsRightAdjoint :=
    (Modules.pullbackPushforwardAdjunction (totalSpace L).hom).isRightAdjoint
  refine e2.trans (e3.trans ((relativeSpec.one_comp_structureHom_eq_unitToPushforwardObjUnit _).trans ?_))
  refine (SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
    (totalSpace L).hom.toRingCatSheafHom).symm.trans ?_
  exact (congrArg ((Modules.pullbackPushforwardAdjunction (totalSpace L).hom).homEquiv _ _)
    (Modules.pullback_η (totalSpace L).hom)).symm

/-- **Variable-level assembly lemma** (concrete objects are compared only through one `exact`; the reasoning is done
with variables). `ρ' : M ⊗ R ≅ M`, `τ' : P ≅ Q ⊗ R`, `ζ : Q ≅ M`, `τ0 = τ0' : T ≅ M ⊗ R`, `ν = 𝟙`: the first three
factors on the left are, by definition, `coefficientZeroIso⁻¹`, `(coefficientModuleIso 0)⁻¹`, `monomialHom 0`;
the two `τ'` and the two `τ0` cancel, `ζ` cancels, leaving `ρ'⁻¹ ≫ (M ◁ u) ≫ θ ≫ g`, then `h4` and
`ρ'⁻¹ ≫ ρ' = 𝟙`. -/
theorem Modules.monomialZero_iso_cancel_bridge {P Q R M T W W' V : X.Modules} (ρ' : M ⊗ R ≅ M) (τ' : P ≅ Q ⊗ R)
    (ζ : Q ≅ M) (τ0 τ0' : T ≅ M ⊗ R) (ν : R ≅ R) (hν : ν = Iso.refl R) (hτ : τ0 = τ0')
    (u : R ⟶ W) (θ : M ⊗ W ⟶ W') (g : W' ⟶ V) (η : M ⟶ V)
    (h4 : (M ◁ u) ≫ θ ≫ g = ρ'.hom ≫ η) :
    ((ρ'.inv ≫ (ζ.inv ⊗ₘ (Iso.refl R).inv)) ≫ τ'.inv) ≫
        ((τ'.hom ≫ (ζ.hom ⊗ₘ ν.hom)) ≫ τ0.inv) ≫ (τ0'.hom ≫ (M ◁ u)) ≫ θ ≫ g = η := by
  subst hν hτ
  simp only [Category.assoc, Iso.refl_inv, Iso.refl_hom, Iso.inv_hom_id_assoc,
    MonoidalCategory.tensorHom_comp_tensorHom_assoc, Iso.inv_hom_id, Category.comp_id,
    MonoidalCategory.id_tensorHom_id, Category.id_comp]
  rw [h4, Iso.inv_hom_id_assoc]

/-- The abstract lemma `whiskerLeft_homEquiv_η_projFormulaHom_map_rightUnitor` for `f^* ⊣ f_*`, with `𝟙_` written
as `SheafOfModules.unit` and `θ` as `projectionFormulaHom` (definitional unfolding). -/
theorem Modules.whiskerLeft_homEquiv_η_projectionFormulaHom_map_rightUnitor
    {T Y : AlgebraicGeometry.Scheme.{u}} (f : T ⟶ Y) (M : Y.Modules) :
    (M ◁ (Modules.pullbackPushforwardAdjunction f).homEquiv _ _
        (CategoryTheory.Functor.OplaxMonoidal.η (Modules.pullback f)
          (self := Modules.pullbackOplaxMonoidal f))) ≫
        Modules.projectionFormulaHom f M (SheafOfModules.unit T.ringCatSheaf) ≫
        (Modules.pushforward f).map (ρ_ ((Modules.pullback f).obj M)).hom =
      (ρ_ M).hom ≫ (Modules.pullbackPushforwardAdjunction f).unit.app M :=
  (Modules.pullbackPushforwardAdjunction f).whiskerLeft_homEquiv_η_projFormulaHom_map_rightUnitor
    (instF := Modules.pullbackOplaxMonoidal f) M

/-- The previous lemma on `Tot(L) → X`, with `T(η)` replaced by the monomial-map factor `Θ_0 ≫ ι_0 ≫ σ`. -/
theorem totalSpace.whiskerLeft_monomialUnit_zero_projectionFormulaHom_map_rightUnitor
    (L M : X.Modules) [L.IsLineBundle] :
    (M ◁ (totalSpace.tensorPowerToSymPart L 0 ≫
        (Modules.symGradedAlgebra (Modules.dual L)).totalIncl 0 ≫
        relativeSpec.structureHom (Modules.symGradedAlgebra (Modules.dual L)).total)) ≫
        Modules.projectionFormulaHom (totalSpace L).hom M
          (SheafOfModules.unit (totalSpace L).left.ringCatSheaf) ≫
        (Modules.pushforward (totalSpace L).hom).map
          (ρ_ ((Modules.pullback (totalSpace L).hom).obj M)).hom =
      (ρ_ M).hom ≫ (Modules.pullbackPushforwardAdjunction (totalSpace L).hom).unit.app M := by
  rw [totalSpace.monomialUnit_zero_eq_homEquiv_η]
  exact Modules.whiskerLeft_homEquiv_η_projectionFormulaHom_map_rightUnitor _ M

/-- `sectionPullbackAlong g s` is the global-sections map of the adjunction unit (definitional). -/
theorem sectionPullbackAlong_eq_unit_val_app {T Y : AlgebraicGeometry.Scheme.{u}} (g : T ⟶ Y) {M : Y.Modules}
    (s : (M.val.obj (Opposite.op ⊤) : Type u)) :
    sectionPullbackAlong g s =
      (((Modules.pullbackPushforwardAdjunction g).unit.app M).val.app (Opposite.op ⊤)).hom s := rfl

/-- The pushforward of a morphism, on global sections, is the morphism on global sections (definitional:
`g⁻¹⊤ = ⊤`). -/
theorem Modules.pushforward_map_val_app_top {T Y : AlgebraicGeometry.Scheme.{u}} (g : T ⟶ Y) {N N' : T.Modules}
    (φ : N ⟶ N') (x : (((Modules.pushforward g).obj N).val.obj (Opposite.op ⊤) : Type u)) :
    ((((Modules.pushforward g).map φ).val.app (Opposite.op ⊤)).hom x : (N'.val.obj (Opposite.op ⊤) : Type u)) =
      (φ.val.app (Opposite.op ⊤)).hom (show (N.val.obj (Opposite.op ⊤) : Type u) from x) := rfl

end AlgebraicGeometry.Scheme

end
