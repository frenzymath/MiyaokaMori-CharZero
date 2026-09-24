import MiyaokaMori.Prelude
import MiyaokaMori.CategoryTheory.InvertibleEvalHomSectionCalculus
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModulesDualEv
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorSectionsCoherence
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.ModulesUnitHomTopSection
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveBundle.ProjectiveBundleUniversalPropertySymPowDesc
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotSectionsPolynomial
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.LineBundleDualEvalIso

/-! # The Hom–section calculus for pullback line bundles on the total space

**The Hom–section calculus for pullback line bundles on `Tot(L)`** (`exists_xiSections_of_pullbackIso`).
Write `p : Tot(L) → C`, `F := p^*`, `A^∨ := dual A`.

Route:
* For a line bundle `A` the evaluation `dualEv A : A^∨ ⊗ A ⟶ O_C` is an **isomorphism**
  (`isIso_internalHomEval_dual`, Stacks 01CT) and the braiding `β_{A,A}` is the **identity**
  (`braiding_hom_eq_id_of_isLineBundle`, Stacks 01CR). These two facts are the only input from geometry.
* With `ev := asIso (dualEv A)` the pair `c := ε ≫ F(ev⁻¹) ≫ δ`, `e := μ ≫ F(ev) ≫ η` on `Tot(L)` satisfies
  `c ≫ e = 𝟙`, and `β_{F A, F A} = 𝟙`; the abstract module `InvertibleEvalHomSectionCalculus`
  (`EvalCalculus.hom_eq_secHom_transport`, `EvalCalculus.pair_secHom_transport`) then gives, for
  `φ : F A ⟶ F B`, the section `secHom φ := c ≫ F A^∨ ◁ φ ≫ μ` of `F(A^∨ ⊗ B)` with `φ = "pair with secHom φ"`,
  and, for `φ ≫ ψ = 𝟙`, `secHom φ · secHom ψ ↦ 1`.
* The bridge between global sections and morphisms out of the unit is `homOfTopSection` / `unitHomEquivTop`
  (`Γ(T, M) ≃ (O_T ⟶ M)`): `sectionTensor a b` corresponds to `(λ_ 𝟙).inv ≫ (a ⊗ₘ b) ≫ tensorIsoTensorObj⁻¹`
  (`homOfTopSection_sectionTensor`), and `xiSectionMul` is `sectionTensor` followed by `pullbackTensorIso⁻¹`
  (`homOfTopSection_xiSectionMul`). `A.zpow (-1) ≅ A^∨` is `LineBundle.zpowNegOneIso`.

References: Stacks 01CM/01CN (Hom and tensor commute with pullback for locally free sheaves; `Hom(A, B) ≅ A^∨ ⊗ B`),
01CT, 01CR; Hartshorne II Ex. 5.1.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
open scoped CategoryTheory.MonoidalCategory

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules.HomSection

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- `homOfTopSection` is natural: `homOfTopSection (φ x) = homOfTopSection x ≫ φ`
(copy of `DualZigzag.homOfTopSection_app_top`, to keep the import closure small). -/
theorem homOfTopSection_comp {M N : X.Modules} (φ : M ⟶ N) (x : Γ(M, ⊤)) :
    AlgebraicGeometry.Scheme.Modules.homOfTopSection N (φ.app ⊤ x) =
      AlgebraicGeometry.Scheme.Modules.homOfTopSection M x ≫ φ := by
  apply (AlgebraicGeometry.Scheme.Modules.unitHomEquivTop N).injective
  have h1 : AlgebraicGeometry.Scheme.Modules.unitHomEquivTop N
      (AlgebraicGeometry.Scheme.Modules.homOfTopSection N (φ.app ⊤ x)) = φ.app ⊤ x :=
    (AlgebraicGeometry.Scheme.Modules.unitHomEquivTop N).apply_symm_apply _
  have h2 : AlgebraicGeometry.Scheme.Modules.unitHomEquivTop M
      (AlgebraicGeometry.Scheme.Modules.homOfTopSection M x) = x :=
    (AlgebraicGeometry.Scheme.Modules.unitHomEquivTop M).apply_symm_apply x
  have h3 : AlgebraicGeometry.Scheme.Modules.unitHomEquivTop N
      (AlgebraicGeometry.Scheme.Modules.homOfTopSection M x ≫ φ) =
      φ.app ⊤ (AlgebraicGeometry.Scheme.Modules.unitHomEquivTop M
        (AlgebraicGeometry.Scheme.Modules.homOfTopSection M x)) := rfl
  rw [h1, h3, h2]

/-- `φ.app ⊤ x` as the section of the morphism `homOfTopSection x ≫ φ`. -/
theorem app_top_eq {M N : X.Modules} (φ : M ⟶ N) (x : Γ(M, ⊤)) :
    φ.app ⊤ x = AlgebraicGeometry.Scheme.Modules.unitHomEquivTop N
      (AlgebraicGeometry.Scheme.Modules.homOfTopSection M x ≫ φ) := by
  rw [← homOfTopSection_comp]
  exact ((AlgebraicGeometry.Scheme.Modules.unitHomEquivTop N).apply_symm_apply _).symm

theorem iso_inv_app_hom_app {A B : X.Modules} (e : A ≅ B) (U : X.Opens) (x : Γ(A, U)) :
    e.inv.app U (e.hom.app U x) = x :=
  ConcreteCategory.congr_hom (congrArg (fun φ => AlgebraicGeometry.Scheme.Modules.Hom.app φ U)
    e.hom_inv_id) x

/-- `(λ_ 𝟙).inv` sends `1` to `1 ⊗ 1` (`leftUnitor_app_tensorSections` inverted). -/
theorem leftUnitor_inv_app_top_one :
    (λ_ (𝟙_ X.Modules)).inv.app ⊤ (1 : Γ(X, ⊤)) =
      AlgebraicGeometry.Scheme.Modules.tensorSections (𝟙_ X.Modules) (𝟙_ X.Modules) ⊤
        (1 : Γ(X, ⊤)) (1 : Γ(X, ⊤)) := by
  have h := AlgebraicGeometry.Scheme.Modules.leftUnitor_app_tensorSections (𝟙_ X.Modules) ⊤
    (1 : Γ(X, ⊤)) (1 : Γ(X, ⊤))
  have h1 : (1 : Γ(X, ⊤)) • (1 : Γ(X, ⊤)) = (1 : Γ(X, ⊤)) := one_smul _ _
  exact (congrArg ((λ_ (𝟙_ X.Modules)).inv.app ⊤) (h.trans h1)).symm.trans (iso_inv_app_hom_app _ _ _)

/-- `tensorIsoTensorObj⁻¹` sends the monoidal pairing back to `sectionTensor`. -/
theorem tensorIsoTensorObj_inv_app_top_tensorSections {M N : X.Modules}
    (s : (M.val.obj (Opposite.op ⊤) : Type u)) (t : (N.val.obj (Opposite.op ⊤) : Type u)) :
    (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj M N).inv.app ⊤
        (AlgebraicGeometry.Scheme.Modules.tensorSections M N ⊤ s t) = sectionTensor s t := by
  have h : (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj M N).hom.app ⊤ (sectionTensor s t) =
      AlgebraicGeometry.Scheme.Modules.tensorSections M N ⊤ s t := rfl
  rw [← h]
  exact iso_inv_app_hom_app _ _ _

/-- **Sections ↔ morphisms, tensor products**:
`homOfTopSection (a ⊗ b) = (λ_ 𝟙).inv ≫ (homOfTopSection a ⊗ₘ homOfTopSection b) ≫ tensorIsoTensorObj⁻¹`. -/
theorem homOfTopSection_sectionTensor {M N : X.Modules} (a : (M.val.obj (Opposite.op ⊤) : Type u))
    (b : (N.val.obj (Opposite.op ⊤) : Type u)) :
    AlgebraicGeometry.Scheme.Modules.homOfTopSection (AlgebraicGeometry.Scheme.Modules.tensor M N)
        (sectionTensor a b) =
      (λ_ (𝟙_ X.Modules)).inv ≫
        CategoryTheory.MonoidalCategoryStruct.tensorHom (C := X.Modules)
          (AlgebraicGeometry.Scheme.Modules.homOfTopSection M a)
          (AlgebraicGeometry.Scheme.Modules.homOfTopSection N b) ≫
        (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj M N).inv := by
  apply (AlgebraicGeometry.Scheme.Modules.unitHomEquivTop _).injective
  have h0 : AlgebraicGeometry.Scheme.Modules.unitHomEquivTop _
      (AlgebraicGeometry.Scheme.Modules.homOfTopSection (AlgebraicGeometry.Scheme.Modules.tensor M N)
        (sectionTensor a b)) = sectionTensor a b :=
    (AlgebraicGeometry.Scheme.Modules.unitHomEquivTop _).apply_symm_apply _
  rw [h0]
  have ha : AlgebraicGeometry.Scheme.Modules.Hom.app
      (AlgebraicGeometry.Scheme.Modules.homOfTopSection M a) ⊤ (1 : Γ(X, ⊤)) = a :=
    (AlgebraicGeometry.Scheme.Modules.unitHomEquivTop M).apply_symm_apply a
  have hb : AlgebraicGeometry.Scheme.Modules.Hom.app
      (AlgebraicGeometry.Scheme.Modules.homOfTopSection N b) ⊤ (1 : Γ(X, ⊤)) = b :=
    (AlgebraicGeometry.Scheme.Modules.unitHomEquivTop N).apply_symm_apply b
  change sectionTensor a b =
    (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj M N).inv.app ⊤
      ((CategoryTheory.MonoidalCategoryStruct.tensorHom (C := X.Modules)
        (AlgebraicGeometry.Scheme.Modules.homOfTopSection M a)
        (AlgebraicGeometry.Scheme.Modules.homOfTopSection N b)).app ⊤
        ((λ_ (𝟙_ X.Modules)).inv.app ⊤ (1 : Γ(X, ⊤))))
  rw [leftUnitor_inv_app_top_one]
  have ht : (CategoryTheory.MonoidalCategoryStruct.tensorHom (C := X.Modules)
        (AlgebraicGeometry.Scheme.Modules.homOfTopSection M a)
        (AlgebraicGeometry.Scheme.Modules.homOfTopSection N b)).app ⊤
        (AlgebraicGeometry.Scheme.Modules.tensorSections (𝟙_ X.Modules) (𝟙_ X.Modules) ⊤
          (1 : Γ(X, ⊤)) (1 : Γ(X, ⊤))) =
      AlgebraicGeometry.Scheme.Modules.tensorSections M N ⊤ a b := by
    refine (AlgebraicGeometry.Scheme.Modules.tensorHom_tensorSections
      (AlgebraicGeometry.Scheme.Modules.homOfTopSection M a)
      (AlgebraicGeometry.Scheme.Modules.homOfTopSection N b) ⊤ (1 : Γ(X, ⊤)) (1 : Γ(X, ⊤))).trans ?_
    exact congrArg₂ (AlgebraicGeometry.Scheme.Modules.tensorSections M N ⊤) ha hb
  rw [ht]
  exact (tensorIsoTensorObj_inv_app_top_tensorSections a b).symm

/-! ### Wrappers typed with the monoidal unit `𝟙_ X.Modules`

`homOfTopSection M s : SheafOfModules.unit X.ringCatSheaf ⟶ M` and the monoidal unit `𝟙_ X.Modules` are
definitionally but not syntactically equal; statements mixing them are not type-correct at reducible
transparency, which makes `rw` fail. The wrappers below carry the `𝟙_` spelling. -/

/-- `homOfTopSection`, typed with the monoidal unit. -/
def homOfTopSectionU (M : X.Modules) (s : (M.val.obj (Opposite.op ⊤) : Type u)) : 𝟙_ X.Modules ⟶ M :=
  AlgebraicGeometry.Scheme.Modules.homOfTopSection M s

/-- `unitHomEquivTop`, typed with the monoidal unit: the section `f(1)` of `f : 𝟙_ ⟶ M`. -/
def secOfHom (M : X.Modules) (f : 𝟙_ X.Modules ⟶ M) : (M.val.obj (Opposite.op ⊤) : Type u) :=
  AlgebraicGeometry.Scheme.Modules.unitHomEquivTop M f

theorem homOfTopSectionU_secOfHom (M : X.Modules) (f : 𝟙_ X.Modules ⟶ M) :
    homOfTopSectionU M (secOfHom M f) = f :=
  (AlgebraicGeometry.Scheme.Modules.unitHomEquivTop M).symm_apply_apply f

theorem app_top_eqU {M N : X.Modules} (φ : M ⟶ N) (x : (M.val.obj (Opposite.op ⊤) : Type u)) :
    φ.app ⊤ x = secOfHom N (homOfTopSectionU M x ≫ φ) :=
  app_top_eq φ x

theorem homOfTopSectionU_sectionTensor {M N : X.Modules} (a : (M.val.obj (Opposite.op ⊤) : Type u))
    (b : (N.val.obj (Opposite.op ⊤) : Type u)) :
    homOfTopSectionU (AlgebraicGeometry.Scheme.Modules.tensor M N) (sectionTensor a b) =
      (λ_ (𝟙_ X.Modules)).inv ≫
        CategoryTheory.MonoidalCategoryStruct.tensorHom (C := X.Modules) (homOfTopSectionU M a)
          (homOfTopSectionU N b) ≫
        (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj M N).inv :=
  homOfTopSection_sectionTensor a b

end AlgebraicGeometry.Scheme.Modules.HomSection

open AlgebraicGeometry.Scheme.Modules.HomSection

/-- `xiSectionMul P P'` is `pullbackTensorIso⁻¹ (P ⊗ P')`: the `eqToHom` in the definition of `xiSectionMul`
is the identity, `LineBundle.tensor_toModules` being `rfl` (proof irrelevance turns it into `eqToHom rfl`). -/
theorem xiSectionMul_eq_app {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L M M' : LineBundle C.toVariety)
    (P : (((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        M.toModules).val.obj (Opposite.op ⊤) : Type u))
    (P' : (((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        M'.toModules).val.obj (Opposite.op ⊤) : Type u)) :
    xiSectionMul L M M' P P' =
      (AlgebraicGeometry.Scheme.Modules.pullbackTensorIso
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom M.toModules M'.toModules).inv.app ⊤
        (sectionTensor P P') := by
  change ((AlgebraicGeometry.Scheme.Modules.pullbackTensorIso
      (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom M.toModules M'.toModules).inv ≫
    CategoryTheory.eqToHom (rfl : (AlgebraicGeometry.Scheme.Modules.pullback
      (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        (AlgebraicGeometry.Scheme.Modules.tensor M.toModules M'.toModules) = _)).app ⊤
    (sectionTensor P P') = _
  rw [CategoryTheory.eqToHom_refl, Category.comp_id]

/-- `homOfTopSection` of `xiSectionMul P P'`: `homOfTopSection (P ⊗ P') ≫ pullbackTensorIso⁻¹`
(the `Eq` is typed by its left-hand side). -/
theorem homOfTopSection_xiSectionMul {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L M M' : LineBundle C.toVariety)
    (P : (((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        M.toModules).val.obj (Opposite.op ⊤) : Type u))
    (P' : (((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        M'.toModules).val.obj (Opposite.op ⊤) : Type u)) :
    AlgebraicGeometry.Scheme.Modules.homOfTopSection _ (xiSectionMul L M M' P P') =
      AlgebraicGeometry.Scheme.Modules.homOfTopSection _ (sectionTensor P P') ≫
        (AlgebraicGeometry.Scheme.Modules.pullbackTensorIso
          (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom M.toModules M'.toModules).inv := by
  rw [xiSectionMul_eq_app]
  exact homOfTopSection_comp (φ := (AlgebraicGeometry.Scheme.Modules.pullbackTensorIso
    (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom M.toModules M'.toModules).inv)
    (sectionTensor P P')

theorem homOfTopSectionU_xiSectionMul {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (L M M' : LineBundle C.toVariety)
    (P : (((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        M.toModules).val.obj (Opposite.op ⊤) : Type u))
    (P' : (((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        M'.toModules).val.obj (Opposite.op ⊤) : Type u)) :
    homOfTopSectionU ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj (M.tensor M').toModules) (xiSectionMul L M M' P P') =
      homOfTopSectionU (AlgebraicGeometry.Scheme.Modules.tensor ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj M.toModules) ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj M'.toModules))
        (sectionTensor P P') ≫
        (AlgebraicGeometry.Scheme.Modules.pullbackTensorIso
          (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom M.toModules M'.toModules).inv :=
  homOfTopSection_xiSectionMul L M M' P P'

/-- The evaluation isomorphism `A^∨ ⊗ A ≅ O_C` of a line bundle (Stacks 01CT, `isIso_internalHomEval_dual`). -/
noncomputable def LineBundle.dualEvIso {k : Type u} [Field k] {X : Variety k} (A : LineBundle X) :
    AlgebraicGeometry.Scheme.Modules.dual A.toModules ⊗ A.toModules ≅ 𝟙_ X.toScheme.Modules :=
  haveI : CategoryTheory.IsIso (AlgebraicGeometry.Scheme.Modules.dualEv A.toModules) :=
    AlgebraicGeometry.Scheme.Modules.isIso_internalHomEval_dual A.toModules
  CategoryTheory.asIso (AlgebraicGeometry.Scheme.Modules.dualEv A.toModules)

/-- **The Hom–section calculus for pullback line bundles on `Tot(L)`.**

Statement. Write `p : Tot(L) → C`, `pb := Modules.pullback p`, `A^∨ := A.zpow (-1)`, `H := A^∨ ⊗ B`, `H' := B^∨ ⊗ A`.
For an isomorphism `α : p^*A ≅ p^*B` there are global sections `s ∈ Γ(Tot, p^*H)`, `s' ∈ Γ(Tot, p^*H')`, a base
morphism `ev : A ⊗ H ⟶ B` on `C` and a base *isomorphism* `μ : H ⊗ H' ≅ O_C` (written `(A.zpow 0).toModules`, which
is `O_C` by definition) such that
(i) `α.hom.app ⊤ Q = (pb ev).app ⊤ (Q · s)` for every `Q ∈ Γ(Tot, p^*A)` (`·` is `xiSectionMul`), and
(ii) `(pb μ.hom).app ⊤ (s · s') = 1`, the unit section `(pullbackUnitIso p).inv.app ⊤ 1 ∈ Γ(Tot, p^*O_C)`.

Proof (as formalized). Let `D := dual A`, `ev₀ := dualEv A : D ⊗ A ≅ O_C` (an isomorphism, Stacks 01CT), and
`β_{A,A} = 𝟙` (Stacks 01CR). Put `c := ε ≫ pb(ev₀⁻¹) ≫ δ`, `e := μ ≫ pb(ev₀) ≫ η` on `Tot(L)`, so `c ≫ e = 𝟙`.
* `s := (c ≫ pb D ◁ α.hom ≫ μ)(1)`, moved to `p^*(A^∨ ⊗ B)` by `zpowNegOneIso⁻¹` and `tensorIsoTensorObj⁻¹`;
  `s'` likewise from `α.inv` (with `B`).
* `ev := tensorIsoTensorObj ≫ A ◁ tensorIsoTensorObj ≫ A ◁ (zpowNegOneIso ▷ B) ≫ [α⁻¹ ≫ β_{A,D} ▷ B ≫ ev₀ ▷ B ≫ λ_B]`.
* `μ := tensorIsoTensorObj ≪≫ (tensorIsoTensorObj ⊗ tensorIsoTensorObj) ≪≫ (zpowNegOneIso ▷ B ⊗ zpowNegOneIso ▷ A) ≪≫
  [α ≫ D_A ◁ (pairing of B with B^∨) ≫ ev₀]`, an isomorphism.
* (i) and (ii) are the abstract identities `EvalCalculus.hom_eq_secHom_transport` and
  `EvalCalculus.pair_secHom_transport` (monoidal algebra: naturality, exchange law, hexagon, symmetry,
  strong monoidal functor identities), transported to sections by `homOfTopSection_xiSectionMul`,
  `homOfTopSection_sectionTensor` and `unitHomEquivTop`.
Edge cases: `Γ(Tot, p^*A)` may be `0` (then (i) is vacuous); the statement is an existential so no data is introduced. -/
theorem exists_xiSections_of_pullbackIso_of_evalCalculus {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
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
  -- geometric input: the evaluation of a line bundle is an isomorphism, its self-braiding is the identity
  have hβA : (β_ A.toModules A.toModules).hom = 𝟙 _ :=
    AlgebraicGeometry.Scheme.Modules.braiding_hom_eq_id_of_isLineBundle A.toModules
  have hβB : (β_ B.toModules B.toModules).hom = 𝟙 _ :=
    AlgebraicGeometry.Scheme.Modules.braiding_hom_eq_id_of_isLineBundle B.toModules
  -- the sections of `α.hom` and `α.inv` (spelled with the modules of the statement)
  let σ : 𝟙_ (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.Modules ⟶ (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj ((A.zpow (-1)).tensor B).toModules :=
    CategoryTheory.MonoidalCategory.EvalCalculus.secHom (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom) A.dualEvIso α.hom ≫
    (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).map (A.zpowNegOneIso.inv ▷ B.toModules) ≫
    (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).map (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj (A.zpow (-1)).toModules B.toModules).inv
  let σ' : 𝟙_ (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.Modules ⟶ (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj ((B.zpow (-1)).tensor A).toModules :=
    CategoryTheory.MonoidalCategory.EvalCalculus.secHom (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom) B.dualEvIso α.inv ≫
    (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).map (B.zpowNegOneIso.inv ▷ A.toModules) ≫
    (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).map (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj (B.zpow (-1)).toModules A.toModules).inv
  have hs : homOfTopSectionU _ (secOfHom ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj ((A.zpow (-1)).tensor B).toModules) σ) = σ := homOfTopSectionU_secOfHom _ σ
  have hs' : homOfTopSectionU _ (secOfHom ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj ((B.zpow (-1)).tensor A).toModules) σ') = σ' := homOfTopSectionU_secOfHom ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj ((B.zpow (-1)).tensor A).toModules) σ'
  -- the base evaluation and the base pairing (canonical spellings `tensor _ _`)
  let evC : AlgebraicGeometry.Scheme.Modules.tensor A.toModules ((A.zpow (-1)).tensor B).toModules ⟶
      B.toModules :=
    (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj A.toModules ((A.zpow (-1)).tensor B).toModules).hom ≫
      A.toModules ◁ (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj (A.zpow (-1)).toModules B.toModules).hom ≫
      A.toModules ◁ (A.zpowNegOneIso.hom ▷ B.toModules) ≫
      CategoryTheory.MonoidalCategory.EvalCalculus.evBase A.dualEvIso B.toModules
  let μC : AlgebraicGeometry.Scheme.Modules.tensor ((A.zpow (-1)).tensor B).toModules
      ((B.zpow (-1)).tensor A).toModules ≅ 𝟙_ _ :=
    AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj ((A.zpow (-1)).tensor B).toModules
        ((B.zpow (-1)).tensor A).toModules ≪≫
      CategoryTheory.MonoidalCategory.tensorIso
        (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj (A.zpow (-1)).toModules B.toModules)
        (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj (B.zpow (-1)).toModules A.toModules) ≪≫
      CategoryTheory.MonoidalCategory.tensorIso
        (CategoryTheory.MonoidalCategory.whiskerRightIso A.zpowNegOneIso B.toModules)
        (CategoryTheory.MonoidalCategory.whiskerRightIso B.zpowNegOneIso A.toModules) ≪≫
      CategoryTheory.MonoidalCategory.EvalCalculus.pairBaseIso A.dualEvIso B.dualEvIso
  refine ⟨secOfHom _ σ, secOfHom ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj ((B.zpow (-1)).tensor A).toModules) σ', evC, μC, ?_, ?_⟩
  · intro Q
    have key := CategoryTheory.MonoidalCategory.EvalCalculus.hom_eq_secHom_transport (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom)
      A.dualEvIso hβA (B := B.toModules) (Av := (A.zpow (-1)).toModules)
      (H := ((A.zpow (-1)).tensor B).toModules)
      (AH := AlgebraicGeometry.Scheme.Modules.tensor A.toModules ((A.zpow (-1)).tensor B).toModules)
      A.zpowNegOneIso
      (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj (A.zpow (-1)).toModules B.toModules)
      (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj A.toModules ((A.zpow (-1)).tensor B).toModules)
      (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _)
      (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjIso _ _ _) rfl α.hom (homOfTopSectionU ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj A.toModules) Q)
    have hQσ : homOfTopSectionU (AlgebraicGeometry.Scheme.Modules.tensor ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj A.toModules) ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj ((A.zpow (-1)).tensor B).toModules)) (sectionTensor Q (secOfHom ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj ((A.zpow (-1)).tensor B).toModules) σ)) =
        (λ_ (𝟙_ (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.Modules)).inv ≫
          CategoryTheory.MonoidalCategoryStruct.tensorHom (C := (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.Modules) (homOfTopSectionU ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj A.toModules) Q) σ ≫
          (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _).inv := by
      rw [homOfTopSectionU_sectionTensor, hs]
    have hxi : @Eq (𝟙_ (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.Modules ⟶ (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
          (AlgebraicGeometry.Scheme.Modules.tensor A.toModules ((A.zpow (-1)).tensor B).toModules))
        (homOfTopSectionU ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj (A.tensor ((A.zpow (-1)).tensor B)).toModules) (xiSectionMul L A ((A.zpow (-1)).tensor B) Q (secOfHom ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj ((A.zpow (-1)).tensor B).toModules) σ)))
        ((λ_ (𝟙_ (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.Modules)).inv ≫
          CategoryTheory.MonoidalCategoryStruct.tensorHom (C := (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.Modules) (homOfTopSectionU ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj A.toModules) Q) σ ≫
          (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _).inv ≫
          (AlgebraicGeometry.Scheme.Modules.pullbackTensorIso
            (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom A.toModules
            ((A.zpow (-1)).tensor B).toModules).inv) :=
      Eq.trans (α := 𝟙_ (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.Modules ⟶ (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
          (AlgebraicGeometry.Scheme.Modules.tensor A.toModules ((A.zpow (-1)).tensor B).toModules))
        (homOfTopSectionU_xiSectionMul L A ((A.zpow (-1)).tensor B) Q _)
        (by rw [hQσ]; simp only [Category.assoc])
    have h1 : homOfTopSectionU ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj (A.tensor ((A.zpow (-1)).tensor B)).toModules) (xiSectionMul L A ((A.zpow (-1)).tensor B) Q (secOfHom ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj ((A.zpow (-1)).tensor B).toModules) σ)) ≫
        (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).map evC = homOfTopSectionU ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj A.toModules) Q ≫ α.hom :=
      (congrArg (fun x : (𝟙_ (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.Modules ⟶ (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
          (AlgebraicGeometry.Scheme.Modules.tensor A.toModules ((A.zpow (-1)).tensor B).toModules)) =>
            x ≫ (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).map evC) hxi).trans
        (by simp only [Category.assoc]; exact key)
    exact (app_top_eqU α.hom Q).trans
      ((congrArg (secOfHom ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj B.toModules)) h1.symm).trans (app_top_eqU ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).map evC) _).symm)
  · have key := CategoryTheory.MonoidalCategory.EvalCalculus.pair_secHom_transport (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom)
      A.dualEvIso B.dualEvIso hβB (Av := (A.zpow (-1)).toModules) (Bv := (B.zpow (-1)).toModules)
      (H := ((A.zpow (-1)).tensor B).toModules) (H' := ((B.zpow (-1)).tensor A).toModules)
      (HH' := AlgebraicGeometry.Scheme.Modules.tensor ((A.zpow (-1)).tensor B).toModules
        ((B.zpow (-1)).tensor A).toModules)
      A.zpowNegOneIso B.zpowNegOneIso
      (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj (A.zpow (-1)).toModules B.toModules)
      (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj (B.zpow (-1)).toModules A.toModules)
      (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj ((A.zpow (-1)).tensor B).toModules
        ((B.zpow (-1)).tensor A).toModules)
      (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _)
      (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjIso _ _ _) rfl α.hom α.inv α.hom_inv_id
    have hσσ' : homOfTopSectionU (AlgebraicGeometry.Scheme.Modules.tensor ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj ((A.zpow (-1)).tensor B).toModules) ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj ((B.zpow (-1)).tensor A).toModules)) (sectionTensor (secOfHom ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj ((A.zpow (-1)).tensor B).toModules) σ) (secOfHom ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj ((B.zpow (-1)).tensor A).toModules) σ')) =
        (λ_ (𝟙_ (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.Modules)).inv ≫
          CategoryTheory.MonoidalCategoryStruct.tensorHom (C := (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.Modules) σ σ' ≫
          (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _).inv := by
      rw [homOfTopSectionU_sectionTensor, hs, hs']
    have hxi : @Eq (𝟙_ (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.Modules ⟶ (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
          (AlgebraicGeometry.Scheme.Modules.tensor ((A.zpow (-1)).tensor B).toModules
            ((B.zpow (-1)).tensor A).toModules))
        (homOfTopSectionU ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj (((A.zpow (-1)).tensor B).tensor ((B.zpow (-1)).tensor A)).toModules)
          (xiSectionMul L ((A.zpow (-1)).tensor B) ((B.zpow (-1)).tensor A) (secOfHom ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj ((A.zpow (-1)).tensor B).toModules) σ) (secOfHom ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj ((B.zpow (-1)).tensor A).toModules) σ')))
        ((λ_ (𝟙_ (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.Modules)).inv ≫
          CategoryTheory.MonoidalCategoryStruct.tensorHom (C := (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.Modules) σ σ' ≫
          (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _).inv ≫
          (AlgebraicGeometry.Scheme.Modules.pullbackTensorIso
            (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ((A.zpow (-1)).tensor B).toModules
            ((B.zpow (-1)).tensor A).toModules).inv) :=
      Eq.trans (α := 𝟙_ (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.Modules ⟶ (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
          (AlgebraicGeometry.Scheme.Modules.tensor ((A.zpow (-1)).tensor B).toModules
            ((B.zpow (-1)).tensor A).toModules))
        (homOfTopSectionU_xiSectionMul L ((A.zpow (-1)).tensor B) ((B.zpow (-1)).tensor A) _ _)
        (by rw [hσσ']; simp only [Category.assoc])
    have h2 : homOfTopSectionU ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj (((A.zpow (-1)).tensor B).tensor ((B.zpow (-1)).tensor A)).toModules)
        (xiSectionMul L ((A.zpow (-1)).tensor B) ((B.zpow (-1)).tensor A) (secOfHom ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj ((A.zpow (-1)).tensor B).toModules) σ) (secOfHom ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj ((B.zpow (-1)).tensor A).toModules) σ')) ≫
        (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).map μC.hom = CategoryTheory.Functor.LaxMonoidal.ε (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom) :=
      (congrArg (fun x : (𝟙_ (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.Modules ⟶ (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
          (AlgebraicGeometry.Scheme.Modules.tensor ((A.zpow (-1)).tensor B).toModules
            ((B.zpow (-1)).tensor A).toModules)) => x ≫ (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).map μC.hom) hxi).trans
        (by simp only [Category.assoc]; exact key)
    have h3 : secOfHom ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj (𝟙_ _)) (CategoryTheory.Functor.LaxMonoidal.ε (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom)) =
        (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso
          (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).inv.app ⊤
          (1 : (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.ringCatSheaf.obj.obj
            (Opposite.op ⊤)) := by
      rw [AlgebraicGeometry.Scheme.Modules.pullback_ε_eq]
      rfl
    exact (app_top_eqU ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).map μC.hom) _).trans ((congrArg (secOfHom ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj (𝟙_ _))) h2).trans h3)

end
