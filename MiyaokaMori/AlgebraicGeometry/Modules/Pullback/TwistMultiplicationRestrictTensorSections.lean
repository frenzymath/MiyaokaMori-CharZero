import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesRestrictMonoidal
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorSectionsCoherence

/-! # The monoidal structure of restriction on pairings of sections

For an open immersion `f : X ⟶ Y`, the strong monoidal structure
`restrictTensorObjIso f M N : R_f(M ⊗ N) ≅ R_f M ⊗ R_f N` of the restriction `R_f` (lifted along
sheafification by `Localization.Monoidal.functorMonoidalOfComp`) evaluated on **pairings of
sections**: for `A ⊆ X` open, `x ∈ Γ(M, f''A)`, `y ∈ Γ(N, f''A)`,
`(restrictTensorObjIso f M N).hom.app A (tensorSections M N (f''A) x y) = tensorSections (R_f M) (R_f N) A x y`.

Proof route (definitional unfolding plus pointwise unit/counit identities):
1. `functorMonoidalOfComp_μ` (Mathlib):
   `μ_{R_f}(L P)(L Q) = (e ⊗ e) ≫ μ_{R^pre ⋙ L_X} P Q ≫ e⁻¹ ≫ R_f(δ_L P Q)` with
   `e = sheafifyRestrictIso`;
2. the `μ_L` of sheafification on pairings of unit images:
   `μ_L(P,Q).inv (η_{P⊗Q}(p ⊗ q)) = tensorSections (L P) (L Q) (η p) (η q)`
   (`tensorSections_unit_unit`; naturality of `δ` and the triangle identities);
3. the `μ` of the presheaf restriction `R^pre` is the identity on pure tensors
   (`restrictPre_μ_tmul`; `ModuleCat.restrictScalars_μ_tmul`);
4. `sheafifyRestrictHom f P` sends `η_{R^pre P}(p)` to `η_P(p)` (`sheafifyRestrictHom_unit`;
   `sheafify_unit_counit_eval`);
5. replace `M = L(G M)` via the counit (`tensorHom_tensorSections`, right triangle identity).

Corollary `restrict_tensor_hom_ext`: two morphisms out of `(Modules.tensor M N)|_f` agreeing on all
pure tensor sections `η(x ⊗ y)` (`x, y` sections over `f''A`) are equal.

References: Stacks 01CD (open immersion case); Mathlib
`CategoryTheory/Localization/Monoidal/Functor.lean` (`functorMonoidalOfComp_μ`).
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace MonoidalCategory
open CategoryTheory.Functor.LaxMonoidal CategoryTheory.Functor.OplaxMonoidal
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

/-- Naturality of the `δ` of a monoidal functor `F` with respect to `tensorHom`, in the form
`δ ≫ (eA ⊗ eB)` (in the style of `MonoidalAux.delta_whiskerRight_comp`). -/
theorem MonoidalAux.delta_tensorHom_comp {C D : Type*} [Category C] [Category D] [MonoidalCategory C]
    [MonoidalCategory D] (F : C ⥤ D) [F.Monoidal] {P P' Q Q' : C} {A B : D}
    (f : P ⟶ P') (g : Q ⟶ Q') (eA : F.obj P' ⟶ A) (eB : F.obj Q' ⟶ B) :
    F.map (f ⊗ₘ g) ≫ (δ F P' Q' ≫ (eA ⊗ₘ eB)) = δ F P Q ≫ ((F.map f ≫ eA) ⊗ₘ (F.map g ≫ eB)) := by
  rw [← Category.assoc, ← Functor.OplaxMonoidal.δ_natural, Category.assoc, tensorHom_comp_tensorHom]

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- `L(η_P ⊗ η_Q) ≫ sheafifyTensorTo (L P) (L Q) = μ_L(P,Q)⁻¹` (naturality of `δ` and the left
triangle identity). -/
theorem sheafify_map_unit_tensorHom_comp_sheafifyTensorTo
    (P Q : _root_.PresheafOfModules.{u} X.ringCatSheaf.obj) :
    (shL X).map ((shAdj X).unit.app P ⊗ₘ (shAdj X).unit.app Q) ≫
        sheafifyTensorTo ((shL X).obj P) ((shL X).obj Q) =
      (Localization.Monoidal.μ (shL X) (shW X) (sheafificationUnitIso X) P Q).inv := by
  refine (MonoidalAux.delta_tensorHom_comp
    (Localization.Monoidal.toMonoidalCategory (shL X) (shW X) (sheafificationUnitIso X)) _ _ _ _).trans ?_
  erw [Adjunction.left_triangle_components, Adjunction.left_triangle_components, MonoidalCategory.tensorHom_id, MonoidalCategory.id_whiskerRight, Category.comp_id]
  rfl

/-- The counit is the identity on unit images (pointwise right triangle identity):
`ε_M (η_{G M} x) = x`. -/
theorem counit_app_unit_app (M : X.Modules) (U : X.Opens) (x : M.val.obj (op U)) :
    ((shAdj X).counit.app M).val.app (op U) (((shAdj X).unit.app ((shG X).obj M)).app (op U) x) = x :=
  congrArg (fun k : (shG X).obj M ⟶ (shG X).obj M => k.app (op U) x)
    ((shAdj X).right_triangle_components (Y := M))

/-- The comparison isomorphism `μ_L(P,Q)` of sheafification on pairings of unit images:
`tensorSections (L P) (L Q) U (η p) (η q) = μ_L(P,Q)⁻¹ (η_{P⊗Q}(p ⊗ q))`. -/
theorem tensorSections_unit_unit (P Q : _root_.PresheafOfModules.{u} X.ringCatSheaf.obj) (U : X.Opens)
    (p : P.obj (op U)) (q : Q.obj (op U)) :
    tensorSections ((shL X).obj P) ((shL X).obj Q) U
        (((shAdj X).unit.app P).app (op U) p) (((shAdj X).unit.app Q).app (op U) q) =
      (Localization.Monoidal.μ (shL X) (shW X) (sheafificationUnitIso X) P Q).inv.val.app (op U)
        (((shAdj X).unit.app (P ⊗ Q)).app (op U) (TensorProduct.tmul _ p q)) := by
  have h2 := congrArg (fun k => k.val.app (op U)
    (((shAdj X).unit.app (P ⊗ Q)).app (op U) (TensorProduct.tmul _ p q)))
    (sheafify_map_unit_tensorHom_comp_sheafifyTensorTo P Q)
  refine Eq.trans ?_ h2
  refine Eq.trans ?_ (sheafify_unit_eval (X := X) ((shAdj X).unit.app P ⊗ₘ (shAdj X).unit.app Q)
    (sheafifyTensorTo ((shL X).obj P) ((shL X).obj Q)) U (TensorProduct.tmul _ p q)).symm
  unfold tensorSections
  congr 2

/-! ### Pointwise auxiliary lemmas (the sheafification adjunction and the values of `μ`/`δ` on unit
images) -/

theorem hom_comp_val_app_apply {A B C : X.Modules} (a : A ⟶ B) (b : B ⟶ C) (U : X.Opens)
    (z : A.val.obj (op U)) :
    (a ≫ b).val.app (op U) z = b.val.app (op U) (a.val.app (op U) z) := rfl

theorem sheafify_map_app_unit {P Q : _root_.PresheafOfModules.{u} X.ringCatSheaf.obj} (φ : P ⟶ Q)
    (U : X.Opens) (p : P.obj (op U)) :
    ((sheafifyZ X).map φ).val.app (op U) (((adjZ X).unit.app P).app (op U) p) =
      ((adjZ X).unit.app Q).app (op U) (φ.app (op U) p) :=
  (congrArg (fun k => k.app (op U) p) ((adjZ X).unit.naturality φ)).symm

theorem sheafify_μ_app_tensorSections_unit (P Q : _root_.PresheafOfModules.{u} X.ringCatSheaf.obj)
    (U : X.Opens) (p : P.obj (op U)) (q : Q.obj (op U)) :
    (μ (sheafifyZ X) P Q).val.app (op U)
        (tensorSections ((sheafifyZ X).obj P) ((sheafifyZ X).obj Q) U
          (((adjZ X).unit.app P).app (op U) p) (((adjZ X).unit.app Q).app (op U) q)) =
      ((adjZ X).unit.app (P ⊗ Q)).app (op U) (TensorProduct.tmul _ p q) := by
  rw [tensorSections_unit_unit]
  exact congrArg (fun k => k.val.app (op U) (((adjZ X).unit.app (P ⊗ Q)).app (op U) (TensorProduct.tmul _ p q)))
    (Localization.Monoidal.μ (shL X) (shW X) (sheafificationUnitIso X) P Q).inv_hom_id

theorem sheafify_δ_app_unit_tmul (P Q : _root_.PresheafOfModules.{u} X.ringCatSheaf.obj)
    (U : X.Opens) (p : P.obj (op U)) (q : Q.obj (op U)) :
    (δ (sheafifyZ X) P Q).val.app (op U) (((adjZ X).unit.app (P ⊗ Q)).app (op U) (TensorProduct.tmul _ p q)) =
      tensorSections ((sheafifyZ X).obj P) ((sheafifyZ X).obj Q) U
        (((adjZ X).unit.app P).app (op U) p) (((adjZ X).unit.app Q).app (op U) q) :=
  (tensorSections_unit_unit P Q U p q).symm

/-- The `hom` of an isomorphism is the identity on the image of `inv` (pointwise). -/
theorem iso_hom_val_app_inv_val_app {M N : X.Modules} (e : M ≅ N) (U : X.Opens) (w : N.val.obj (op U)) :
    e.hom.val.app (op U) (e.inv.val.app (op U) w) = w :=
  congrArg (fun k => k.val.app (op U) w) e.inv_hom_id

variable {Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) [AlgebraicGeometry.IsOpenImmersion f]

/-- The `μ` of the presheaf restriction `restrictPre f` is the identity on pure tensors. -/
theorem restrictPre_μ_tmul (P Q : _root_.PresheafOfModules.{u} Y.ringCatSheaf.obj) (A : X.Opens)
    (p : P.obj (op (f ''ᵁ A))) (q : Q.obj (op (f ''ᵁ A))) :
    (μ (restrictPre f) P Q).app (op A)
        (TensorProduct.tmul (X.presheaf.obj (op A))
          (show ((restrictPre f).obj P).obj (op A) from p)
          (show ((restrictPre f).obj Q).obj (op A) from q)) =
      (TensorProduct.tmul (Y.presheaf.obj (op (f ''ᵁ A))) p q : (P ⊗ Q).obj (op (f ''ᵁ A))) := by
  letI h1 : (_root_.PresheafOfModules.pushforward₀OfCommRingCat.{u} f.opensFunctor Y.presheaf).Monoidal :=
    inferInstance
  letI h2 : (_root_.PresheafOfModules.restrictScalarsC.{u}
      (R := X.presheaf) (R' := f.opensFunctor.op ⋙ Y.presheaf) (restrictAlpha f)).Monoidal :=
    @_root_.PresheafOfModules.restrictScalarsC_monoidal _ _ _ _ (restrictAlpha f) (isIso_restrictAlpha f)
  change ((_root_.PresheafOfModules.restrictScalarsC.{u} (R := X.presheaf) (R' := f.opensFunctor.op ⋙ Y.presheaf)
      (restrictAlpha f)).map
      (μ (_root_.PresheafOfModules.pushforward₀OfCommRingCat.{u} f.opensFunctor Y.presheaf) P Q)).app (op A)
    ((μ (_root_.PresheafOfModules.restrictScalarsC.{u} (R := X.presheaf) (R' := f.opensFunctor.op ⋙ Y.presheaf)
        (restrictAlpha f))
      ((_root_.PresheafOfModules.pushforward₀OfCommRingCat.{u} f.opensFunctor Y.presheaf).obj P)
      ((_root_.PresheafOfModules.pushforward₀OfCommRingCat.{u} f.opensFunctor Y.presheaf).obj Q)).app (op A)
      (TensorProduct.tmul _ p q)) = _
  erw [ModuleCat.restrictScalars_μ_tmul]
  rfl

/-- `sheafifyRestrictHom f P : L_X(P|_X) ⟶ (L_Y P)|_X` sends `η_{P|_X}(p)` to `η_P(p)`. -/
theorem sheafifyRestrictHom_unit (P : _root_.PresheafOfModules.{u} Y.ringCatSheaf.obj) (A : X.Opens)
    (p : P.obj (op (f ''ᵁ A))) :
    (sheafifyRestrictHom f P).val.app (op A)
        (((adjZ X).unit.app ((restrictPre f).obj P)).app (op A)
          (show ((restrictPre f).obj P).obj (op A) from p)) =
      ((adjZ Y).unit.app P).app (op (f ''ᵁ A)) p := by
  rw [sheafifyRestrictHom_eq]
  exact sheafify_unit_counit_eval (X := X) (A := (restrictFunctor f).obj ((sheafifyZ Y).obj P))
    (restrictUnit f P) A (show ((restrictPre f).obj P).obj (op A) from p)

/-- The lifting isomorphism `e : R^pre ⋙ L_X ≅ L_Y ⋙ R_f` (the `Lifting.iso` of `liftingRestrict`,
packaged as a constant). -/
def liftingIsoR : sheafifyZ Y ⋙ restrictFunctor f ≅ restrictPre f ⋙ sheafifyZ X :=
  Localization.Lifting.iso (sheafifyZ Y) (sheafificationW Y) (restrictPre f ⋙ sheafifyZ X) (restrictFunctor f)

theorem liftingIsoR_hom_app_unit (P : _root_.PresheafOfModules.{u} Y.ringCatSheaf.obj) (A : X.Opens)
    (p : P.obj (op (f ''ᵁ A))) :
    ((liftingIsoR f).hom.app P).val.app (op A) (((adjZ Y).unit.app P).app (op (f ''ᵁ A)) p) =
      ((adjZ X).unit.app ((restrictPre f).obj P)).app (op A)
        (show ((restrictPre f).obj P).obj (op A) from p) := by
  change (CategoryTheory.inv (sheafifyRestrictHom f P)).val.app (op A) _ = _
  rw [← sheafifyRestrictHom_unit f P A p]
  exact congrArg (fun k => k.val.app (op A) (((adjZ X).unit.app ((restrictPre f).obj P)).app (op A)
    (show ((restrictPre f).obj P).obj (op A) from p))) (IsIso.hom_inv_id (sheafifyRestrictHom f P))

theorem liftingIsoR_inv_app_unit (P : _root_.PresheafOfModules.{u} Y.ringCatSheaf.obj) (A : X.Opens)
    (p : P.obj (op (f ''ᵁ A))) :
    ((liftingIsoR f).inv.app P).val.app (op A)
        (((adjZ X).unit.app ((restrictPre f).obj P)).app (op A)
          (show ((restrictPre f).obj P).obj (op A) from p)) =
      ((adjZ Y).unit.app P).app (op (f ''ᵁ A)) p :=
  sheafifyRestrictHom_unit f P A p

theorem restrictFunctor_map_val_app_apply {M N : Y.Modules} (φ : M ⟶ N) (A : X.Opens)
    (z : M.val.obj (op (f ''ᵁ A))) :
    ((restrictFunctor f).map φ).val.app (op A) z = φ.val.app (op (f ''ᵁ A)) z := rfl

theorem tensorHom_tensorSections_restrict {M N : Y.Modules} {M' N' : X.Modules}
    (φ : (restrictFunctor f).obj M ⟶ M') (ψ : (restrictFunctor f).obj N ⟶ N') (A : X.Opens)
    (a : M.val.obj (op (f ''ᵁ A))) (b : N.val.obj (op (f ''ᵁ A))) :
    (φ ⊗ₘ ψ).val.app (op A) (tensorSections ((restrictFunctor f).obj M) ((restrictFunctor f).obj N) A a b) =
      tensorSections M' N' A (φ.val.app (op A) a) (ψ.val.app (op A) b) :=
  tensorHom_tensorSections (X := X) φ ψ A a b

theorem μ_restrictPre_comp_sheafify_app_aux (P Q : _root_.PresheafOfModules.{u} Y.ringCatSheaf.obj) (A : X.Opens)
    (p : P.obj (op (f ''ᵁ A))) (q : Q.obj (op (f ''ᵁ A))) :
    (μ (restrictPre f ⋙ sheafifyZ X) P Q).val.app (op A)
        (tensorSections ((sheafifyZ X).obj ((restrictPre f).obj P)) ((sheafifyZ X).obj ((restrictPre f).obj Q)) A
          (((adjZ X).unit.app ((restrictPre f).obj P)).app (op A) (show ((restrictPre f).obj P).obj (op A) from p))
          (((adjZ X).unit.app ((restrictPre f).obj Q)).app (op A) (show ((restrictPre f).obj Q).obj (op A) from q))) =
      ((adjZ X).unit.app ((restrictPre f).obj (P ⊗ Q))).app (op A)
        (show ((restrictPre f).obj (P ⊗ Q)).obj (op A) from TensorProduct.tmul _ p q) := by
  rw [Functor.LaxMonoidal.comp_μ, hom_comp_val_app_apply]
  rw [sheafify_μ_app_tensorSections_unit]
  erw [sheafify_map_app_unit (X := X)]
  exact congrArg (((adjZ X).unit.app ((restrictPre f).obj (P ⊗ Q))).app (op A)) (restrictPre_μ_tmul f P Q A p q)

/-- As above, with the module written `(restrictPre f ⋙ sheafifyZ X).obj P` (the spelling appearing in
`functorMonoidalOfComp_μ`). -/
theorem μ_restrictPre_comp_sheafify_app (P Q : _root_.PresheafOfModules.{u} Y.ringCatSheaf.obj) (A : X.Opens)
    (p : P.obj (op (f ''ᵁ A))) (q : Q.obj (op (f ''ᵁ A))) :
    (μ (restrictPre f ⋙ sheafifyZ X) P Q).val.app (op A)
        (tensorSections ((restrictPre f ⋙ sheafifyZ X).obj P) ((restrictPre f ⋙ sheafifyZ X).obj Q) A
          (((adjZ X).unit.app ((restrictPre f).obj P)).app (op A) (show ((restrictPre f).obj P).obj (op A) from p))
          (((adjZ X).unit.app ((restrictPre f).obj Q)).app (op A) (show ((restrictPre f).obj Q).obj (op A) from q))) =
      ((adjZ X).unit.app ((restrictPre f).obj (P ⊗ Q))).app (op A)
        (show ((restrictPre f).obj (P ⊗ Q)).obj (op A) from TensorProduct.tmul _ p q) :=
  μ_restrictPre_comp_sheafify_app_aux f P Q A p q

theorem μ_restrict_eq (P Q : _root_.PresheafOfModules.{u} Y.ringCatSheaf.obj) :
    letI := restrictFunctor_monoidal f
    μ (restrictFunctor f) ((sheafifyZ Y).obj P) ((sheafifyZ Y).obj Q) =
      ((liftingIsoR f).hom.app P ⊗ₘ (liftingIsoR f).hom.app Q) ≫ μ (restrictPre f ⋙ sheafifyZ X) P Q ≫
        (liftingIsoR f).inv.app (P ⊗ Q) ≫ (restrictFunctor f).map (δ (sheafifyZ Y) P Q) :=
  Localization.Monoidal.functorMonoidalOfComp_μ (sheafifyZ Y) (sheafificationW Y) (restrictFunctor f)
    (restrictPre f ⋙ sheafifyZ X) P Q

theorem μ_restrict_app_tensorSections_unit (P Q : _root_.PresheafOfModules.{u} Y.ringCatSheaf.obj) (A : X.Opens)
    (p : P.obj (op (f ''ᵁ A))) (q : Q.obj (op (f ''ᵁ A))) :
    letI := restrictFunctor_monoidal f
    (μ (restrictFunctor f) ((sheafifyZ Y).obj P) ((sheafifyZ Y).obj Q)).val.app (op A)
        (tensorSections ((restrictFunctor f).obj ((sheafifyZ Y).obj P)) ((restrictFunctor f).obj ((sheafifyZ Y).obj Q)) A
          (((adjZ Y).unit.app P).app (op (f ''ᵁ A)) p) (((adjZ Y).unit.app Q).app (op (f ''ᵁ A)) q)) =
      tensorSections ((sheafifyZ Y).obj P) ((sheafifyZ Y).obj Q) (f ''ᵁ A)
        (((adjZ Y).unit.app P).app (op (f ''ᵁ A)) p) (((adjZ Y).unit.app Q).app (op (f ''ᵁ A)) q) := by
  letI := restrictFunctor_monoidal f
  rw [μ_restrict_eq, hom_comp_val_app_apply, hom_comp_val_app_apply, hom_comp_val_app_apply]
  have s1 : ((liftingIsoR f).hom.app P ⊗ₘ (liftingIsoR f).hom.app Q).val.app (op A)
      (tensorSections ((restrictFunctor f).obj ((sheafifyZ Y).obj P)) ((restrictFunctor f).obj ((sheafifyZ Y).obj Q)) A
        (((adjZ Y).unit.app P).app (op (f ''ᵁ A)) p) (((adjZ Y).unit.app Q).app (op (f ''ᵁ A)) q)) =
      tensorSections ((restrictPre f ⋙ sheafifyZ X).obj P) ((restrictPre f ⋙ sheafifyZ X).obj Q) A
        (((adjZ X).unit.app ((restrictPre f).obj P)).app (op A) (show ((restrictPre f).obj P).obj (op A) from p))
        (((adjZ X).unit.app ((restrictPre f).obj Q)).app (op A) (show ((restrictPre f).obj Q).obj (op A) from q)) :=
    (tensorHom_tensorSections_restrict f _ _ A _ _).trans
      (congrArg₂ (tensorSections _ _ A) (liftingIsoR_hom_app_unit f P A p) (liftingIsoR_hom_app_unit f Q A q))
  rw [s1]
  have s2 := μ_restrictPre_comp_sheafify_app f P Q A p q
  rw [s2]
  have s3 := liftingIsoR_inv_app_unit f (P ⊗ Q) A (TensorProduct.tmul _ p q)
  exact (congrArg (fun w => ((restrictFunctor f).map (δ (sheafifyZ Y) P Q)).val.app (op A) w) s3).trans
    (sheafify_δ_app_unit_tmul (X := Y) P Q (f ''ᵁ A) p q)

/-- The inverse direction: `μ_{R_f}` sends the pairing of sections in `Γ(R_f M ⊗ R_f N, A)` back to
the pairing in `Γ(M ⊗ N, f''A)`.

Proof (pointwise identities): `(rTOI).inv = μ_{R_f} M N` (`Iso.symm_inv`, `μIso_hom`).
1. Replace `M`, `N` by `L(G M)`, `L(G N)`: `Functor.LaxMonoidal.μ_natural` for the counits
   `ε_M`, `ε_N` gives `(R ε_M ⊗ R ε_N) ≫ μ M N = μ (LGM) (LGN) ≫ R(ε_M ⊗ ε_N)`; since
   `x = ε_M(η x)` (`counit_app_unit_app`),
   `tensorSections (R M) (R N) A x y = (R ε ⊗ R ε)(tensorSections (R(LGM)) (R(LGN)) A (η x) (η y))`
   (`tensorHom_tensorSections`).
2. `Localization.Monoidal.functorMonoidalOfComp_μ`:
   `μ_{R_f} (L P) (L Q) = (e.hom ⊗ e.hom) ≫ μ_{R^pre ⋙ L_X} P Q ≫ e.inv ≫ R_f(δ_L P Q)`, where
   `e = Lifting.iso = (sheafifyRestrictIso f).symm` and `e.hom.app P = (asIso (sheafifyRestrictHom f P)).inv`.
3. Evaluate term by term: `e.hom` sends `η_P x` back to `η_{R^pre P} x` (`sheafifyRestrictHom_unit`
   inverted); `μ_{L_X}` sends `tensorSections (L P')(L Q') A (η' x)(η' y)` to `η'(x ⊗ y)`
   (`tensorSections_unit_unit`); `L_X(μ_{R^pre})` on the image of `η'` gives `η'(x ⊗_{f''A} y)` by
   `sheafify_unit_eval` and `restrictPre_μ_tmul`; `e.inv = sheafifyRestrictHom` gives
   `η_{P⊗Q}(x ⊗ y)` (`sheafifyRestrictHom_unit`); `R_f(δ_L)` at `A` is `(μ_L P Q).inv` at `f''A`,
   which gives `tensorSections (LP)(LQ) (f''A) (η x)(η y)` by `tensorSections_unit_unit`; finally
   `R(ε ⊗ ε)` gives `tensorSections M N (f''A) (ε η x)(ε η y) = tensorSections M N (f''A) x y`.
   Instance-spelling issues with `comp_μ` are handled by `change` to the composite form, as in
   `restrictPre_μ_tmul`. -/
theorem restrictTensorObjIso_inv_app_tensorSections (M N : Y.Modules) (A : X.Opens)
    (x : M.val.obj (op (f ''ᵁ A))) (y : N.val.obj (op (f ''ᵁ A))) :
    (restrictTensorObjIso f M N).inv.app A (tensorSections (M.restrict f) (N.restrict f) A x y) =
      tensorSections M N (f ''ᵁ A) x y := by
  letI := restrictFunctor_monoidal f
  have e0 : ∀ z, (restrictTensorObjIso f M N).inv.app A z = (μ (restrictFunctor f) M N).val.app (op A) z :=
    fun _ => rfl
  refine (e0 _).trans ?_
  have hx : x = ((restrictFunctor f).map ((shAdj Y).counit.app M)).val.app (op A)
      (((shAdj Y).unit.app ((shG Y).obj M)).app (op (f ''ᵁ A)) x) :=
    (counit_app_unit_app (X := Y) M (f ''ᵁ A) x).symm
  have hy : y = ((restrictFunctor f).map ((shAdj Y).counit.app N)).val.app (op A)
      (((shAdj Y).unit.app ((shG Y).obj N)).app (op (f ''ᵁ A)) y) :=
    (counit_app_unit_app (X := Y) N (f ''ᵁ A) y).symm
  have h1 : tensorSections (M.restrict f) (N.restrict f) A x y =
      ((restrictFunctor f).map ((shAdj Y).counit.app M) ⊗ₘ
        (restrictFunctor f).map ((shAdj Y).counit.app N)).val.app (op A)
        (tensorSections ((restrictFunctor f).obj ((shL Y).obj ((shG Y).obj M)))
          ((restrictFunctor f).obj ((shL Y).obj ((shG Y).obj N))) A
          (((shAdj Y).unit.app ((shG Y).obj M)).app (op (f ''ᵁ A)) x)
          (((shAdj Y).unit.app ((shG Y).obj N)).app (op (f ''ᵁ A)) y)) :=
    (congrArg₂ (tensorSections _ _ A) hx hy).trans (tensorHom_tensorSections_restrict f _ _ A _ _).symm
  rw [h1]
  have h2 := congrArg (fun k => k.val.app (op A)
      (tensorSections ((restrictFunctor f).obj ((shL Y).obj ((shG Y).obj M)))
          ((restrictFunctor f).obj ((shL Y).obj ((shG Y).obj N))) A
          (((shAdj Y).unit.app ((shG Y).obj M)).app (op (f ''ᵁ A)) x)
          (((shAdj Y).unit.app ((shG Y).obj N)).app (op (f ''ᵁ A)) y)))
    (Functor.LaxMonoidal.μ_natural (restrictFunctor f) ((shAdj Y).counit.app M) ((shAdj Y).counit.app N))
  simp only [hom_comp_val_app_apply] at h2
  refine h2.trans ?_
  have s := μ_restrict_app_tensorSections_unit f ((shG Y).obj M) ((shG Y).obj N) A x y
  refine (congrArg (fun w => ((restrictFunctor f).map ((shAdj Y).counit.app M ⊗ₘ (shAdj Y).counit.app N)).val.app
    (op A) w) s).trans ?_
  have s5 := tensorHom_tensorSections (X := Y) ((shAdj Y).counit.app M) ((shAdj Y).counit.app N) (f ''ᵁ A)
    (((shAdj Y).unit.app ((shG Y).obj M)).app (op (f ''ᵁ A)) x)
    (((shAdj Y).unit.app ((shG Y).obj N)).app (op (f ''ᵁ A)) y)
  exact s5.trans (congrArg₂ (tensorSections M N (f ''ᵁ A)) (counit_app_unit_app (X := Y) M (f ''ᵁ A) x)
    (counit_app_unit_app (X := Y) N (f ''ᵁ A) y))

/-- **The strong monoidal structure of restriction on pairings of sections**:
`(R_f(M ⊗ N) ≅ R_f M ⊗ R_f N).hom` sends the pairing `x ⊗ y` in `Γ(M ⊗ N, f''A)` to the pairing
`x ⊗ y` in `Γ(R_f M ⊗ R_f N, A)`. Proof: by `restrictTensorObjIso_inv_app_tensorSections` and
`Iso.inv_hom_id_app` (pointwise), `hom (tensorSections M N (f''A) x y) =
hom (inv (tensorSections (R M) (R N) A x y)) = tensorSections (R M) (R N) A x y`. -/
theorem restrictTensorObjIso_hom_app_tensorSections (M N : Y.Modules) (A : X.Opens)
    (x : M.val.obj (op (f ''ᵁ A))) (y : N.val.obj (op (f ''ᵁ A))) :
    (restrictTensorObjIso f M N).hom.app A (tensorSections M N (f ''ᵁ A) x y) =
      tensorSections (M.restrict f) (N.restrict f) A x y := by
  have e0 : ∀ z, (restrictTensorObjIso f M N).hom.app A z = (restrictTensorObjIso f M N).hom.val.app (op A) z :=
    fun _ => rfl
  refine (e0 _).trans ?_
  rw [← restrictTensorObjIso_inv_app_tensorSections f M N A x y]
  exact iso_hom_val_app_inv_val_app (restrictTensorObjIso f M N) A _

/-- The comparison isomorphism `Θ : tensor (R M) (R N) ⟶ (tensor M N)|_f` (a composite of three
isomorphisms). -/
def restrictTensorComparison (M N : Y.Modules) :
    AlgebraicGeometry.Scheme.Modules.tensor ((restrictFunctor f).obj M) ((restrictFunctor f).obj N) ⟶
      (AlgebraicGeometry.Scheme.Modules.tensor M N).restrict f :=
  (tensorIsoTensorObj _ _).hom ≫ (restrictTensorObjIso f M N).inv ≫
    (restrictFunctor f).map (tensorIsoTensorObj M N).inv

theorem isIso_restrictTensorComparison (M N : Y.Modules) : IsIso (restrictTensorComparison f M N) := by
  unfold restrictTensorComparison
  infer_instance

/-- `Θ` on pure tensor sections: `Θ (η'(x ⊗ y)) = η(x ⊗ y)`. -/
theorem restrictTensorComparison_app_unit (M N : Y.Modules) (A : X.Opens)
    (x : M.val.obj (op (f ''ᵁ A))) (y : N.val.obj (op (f ''ᵁ A))) :
    (restrictTensorComparison f M N).val.app (op A)
        (((shAdj X).unit.app ((shG X).obj ((restrictFunctor f).obj M) ⊗ (shG X).obj ((restrictFunctor f).obj N))).app
          (op A) (TensorProduct.tmul _ x y)) =
      ((shAdj Y).unit.app ((shG Y).obj M ⊗ (shG Y).obj N)).app (op (f ''ᵁ A)) (TensorProduct.tmul _ x y) := by
  refine (hom_comp_val_app_apply _ _ A _).trans ?_
  refine (congrArg (fun w => ((restrictTensorObjIso f M N).inv ≫
    (restrictFunctor f).map (tensorIsoTensorObj M N).inv).val.app (op A) w)
    (show (tensorIsoTensorObj _ _).hom.val.app (op A) _ =
      tensorSections ((restrictFunctor f).obj M) ((restrictFunctor f).obj N) A x y from rfl)).trans ?_
  refine (hom_comp_val_app_apply _ _ A _).trans ?_
  refine (congrArg (fun w => ((restrictFunctor f).map (tensorIsoTensorObj M N).inv).val.app (op A) w)
    (restrictTensorObjIso_inv_app_tensorSections f M N A x y)).trans ?_
  exact tensorToSheafify_tensorSections M N (f ''ᵁ A) x y

/-- The transpose under the sheafification adjunction on sections: `(g^♭).app U p = g (η p)` (for
morphisms out of `tensor A B`). -/
theorem homEquiv_tensor_app_apply (A B Q : X.Modules) (g : AlgebraicGeometry.Scheme.Modules.tensor A B ⟶ Q)
    (U : X.Opens) (p : ((shG X).obj A ⊗ (shG X).obj B).obj (op U)) :
    ((shAdj X).homEquiv ((shG X).obj A ⊗ (shG X).obj B) Q g).app (op U) p =
      g.val.app (op U) (((shAdj X).unit.app ((shG X).obj A ⊗ (shG X).obj B)).app (op U) p) := by
  have e := Adjunction.homEquiv_unit (shAdj X) ((shG X).obj A ⊗ (shG X).obj B) Q g
  rw [e]
  rfl

/-- A morphism out of `(Modules.tensor M N)|_f` is determined by its values on the pure tensor
sections `η(x ⊗ y)` (`x ∈ Γ(M, f''A)`, `y ∈ Γ(N, f''A)`).

Proof: `Θ := (tensorIsoTensorObj (R M) (R N)).hom ≫ (restrictTensorObjIso f M N).inv ≫ R_f.map (tensorIsoTensorObj M N).inv`
is an isomorphism `tensor (R M) (R N) ≅ (tensor M N)|_f`, so `g₁ = g₂ ⇔ Θ ≫ g₁ = Θ ≫ g₂`
(`cancel_epi`). `tensor (R M) (R N) = L_X(G(R M) ⊗ G(R N))` is a sheafification, so morphisms out
of it are determined by their transposes under the sheafification adjunction
(`Adjunction.homEquiv` is injective); the transpose is a morphism out of a presheaf tensor
product, which `ModuleCat.MonoidalCategory.tensor_ext` reduces to the values on pure tensors
`x ⊗ y`, i.e. `(Θ ≫ gᵢ).app A (η(x ⊗ y))`. And `Θ.app A (η(x ⊗ y)) = η(x ⊗ y)` (at `f''A`): the
`hom` of `tensorIsoTensorObj` sends `η(x⊗y)` to `tensorSections` (by definition),
`restrictTensorObjIso_inv_app_tensorSections` sends `tensorSections (R M)(R N) A x y` to
`tensorSections M N (f''A) x y`, and `tensorToSheafify_tensorSections` sends it back to `η(x ⊗ y)`. -/
theorem restrict_tensor_hom_ext (M N : Y.Modules) {Q : X.Modules}
    (g₁ g₂ : (AlgebraicGeometry.Scheme.Modules.tensor M N).restrict f ⟶ Q)
    (h : ∀ (A : X.Opens) (x : M.val.obj (op (f ''ᵁ A))) (y : N.val.obj (op (f ''ᵁ A))),
      g₁.app A (((shAdj Y).unit.app ((shG Y).obj M ⊗ (shG Y).obj N)).app (op (f ''ᵁ A))
          (TensorProduct.tmul _ x y)) =
        g₂.app A (((shAdj Y).unit.app ((shG Y).obj M ⊗ (shG Y).obj N)).app (op (f ''ᵁ A))
          (TensorProduct.tmul _ x y))) :
    g₁ = g₂ := by
  haveI := isIso_restrictTensorComparison f M N
  rw [← cancel_epi (restrictTensorComparison f M N)]
  refine ((shAdj X).homEquiv ((shG X).obj ((restrictFunctor f).obj M) ⊗ (shG X).obj ((restrictFunctor f).obj N))
    Q).injective ?_
  refine _root_.PresheafOfModules.hom_ext (fun U => ?_)
  induction U using Opposite.rec with
  | op A =>
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro x y
  have key : ∀ g : (AlgebraicGeometry.Scheme.Modules.tensor M N).restrict f ⟶ Q,
      ((shAdj X).homEquiv ((shG X).obj ((restrictFunctor f).obj M) ⊗ (shG X).obj ((restrictFunctor f).obj N)) Q
          (restrictTensorComparison f M N ≫ g)).app (op A) (TensorProduct.tmul _ x y) =
        g.app A (((shAdj Y).unit.app ((shG Y).obj M ⊗ (shG Y).obj N)).app (op (f ''ᵁ A))
          (TensorProduct.tmul _ x y)) := fun g => by
    refine (homEquiv_tensor_app_apply _ _ Q (restrictTensorComparison f M N ≫ g) A _).trans ?_
    refine (hom_comp_val_app_apply _ _ A _).trans ?_
    exact congrArg (g.val.app (op A)) (restrictTensorComparison_app_unit f M N A x y)
  exact (key g₁).trans ((h A x y).trans (key g₂).symm)

end AlgebraicGeometry.Scheme.Modules

end
