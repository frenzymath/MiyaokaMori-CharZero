import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPullbackMonoidal
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPullbackTensor
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorMonoidalIso
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorPowCanonicalIso
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.EvaluateHomogeneousAtSections
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorPower
import MiyaokaMori.AlgebraicGeometry.Morphisms.SchemeOverBase
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.SectionPullbackAlong
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.SheafOfModulesMonoidal
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleFrame
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorSectionsCoherence
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModuleSectionPullback

/-! # Local formulas for the evaluation of homogeneous polynomials at sections

Two basic properties of the evaluation of homogeneous polynomials at sections of a line bundle:
(1) compatibility with pullback along a morphism: `g^*F(f_0,…,f_N) = F(g^*f_0,…,g^*f_N)` (through
`g^*(A^{⊗e}) ≅ (g^*A)^{⊗e}`); (2) on the trivial line bundle it is polynomial evaluation: for `A = O_X`,
`F(g_0,…,g_N) = eval₂ g F` (through `O^{⊗e} ≅ O`). Together they give the local formula: if `A|_U ≅ O_U` and
`f_i = g_i ε`, then `F(f) = F(g)·ε^{⊗e}`; independence of the ordering (the symmetric action on tensor powers
of a line bundle is trivial) also follows locally from (2).
-/
/- `sectionPullbackAlong` is by definition the adjunction unit, and `ModuleSections.pullback` is its `Γ`-typed
reducible abbreviation: the proofs below use `simp only [sectionPullbackAlong_eq_pullback]` (to reach the
latter) or plain `unfold sectionPullbackAlong` (to reach the unit). -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

private theorem evalHomogeneousAtSections_pullback_monomial_zero {k : Type u} [Field k]
    {X Y : AlgebraicGeometry.Scheme.{u}}
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [Y.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (g : Y ⟶ X) [g.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (A : X.Modules) [A.IsLineBundle] (N : ℕ) (f : Fin (N + 1) → (A.val.obj (Opposite.op ⊤) : Type u))
    (q : Fin 0 → Fin (N + 1)) :
    (AlgebraicGeometry.Scheme.Modules.pullbackTensorPowIso g A 0).hom.app ⊤
        (sectionPullbackAlong g (evalHomogeneousAtSections.monomial A f 0 q)) =
      evalHomogeneousAtSections.monomial ((AlgebraicGeometry.Scheme.Modules.pullback g).obj A)
        (fun i => sectionPullbackAlong g (f i)) 0 q := by
  simp only [AlgebraicGeometry.Scheme.Modules.pullbackTensorPowIso,
    evalHomogeneousAtSections.monomial]
  change (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso g).hom.app ⊤
      (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
        (SheafOfModules.unit X.ringCatSheaf)).app ⊤
        (1 : X.ringCatSheaf.obj.obj (Opposite.op (⊤ : X.Opens)))) =
    (1 : Y.ringCatSheaf.obj.obj (Opposite.op (⊤ : Y.Opens)))
  letI : (SheafOfModules.pushforward.{u} g.toRingCatSheafHom).IsRightAdjoint :=
    (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction g).isRightAdjoint
  change AlgebraicGeometry.Scheme.Modules.Hom.app
      (SheafOfModules.pullbackObjUnitToUnit g.toRingCatSheafHom) ⊤
      (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
        (SheafOfModules.unit X.ringCatSheaf)).app ⊤
        (1 : X.ringCatSheaf.obj.obj (Opposite.op (⊤ : X.Opens)))) =
    (1 : Y.ringCatSheaf.obj.obj (Opposite.op (⊤ : Y.Opens)))
  exact AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback_unit_one g

private theorem tensorIsoTensorObj_sectionTensor {X : AlgebraicGeometry.Scheme.{u}}
    {M N : X.Modules} (s : (M.val.obj (Opposite.op ⊤) : Type u))
    (t : (N.val.obj (Opposite.op ⊤) : Type u)) :
    (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj M N).hom.app ⊤
        (sectionTensor s t) =
      AlgebraicGeometry.Scheme.Modules.tensorSections M N ⊤ s t := by
  rfl

private theorem tensorIsoTensorObj_inv_tensorSections {X : AlgebraicGeometry.Scheme.{u}}
    {M N : X.Modules} (s : (M.val.obj (Opposite.op ⊤) : Type u))
    (t : (N.val.obj (Opposite.op ⊤) : Type u)) :
    (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj M N).inv.val.app (Opposite.op ⊤)
        (AlgebraicGeometry.Scheme.Modules.tensorSections M N ⊤ s t) =
      sectionTensor s t := by
  let e := AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj M N
  have hinj : Function.Injective (fun z => (e.hom.val.app (Opposite.op ⊤)).hom z) := by
    intro a b hab
    have h := congrArg (fun φ => (φ.val.app (Opposite.op ⊤)).hom) e.hom_inv_id
    have h' := congrArg (fun φ => φ (a)) h
    have h'' := congrArg (fun φ => φ (b)) h
    change (e.inv.val.app (Opposite.op ⊤)).hom
        ((e.hom.val.app (Opposite.op ⊤)).hom a) = a at h'
    change (e.inv.val.app (Opposite.op ⊤)).hom
        ((e.hom.val.app (Opposite.op ⊤)).hom b) = b at h''
    calc
      a = (e.inv.val.app (Opposite.op ⊤)).hom
          ((e.hom.val.app (Opposite.op ⊤)).hom a) := h'.symm
      _ = (e.inv.val.app (Opposite.op ⊤)).hom
          ((e.hom.val.app (Opposite.op ⊤)).hom b) := congrArg _ hab
      _ = b := h''
  apply hinj
  have h := congrArg (fun φ => (φ.val.app (Opposite.op ⊤)).hom
      (AlgebraicGeometry.Scheme.Modules.tensorSections M N ⊤ s t)) e.inv_hom_id
  change (e.hom.val.app (Opposite.op ⊤)).hom
      ((e.inv.val.app (Opposite.op ⊤)).hom
        (AlgebraicGeometry.Scheme.Modules.tensorSections M N ⊤ s t)) =
    AlgebraicGeometry.Scheme.Modules.tensorSections M N ⊤ s t at h
  calc
    _ = AlgebraicGeometry.Scheme.Modules.tensorSections M N ⊤ s t := h
    _ = (e.hom.val.app (Opposite.op ⊤)).hom (sectionTensor s t) :=
      (tensorIsoTensorObj_sectionTensor s t).symm

private theorem evalHomogeneousAtSections_pullback_monomial {k : Type u} [Field k]
    {X Y : AlgebraicGeometry.Scheme.{u}}
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [Y.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (g : Y ⟶ X) [g.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (A : X.Modules) [A.IsLineBundle] {N : ℕ}
    (f : Fin (N + 1) → (A.val.obj (Opposite.op ⊤) : Type u)) :
    ∀ e (q : Fin e → Fin (N + 1)),
      (AlgebraicGeometry.Scheme.Modules.pullbackTensorPowIso g A e).hom.app ⊤
          (sectionPullbackAlong g (evalHomogeneousAtSections.monomial A f e q)) =
        evalHomogeneousAtSections.monomial ((AlgebraicGeometry.Scheme.Modules.pullback g).obj A)
          (fun i => sectionPullbackAlong g (f i)) e q := by
  intro e
  induction e with
  | zero =>
      intro q
      exact evalHomogeneousAtSections_pullback_monomial_zero (k := k) g A N f q
  | succ e ih =>
      intro q
      simp [AlgebraicGeometry.Scheme.Modules.pullbackTensorPowIso,
        evalHomogeneousAtSections.monomial, Iso.trans_hom]
      change (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj
          (AlgebraicGeometry.Scheme.Modules.tensorPow
            ((AlgebraicGeometry.Scheme.Modules.pullback g).obj A) e)
          ((AlgebraicGeometry.Scheme.Modules.pullback g).obj A)).inv.app ⊤
        ((CategoryTheory.MonoidalCategory.whiskerRightIso
          (AlgebraicGeometry.Scheme.Modules.pullbackTensorPowIso g A e)
          ((AlgebraicGeometry.Scheme.Modules.pullback g).obj A)).hom.app ⊤
          ((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj
            ((AlgebraicGeometry.Scheme.Modules.pullback g).obj (A.tensorPow e))
            ((AlgebraicGeometry.Scheme.Modules.pullback g).obj A)).hom.app ⊤
            ((AlgebraicGeometry.Scheme.Modules.pullbackTensorIso g (A.tensorPow e) A).hom.app ⊤
              (sectionPullbackAlong g
                (sectionTensor (evalHomogeneousAtSections.monomial A f e
                  (fun i => q i.castSucc)) (f (q (Fin.last e)))))))) = _
      rw [AlgebraicGeometry.Scheme.Modules.pullbackTensorIso_sectionTensor]
      rw [tensorIsoTensorObj_sectionTensor]
      have hwhisker :
          (CategoryTheory.MonoidalCategory.whiskerRightIso
            (AlgebraicGeometry.Scheme.Modules.pullbackTensorPowIso g A e)
            ((AlgebraicGeometry.Scheme.Modules.pullback g).obj A)).hom =
            CategoryTheory.MonoidalCategoryStruct.tensorHom
              (C := Y.Modules)
              (AlgebraicGeometry.Scheme.Modules.pullbackTensorPowIso g A e).hom
              (𝟙 ((AlgebraicGeometry.Scheme.Modules.pullback g).obj A)) := by
        rw [CategoryTheory.MonoidalCategory.tensorHom_id]
        rfl
      rw [hwhisker]
      change (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj
          (AlgebraicGeometry.Scheme.Modules.tensorPow ((AlgebraicGeometry.Scheme.Modules.pullback g).obj A) e)
          ((AlgebraicGeometry.Scheme.Modules.pullback g).obj A)).inv.val.app (Opposite.op ⊤)
        ((CategoryTheory.MonoidalCategoryStruct.tensorHom (C := Y.Modules)
          (AlgebraicGeometry.Scheme.Modules.pullbackTensorPowIso g A e).hom
          (𝟙 ((AlgebraicGeometry.Scheme.Modules.pullback g).obj A))).val.app (Opposite.op ⊤)
          (AlgebraicGeometry.Scheme.Modules.tensorSections
            ((AlgebraicGeometry.Scheme.Modules.pullback g).obj (A.tensorPow e))
            ((AlgebraicGeometry.Scheme.Modules.pullback g).obj A) ⊤
            (sectionPullbackAlong g (evalHomogeneousAtSections.monomial A f e
              (fun i => q i.castSucc)))
            (sectionPullbackAlong g (f (q (Fin.last e)))))) = _
      rw [AlgebraicGeometry.Scheme.Modules.tensorHom_tensorSections]
      have hi := ih (fun i => q i.castSucc)
      change (ConcreteCategory.hom
          ((AlgebraicGeometry.Scheme.Modules.pullbackTensorPowIso g A e).hom.val.app (Opposite.op ⊤)))
          (sectionPullbackAlong g (evalHomogeneousAtSections.monomial A f e
            (fun i => q i.castSucc))) = _ at hi
      rw [hi]
      rw [tensorIsoTensorObj_inv_tensorSections]
      change sectionTensor
        (evalHomogeneousAtSections.monomial ((AlgebraicGeometry.Scheme.Modules.pullback g).obj A)
          (fun i => sectionPullbackAlong g (f i)) e fun i => q i.castSucc)
        (sectionPullbackAlong g (f (q (Fin.last e)))) = _
      rfl

private theorem sectionPullbackAlong_sum {X Y : AlgebraicGeometry.Scheme.{u}}
    (g : Y ⟶ X) {M : X.Modules} {ι : Type*} (s : Finset ι)
    (h : ι → (M.val.obj (Opposite.op ⊤) : Type u)) :
    sectionPullbackAlong g (∑ i ∈ s, h i) =
      ∑ i ∈ s, sectionPullbackAlong g (h i) := by
  unfold sectionPullbackAlong
  change (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M).val.app
    (Opposite.op ⊤)).hom (∑ i ∈ s, h i) = _
  rw [map_sum]
  rfl

private theorem sectionPullbackAlong_smul {X Y : AlgebraicGeometry.Scheme.{u}}
    (g : Y ⟶ X) {M : X.Modules}
    (a : Γ(X, ⊤))
    (s : (M.val.obj (Opposite.op ⊤) : Type u)) :
    sectionPullbackAlong g
        ((show X.ringCatSheaf.obj.obj (Opposite.op ⊤) from a) • s) =
      (show Y.ringCatSheaf.obj.obj (Opposite.op ⊤) from g.appTop a) •
        sectionPullbackAlong g s := by
  unfold sectionPullbackAlong
  exact (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M).val.app
    (Opposite.op ⊤)).hom.map_smul _ s

private theorem base_scalar_pullback {k : Type u} [Field k]
    {X Y : AlgebraicGeometry.Scheme.{u}}
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [Y.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (g : Y ⟶ X) [g.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (c : k) :
    g.appTop (((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
      (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)).appTop).hom c) =
      ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
        (Y ↘ AlgebraicGeometry.Spec (CommRingCat.of k)).appTop).hom c := by
  have hbase : g ≫ (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      (Y ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    (inferInstance : g.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))).1
  have hbaseTop : (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)).appTop ≫ g.appTop =
      (Y ↘ AlgebraicGeometry.Spec (CommRingCat.of k)).appTop := by
    rw [← AlgebraicGeometry.Scheme.Hom.comp_appTop, hbase]
  change g.appTop ((X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)).appTop
      ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c)) =
    (Y ↘ AlgebraicGeometry.Spec (CommRingCat.of k)).appTop
      ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c)
  exact congrArg (fun h => h ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom c))
    (congrArg (fun h => h.hom) hbaseTop)

private theorem unitTensorPowIso_monomial {k : Type u} [Field k]
    {X : AlgebraicGeometry.Scheme.{u}}
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    {N : ℕ} (g : Fin (N + 1) → Γ(X, ⊤)) :
    ∀ e (q : Fin e → Fin (N + 1)),
      (AlgebraicGeometry.Scheme.Modules.unitTensorPowIso X e).hom.app ⊤
      (evalHomogeneousAtSections.monomial
          (SheafOfModules.unit X.ringCatSheaf)
          (fun i => (g i : (SheafOfModules.unit X.ringCatSheaf).val.obj (Opposite.op ⊤))) e q) =
      ∏ i, (g (q i) : (SheafOfModules.unit X.ringCatSheaf).val.obj (Opposite.op ⊤)) := by
  intro e
  induction e with
  | zero =>
      intro q
      simp [AlgebraicGeometry.Scheme.Modules.unitTensorPowIso,
        evalHomogeneousAtSections.monomial]
      rfl
  | succ e ih =>
      intro q
      simp [AlgebraicGeometry.Scheme.Modules.unitTensorPowIso,
        evalHomogeneousAtSections.monomial]
      let U : X.Modules := SheafOfModules.unit X.ringCatSheaf
      change (CategoryTheory.MonoidalCategoryStruct.leftUnitor U).hom.app ⊤
        ((CategoryTheory.MonoidalCategory.whiskerRightIso
          (AlgebraicGeometry.Scheme.Modules.unitTensorPowIso X e ≪≫
            CategoryTheory.eqToIso (show U =
              CategoryTheory.MonoidalCategoryStruct.tensorUnit X.Modules by
                dsimp [U]; with_unfolding_all rfl)) U).hom.app ⊤
          ((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj
            (AlgebraicGeometry.Scheme.Modules.tensorPow U e) U).hom.app ⊤
            (sectionTensor
              (evalHomogeneousAtSections.monomial U (fun i => g i) e
                (fun i => q i.castSucc))
              (g (q (Fin.last e)))))) = _
      have hbridge := tensorIsoTensorObj_sectionTensor
        (M := U.tensorPow e) (N := U)
        (evalHomogeneousAtSections.monomial U (fun i => g i) e
          (fun i => q i.castSucc)) (g (q (Fin.last e)))
      rw [hbridge]
      have hwhisker :
          (CategoryTheory.MonoidalCategory.whiskerRightIso
            (AlgebraicGeometry.Scheme.Modules.unitTensorPowIso X e ≪≫
              CategoryTheory.eqToIso (show U =
                CategoryTheory.MonoidalCategoryStruct.tensorUnit X.Modules by
                  dsimp [U]; with_unfolding_all rfl)) U).hom =
            CategoryTheory.MonoidalCategoryStruct.tensorHom
              (C := X.Modules)
              (AlgebraicGeometry.Scheme.Modules.unitTensorPowIso X e ≪≫
                CategoryTheory.eqToIso (show U =
                  CategoryTheory.MonoidalCategoryStruct.tensorUnit X.Modules by
                    dsimp [U]; with_unfolding_all rfl)).hom
              (𝟙 U) := by
        rw [CategoryTheory.MonoidalCategory.tensorHom_id]
        rfl
      rw [hwhisker]
      change (CategoryTheory.MonoidalCategoryStruct.leftUnitor U).hom.val.app (Opposite.op ⊤)
        ((CategoryTheory.MonoidalCategoryStruct.tensorHom (C := X.Modules)
          (AlgebraicGeometry.Scheme.Modules.unitTensorPowIso X e ≪≫
            CategoryTheory.eqToIso (show U =
              CategoryTheory.MonoidalCategoryStruct.tensorUnit X.Modules by
                dsimp [U]; with_unfolding_all rfl)).hom
          (𝟙 U)).val.app (Opposite.op ⊤)
          ((U.tensorPow e).tensorSections U ⊤
            (evalHomogeneousAtSections.monomial U (fun i => g i) e
              (fun i => q i.castSucc)) (g (q (Fin.last e))))) = _
      let E := AlgebraicGeometry.Scheme.Modules.unitTensorPowIso X e ≪≫
        CategoryTheory.eqToIso (show U =
          CategoryTheory.MonoidalCategoryStruct.tensorUnit X.Modules by
            dsimp [U]; with_unfolding_all rfl)
      have htensor := AlgebraicGeometry.Scheme.Modules.tensorHom_tensorSections
        (φ := E.hom) (ψ := (𝟙 U)) ⊤
        (evalHomogeneousAtSections.monomial U (fun i => g i) e
          (fun i => q i.castSucc)) (g (q (Fin.last e)))
      rw [htensor]
      change (CategoryTheory.MonoidalCategoryStruct.leftUnitor U).hom.app ⊤
        ((CategoryTheory.MonoidalCategoryStruct.tensorUnit X.Modules).tensorSections U ⊤ _ _) = _
      have hleft := AlgebraicGeometry.Scheme.Modules.leftUnitor_app_tensorSections U ⊤
        ((ConcreteCategory.hom (E.hom.val.app (Opposite.op ⊤)))
          (evalHomogeneousAtSections.monomial U (fun i => g i) e
            (fun i => q i.castSucc)))
        ((ConcreteCategory.hom (((𝟙 U : U ⟶ U).val.app (Opposite.op ⊤))))
          (g (q (Fin.last e))))
      rw [hleft]
      dsimp [E]
      have hi := ih (fun i => q i.castSucc)
      change (ConcreteCategory.hom
          ((AlgebraicGeometry.Scheme.Modules.unitTensorPowIso X e).hom.val.app
            (Opposite.op ⊤)))
          (evalHomogeneousAtSections.monomial U (fun i => g i) e
            (fun i => q i.castSucc)) = _ at hi
      have hE :
          (ConcreteCategory.hom
            ((AlgebraicGeometry.Scheme.Modules.unitTensorPowIso X e ≪≫
              CategoryTheory.eqToIso (show U =
                CategoryTheory.MonoidalCategoryStruct.tensorUnit X.Modules by
                  dsimp [U]; with_unfolding_all rfl)).hom.val.app (Opposite.op ⊤)))
            (evalHomogeneousAtSections.monomial U (fun i => g i) e
              (fun i => q i.castSucc)) =
          (ConcreteCategory.hom
            ((AlgebraicGeometry.Scheme.Modules.unitTensorPowIso X e).hom.val.app
              (Opposite.op ⊤)))
            (evalHomogeneousAtSections.monomial U (fun i => g i) e
              (fun i => q i.castSucc)) := by
        rfl
      rw [hE, hi]
      have hid :
          (ConcreteCategory.hom ((𝟙 U : U ⟶ U).val.app (Opposite.op ⊤)))
              (g (q (Fin.last e))) = g (q (Fin.last e)) := by
        rfl
      rw [hid]
      rw [Fin.prod_univ_castSucc]
      rfl

/- `θ` is the canonical isomorphism `pullbackTensorPowIso`, not an existentially quantified one. -/

theorem evalHomogeneousAtSections_pullback {k : Type u} [Field k] {X Y : AlgebraicGeometry.Scheme.{u}}
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] [Y.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (g : Y ⟶ X) [g.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))] (A : X.Modules) [A.IsLineBundle]
    {N e : ℕ} (F : MvPolynomial (Fin (N + 1)) k) (hF : F.IsHomogeneous e)
    (f : Fin (N + 1) → (A.val.obj (Opposite.op ⊤) : Type u)) :
    (AlgebraicGeometry.Scheme.Modules.pullbackTensorPowIso g A e).hom.app ⊤
        (sectionPullbackAlong g (evalHomogeneousAtSections A F hF f)) =
      evalHomogeneousAtSections ((AlgebraicGeometry.Scheme.Modules.pullback g).obj A) F hF
        (fun i => sectionPullbackAlong g (f i)) := by
  simp only [evalHomogeneousAtSections]
  rw [sectionPullbackAlong_sum]
  change (((AlgebraicGeometry.Scheme.Modules.pullbackTensorPowIso g A e).hom.val.app
    (Opposite.op ⊤)).hom) (∑ i ∈ F.support.attach, _) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro x hx
  have hsmul := sectionPullbackAlong_smul (g := g)
    (a := ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
      (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)).appTop).hom
      (MvPolynomial.coeff (↑x) F))
    (s := evalHomogeneousAtSections.monomial A f e
      (evalHomogeneousAtSections.indices (↑x) (hF (MvPolynomial.mem_support_iff.mp x.property))))
  rw [hsmul]
  rw [map_smul]
  rw [base_scalar_pullback]
  congr 1
  exact evalHomogeneousAtSections_pullback_monomial (k := k) g A f e
    (evalHomogeneousAtSections.indices (↑x)
      (hF (MvPolynomial.mem_support_iff.mp x.property)))

/- `θ` is the canonical isomorphism `unitTensorPowIso` (`O^{⊗e} ≅ O`, iterated left unitor). -/

open AlgebraicGeometry in

theorem evalHomogeneousAtSections_unit {k : Type u} [Field k] {X : AlgebraicGeometry.Scheme.{u}}
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {N e : ℕ}
    (F : MvPolynomial (Fin (N + 1)) k) (hF : F.IsHomogeneous e) (g : Fin (N + 1) → Γ(X, ⊤)) :
    (AlgebraicGeometry.Scheme.Modules.unitTensorPowIso X e).hom.app ⊤
        (evalHomogeneousAtSections (SheafOfModules.unit X.ringCatSheaf) F hF g) =
      MvPolynomial.eval₂ ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
        (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)).appTop).hom g F := by
  simp only [evalHomogeneousAtSections]
  rw [MvPolynomial.eval₂_eq]
  conv_rhs => rw [← F.support.sum_attach]
  change (((AlgebraicGeometry.Scheme.Modules.unitTensorPowIso X e).hom.val.app
    (Opposite.op ⊤)).hom) (∑ i ∈ F.support.attach, _) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro x hx
  change (((AlgebraicGeometry.Scheme.Modules.unitTensorPowIso X e).hom.val.app
      (Opposite.op ⊤)).hom)
      ((show X.ringCatSheaf.obj.obj (Opposite.op ⊤) from
        ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
          (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)).appTop).hom
          (MvPolynomial.coeff (↑x) F)) • _ ) = _
  rw [map_smul]
  have hm := unitTensorPowIso_monomial (k := k) g e
    (evalHomogeneousAtSections.indices (↑x)
      (hF (MvPolynomial.mem_support_iff.mp x.property)))
  change (ConcreteCategory.hom
      ((AlgebraicGeometry.Scheme.Modules.unitTensorPowIso X e).hom.val.app
        (Opposite.op ⊤)))
      (evalHomogeneousAtSections.monomial (SheafOfModules.unit X.ringCatSheaf) g e
        (evalHomogeneousAtSections.indices (↑x)
          (hF (MvPolynomial.mem_support_iff.mp x.property)))) = _ at hm
  rw [hm]
  change ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
      (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)).appTop).hom
      (MvPolynomial.coeff (↑x) F) *
      (∏ i, g (evalHomogeneousAtSections.indices (↑x)
        (hF (MvPolynomial.mem_support_iff.mp x.property)) i)) = _
  let α : Fin (N + 1) →₀ ℕ := ↑x
  let hα : Finsupp.weight 1 α = e := hF (MvPolynomial.mem_support_iff.mp x.property)
  let s := α.toMultiset.sort (· ≤ ·)
  have hslen : s.length = e := by
    dsimp [s]
    rw [Multiset.length_sort, Finsupp.card_toMultiset, ← hα, Finsupp.weight_apply]
    simp [Finsupp.sum]
  have hprod : (∏ i : Fin e, g (s.get (i.cast hslen.symm))) = (s.map g).prod := by
    calc
      (∏ i : Fin e, g (s.get (i.cast hslen.symm))) =
          ∏ j : Fin s.length, g (s.get j) := by
        apply Fintype.prod_equiv (finCongr hslen.symm)
        intro i
        rfl
      _ = (s.map g).prod := Fin.prod_univ_fun_getElem s g
  have hprod' : (∏ i : Fin e, g (evalHomogeneousAtSections.indices (↑x)
      (hF (MvPolynomial.mem_support_iff.mp x.property)) i)) = (s.map g).prod := by
    simpa [evalHomogeneousAtSections.indices, s, α] using hprod
  have hsort : (s.map g).prod = (α.toMultiset.map g).prod := by
    have hs : (s : Multiset (Fin (N + 1))) = α.toMultiset := by
      dsimp [s]
      exact Multiset.sort_eq _ _
    have hmap := congrArg (Multiset.map g) hs
    rw [← Multiset.prod_coe]
    rw [← Multiset.map_coe]
    exact congrArg Multiset.prod hmap
  rw [hprod', hsort]
  congr 1
  simpa [Finsupp.toFinset_toMultiset, Finsupp.count_toMultiset] using
    (Finset.prod_multiset_map_count (α.toMultiset) g)

end
