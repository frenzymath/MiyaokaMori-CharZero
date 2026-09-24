import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.DualCoevZigzag
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPullbackMonoidal
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPushforwardLaxMonoidal
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.SectionPullbackAlong

/-! # The triangle identities on the total space, transported along the pullback

**The two triangle identities on `T`, in unfolded form.** For `g : T ⟶ X` and `V` locally free of finite
type on `X`, the pair `(g^*coev_V, g^*ev_V)` (conjugated by the strong monoidal structure of `g^*`:
`c_T = ε ≫ g^*c ≫ δ`, `ev_T = μ ≫ g^*ev ≫ η`) again satisfies both zigzag identities
(`Zigzag.Z1_map` / `Zigzag.Z2_map` applied to `zigzag1` / `zigzag2` of `DualCoevZigzag`), hence by the abstract
`Zigzag.lemmaB` / `Zigzag.lemmaA`:

* `triangle1`: for `ψ : g^*V^∨ ⟶ O_T`, the functional attached to the section `(ψ ⊗ id)(g^*coev)` is `ψ`;
* `triangle2`: for `s ∈ Γ(T, g^*V)`, the section `(ψ_s ⊗ id)(g^*coev)` with `ψ_s = ⟨-, s⟩` is `s`.

Both are stated **exactly in the form obtained by unfolding** `totalSpace.functionalOfSectionCore` and
`totalSpace.sectionOfFunctionalCore` (`TotalSpaceSectionConstructions`), so that the
theorems `functionalOfSectionCore_sectionOfFunctionalCore` / `sectionOfFunctionalCore_functionalOfSectionCore`
there are `exact` applications of these. The bridge between the section level and the morphism level is
`Γ(T, M) ≃ (O_T ⟶ M)` (`homOfTopSection_app_top`, `homOfTopSection_sectionPullbackAlong`:
`homOfTopSection (g^*x) = (pullbackUnitIso g).inv ≫ g^*(homOfTopSection x)`).

Spelling note. `functionalOfSectionCore` is written with `internalHomEval V O_X : 𝓗om(V,O_X) ⊗ V ⟶ O_X`, while
everything here uses `dualEv V : V^∨ ⊗ V ⟶ O_X`. Unifying the *types*
`V^∨ = 𝓗om(V, O_X)` costs ~7 s (see `DualEvSections`); but `dualEv V` is *by definition* the term
`internalHomEval V O_X` (`def dualEv … := by apply internalHomEval …`), and in the elaborated body of
`functionalOfSectionCore` the implicit object argument of `Functor.map` is already `V^∨ ⊗ V` (expected-type
propagation), so `(pullback g).map (dualEv V)` and the term in `functionalOfSectionCore` are equal by a
single δ-step — the `exact` in `TotalSpaceSectionConstructions` is cheap. (Stating these theorems with
`internalHomEval` instead costs ~15 s per statement, measured.)

References: Stacks 01CM/01CN, 01LQ.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
open scoped CategoryTheory.MonoidalCategory

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules.DualZigzag

variable {X T : AlgebraicGeometry.Scheme.{u}}

/-! ### `Γ(T, M) ≃ (O_T ⟶ M)` and naturality -/

/-- `homOfTopSection` is natural: `homOfTopSection (φ x) = homOfTopSection x ≫ φ`. -/
theorem homOfTopSection_app_top {M N : T.Modules} (φ : M ⟶ N) (x : Γ(M, ⊤)) :
    homOfTopSection N (φ.app ⊤ x) = homOfTopSection M x ≫ φ := by
  apply (unitHomEquivTop N).injective
  have h1 : unitHomEquivTop N (homOfTopSection N (φ.app ⊤ x)) = φ.app ⊤ x :=
    (unitHomEquivTop N).apply_symm_apply _
  have h2 : unitHomEquivTop M (homOfTopSection M x) = x := (unitHomEquivTop M).apply_symm_apply x
  have h3 : unitHomEquivTop N (homOfTopSection M x ≫ φ) =
      φ.app ⊤ (unitHomEquivTop M (homOfTopSection M x)) := rfl
  rw [h1, h3, h2]

/-- The adjoint transpose of `pullbackUnitIso g` is Mathlib's `unitToPushforwardObjUnit` (`g^♯` on
sections); copy of `homEquiv_pullbackUnitIso_hom_eq` in `TotalSpaceSectionConstructions`. -/
theorem homEquiv_pullbackUnitIso_hom_eq' (g : T ⟶ X) :
    (pullbackPushforwardAdjunction g).homEquiv _ _ (pullbackUnitIso g).hom =
      SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom := by
  rw [← pullback_η]
  exact (congrArg _ rfl).trans ((Equiv.apply_symm_apply _ _).trans (pushforwardLaxMonoidal_ε g))

/-- `pullbackUnitIso g` sends `η(1)` to `1`. -/
theorem pullbackUnitIso_hom_app_unit_one (g : T ⟶ X) :
    (pullbackUnitIso g).hom.app (g ⁻¹ᵁ ⊤)
        (((pullbackPushforwardAdjunction g).unit.app (SheafOfModules.unit X.ringCatSheaf)).app ⊤
          (1 : Γ(X, ⊤))) = (1 : Γ(T, g ⁻¹ᵁ ⊤)) := by
  have h1 : ((pullbackPushforwardAdjunction g).homEquiv _ _ (pullbackUnitIso g).hom).app ⊤
      (1 : Γ(X, ⊤)) = (1 : Γ(T, g ⁻¹ᵁ ⊤)) := by
    rw [homEquiv_pullbackUnitIso_hom_eq']
    exact map_one (g.app ⊤).hom
  have h2 : (pullbackPushforwardAdjunction g).homEquiv _ _ (pullbackUnitIso g).hom =
      (pullbackPushforwardAdjunction g).unit.app _ ≫ (pushforward g).map (pullbackUnitIso g).hom :=
    Adjunction.homEquiv_unit (pullbackPushforwardAdjunction g) _ _ (pullbackUnitIso g).hom
  have h3 := congrArg (fun k : SheafOfModules.unit X.ringCatSheaf ⟶
      (pushforward g).obj (SheafOfModules.unit T.ringCatSheaf) =>
    AlgebraicGeometry.Scheme.Modules.Hom.app k ⊤ (1 : Γ(X, ⊤))) h2
  exact h3.symm.trans h1

/-- The morphism `O_T ⟶ g^*M` attached to a pulled-back global section `g^*x` is
`(pullbackUnitIso g).inv ≫ g^*(homOfTopSection x)`. -/
theorem homOfTopSection_sectionPullbackAlong (g : T ⟶ X) (M : X.Modules) (x : Γ(M, ⊤)) :
    homOfTopSection ((pullback g).obj M) (sectionPullbackAlong g x) =
      (pullbackUnitIso g).inv ≫ (pullback g).map (homOfTopSection M x) := by
  apply (unitHomEquivTop _).injective
  have h1 : unitHomEquivTop _ (homOfTopSection ((pullback g).obj M) (sectionPullbackAlong g x)) =
      sectionPullbackAlong g x := (unitHomEquivTop _).apply_symm_apply _
  rw [h1]
  have hu : (pullbackUnitIso g).inv.app ⊤ (unitOne (⊤ : T.Opens)) =
      ((pullbackPushforwardAdjunction g).unit.app (SheafOfModules.unit X.ringCatSheaf)).app ⊤
        (unitOne (⊤ : X.Opens)) :=
    iso_inv_app_eq _ _ (pullbackUnitIso_hom_app_unit_one g)
  have hnat := congrArg (fun k => AlgebraicGeometry.Scheme.Modules.Hom.app k ⊤ (unitOne (⊤ : X.Opens)))
    ((pullbackPushforwardAdjunction g).unit.naturality (homOfTopSection M x))
  have hx : AlgebraicGeometry.Scheme.Modules.Hom.app (homOfTopSection M x) ⊤ (unitOne (⊤ : X.Opens)) = x :=
    (unitHomEquivTop M).apply_symm_apply x
  have hnat' : ((pullbackPushforwardAdjunction g).unit.app M).app ⊤
      (AlgebraicGeometry.Scheme.Modules.Hom.app (homOfTopSection M x) ⊤ (unitOne (⊤ : X.Opens))) =
      ((pullback g).map (homOfTopSection M x)).app (g ⁻¹ᵁ ⊤)
        (((pullbackPushforwardAdjunction g).unit.app (SheafOfModules.unit X.ringCatSheaf)).app ⊤
          (unitOne (⊤ : X.Opens))) := hnat
  exact ((congrArg (fun z => ((pullbackPushforwardAdjunction g).unit.app M).app ⊤ z) hx).symm.trans hnat').trans
    (congrArg (fun z => ((pullback g).map (homOfTopSection M x)).app (g ⁻¹ᵁ ⊤) z) hu.symm)

/-! ### The strong monoidal structure of `g^*` in the names of `ModulesPullbackMonoidal` -/

theorem η_eq (g : T ⟶ X) :
    Functor.OplaxMonoidal.η (pullback g) (self := Functor.Monoidal.toOplaxMonoidal) =
      (pullbackUnitIso g).hom := pullback_η g

theorem ε_eq (g : T ⟶ X) :
    Functor.LaxMonoidal.ε (pullback g) = (pullbackUnitIso g).inv := pullback_ε_eq g

theorem δ_eq (g : T ⟶ X) (M N : X.Modules) :
    Functor.OplaxMonoidal.δ (pullback g) (self := Functor.Monoidal.toOplaxMonoidal) M N =
      pullbackTensorObjHom g M N := rfl

theorem μ_eq (g : T ⟶ X) (M N : X.Modules) :
    Functor.LaxMonoidal.μ (pullback g) M N = (pullbackTensorObjIso g M N).inv := pullback_μ_eq g M N

/-! ### The triangle identities on `T` -/

/-- **Triangle identity (coev then ev), unfolded form** of
`totalSpace.functionalOfSectionCore V T (totalSpace.sectionOfFunctionalCore V T ψ) = ψ`. -/
theorem triangle1 (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType] (T : CategoryTheory.Over X)
    (ψ : (pullback T.hom).obj (dual V) ⟶ 𝟙_ T.left.Modules) :
    (ρ_ ((pullback T.hom).obj (dual V))).inv ≫
      ((pullback T.hom).obj (dual V) ◁ homOfTopSection ((pullback T.hom).obj V)
        (((pullback T.hom).map (tensorIsoTensorObj (dual V) V).hom ≫ pullbackTensorObjHom T.hom (dual V) V ≫
          (ψ ▷ (pullback T.hom).obj V) ≫ (λ_ ((pullback T.hom).obj V)).hom).app ⊤
          (sectionPullbackAlong T.hom (coevSection V)))) ≫
      (pullbackTensorObjIso T.hom (dual V) V).inv ≫
      (pullback T.hom).map (dualEv V) ≫
      (pullbackUnitIso T.hom).hom = ψ := by
  have key := CategoryTheory.MonoidalCategory.Zigzag.lemmaB
    (CategoryTheory.MonoidalCategory.Zigzag.Z1_map (pullback T.hom) (zigzag1 V)) ψ
  rw [ε_eq, η_eq, δ_eq, μ_eq] at key
  have hm : (pullback T.hom).map (coevHom V) =
      (pullback T.hom).map (homOfTopSection _ (coevSection V)) ≫
        (pullback T.hom).map (tensorIsoTensorObj (dual V) V).hom := Functor.map_comp _ _ _
  rw [hm] at key
  have hA := homOfTopSection_app_top ((pullback T.hom).map (tensorIsoTensorObj (dual V) V).hom ≫
    pullbackTensorObjHom T.hom (dual V) V ≫ (ψ ▷ (pullback T.hom).obj V) ≫ (λ_ ((pullback T.hom).obj V)).hom)
    (sectionPullbackAlong T.hom (coevSection V))
  have hB := homOfTopSection_sectionPullbackAlong T.hom (tensor (dual V) V) (coevSection V)
  rw [hB] at hA
  rw [hA]
  simp only [Category.assoc] at key ⊢
  exact key

/-- **Triangle identity (ev then coev), unfolded form** of
`totalSpace.sectionOfFunctionalCore V T (totalSpace.functionalOfSectionCore V T s) = s`. -/
theorem triangle2 (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType] (T : CategoryTheory.Over X)
    (s : Γ((pullback T.hom).obj V, ⊤)) :
    ((pullback T.hom).map (tensorIsoTensorObj (dual V) V).hom ≫ pullbackTensorObjHom T.hom (dual V) V ≫
      (((ρ_ ((pullback T.hom).obj (dual V))).inv ≫
          ((pullback T.hom).obj (dual V) ◁ homOfTopSection ((pullback T.hom).obj V) s) ≫
          (pullbackTensorObjIso T.hom (dual V) V).inv ≫
          (pullback T.hom).map (dualEv V) ≫
          (pullbackUnitIso T.hom).hom : (pullback T.hom).obj (dual V) ⟶ 𝟙_ T.left.Modules) ▷
        (pullback T.hom).obj V) ≫
      (λ_ ((pullback T.hom).obj V)).hom).app ⊤ (sectionPullbackAlong T.hom (coevSection V)) = s := by
  have key := CategoryTheory.MonoidalCategory.Zigzag.lemmaA
    (CategoryTheory.MonoidalCategory.Zigzag.Z2_map (pullback T.hom) (zigzag2 V))
    (homOfTopSection ((pullback T.hom).obj V) s)
  rw [ε_eq, η_eq, δ_eq, μ_eq] at key
  have hm : (pullback T.hom).map (coevHom V) =
      (pullback T.hom).map (homOfTopSection _ (coevSection V)) ≫
        (pullback T.hom).map (tensorIsoTensorObj (dual V) V).hom := Functor.map_comp _ _ _
  rw [hm] at key
  apply (unitHomEquivTop ((pullback T.hom).obj V)).symm.injective
  have hA := homOfTopSection_app_top ((pullback T.hom).map (tensorIsoTensorObj (dual V) V).hom ≫
    pullbackTensorObjHom T.hom (dual V) V ≫
      (((ρ_ ((pullback T.hom).obj (dual V))).inv ≫
          ((pullback T.hom).obj (dual V) ◁ homOfTopSection ((pullback T.hom).obj V) s) ≫
          (pullbackTensorObjIso T.hom (dual V) V).inv ≫
          (pullback T.hom).map (dualEv V) ≫
          (pullbackUnitIso T.hom).hom : (pullback T.hom).obj (dual V) ⟶ 𝟙_ T.left.Modules) ▷
        (pullback T.hom).obj V) ≫
      (λ_ ((pullback T.hom).obj V)).hom) (sectionPullbackAlong T.hom (coevSection V))
  have hB := homOfTopSection_sectionPullbackAlong T.hom (tensor (dual V) V) (coevSection V)
  rw [hB] at hA
  refine hA.trans ?_
  simp only [Category.assoc] at key ⊢
  exact key

end AlgebraicGeometry.Scheme.Modules.DualZigzag

end
