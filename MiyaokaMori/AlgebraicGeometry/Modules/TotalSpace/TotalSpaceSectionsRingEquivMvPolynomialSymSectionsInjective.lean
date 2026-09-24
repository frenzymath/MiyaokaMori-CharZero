import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.TotalSpaceSectionsRingEquivMvPolynomialSymSectionsSurjective
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotalSpaceSectionConstructions
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.PullbackSectionsNativeBaseChange

/-! # The section ring of `Sym W` on an affine open is the symmetric algebra of the sections

For `W` quasi-coherent on a scheme `X` and `U ⊆ X` an affine open, write `R := Γ(X, U)`, `N := Γ(U, W)`,
`A(U) := Γ(U, Sym W) = (symGradedAlgebra W).total.sectionsRing U` (an `R`-algebra through `sectionsUnit`) and
`ι_U := symGenTotalLinearMap W U : N →ₗ[R] A(U)` (degree-one inclusion).

* `symGradedAlgebra_lift_symGenTotalLinearMap_surjective` (companion module): `lift ι_U : Sym_R N → A(U)` is
  surjective.
* `symGradedAlgebra_exists_algHom_retraction_symGenTotalLinearMap`: there is an
  `R`-algebra map `G : A(U) → Sym_R N` with `G (ι_U n) = ι n`. Then `G ∘ lift ι_U = id` (`SymmetricAlgebra.algHom_ext`),
  so `lift ι_U` is injective (`symGradedAlgebra_lift_symGenTotalLinearMap_injective`).
* `symGradedAlgebra_sectionsRing_isSymmetricAlgebra_of_retraction`: both halves give `IsSymmetricAlgebra ι_U`
  (the statement of `SymGradedAlgebraSectionsIsSymmetricAlgebra`, whose proof is this one line).

## The retraction

`G` is `Γ(U, -)` of an `O_X`-algebra map `Φ : Sym W → g_* O_T`, where `T := Spec B`, `B := Sym_R N` and
`g : T → X` is `Spec.map (algebraMap R B) ≫ U.fromSpec`, followed by `Γ(U, g_* O_T) = Γ(T, g⁻¹U) → Γ(T, ⊤) ≅ B`
(`g⁻¹U = ⊤`, `Scheme.ΓSpecIso`).

* `symAlgebraMapOfFunctional g W ψ : Sym W → g_* O_T` for any `ψ : g^* W → O_T` — the general-`W` version of
  `totalSpace.algebraMapOfFunctionalCore` (`TotalSpaceSectionConstructions`, there written for `W = V^∨`):
  degreewise `homEquiv (symGradedPullbackDesc g ψ m ≫ unitPowCollapse T m)`. It is an algebra map
  (`symAlgebraMapOfFunctional_isAlgebraMap`, from `mul_homEquiv_symGradedPullbackDesc_aux` and
  `pullback_map_one_symGradedPullbackDesc_zero`, which were already stated for arbitrary quasi-coherent `W`), its unit
  is `g^♯` (`symAlgebraMapOfFunctional_one_comp`) and its degree-one part is `homEquiv ψ`
  (`symGen_ι_symAlgebraMapOfFunctional`).
* `ψ` comes from the affine tilde adjunction on `T` (`AffineTilde.exists_hom_of_linear`) applied to the
  `Γ(T, ⊤)`-linear map `Γ(T, g^*W) → Γ(T, ⊤)` obtained by transporting `B ⊗_R N → B`, `b ⊗ n ↦ b · ι n`, along the
  base-change isomorphism `Γ(T, ⊤) ⊗_R N ≅ Γ(T, g^*W)` (`isIso_transpose_pullbackSectionsNative`, Stacks 01I9).
* `specMap_fromSpec_appLE_top_comp_ΓSpecIso`: the ring map `R → Γ(T, ⊤)` induced by `g` is `algebraMap R B` under
  `ΓSpecIso` (`fromSpec_app_self`, `ΓSpecIso_naturality`); this gives `G (algebraMap r) = algebraMap r`.

References: Bourbaki Algebra III §6 no. 6; Stacks 01CG (Sym of a quasi-coherent module), 01I8/01I9 (quasi-coherent
modules on an affine scheme are determined by their global sections; base change of sections), 01LQ (maps to a
relative Spec are algebra maps).
-/
set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry CategoryTheory.MonoidalCategory

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

section SymAlgebraMap

variable {T : AlgebraicGeometry.Scheme.{u}} (g : T ⟶ X) (W : X.Modules)

/-- The `O_X`-algebra map `Sym W → g_* O_T` attached to a functional `ψ : g^* W → O_T`. -/
def symAlgebraMapOfFunctional (ψ : (pullback g).obj W ⟶ SheafOfModules.unit T.ringCatSheaf) :
    (symGradedAlgebra W).total.carrier ⟶ (pushforward g).obj (SheafOfModules.unit T.ringCatSheaf) :=
  Sigma.desc fun m ↦ (pullbackPushforwardAdjunction g).homEquiv _ _
    (symGradedPullbackDesc g ψ m ≫ unitPowCollapse T m)

theorem ι_symAlgebraMapOfFunctional (ψ : (pullback g).obj W ⟶ SheafOfModules.unit T.ringCatSheaf) (k : ℕ) :
    Sigma.ι (symGradedAlgebra W).part k ≫ symAlgebraMapOfFunctional g W ψ =
      (pullbackPushforwardAdjunction g).homEquiv _ _ (symGradedPullbackDesc g ψ k ≫ unitPowCollapse T k) :=
  Sigma.ι_desc _ _

theorem symAlgebraMapOfFunctional_mul_comp [hq : W.IsQuasicoherent]
    (ψ : (pullback g).obj W ⟶ SheafOfModules.unit T.ringCatSheaf) :
    (symGradedAlgebra W).total.mul ≫ symAlgebraMapOfFunctional g W ψ =
      (symAlgebraMapOfFunctional g W ψ ⊗ₘ symAlgebraMapOfFunctional g W ψ) ≫ pushforwardUnitMul g := by
  apply tensorObj_sigma_hom_ext
  intro m n
  have e1 : (Sigma.ι (symGradedAlgebra W).part m ⊗ₘ Sigma.ι (symGradedAlgebra W).part n) ≫
        (symGradedAlgebra W).total.mul ≫ symAlgebraMapOfFunctional g W ψ =
      (symGradedAlgebra W).mul m n ≫ Sigma.ι (symGradedAlgebra W).part (m + n) ≫
        symAlgebraMapOfFunctional g W ψ :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun z => z ≫ symAlgebraMapOfFunctional g W ψ)
        (GradedQCAlgebra.total_mul_component _ m n)).trans (Category.assoc _ _ _))
  refine e1.trans (Eq.trans ?_ (MonoidalCategory.tensorHom_comp_tensorHom_assoc _ _ _ _ _).symm)
  refine (congrArg (fun z => (symGradedAlgebra W).mul m n ≫ z) (ι_symAlgebraMapOfFunctional g W ψ (m + n))).trans
    (Eq.trans ?_ (congrArg (fun z => z ≫ pushforwardUnitMul g)
      (congrArg₂ (fun a b => a ⊗ₘ b) (ι_symAlgebraMapOfFunctional g W ψ m)
        (ι_symAlgebraMapOfFunctional g W ψ n))).symm)
  exact mul_homEquiv_symGradedPullbackDesc_aux g W hq ψ _ (symGradedAlgebra_of_isQuasicoherent _ hq) _
    (fun m => symGradedPullbackDesc_heq g hq ψ m) m n

theorem symAlgebraMapOfFunctional_one_comp [hq : W.IsQuasicoherent]
    (ψ : (pullback g).obj W ⟶ SheafOfModules.unit T.ringCatSheaf) :
    (symGradedAlgebra W).total.one ≫ symAlgebraMapOfFunctional g W ψ =
      SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom := by
  let S := symGradedAlgebra W
  let f : ∀ m, S.part m ⟶ (pushforward g).obj (SheafOfModules.unit T.ringCatSheaf) := fun m ↦
    (pullbackPushforwardAdjunction g).homEquiv _ _ (symGradedPullbackDesc g ψ m ≫ unitPowCollapse T m)
  have hcomp : S.total.one ≫ Sigma.desc f = S.one ≫ f 0 := by
    change (S.one ≫ Sigma.ι S.part 0) ≫ Sigma.desc f = S.one ≫ f 0
    rw [Category.assoc, Sigma.ι_desc]
  have h2 : S.one ≫ f 0 = (pullbackPushforwardAdjunction g).homEquiv _ _ (pullbackUnitIso g).hom := by
    show S.one ≫ (pullbackPushforwardAdjunction g).homEquiv _ _
      (symGradedPullbackDesc g ψ 0 ≫ unitPowCollapse T 0) = _
    rw [← Adjunction.homEquiv_naturality_left]
    congr 1
    show (pullback g).map S.one ≫ symGradedPullbackDesc g ψ 0 ≫ 𝟙 _ = _
    rw [Category.comp_id]
    exact pullback_map_one_symGradedPullbackDesc_zero g W hq ψ
  change S.total.one ≫ Sigma.desc f = _
  rw [hcomp, h2, homEquiv_pullbackUnitIso_hom_eq]

theorem symAlgebraMapOfFunctional_isAlgebraMap [W.IsQuasicoherent]
    (ψ : (pullback g).obj W ⟶ SheafOfModules.unit T.ringCatSheaf) :
    (symGradedAlgebra W).total.IsAlgebraMapToPushforward g (symAlgebraMapOfFunctional g W ψ) := by
  refine ⟨QCAlgebra.isAlgebraMap_mul_of_mul_comp _ _ _ (symAlgebraMapOfFunctional_mul_comp g W ψ), fun U => ?_⟩
  change (show Γ(T, g ⁻¹ᵁ U) from
    (((symGradedAlgebra W).total.one ≫ symAlgebraMapOfFunctional g W ψ).app U) (show Γ(X, U) from 1)) = 1
  rw [symAlgebraMapOfFunctional_one_comp]
  exact map_one (g.app U).hom

theorem symGen_ι_symAlgebraMapOfFunctional [hq : W.IsQuasicoherent]
    (ψ : (pullback g).obj W ⟶ SheafOfModules.unit T.ringCatSheaf) :
    symGen W ≫ Sigma.ι (symGradedAlgebra W).part 1 ≫ symAlgebraMapOfFunctional g W ψ =
      (pullbackPushforwardAdjunction g).homEquiv _ _ ψ := by
  rw [ι_symAlgebraMapOfFunctional]
  refine (Adjunction.homEquiv_naturality_left (pullbackPushforwardAdjunction g) _ _).symm.trans ?_
  exact congrArg _ (pullback_map_symGen_symGradedPullbackDesc_one g W hq ψ)


end SymAlgebraMap

/-- For an affine open `U ⊆ X`, a ring hom `φ : Γ(X, U) → B` and the composite
`g := Spec.map φ ≫ fromSpec : Spec B → X`, the ring map `Γ(X, U) → Γ(Spec B, ⊤)` induced by `g` is `φ` under
`ΓSpecIso B` (`fromSpec_app_self`, `ΓSpecIso_naturality`). -/
theorem specMap_fromSpec_appLE_top_comp_ΓSpecIso {U : X.Opens} (hU : AlgebraicGeometry.IsAffineOpen U)
    {B : CommRingCat.{u}} (φ : Γ(X, U) ⟶ B) (h : ⊤ ≤ (Spec.map φ ≫ hU.fromSpec) ⁻¹ᵁ U) :
    (Spec.map φ ≫ hU.fromSpec).appLE U ⊤ h ≫ (Scheme.ΓSpecIso B).hom = φ := by
  have h2 : ∀ e, (Spec.map φ).appLE ⊤ ⊤ e = (Spec.map φ).appTop := fun e => (Spec.map φ).appLE_eq_app
  have h' : ⊤ ≤ Spec.map φ ⁻¹ᵁ (hU.fromSpec ⁻¹ᵁ U) := h
  have h1 : (Spec.map φ ≫ hU.fromSpec).appLE U ⊤ h =
      hU.fromSpec.app U ≫ (Spec.map φ).appLE (hU.fromSpec ⁻¹ᵁ U) ⊤ h' :=
    Scheme.Hom.comp_appLE _ _ _ _ _
  rw [h1, hU.fromSpec_app_self]
  simp only [Category.assoc]
  rw [Scheme.Hom.map_appLE_assoc, h2, Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]

/-- **An algebra retraction of the degree-one inclusion.** For `W` quasi-coherent and `U` affine there is a
`Γ(X, U)`-algebra map `G : A(U) → Sym_{Γ(X,U)} Γ(U, W)` sending `ι_U n = symGenTotalLinearMap W U n` to
`SymmetricAlgebra.ι n`. (Together with the surjectivity of `lift ι_U` this is `IsSymmetricAlgebra ι_U`; `G` is then
`(lift ι_U)⁻¹`.)

Proof (as formalized). Write `R := Γ(X, U)`, `N := Γ(U, W)`, `B := Sym_R N`.
1. **A scheme with function ring `B`.** `T := Spec B`, `g : T → X` the composite `Spec.map (algebraMap R B) ≫
   U.fromSpec`. Then `g⁻¹ U = ⊤` (`fromSpec_preimage_self`), and the ring map `R → Γ(T, ⊤)` induced by `g`
   (`g.appLE U ⊤`) is `algebraMap R B` under `e := ΓSpecIso B` (`specMap_fromSpec_appLE_top_comp_ΓSpecIso`).
2. **A functional `β : g^* W → O_T` with `β(g^*n) = e⁻¹(ι n)`.** By the affine tilde adjunction on `T`
   (`AffineTilde.exists_hom_of_linear`; `g^*W` is quasi-coherent), `β` is given by a `Γ(T, ⊤)`-linear map
   `l : Γ(T, g^*W) → Γ(T, ⊤)`. The transpose `t : Γ(T, ⊤) ⊗_R N → Γ(T, g^*W)` of the unit `n ↦ (g^*n)|_⊤`
   (`pullbackSectionsNative`) is an isomorphism (`isIso_transpose_pullbackSectionsNative`, Stacks 01I9), and
   `l := (b ⊗ n ↦ b · e⁻¹(ι n)) ∘ t⁻¹` (the `extendScalars ⊣ restrictScalars` transpose of the `R`-linear map
   `n ↦ e⁻¹(ι n)`); so `l ((g^*n)|_⊤) = e⁻¹(ι n)`.
3. **The algebra map `Φ := symAlgebraMapOfFunctional g W β : Sym W → g_* O_T`**, multiplicative and unital
   (`symAlgebraMapOfFunctional_isAlgebraMap`), with unit `g^♯` (`symAlgebraMapOfFunctional_one_comp`) and degree-one
   part `homEquiv β` (`symGen_ι_symAlgebraMapOfFunctional`).
4. **Sections over `U`.** `G a := e (Φ.app U a |_⊤)`, with `Γ(U, g_* O_T) = Γ(T, g⁻¹U)` and the restriction to
   `⊤ ⊆ g⁻¹U`. It is a ring homomorphism by step 3 (`a * b = total.mul.app U (tensorSections a b)`,
   `sectionsMul_eq_mul_tensorSections`), and `G (sectionsUnit r) = e (g.appLE U ⊤ r) = algebraMap r` by step 1.
   On degree one, `(homEquiv β).app U n = β.app (g⁻¹U) (unit n)`, whose restriction to `⊤` is `β.app ⊤ ((g^*n)|_⊤)`
   (naturality) `= l ((g^*n)|_⊤) = e⁻¹(ι n)` by step 2, so `G (ι_U n) = ι n`.

References: Bourbaki Algebra III §6 no. 6; Stacks 01CG, 01I8/01I9, 01LQ.

Edge cases: `U = ∅` (`R = 0`, `B = 0`, `A(U) = 0`, `T = ∅`; everything is `0`); `W = 0` (`N = 0`, `B = R`,
`A(U) = R`, `T ≅ U`; `G = id`); `W` not quasi-coherent is excluded (the trivial branch of `symGradedAlgebra` would
give `A(U) = R` while `N` may be nonzero, and no such `G` need exist). -/
theorem symGradedAlgebra_exists_algHom_retraction_symGenTotalLinearMap (W : X.Modules) [W.IsQuasicoherent]
    (U : X.affineOpens) :
    letI := ((symGradedAlgebra W).total.sectionsUnit U.1).toAlgebra
    ∃ G : (symGradedAlgebra W).total.sectionsRing U.1 →ₐ[Γ(X, U.1)] SymmetricAlgebra Γ(X, U.1) Γ(W, U.1),
      ∀ n : Γ(W, U.1), G (symGenTotalLinearMap W U.1 n) = SymmetricAlgebra.ι Γ(X, U.1) Γ(W, U.1) n := by
  let _ := ((symGradedAlgebra W).total.sectionsUnit U.1).toAlgebra
  -- Step 1: the affine scheme `T := Spec B`, `B := Sym_R N`, mapping to `X` through `U`.
  let B : CommRingCat.{u} := CommRingCat.of (SymmetricAlgebra Γ(X, U.1) Γ(W, U.1))
  let φ : Γ(X, U.1) ⟶ B :=
    CommRingCat.ofHom (algebraMap Γ(X, U.1) (SymmetricAlgebra Γ(X, U.1) Γ(W, U.1)))
  let g : Spec B ⟶ X := Spec.map φ ≫ U.2.fromSpec
  have hpre : g ⁻¹ᵁ U.1 = ⊤ := by
    show Spec.map φ ⁻¹ᵁ (U.2.fromSpec ⁻¹ᵁ U.1) = ⊤
    rw [U.2.fromSpec_preimage_self]
    rfl
  have h : ⊤ ≤ g ⁻¹ᵁ U.1 := hpre.symm.le
  let e : Γ(Spec B, ⊤) ≅ B := Scheme.ΓSpecIso B
  let f : Γ(X, U.1) →+* Γ(Spec B, ⊤) := (g.appLE U.1 ⊤ h).hom
  have hkey : g.appLE U.1 ⊤ h ≫ e.hom = φ := specMap_fromSpec_appLE_top_comp_ΓSpecIso U.2 φ h
  have hf : ∀ r : Γ(X, U.1),
      e.hom.hom (f r) = algebraMap Γ(X, U.1) (SymmetricAlgebra Γ(X, U.1) Γ(W, U.1)) r := fun r => by
    have h0 := ConcreteCategory.congr_hom hkey r
    rw [ConcreteCategory.comp_apply] at h0
    exact h0
  have hf' : ∀ r : Γ(X, U.1),
      f r = e.inv.hom (algebraMap Γ(X, U.1) (SymmetricAlgebra Γ(X, U.1) Γ(W, U.1)) r) := fun r => by
    rw [← hf r]
    exact (e.hom_inv_id_apply (f r)).symm
  -- Step 2: the `R`-linear map `j : N → Γ(T, ⊤)`, `n ↦ e⁻¹(ι n)`, and the functional `β : g^*W → O_T`.
  let j : ModuleCat.of Γ(X, U.1) Γ(W, U.1) ⟶
      (ModuleCat.restrictScalars f).obj (ModuleCat.of Γ(Spec B, ⊤) Γ(Spec B, ⊤)) :=
    ModuleCat.ofHom (Y := (ModuleCat.restrictScalars f).obj (ModuleCat.of Γ(Spec B, ⊤) Γ(Spec B, ⊤)))
      { toFun := fun n => e.inv.hom (SymmetricAlgebra.ι Γ(X, U.1) Γ(W, U.1) n)
        map_add' := fun a b => by
          show e.inv.hom (SymmetricAlgebra.ι Γ(X, U.1) Γ(W, U.1) (a + b)) =
            e.inv.hom (SymmetricAlgebra.ι Γ(X, U.1) Γ(W, U.1) a) +
              e.inv.hom (SymmetricAlgebra.ι Γ(X, U.1) Γ(W, U.1) b)
          rw [map_add, map_add]
        map_smul' := fun r n => by
          show e.inv.hom (SymmetricAlgebra.ι Γ(X, U.1) Γ(W, U.1) (r • n)) =
            f r • e.inv.hom (SymmetricAlgebra.ι Γ(X, U.1) Γ(W, U.1) n)
          rw [LinearMap.map_smul, Algebra.smul_def, map_mul, hf', smul_eq_mul] }
  let t := ((ModuleCat.extendRestrictScalarsAdj f).homEquiv _ _).symm (pullbackSectionsNative g W U.1 ⊤ h)
  have : IsIso t := isIso_transpose_pullbackSectionsNative g W U.1 U.2 ⊤ (isAffineOpen_top _) h
  let l₁ := ((ModuleCat.extendRestrictScalarsAdj f).homEquiv _ _).symm j
  let l' := inv t ≫ l₁
  let l : Γ((pullback g).obj W, ⊤) →ₗ[Γ(Spec B, ⊤)] Γ(Spec B, ⊤) := l'.hom
  have hl : ∀ n : Γ(W, U.1),
      l (pullbackSectionsOn g W U.1 ⊤ h n) = e.inv.hom (SymmetricAlgebra.ι Γ(X, U.1) Γ(W, U.1) n) := by
    intro n
    have h1 := ModuleCat.extendRestrictScalarsAdj_homEquiv_apply t n
    rw [Equiv.apply_symm_apply] at h1
    have h2 := ModuleCat.extendRestrictScalarsAdj_homEquiv_apply l₁ n
    rw [Equiv.apply_symm_apply] at h2
    show l' (pullbackSectionsNative g W U.1 ⊤ h n) = _
    rw [h1]
    change (t ≫ inv t ≫ l₁) _ = _
    rw [IsIso.hom_inv_id_assoc]
    exact h2.symm
  obtain ⟨β, hβ⟩ := AffineTilde.exists_hom_of_linear (X := Spec B) (N := (pullback g).obj W)
    (G := SheafOfModules.unit (Spec B).ringCatSheaf) l
  -- Step 3: the algebra map `Φ : Sym W → g_* O_T` and its sections over `U`.
  let Φ := symAlgebraMapOfFunctional g W β
  have hΦ := symAlgebraMapOfFunctional_isAlgebraMap g W β
  let res : Γ(Spec B, g ⁻¹ᵁ U.1) ⟶ Γ(Spec B, ⊤) := (Spec B).presheaf.map (homOfLE h).op
  let res' : Γ((pushforward g).obj (SheafOfModules.unit (Spec B).ringCatSheaf), U.1) → Γ(Spec B, ⊤) :=
    fun z => res.hom (show Γ(Spec B, g ⁻¹ᵁ U.1) from z)
  have hres_mul : ∀ a b : (symGradedAlgebra W).total.sectionsRing U.1,
      res' ((Φ.app U.1).hom (a * b)) = res' ((Φ.app U.1).hom a) * res' ((Φ.app U.1).hom b) := by
    intro a b
    rw [QCAlgebra.sectionsMul_eq_mul_tensorSections]
    exact (congrArg res' (hΦ.1 U.1 a b)).trans (map_mul res.hom _ _)
  have hres_one : res' ((Φ.app U.1).hom (1 : (symGradedAlgebra W).total.sectionsRing U.1)) = 1 :=
    (congrArg res' (hΦ.2 U.1)).trans (map_one res.hom)
  have hres_add : ∀ a b : (symGradedAlgebra W).total.sectionsRing U.1,
      res' ((Φ.app U.1).hom (a + b)) = res' ((Φ.app U.1).hom a) + res' ((Φ.app U.1).hom b) := fun a b =>
    (congrArg res' (map_add (Φ.app U.1).hom a b)).trans (map_add res.hom _ _)
  have hres_zero : res' ((Φ.app U.1).hom (0 : (symGradedAlgebra W).total.sectionsRing U.1)) = 0 :=
    (congrArg res' (map_zero (Φ.app U.1).hom)).trans (map_zero res.hom)
  let G₀ : (symGradedAlgebra W).total.sectionsRing U.1 →+* SymmetricAlgebra Γ(X, U.1) Γ(W, U.1) :=
    { toFun := fun a => e.hom.hom (res' ((Φ.app U.1).hom a))
      map_one' := by rw [hres_one, map_one]
      map_mul' := fun a b => by rw [hres_mul, map_mul]
      map_zero' := by rw [hres_zero, map_zero]
      map_add' := fun a b => by rw [hres_add, map_add] }
  have hcomm : ∀ r : Γ(X, U.1), G₀ ((symGradedAlgebra W).total.sectionsUnit U.1 r) =
      algebraMap Γ(X, U.1) (SymmetricAlgebra Γ(X, U.1) Γ(W, U.1)) r := by
    intro r
    have h1 : (Φ.app U.1).hom (((symGradedAlgebra W).total.one.app U.1).hom r) =
        (((symGradedAlgebra W).total.one ≫ Φ).app U.1).hom r := rfl
    show e.hom.hom (res' ((Φ.app U.1).hom (((symGradedAlgebra W).total.one.app U.1).hom r))) = _
    rw [h1, symAlgebraMapOfFunctional_one_comp]
    exact hf r
  refine ⟨{ toRingHom := G₀, commutes' := hcomm }, fun n => ?_⟩
  -- Step 4: degree one.
  have h1 : (Φ.app U.1).hom (((symGen W ≫ (symGradedAlgebra W).totalIncl 1).app U.1).hom n) =
      (β.app (g ⁻¹ᵁ U.1)).hom (pullbackUnitHom g W U.1 n) := by
    have e1 : (Φ.app U.1).hom (((symGen W ≫ (symGradedAlgebra W).totalIncl 1).app U.1).hom n) =
        (((symGen W ≫ Sigma.ι (symGradedAlgebra W).part 1 ≫ Φ).app U.1).hom n) := rfl
    rw [e1, symGen_ι_symAlgebraMapOfFunctional]
    rfl
  have h3 : res.hom ((β.app (g ⁻¹ᵁ U.1)).hom (pullbackUnitHom g W U.1 n)) =
      (β.app ⊤).hom (pullbackSectionsOn g W U.1 ⊤ h n) :=
    (_root_.PresheafOfModules.naturality_apply β.val (homOfLE h).op (pullbackUnitHom g W U.1 n)).symm
  show e.hom.hom (res' ((Φ.app U.1).hom (((symGen W ≫ (symGradedAlgebra W).totalIncl 1).app U.1).hom n))) = _
  rw [h1]
  show e.hom.hom (res.hom ((β.app (g ⁻¹ᵁ U.1)).hom (pullbackUnitHom g W U.1 n))) = _
  rw [h3, hβ]
  exact (congrArg (fun z => e.hom.hom z) (hl n)).trans (e.inv_hom_id_apply _)


/-- **Injectivity half of `IsSymmetricAlgebra`**: `lift ι_U` has the left inverse `G` of
`symGradedAlgebra_exists_algHom_retraction_symGenTotalLinearMap` (`G ∘ lift ι_U = id` by
`SymmetricAlgebra.algHom_ext`, both sides being the identity on `ι n`). -/
theorem symGradedAlgebra_lift_symGenTotalLinearMap_injective (W : X.Modules) [W.IsQuasicoherent]
    (U : X.affineOpens) :
    letI := ((symGradedAlgebra W).total.sectionsUnit U.1).toAlgebra
    Function.Injective (SymmetricAlgebra.lift (symGenTotalLinearMap W U.1)) := by
  let _ := ((symGradedAlgebra W).total.sectionsUnit U.1).toAlgebra
  obtain ⟨G, hG⟩ := symGradedAlgebra_exists_algHom_retraction_symGenTotalLinearMap W U
  have hcomp : G.comp (SymmetricAlgebra.lift (symGenTotalLinearMap W U.1)) = AlgHom.id _ _ := by
    refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun n => ?_)
    show G (SymmetricAlgebra.lift (symGenTotalLinearMap W U.1) (SymmetricAlgebra.ι _ _ n)) =
      SymmetricAlgebra.ι _ _ n
    rw [SymmetricAlgebra.lift_ι_apply, hG]
  intro a b hab
  have ha := DFunLike.congr_fun hcomp a
  have hb := DFunLike.congr_fun hcomp b
  simp only [AlgHom.comp_apply, AlgHom.id_apply] at ha hb
  rw [← ha, ← hb, hab]

/-- **`A(U)` is the symmetric algebra of `Γ(U, W)`**: `lift ι_U` is bijective, being surjective
(`symGradedAlgebra_lift_symGenTotalLinearMap_surjective`) and injective
(`symGradedAlgebra_lift_symGenTotalLinearMap_injective`). -/
theorem symGradedAlgebra_sectionsRing_isSymmetricAlgebra_of_retraction (W : X.Modules) [W.IsQuasicoherent]
    (U : X.affineOpens) :
    letI := ((symGradedAlgebra W).total.sectionsUnit U.1).toAlgebra
    IsSymmetricAlgebra (symGenTotalLinearMap W U.1) :=
  ⟨symGradedAlgebra_lift_symGenTotalLinearMap_injective W U,
    symGradedAlgebra_lift_symGenTotalLinearMap_surjective W U⟩

end AlgebraicGeometry.Scheme.Modules

end
