import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.ModuleUnit
import MiyaokaMori.AlgebraicGeometry.Cohomology.Cech.CechPullbackMap
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.PullbackUnitOpenImmersion
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.SchemeModulesPullbackFreeIso
import MiyaokaMori.AlgebraicGeometry.Modules.Glue.VectorBundleFamilyFromCocycle

/-! # Computing pullbacks on sections: structure sheaf, free sheaves, and open immersion squares

Section-level computations of pullback (independent of `C` and `A¹`):

* `pullbackObjUnitToUnit` sends the pulled-back structure sheaf section `η(a)|_W` to `f.appLE V W a`;
* `pullbackObjFreeIso` sends the pulled-back standard section `η(e_i)|_W` to `e_i`;
* for an open immersion square `f' ≫ k = j ≫ f`, the base-change isomorphism
  `baseChangeIso : (f^*N)|_j ≅ f'^*(N|_k)` (assembled in five steps from
  `restrictFunctorIsoPullback`, `pullbackComp`, `pullbackCongr`) sends
  `pullbackSectionsOn f N (k''B) (j''A) x` to `pullbackSectionsOn f' (N|_k) B A x` on sections.

References: Hartshorne II Ex. 5.18 (pullback preserves local trivializations); Mathlib
`SheafOfModules.pullbackObjFreeIso`, `pullback_map_ιFree_comp_pullbackObjFreeIso_hom`;
`PullbackUnitOpenImmersion.lean` (`restrictFunctorIsoPullback_hom_app_apply`,
`pullbackComp_inv_app_unit`, `pullbackCongr_hom_app_pullbackSectionsOn`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

open AlgebraicGeometry bundleFamilyOfCocycle

variable {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)

/-- Morphisms commute with restriction (elementwise). -/
theorem app_res' {M N : X.Modules} (φ : M ⟶ N) {U U' : X.Opens} (h : U' ≤ U) (x : Γ(M, U)) :
    φ.app U' (M.presheaf.map (homOfLE h).op x) = N.presheaf.map (homOfLE h).op (φ.app U x) :=
  congr($(φ.val.naturality (homOfLE h).op) x)

/-- Restriction along `le_rfl` is the identity. -/
theorem map_homOfLE_rfl {M : X.Modules} (U : X.Opens) (x : Γ(M, U)) :
    M.presheaf.map (homOfLE (le_refl U)).op x = x := by
  have : (homOfLE (le_refl U) : U ⟶ U) = 𝟙 U := Subsingleton.elim _ _
  rw [this, op_id, CategoryTheory.Functor.map_id]
  rfl

theorem pullbackSectionsOn_self (M : Y.Modules) (V : Y.Opens) (s : Γ(M, V)) :
    pullbackSectionsOn f M V (f ⁻¹ᵁ V) le_rfl s = pullbackUnitHom f M V s := by
  rw [pullbackSectionsOn_apply]
  exact map_homOfLE_rfl _ _

/-- A pulled-back morphism applied to a pulled-back section. -/
theorem pullback_map_app_pullbackSectionsOn_bc {M N : Y.Modules} (ψ : M ⟶ N) (V : Y.Opens)
    (W : X.Opens) (h : W ≤ f ⁻¹ᵁ V) (s : Γ(M, V)) :
    ((AlgebraicGeometry.Scheme.Modules.pullback f).map ψ).app W (pullbackSectionsOn f M V W h s) =
      pullbackSectionsOn f N V W h (ψ.app V s) := by
  rw [pullbackSectionsOn_apply, pullbackSectionsOn_apply, app_res']
  congr 1
  exact unit_naturality_app f ψ V s

/-- Restrict the source section first, then pull back (`pullbackSectionsOn_restrict` without the
outer restriction). -/
theorem pullbackSectionsOn_res (M : Y.Modules) {V W : Y.Opens} {W' : X.Opens} (h : W' ≤ f ⁻¹ᵁ V)
    (h' : W' ≤ f ⁻¹ᵁ W) (hW : W ≤ V) (s : Γ(M, V)) :
    pullbackSectionsOn f M V W' h s =
      pullbackSectionsOn f M W W' h' (M.presheaf.map (homOfLE hW).op s) := by
  rw [← pullbackSectionsOn_restrict f M h h' hW le_rfl s]
  exact (map_homOfLE_rfl _ _).symm

/-- The `hom` of `pullbackComp` sends a twice pulled-back section to the section pulled back once. -/
theorem pullbackComp_hom_app_pullbackSectionsOn {Z : AlgebraicGeometry.Scheme.{u}} (g : Y ⟶ Z)
    (M : Z.Modules) (U : Z.Opens) (W : X.Opens) (h : W ≤ f ⁻¹ᵁ (g ⁻¹ᵁ U)) (h' : W ≤ (f ≫ g) ⁻¹ᵁ U)
    (s : Γ(M, U)) :
    ((pullbackComp f g).app M).hom.app W
        (pullbackSectionsOn f ((AlgebraicGeometry.Scheme.Modules.pullback g).obj M) (g ⁻¹ᵁ U) W h
          (pullbackUnitHom g M U s)) =
      pullbackSectionsOn (f ≫ g) M U W h' s := by
  have key := pullbackComp_inv_app_unit f g M U s
  have key' : ((pullbackComp f g).app M).hom.app ((f ≫ g) ⁻¹ᵁ U)
      (pullbackUnitHom f ((AlgebraicGeometry.Scheme.Modules.pullback g).obj M) (g ⁻¹ᵁ U)
        (pullbackUnitHom g M U s)) =
      pullbackUnitHom (f ≫ g) M U s := by
    rw [show pullbackUnitHom f ((AlgebraicGeometry.Scheme.Modules.pullback g).obj M) (g ⁻¹ᵁ U)
        (pullbackUnitHom g M U s) =
        ((pullbackComp f g).app M).inv.app ((f ≫ g) ⁻¹ᵁ U) (pullbackUnitHom (f ≫ g) M U s) from
      key.symm]
    exact modIso_hom_app_inv_app ((pullbackComp f g).app M) _ _
  rw [pullbackSectionsOn_apply, pullbackSectionsOn_apply]
  refine (app_res' ((pullbackComp f g).app M).hom h _).trans ?_
  exact congrArg _ key'

theorem pullbackComp_inv_app_pullbackSectionsOn {Z : AlgebraicGeometry.Scheme.{u}} (g : Y ⟶ Z)
    (M : Z.Modules) (U : Z.Opens) (W : X.Opens) (h : W ≤ f ⁻¹ᵁ (g ⁻¹ᵁ U)) (h' : W ≤ (f ≫ g) ⁻¹ᵁ U)
    (s : Γ(M, U)) :
    ((pullbackComp f g).app M).inv.app W (pullbackSectionsOn (f ≫ g) M U W h' s) =
      pullbackSectionsOn f ((AlgebraicGeometry.Scheme.Modules.pullback g).obj M) (g ⁻¹ᵁ U) W h
        (pullbackUnitHom g M U s) := by
  rw [← pullbackComp_hom_app_pullbackSectionsOn f g M U W h h' s]
  exact modIso_inv_app_hom_app ((pullbackComp f g).app M) _ _

/-- The inverse of `restrictFunctorIsoPullback` sends a pulled-back section back to the original section. -/
theorem restrictFunctorIsoPullback_inv_app_pullbackSectionsOn (j : X ⟶ Y) [IsOpenImmersion j]
    (M : Y.Modules) (W : X.Opens) (h : W ≤ j ⁻¹ᵁ (j ''ᵁ W)) (x : Γ(M, j ''ᵁ W)) :
    ((restrictFunctorIsoPullback j).app M).inv.app W (pullbackSectionsOn j M (j ''ᵁ W) W h x) = x := by
  rw [← restrictFunctorIsoPullback_hom_app_apply j M W x]
  exact modIso_inv_app_hom_app ((restrictFunctorIsoPullback j).app M) _ _

/-! ## Structure sheaf and free sheaves -/

/-- `SheafOfModules.pullbackObjUnitToUnit`, typed as a morphism in `X.Modules`. -/
noncomputable def pullbackObjUnitToUnit' :
    (AlgebraicGeometry.Scheme.Modules.pullback f).obj (unitModule Y) ⟶ unitModule X :=
  haveI : (SheafOfModules.pushforward.{u} f.toRingCatSheafHom).IsRightAdjoint :=
    (pullbackPushforwardAdjunction f).isRightAdjoint
  SheafOfModules.pullbackObjUnitToUnit f.toRingCatSheafHom

/-- `pullbackObjUnitToUnit` acts on pulled-back structure sheaf sections as `f.app`. -/
theorem pullbackObjUnitToUnit'_app_unit (V : Y.Opens) (a : Γ(Y, V)) :
    (pullbackObjUnitToUnit' f).app (f ⁻¹ᵁ V) (pullbackUnitHom f (unitModule Y) V (toUnit a)) =
      toUnit (f.app V a) := by
  have : (SheafOfModules.pushforward.{u} f.toRingCatSheafHom).IsRightAdjoint :=
    (pullbackPushforwardAdjunction f).isRightAdjoint
  have h := SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
    f.toRingCatSheafHom
  rw [Adjunction.homEquiv_unit] at h
  have h1 := ConcreteCategory.congr_hom (congrArg (fun ψ => Hom.app ψ V) h) (toUnit a)
  exact h1

theorem pullbackObjUnitToUnit'_app_pullbackSectionsOn (V : Y.Opens) (W : X.Opens) (h : W ≤ f ⁻¹ᵁ V)
    (a : Γ(Y, V)) :
    (pullbackObjUnitToUnit' f).app W (pullbackSectionsOn f (unitModule Y) V W h (toUnit a)) =
      toUnit (f.appLE V W h a) := by
  rw [pullbackSectionsOn_apply, app_res', pullbackObjUnitToUnit'_app_unit]
  rfl

/-- `pullbackObjFreeIso` sends pulled-back standard sections to standard sections. -/
theorem pullbackObjFreeIso_hom_app_pullbackSectionsOn_freeSec {I : Type u} (i : I) (V : Y.Opens)
    (W : X.Opens) (h : W ≤ f ⁻¹ᵁ V) :
    (AlgebraicGeometry.Scheme.Modules.pullbackObjFreeIso f I).hom.app W
        (pullbackSectionsOn f (Modules.free I) V W h (freeSec I i V)) =
      freeSec I i W := by
  have : (SheafOfModules.pushforward.{u} f.toRingCatSheafHom).IsRightAdjoint :=
    (pullbackPushforwardAdjunction f).isRightAdjoint
  have key := SheafOfModules.pullback_map_ιFree_comp_pullbackObjFreeIso_hom f.toRingCatSheafHom
    (I := I) i
  have h1 := ConcreteCategory.congr_hom (congrArg (fun ψ => Hom.app ψ W) key)
    (pullbackSectionsOn f (unitModule Y) V W h (unitOne Y V))
  change (AlgebraicGeometry.Scheme.Modules.pullbackObjFreeIso f I).hom.app W
      (((AlgebraicGeometry.Scheme.Modules.pullback f).map (ιFree' I i)).app W
        (pullbackSectionsOn f (unitModule Y) V W h (unitOne Y V))) =
    (ιFree' I i).app W ((pullbackObjUnitToUnit' f).app W
      (pullbackSectionsOn f (unitModule Y) V W h (unitOne Y V))) at h1
  rw [pullback_map_app_pullbackSectionsOn_bc, ιFree_app_one] at h1
  rw [h1]
  change (ιFree' I i).app W ((pullbackObjUnitToUnit' f).app W
      (pullbackSectionsOn f (unitModule Y) V W h (toUnit (1 : Γ(Y, V))))) = _
  rw [pullbackObjUnitToUnit'_app_pullbackSectionsOn, map_one]
  exact ιFree_app_one i W

/-! ## The base-change isomorphism of an open immersion square -/

section BaseChange

variable {X' Y' : AlgebraicGeometry.Scheme.{u}} (f' : X' ⟶ Y') (j : X' ⟶ X) (k : Y' ⟶ Y)
  [IsOpenImmersion j] [IsOpenImmersion k] (sq : f' ≫ k = j ≫ f)

/-- The base-change isomorphism `(f^*N)|_j ≅ f'^*(N|_k)` of an open immersion square `f' ≫ k = j ≫ f`. -/
noncomputable def baseChangeIso (N : Y.Modules) :
    ((AlgebraicGeometry.Scheme.Modules.pullback f).obj N).restrict j ≅
      (AlgebraicGeometry.Scheme.Modules.pullback f').obj (N.restrict k) :=
  (restrictFunctorIsoPullback j).app _ ≪≫ (pullbackComp j f).app N ≪≫
    (pullbackCongr sq.symm).app N ≪≫ ((pullbackComp f' k).app N).symm ≪≫
    (AlgebraicGeometry.Scheme.Modules.pullback f').mapIso ((restrictFunctorIsoPullback k).app N).symm

/-- The base-change isomorphism on sections: `f^*x|_{j''A} ↦ f'^*x|_A`. -/
theorem baseChangeIso_hom_app (N : Y.Modules) (B : Y'.Opens) (A : X'.Opens)
    (h : j ''ᵁ A ≤ f ⁻¹ᵁ (k ''ᵁ B)) (h' : A ≤ f' ⁻¹ᵁ B) (x : Γ(N, k ''ᵁ B)) :
    (baseChangeIso f f' j k sq N).hom.app A (pullbackSectionsOn f N (k ''ᵁ B) (j ''ᵁ A) h x) =
      pullbackSectionsOn f' (N.restrict k) B A h' x := by
  have hA : A ≤ j ⁻¹ᵁ (j ''ᵁ A) := le_of_eq (j.preimage_image_eq A).symm
  have h₁ : A ≤ j ⁻¹ᵁ (f ⁻¹ᵁ (k ''ᵁ B)) := hA.trans ((Opens.map j.base).map (homOfLE h)).le
  have h₂ : A ≤ (j ≫ f) ⁻¹ᵁ (k ''ᵁ B) := h₁
  have h₃ : A ≤ (f' ≫ k) ⁻¹ᵁ (k ''ᵁ B) := by rw [sq]; exact h₂
  have h₄ : A ≤ f' ⁻¹ᵁ (k ⁻¹ᵁ (k ''ᵁ B)) := h₃
  have hB : B ≤ k ⁻¹ᵁ (k ''ᵁ B) := le_of_eq (k.preimage_image_eq B).symm
  change ((AlgebraicGeometry.Scheme.Modules.pullback f').map
      ((restrictFunctorIsoPullback k).app N).inv).app A
    (((pullbackComp f' k).app N).inv.app A
      (((pullbackCongr sq.symm).app N).hom.app A
        (((pullbackComp j f).app N).hom.app A
          (((restrictFunctorIsoPullback j).app
              ((AlgebraicGeometry.Scheme.Modules.pullback f).obj N)).hom.app A
            (pullbackSectionsOn f N (k ''ᵁ B) (j ''ᵁ A) h x))))) = _
  -- step 1: `restrictFunctorIsoPullback j`
  rw [restrictFunctorIsoPullback_hom_app_apply]
  -- step 2: `pullbackComp j f`
  rw [pullbackSectionsOn_apply f N (k ''ᵁ B) (j ''ᵁ A) h x]
  rw [← pullbackSectionsOn_res j ((AlgebraicGeometry.Scheme.Modules.pullback f).obj N) h₁ _ h
    (pullbackUnitHom f N (k ''ᵁ B) x)]
  rw [pullbackComp_hom_app_pullbackSectionsOn j f N (k ''ᵁ B) A h₁ h₂]
  -- step 3: `pullbackCongr`
  rw [pullbackCongr_hom_app_pullbackSectionsOn sq.symm N (k ''ᵁ B) A h₂ h₃]
  -- step 4: the inverse of `pullbackComp f' k`
  rw [pullbackComp_inv_app_pullbackSectionsOn f' k N (k ''ᵁ B) A h₄ h₃]
  rw [pullbackSectionsOn_res f' _ h₄ h' hB]
  -- step 5: the pullback of the inverse of `restrictFunctorIsoPullback k`
  rw [pullback_map_app_pullbackSectionsOn_bc]
  congr 1
  rw [← pullbackSectionsOn_apply k N (k ''ᵁ B) B hB x]
  exact restrictFunctorIsoPullback_inv_app_pullbackSectionsOn k N B hB x

include sq in
/-- In an open immersion square, `A ≤ f'⁻¹B` implies `j''A ≤ f⁻¹(k''B)`. -/
theorem image_le_preimage_image_of_sq (A : X'.Opens) (B : Y'.Opens) (hAB : A ≤ f' ⁻¹ᵁ B) :
    j ''ᵁ A ≤ f ⁻¹ᵁ (k ''ᵁ B) := by
  rintro x ⟨a, ha, rfl⟩
  refine ⟨f' a, hAB ha, ?_⟩
  change (f' ≫ k).base a = (j ≫ f).base a
  rw [sq]

/-- The pulled-back block isomorphism `ε := bc ≪≫ f'^*(e) ≪≫ pullbackObjFreeIso : (f^*N)|_j ≅ O^{(I)}`. -/
noncomputable def baseChangeFreeIso (N : Y.Modules) {I : Type u}
    (e : N.restrict k ≅ Modules.free (X := Y') I) :
    ((AlgebraicGeometry.Scheme.Modules.pullback f).obj N).restrict j ≅ Modules.free (X := X') I :=
  baseChangeIso f f' j k sq N ≪≫ (AlgebraicGeometry.Scheme.Modules.pullback f').mapIso e ≪≫
    AlgebraicGeometry.Scheme.Modules.pullbackObjFreeIso f' I

/-- The inverse of `ε` sends the standard section `e_i` to the pulled-back frame section `f^*(e⁻¹(e_i))`. -/
theorem baseChangeFreeIso_inv_app_freeSec (N : Y.Modules) {I : Type u}
    (e : N.restrict k ≅ Modules.free (X := Y') I) (i : I) (A : X'.Opens) :
    (baseChangeFreeIso f f' j k sq N e).inv.app A (freeSec I i A) =
      pullbackSectionsOn f N (k ''ᵁ ⊤) (j ''ᵁ A)
        (image_le_preimage_image_of_sq f f' j k sq A ⊤ le_top) (e.inv.app ⊤ (freeSec I i ⊤)) := by
  change (baseChangeIso f f' j k sq N).inv.app A
    (((AlgebraicGeometry.Scheme.Modules.pullback f').map e.inv).app A
      ((AlgebraicGeometry.Scheme.Modules.pullbackObjFreeIso f' I).inv.app A (freeSec I i A))) = _
  have hA : A ≤ f' ⁻¹ᵁ (⊤ : Y'.Opens) := le_top
  have h1 : (AlgebraicGeometry.Scheme.Modules.pullbackObjFreeIso f' I).inv.app A (freeSec I i A) =
      pullbackSectionsOn f' (Modules.free I) ⊤ A hA (freeSec I i ⊤) := by
    rw [← pullbackObjFreeIso_hom_app_pullbackSectionsOn_freeSec f' i ⊤ A hA]
    exact modIso_inv_app_hom_app _ _ _
  rw [h1]
  refine (congrArg _ (pullback_map_app_pullbackSectionsOn_bc f' e.inv ⊤ A hA (freeSec I i ⊤))).trans ?_
  rw [← baseChangeIso_hom_app f f' j k sq N ⊤ A
    (image_le_preimage_image_of_sq f f' j k sq A ⊤ le_top) hA (e.inv.app ⊤ (freeSec I i ⊤))]
  exact modIso_inv_app_hom_app _ _ _

/-- `ε` on pulled-back sections: apply `e`, pull back, then apply `pullbackObjFreeIso`. -/
theorem baseChangeFreeIso_hom_app_pullbackSectionsOn (N : Y.Modules) {I : Type u}
    (e : N.restrict k ≅ Modules.free (X := Y') I) (B : Y'.Opens) (A : X'.Opens)
    (h : j ''ᵁ A ≤ f ⁻¹ᵁ (k ''ᵁ B)) (h' : A ≤ f' ⁻¹ᵁ B) (x : Γ(N, k ''ᵁ B)) :
    (baseChangeFreeIso f f' j k sq N e).hom.app A
        (pullbackSectionsOn f N (k ''ᵁ B) (j ''ᵁ A) h x) =
      (AlgebraicGeometry.Scheme.Modules.pullbackObjFreeIso f' I).hom.app A
        (pullbackSectionsOn f' (Modules.free I) B A h' (e.hom.app B x)) := by
  change (AlgebraicGeometry.Scheme.Modules.pullbackObjFreeIso f' I).hom.app A
    (((AlgebraicGeometry.Scheme.Modules.pullback f').map e.hom).app A
      ((baseChangeIso f f' j k sq N).hom.app A
        (pullbackSectionsOn f N (k ''ᵁ B) (j ''ᵁ A) h x))) = _
  rw [baseChangeIso_hom_app f f' j k sq N B A h h' x]
  exact congrArg _ (pullback_map_app_pullbackSectionsOn_bc f' e.hom B A h' x)

end BaseChange

/-! ## Semilinearity and sums -/

/-- Semilinearity of the pullback of sections: `f^*(c • y) = f^♯(c) • f^*y` (in `f.appLE` form). -/
theorem pullbackSectionsOn_smul' (M : Y.Modules) (B : Y.Opens) (A : X.Opens) (h : A ≤ f ⁻¹ᵁ B)
    (c : Γ(Y, B)) (y : Γ(M, B)) :
    pullbackSectionsOn f M B A h (c • y) = f.appLE B A h c • pullbackSectionsOn f M B A h y := by
  rw [pullbackSectionsOn_apply, pullbackSectionsOn_apply, pullbackUnitHom_smul,
    AlgebraicGeometry.Scheme.Modules.map_smul]
  rfl

/-- `pullbackObjFreeIso` sends a pulled-back sum of "coefficient × standard section" to the sum of
"coefficient through `f^♯` × standard section". -/
theorem pullbackObjFreeIso_hom_app_pullbackSectionsOn_sum {I : Type u} [Fintype I] (B : Y.Opens)
    (A : X.Opens) (h : A ≤ f ⁻¹ᵁ B) (c : I → Γ(Y, B)) :
    (AlgebraicGeometry.Scheme.Modules.pullbackObjFreeIso f I).hom.app A
        (pullbackSectionsOn f (Modules.free I) B A h (∑ i, c i • freeSec I i B)) =
      ∑ i, f.appLE B A h (c i) • freeSec I i A := by
  rw [map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pullbackSectionsOn_smul']
  erw [Hom.app_smul]
  rw [pullbackObjFreeIso_hom_app_pullbackSectionsOn_freeSec]


end AlgebraicGeometry.Scheme.Modules

end
