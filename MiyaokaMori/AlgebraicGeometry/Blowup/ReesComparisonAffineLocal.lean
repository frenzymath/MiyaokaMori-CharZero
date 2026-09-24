import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.PullbackSectionsNativeBaseChange
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPullbackMonoidal
import MiyaokaMori.AlgebraicGeometry.Blowup.ReesAlgebraSheaf
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjBaseChangeUnit

/-! # The Rees comparison map and its affine-local computation

The comparison map `ψₙ := g^*(I.powι n) ≫ ε' : g^*(Iⁿ) ⟶ O_{X₁}` (with `ε' = pullbackUnitIso g`,
`g^*O_{X₂} ≅ O_{X₁}`) and its **affine-local computation**: for affine opens `U ⊆ X₂`, `V ⊆ X₁` with
`V ≤ g⁻¹U`, `A := Γ(X₂, U)`, `B := Γ(X₁, V)`, `φ := g.appLE U V`, `N := Γ(U, Iⁿ) ⊆ A`,

* `ψₙ.app V ∘ (B ⊗_A N → Γ(V, g^*Iⁿ)) = (b ⊗ x ↦ b·φ(x))`  (`reesComparison_app_transposeNative`);
* `range (ψₙ.app V) = N·B = N.map φ`  (`range_reesComparison_app`, no flatness needed);
* `g` flat ⇒ `ψₙ.app V` injective  (`reesComparison_app_injective`; `Module.Flat`).

The pure algebra (`MiyaokaMori.FlatIdealBaseChange`): for `φ : A → B` and an ideal `N ⊆ A`, the map
`B ⊗_A N → B`, `b ⊗ x ↦ b φ(x)` has range `N.map φ` and is injective when `φ` is flat
(it is `B ⊗ N → B ⊗ A ≅ B`, `Module.Flat.lTensor_preserves_injective_linearMap`).

Source: Stacks 0805 (first paragraph of the proof), Stacks 01I9 (sections of a pullback on affines);
this is the affine-local half of `reesAlgebra_comap_iso_pullback_of_flat`. The surjectivity of the
canonical map `B ⊗_A N → Γ(V, g^*Iⁿ)` uses the quasi-coherence of `Iⁿ`
(`IdealSheafData.pow_isQuasicoherent`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry TensorProduct

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X₁ X₂ : AlgebraicGeometry.Scheme.{u}} (g : X₁ ⟶ X₂)

/-- `ε'_{g⁻¹U}(g^*t) = g^♯(t)`: the section form of Mathlib's
`pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit`. (The same statement with
`𝟙_ X.Modules` in place of `SheafOfModules.unit` is
`pullbackUnitIso_hom_app_pullbackUnitHom` in `WeightedPolynomialAtlasPullback`;
that module is far heavier, so the lemma is kept private here.) -/
private theorem pullbackUnitIso_hom_app_pullbackUnitHom_unit (U : X₂.Opens) (t : Γ(X₂, U)) :
    (pullbackUnitIso g).hom.app (g ⁻¹ᵁ U)
      (pullbackUnitHom g (SheafOfModules.unit X₂.ringCatSheaf) U t) = g.app U t := by
  have : (SheafOfModules.pushforward.{u} g.toRingCatSheafHom).IsRightAdjoint :=
    (pullbackPushforwardAdjunction g).isRightAdjoint
  have h := SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit
    g.toRingCatSheafHom
  rw [Adjunction.homEquiv_unit] at h
  exact congrArg (fun q => (q.val.app (op U)).hom t) h

/-- `ε'_V((g^*t)|_V) = g.appLE U V t` for `V ≤ g⁻¹U`: the comparison `g^*O_{X₂} ⟶ O_{X₁}` on the
pulled-back section of `t ∈ Γ(X₂, U)` is the ring map `Γ(X₂, U) → Γ(X₁, V)`. -/
theorem pullbackUnitIso_hom_app_pullbackSectionsOn_unit (U : X₂.Opens) (V : X₁.Opens)
    (h : V ≤ g ⁻¹ᵁ U) (t : Γ(X₂, U)) :
    (pullbackUnitIso g).hom.app V
      (pullbackSectionsOn g (SheafOfModules.unit X₂.ringCatSheaf) U V h t) = g.appLE U V h t := by
  erw [pullbackSectionsOn_apply]
  have := ConcreteCategory.congr_hom ((pullbackUnitIso g).hom.mapPresheaf.naturality (homOfLE h).op)
    (pullbackUnitHom g (SheafOfModules.unit X₂.ringCatSheaf) U t)
  simp only [ConcreteCategory.comp_apply] at this
  erw [this, pullbackUnitIso_hom_app_pullbackUnitHom_unit]
  rfl

/-- The transpose `Γ(X₁,V) ⊗_{Γ(X₂,U)} Γ(M,U) → Γ(V, g^*M)` of `pullbackSectionsNative` sends
`b ⊗ s` to `b • (g^*s)|_V` (`ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars`). -/
theorem transpose_pullbackSectionsNative_tmul (M : X₂.Modules) (U : X₂.Opens) (V : X₁.Opens)
    (h : V ≤ g ⁻¹ᵁ U) (b : Γ(X₁, V)) (s : Γ(M, U)) :
    (((ModuleCat.extendRestrictScalarsAdj (g.appLE U V h).hom).homEquiv _ _).symm
        (pullbackSectionsNative g M U V h))
      (@TensorProduct.tmul Γ(X₂, U) _ ((ModuleCat.restrictScalars (g.appLE U V h).hom).obj
        (ModuleCat.of Γ(X₁, V) Γ(X₁, V))) Γ(M, U) _ _ _ _ b s) =
      b • pullbackSectionsOn g M U V h s := by
  rfl

end AlgebraicGeometry.Scheme.Modules

namespace MiyaokaMori.FlatIdealBaseChange

variable {A B : Type u} [CommRing A] [CommRing B] (φ : A →+* B) (N : Ideal A)

/-- `B` as an `A`-module along `φ` (Mathlib's `restrictScalars`), the ring of scalars of
`extendScalars φ`. -/
abbrev B' : ModuleCat.{u} A := (ModuleCat.restrictScalars φ).obj (ModuleCat.of B B)

/-- `N → B`, `x ↦ φ x`, as an `A`-linear map into `B` with scalars restricted along `φ`. -/
def toRestrict : ModuleCat.of A N ⟶ B' φ :=
  ModuleCat.ofHom (Y := B' φ)
    { toFun := fun x => (φ x.1 : B)
      map_add' := fun x y => by
        change φ (x.1 + y.1) = φ x.1 + φ y.1
        exact map_add φ x.1 y.1
      map_smul' := fun a x => by
        change φ (a * x.1) = φ a * φ x.1
        exact map_mul φ a x.1 }

/-- `B ⊗_A N → B`, `b ⊗ x ↦ b · φ x`. -/
def tensorMul : (ModuleCat.extendScalars φ).obj (ModuleCat.of A N) ⟶ ModuleCat.of B B :=
  ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars φ (toRestrict φ N)

theorem tensorMul_tmul (b : B) (x : N) :
    tensorMul φ N (@TensorProduct.tmul A _ (B' φ) N _ _ _ _ (b : B' φ) x) = b * φ x.1 := rfl

/-- The image of `B ⊗_A N → B` is the extended ideal `N·B = N.map φ`. -/
theorem range_tensorMul : LinearMap.range (tensorMul φ N).hom = N.map φ := by
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact zero_mem _
    | tmul b x =>
      rw [tensorMul_tmul]
      exact Ideal.mul_mem_left (α := B) _ b (Ideal.mem_map_of_mem φ x.2)
    | add y z hy hz =>
      rw [map_add]
      exact add_mem hy hz
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    refine ⟨@TensorProduct.tmul A _ (B' φ) N _ _ _ _ ((1 : B) : B' φ) ⟨x, hx⟩, ?_⟩
    rw [tensorMul_tmul, one_mul]

/-- `tensorMul` is the composite `B ⊗ N → B ⊗ A ≅ B`. -/
theorem tensorMul_eq (z : (ModuleCat.extendScalars φ).obj (ModuleCat.of A N)) :
    tensorMul φ N z =
      TensorProduct.rid A (B' φ) (LinearMap.lTensor (B' φ) N.subtype z) := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | tmul b x =>
    rw [tensorMul_tmul, LinearMap.lTensor_tmul, TensorProduct.rid_tmul]
    change @HMul.hMul B B B instHMul b (φ x.1) = @HMul.hMul B B B instHMul (φ x.1) b
    exact mul_comm _ _
  | add y z hy hz => rw [map_add, map_add, map_add, hy, hz]

/-- **Flat base change of an ideal**: for `φ : A → B` flat, `B ⊗_A N → B` is injective
(tensoring `N ↪ A` with the flat module `B` stays injective). -/
theorem injective_tensorMul (hφ : φ.Flat) : Function.Injective (tensorMul φ N) := by
  haveI : Module.Flat A (B' φ) := hφ
  have hinj : Function.Injective (LinearMap.lTensor (B' φ) N.subtype) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective
  intro z w hzw
  apply hinj
  apply (TensorProduct.rid A (B' φ)).injective
  rw [← tensorMul_eq, ← tensorMul_eq]
  exact hzw

end MiyaokaMori.FlatIdealBaseChange

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X₁ X₂ : AlgebraicGeometry.Scheme.{u}} (g : X₁ ⟶ X₂) (I : X₂.IdealSheafData)

/-- The comparison map `ψₙ := g^*(I.powι n) ≫ ε' : g^*(Iⁿ) ⟶ O_{X₁}`, where
`ε' = (pullbackUnitIso g).hom : g^*O_{X₂} ≅ O_{X₁}` (Stacks 0805, first paragraph). -/
def reesComparison (n : ℕ) :
    (AlgebraicGeometry.Scheme.Modules.pullback g).obj (I.pow n) ⟶
      SheafOfModules.unit X₁.ringCatSheaf :=
  (AlgebraicGeometry.Scheme.Modules.pullback g).map (I.powι n) ≫
    (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso g).hom

theorem powι_app_apply (n : ℕ) (W : X₂.Opens) (s : Γ(I.pow n, W)) :
    (I.powι n).app W s = s.1 := rfl

section Affine

variable (n : ℕ) (U : X₂.affineOpens) (V : X₁.affineOpens) (h : V.1 ≤ g ⁻¹ᵁ U.1)

/-- The canonical map `Γ(X₁,V) ⊗_{Γ(X₂,U)} Γ(U, Iⁿ) → Γ(V, g^*Iⁿ)` (transpose of section pullback),
an isomorphism by Stacks 01I9 (`isIso_transpose_pullbackSectionsNative`). -/
abbrev transposeNative :
    (ModuleCat.extendScalars (g.appLE U.1 V.1 h).hom).obj
        (ModuleCat.of Γ(X₂, U.1) Γ(I.pow n, U.1)) ⟶
      ModuleCat.of Γ(X₁, V.1) Γ((AlgebraicGeometry.Scheme.Modules.pullback g).obj (I.pow n), V.1) :=
  ((ModuleCat.extendRestrictScalarsAdj (g.appLE U.1 V.1 h).hom).homEquiv _ _).symm
    (AlgebraicGeometry.Scheme.Modules.pullbackSectionsNative g (I.pow n) U.1 V.1 h)

/-- `ψₙ.app V (b ⊗ s) = b · φ(s)`: under the tensor description of `Γ(V, g^*Iⁿ)`, the comparison
map is `Γ(X₁,V) ⊗_A Γ(U,Iⁿ) → Γ(X₁,V)`, `b ⊗ x ↦ b φ(x)`. -/
theorem reesComparison_app_transposeNative
    (z : (ModuleCat.extendScalars (g.appLE U.1 V.1 h).hom).obj
        (ModuleCat.of Γ(X₂, U.1) Γ(I.pow n, U.1))) :
    (I.reesComparison g n).app V.1 (transposeNative g I n U V h z) =
      MiyaokaMori.FlatIdealBaseChange.tensorMul (g.appLE U.1 V.1 h).hom
        ((I.powSubmodule n).obj (op U.1)) z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero, map_zero]
  | tmul b s =>
    erw [AlgebraicGeometry.Scheme.Modules.transpose_pullbackSectionsNative_tmul,
      MiyaokaMori.FlatIdealBaseChange.tensorMul_tmul]
    rw [AlgebraicGeometry.Scheme.Modules.Hom.app_smul, reesComparison,
      AlgebraicGeometry.Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
      AlgebraicGeometry.Scheme.Modules.pullback_map_app_pullbackSectionsOn, powι_app_apply]
    erw [AlgebraicGeometry.Scheme.Modules.pullbackUnitIso_hom_app_pullbackSectionsOn_unit]
    rfl
  | add y z hy hz => rw [map_add, map_add, map_add, hy, hz]

/-- Every section of `g^*Iⁿ` over `V` is a sum of `b • (g^*s)|_V` (Stacks 01I9; uses the
quasi-coherence of `Iⁿ`). -/
theorem transposeNative_surjective : Function.Surjective (transposeNative g I n U V h) := by
  haveI := I.pow_isQuasicoherent n
  haveI : IsIso (transposeNative g I n U V h) :=
    AlgebraicGeometry.Scheme.Modules.isIso_transpose_pullbackSectionsNative g (I.pow n) U.1 U.2 V.1
      V.2 h
  exact (ConcreteCategory.bijective_of_isIso _).2

/-- **Affine-local image of `ψₙ`**: on `V ≤ g⁻¹U`, the image of `ψₙ` is the extended ideal
`Γ(U, Iⁿ)·Γ(X₁, V)`. No flatness needed. -/
theorem range_reesComparison_app :
    Set.range ((I.reesComparison g n).app V.1) =
      ((Ideal.map (g.appLE U.1 V.1 h).hom ((I.powSubmodule n).obj (op U.1)) : Ideal Γ(X₁, V.1)) :
        Set Γ(X₁, V.1)) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨z, rfl⟩ := transposeNative_surjective g I n U V h x
    rw [reesComparison_app_transposeNative]
    have hz : MiyaokaMori.FlatIdealBaseChange.tensorMul (g.appLE U.1 V.1 h).hom
        ((I.powSubmodule n).obj (op U.1)) z ∈ LinearMap.range
          (MiyaokaMori.FlatIdealBaseChange.tensorMul (g.appLE U.1 V.1 h).hom
            ((I.powSubmodule n).obj (op U.1))).hom := ⟨z, rfl⟩
    rw [MiyaokaMori.FlatIdealBaseChange.range_tensorMul] at hz
    exact hz
  · intro hy
    have hy' : y ∈ LinearMap.range
        (MiyaokaMori.FlatIdealBaseChange.tensorMul (g.appLE U.1 V.1 h).hom
          ((I.powSubmodule n).obj (op U.1))).hom := by
      rw [MiyaokaMori.FlatIdealBaseChange.range_tensorMul]
      exact hy
    obtain ⟨z, rfl⟩ := hy'
    exact ⟨transposeNative g I n U V h z, reesComparison_app_transposeNative g I n U V h z⟩

include U h in
/-- **Affine-local injectivity of `ψₙ`** for `g` flat: `Γ(U,Iⁿ) ⊗_A B → B` is injective because
`B` is a flat `A`-module (`Scheme.Hom.flat_appLE`). This is where flatness enters Stacks 0805. -/
theorem reesComparison_app_injective [AlgebraicGeometry.Flat g] :
    Function.Injective ((I.reesComparison g n).app V.1) := by
  intro x y hxy
  obtain ⟨z, rfl⟩ := transposeNative_surjective g I n U V h x
  obtain ⟨w, rfl⟩ := transposeNative_surjective g I n U V h y
  rw [reesComparison_app_transposeNative, reesComparison_app_transposeNative] at hxy
  rw [MiyaokaMori.FlatIdealBaseChange.injective_tensorMul _ _ (g.flat_appLE U.2 V.2 h) hxy]

end Affine

end AlgebraicGeometry.Scheme.IdealSheafData

end
