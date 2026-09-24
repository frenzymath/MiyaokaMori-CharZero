import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModulePullbackStalkTensorBijective

/-! # Stalks of the pullback along an open immersion

When the stalk map `g.stalkMap x : O_{Y,g x} → O_{X,x}` of `g : X ⟶ Y` is an isomorphism (e.g. `g`
an open immersion), the unit `u : M_{g x} → (g^*M)_x` of the pullback–pushforward adjunction on
stalks is bijective and sends the germ of a section to the germ of the pulled-back section. In
particular, for an open immersion `j : U → X` and `M : X.Modules`, `(j^*M)_y ≅ M_{j y}`
(semilinearly along `j.stalkMap y`).

Proof:
1. Pure algebra: if `φ : A → B` is a ring isomorphism, then `m ↦ 1 ⊗ m : M → B ⊗_A M` is bijective —
   `φ⁻¹` gives an `A`-linear isomorphism `B ≃ₗ[A] A`; composing with `TensorProduct.congr` and
   `TensorProduct.lid` gives `Φ : B ⊗_A M ≃ₗ[A] M`, and `Φ.symm m = 1 ⊗ m` by direct computation.
2. By `modulePullbackStalkTensorMap_bijective`, the canonical map
   `modulePullbackStalkTensorMap : O_{X,x} ⊗_{O_{Y,g x}} M_{g x} → (g^*M)_x` is bijective and sends
   `1 ⊗ m ↦ 1 • u m = u m` on pure tensors (`modulePullbackStalkTensorMap_tmul`). So `u` is the
   composite of two bijections.
3. The stalk map of an open immersion is an isomorphism (Mathlib instance `IsIso (g.stalkMap x)` for
   `AlgebraicGeometry.IsOpenImmersion`); in `CommRingCat` an isomorphism is a bijection of the
   underlying functions, so step 2 applies.
4. Compatibility with germs is `modulePullbackStalkUnitAddHom_germ`.

Source: Stacks 01AX (pullback along an open immersion does not change stalks).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open CategoryTheory Opposite
open scoped AlgebraicGeometry TensorProduct

namespace MiyaokaMori.PullbackStalkOpenImmersion

universe u

/-- Extension of scalars along a ring isomorphism: `m ↦ 1 ⊗ m` is bijective. -/
theorem oneTmul_bijective {A B M : Type u} [CommRing A] [CommRing B]
    [AddCommGroup M] [Module A M] (φ : A →+* B) (hφ : Function.Bijective φ) :
    letI := φ.toAlgebra
    Function.Bijective (fun m : M ↦ (1 : B) ⊗ₜ[A] m) := by
  letI := φ.toAlgebra
  let ε : A ≃+* B := RingEquiv.ofBijective φ hφ
  have hsmul : ∀ (a : A) (b : B), a • b = φ a * b := fun a b ↦ rfl
  -- `B` as an `A`-module is isomorphic to `A`
  let eB : B ≃ₗ[A] A :=
    { ε.symm with
      map_smul' := fun a b ↦ by
        show (ε.symm (a • b) : A) = a • ε.symm b
        rw [hsmul]
        show (ε.symm (ε a * b) : A) = a * ε.symm b
        rw [map_mul, ε.symm_apply_apply] }
  let Φ : B ⊗[A] M ≃ₗ[A] M :=
    (TensorProduct.congr eB (LinearEquiv.refl A M)).trans (TensorProduct.lid A M)
  have hΦ : ∀ m : M, Φ.symm m = (1 : B) ⊗ₜ[A] m := by
    intro m
    show (TensorProduct.congr eB (LinearEquiv.refl A M)).symm
      ((TensorProduct.lid A M).symm m) = _
    rw [TensorProduct.lid_symm_apply, TensorProduct.congr_symm_tmul]
    change eB.symm 1 ⊗ₜ[A] m = _
    have : eB.symm (1 : A) = (1 : B) := by
      show ε (1 : A) = (1 : B)
      exact map_one ε
    rw [this]
  have : (fun m : M ↦ (1 : B) ⊗ₜ[A] m) = Φ.symm := funext fun m ↦ (hΦ m).symm
  rw [this]
  exact Φ.symm.bijective

/-- When the stalk map is an isomorphism, the unit map on pullback stalks is bijective. -/
theorem modulePullbackStalkUnit_bijective {X Y : AlgebraicGeometry.Scheme.{u}} (g : X ⟶ Y)
    (M : Y.Modules) (x : X) [IsIso (g.stalkMap x)] :
    Function.Bijective (AlgebraicGeometry.Scheme.Modules.modulePullbackStalkUnit g M x) := by
  letI := AlgebraicGeometry.Scheme.Modules.modulePullbackStalkAlgebra g x
  have hφ : Function.Bijective (g.stalkMap x).hom :=
    (ConcreteCategory.bijective_of_isIso (g.stalkMap x))
  have h1 := oneTmul_bijective (M := M.presheaf.stalk (g.base x)) (g.stalkMap x).hom hφ
  have h2 := MiyaokaMori.PullbackStalkTensor.modulePullbackStalkTensorMap_bijective g M x
  have hcomp : (fun m : M.presheaf.stalk (g.base x) ↦
      AlgebraicGeometry.Scheme.Modules.modulePullbackStalkUnit g M x m) =
      (fun z ↦ AlgebraicGeometry.Scheme.Modules.modulePullbackStalkTensorMap g M x z) ∘
        (fun m : M.presheaf.stalk (g.base x) ↦
          (1 : X.presheaf.stalk x) ⊗ₜ[Y.presheaf.stalk (g.base x)] m) := by
    funext m
    show _ = AlgebraicGeometry.Scheme.Modules.modulePullbackStalkTensorMap g M x
      ((1 : X.presheaf.stalk x) ⊗ₜ[Y.presheaf.stalk (g.base x)] m)
    rw [AlgebraicGeometry.Scheme.Modules.modulePullbackStalkTensorMap_tmul, one_smul]
  show Function.Bijective (fun m ↦ AlgebraicGeometry.Scheme.Modules.modulePullbackStalkUnit g M x m)
  rw [hcomp]
  exact h2.comp h1

/-- The stalk isomorphism `(j^*M)_y ≅ M_{j y}` for an open immersion (an additive isomorphism,
semilinear along `j.stalkMap y`). -/
def modulePullbackStalkEquivOfIsIso {X Y : AlgebraicGeometry.Scheme.{u}} (g : X ⟶ Y)
    (M : Y.Modules) (x : X) [IsIso (g.stalkMap x)] :
    M.presheaf.stalk (g.base x) ≃+ AlgebraicGeometry.Scheme.Modules.modulePullbackStalk g M x :=
  AddEquiv.ofBijective (AlgebraicGeometry.Scheme.Modules.modulePullbackStalkUnit g M x).toAddMonoidHom
    (modulePullbackStalkUnit_bijective g M x)

/-- The isomorphism sends the germ of a section to the germ of the pulled-back section. -/
theorem modulePullbackStalkEquivOfIsIso_germ {X Y : AlgebraicGeometry.Scheme.{u}} (g : X ⟶ Y)
    (M : Y.Modules) (x : X) [IsIso (g.stalkMap x)] (U : Y.Opens) (hx : g.base x ∈ U)
    (m : M.val.obj (op U)) :
    modulePullbackStalkEquivOfIsIso g M x ((M.presheaf.germ U (g.base x) hx).hom m) =
      (((AlgebraicGeometry.Scheme.Modules.pullback g).obj M).presheaf.germ
        (g ⁻¹ᵁ U) x hx).hom
        (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction g).unit.app M).app U m) :=
  AlgebraicGeometry.Scheme.Modules.modulePullbackStalkUnitAddHom_germ g M x U hx m

end MiyaokaMori.PullbackStalkOpenImmersion

end
