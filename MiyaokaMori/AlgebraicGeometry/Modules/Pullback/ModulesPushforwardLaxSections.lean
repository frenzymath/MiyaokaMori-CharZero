import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPushforwardLaxMonoidal
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorSectionsCoherence

/-! # The lax monoidal structure of pushforward on section pairings

The lax structure `μ : f_*A ⊗ f_*B ⟶ f_*(A ⊗ B)` of the pushforward of sheaves of modules
(`pushforwardLaxMonoidal`) evaluated on a pairing of sections: for `U ⊆ Y` open,
`a ∈ A(f⁻¹U)`, `b ∈ B(f⁻¹U)`, we have `μ_U(a ⊗ b) = a ⊗ b ∈ (A ⊗ B)(f⁻¹U)` (both sides are
`Modules.tensorSections`). This is the one characterization needed to connect the oplax `δ`
(`pullbackTensorObjHom`) with the section formulas.

Proof: unfold the transported `μ` as `(c⁻¹ ⊗ c⁻¹) ≫ μ_L ≫ L(μ^{pre}) ≫ L(f_*^{pre} μ_G) ≫ c`; the
first two factors are `tensorToSheafify (f_*A) (f_*B)`, the last three are `L(h) ≫ c` with
`h := μ^{pre}_{GA,GB} ≫ f_*^{pre}(σ_{A,B})`, `σ = tensorSectionsHom` (`= μ_G`, `rfl`).
`tensorToSheafify_tensorSections` sends the pairing to the image `η^{sh}(a ⊗ₜ b)` of the
sheafification unit; `sheafify_unit_counit_eval` gives `(L(h) ≫ c)(η^{sh} x) = h x`; and
`h(a ⊗ₜ b) = σ_{f⁻¹U}(a ⊗ₜ b) = tensorSections A B (f⁻¹U) a b`, since the `μ` of the presheaf
pushforward is the identity on pure tensors (`ModuleCat.restrictScalars_μ_tmul`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
universe u
open CategoryTheory MonoidalCategory Opposite
open CategoryTheory.Functor.LaxMonoidal
open scoped AlgebraicGeometry

noncomputable section
namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)

/-- The `μ` of `G = forgetPre` is the presheaf morphism `tensorSectionsHom` of section pairings. -/
theorem forgetPre_μ (A B : X.Modules) :
    letI := forgetPre_lax X
    μ (forgetPre X) A B = tensorSectionsHom A B := rfl

/-- The `μ` of the presheaf pushforward is the identity on pure tensors. -/
theorem pushforwardPre_μ_tmul (P Q : _root_.PresheafOfModules.{u} X.ringCatSheaf.obj)
    (U : Y.Opens) (p : P.obj (op (f ⁻¹ᵁ U))) (q : Q.obj (op (f ⁻¹ᵁ U))) :
    letI := pushforwardPre_lax f
    (μ (pushforwardPre f) P Q).app (op U)
        (TensorProduct.tmul (Y.presheaf.obj (op U))
          (show ((pushforwardPre f).obj P).obj (op U) from p)
          (show ((pushforwardPre f).obj Q).obj (op U) from q)) =
      (TensorProduct.tmul (X.presheaf.obj (op (f ⁻¹ᵁ U))) p q :
        (P ⊗ Q).obj (op (f ⁻¹ᵁ U))) := by
  exact (ModuleCat.restrictScalars_μ_tmul (f.c.app (op U)).hom _ _ p q).trans rfl

/-- Unfolding of the transported `μ`: `tensorToSheafify`, then `L(h)`, then the sheafification counit. -/
theorem pushforwardLaxMonoidal_μ_eq (A B : X.Modules) :
    letI := pushforwardLaxMonoidal f
    μ (pushforward f) A B =
      tensorToSheafify ((pushforward f).obj A) ((pushforward f).obj B) ≫
        (shL Y).map (μ (pushforwardPre f) ((shG X).obj A) ((shG X).obj B)
            (self := pushforwardPre_lax f) ≫
          (pushforwardPre f).map (tensorSectionsHom A B)) ≫
        (shAdj Y).counit.app ((pushforward f).obj (A ⊗ B)) := by
  let _ := forgetPre_lax X
  let _ := pushforwardPre_lax f
  unfold pushforwardLaxMonoidal
  rw [Functor.LaxMonoidal.transport_μ]
  erw [Functor.LaxMonoidal.comp_μ, Functor.LaxMonoidal.comp_μ]
  refine Eq.trans ?_ (congrArg
    (tensorToSheafify ((pushforward f).obj A) ((pushforward f).obj B) ≫ ·)
    (congrArg (· ≫ (shAdj Y).counit.app ((pushforward f).obj (A ⊗ B)))
      ((shL Y).map_comp _ _).symm))
  simp only [Category.assoc]
  rfl

/-- **The `μ` of pushforward on a pairing of sections**: `μ_U(a ⊗ b) = a ⊗ b` (the right-hand side is
the section pairing on `X` over `f⁻¹U`). -/
theorem pushforwardLaxMonoidal_μ_tensorSections (A B : X.Modules) (U : Y.Opens)
    (a : A.val.obj (op (f ⁻¹ᵁ U))) (b : B.val.obj (op (f ⁻¹ᵁ U))) :
    letI := pushforwardLaxMonoidal f
    (μ (pushforward f) A B).val.app (op U)
        (tensorSections ((pushforward f).obj A) ((pushforward f).obj B) U a b) =
      tensorSections A B (f ⁻¹ᵁ U) a b := by
  rw [pushforwardLaxMonoidal_μ_eq]
  have h2 := tensorToSheafify_tensorSections ((pushforward f).obj A) ((pushforward f).obj B) U a b
  refine (congrArg (fun z => ((shL Y).map (μ (pushforwardPre f) ((shG X).obj A) ((shG X).obj B)
            (self := pushforwardPre_lax f) ≫
          (pushforwardPre f).map (tensorSectionsHom A B)) ≫
        (shAdj Y).counit.app ((pushforward f).obj (A ⊗ B))).val.app (op U) z) h2).trans ?_
  refine (sheafify_unit_counit_eval (X := Y) (A := (pushforward f).obj (A ⊗ B))
    (μ (pushforwardPre f) ((shG X).obj A) ((shG X).obj B) (self := pushforwardPre_lax f) ≫
      (pushforwardPre f).map (tensorSectionsHom A B)) U _).trans ?_
  exact congrArg ((tensorSectionsHom A B).app (op (f ⁻¹ᵁ U)))
    (pushforwardPre_μ_tmul f ((shG X).obj A) ((shG X).obj B) U a b)

end AlgebraicGeometry.Scheme.Modules
end
