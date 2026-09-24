import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.Vanishing.Stacks02uxAux
import MiyaokaMori.AlgebraicGeometry.Cohomology.ExtendByZero.Stacks02uxExtendByZeroDesc

/-! # The canonical inclusion `j_!ℤ_U ⟶ ℤ_X`

Stacks 0A38 speaks of sections of the constant sheaf `ℤ_X` over an open `U`, i.e. of the canonical
inclusion `c_U : j_!ℤ_U ⟶ ℤ_X` ("the section `1` over `U`") and its multiples `n • c_U` ("the constant
section `n` over `U`"). Here

* `constantInclusion U : j_!ℤ_U ⟶ ℤ_X` is `extendByZeroDesc U` (the transpose along `j_! ⊣ j^{-1}`,
  `Stacks02uxExtendByZeroDesc.lean`) of the canonical isomorphism `ℤ_U ≅ (ℤ_X)|_U` (`restrictConstantSheafIso`);
* it is characterised by `constantInclusion_comp_restrictUnit`: composed with the restriction map
  `η_U : ℤ_X ⟶ j_*(ℤ_X|_U)` (`restrictUnit`) it is `j_!ℤ_U ⟶ j_*ℤ_U ≅ j_*(ℤ_X|_U)` (i.e. on sections coming
  from the presheaf `V ↦ ℤ_U(V)` for `V ⊆ U` it is the canonical identification `ℤ_U(V) = ℤ_X(V)`);
* it is a monomorphism (`constantInclusion_mono`; this also proves `exists_mono_extendByZeroConstant_to_constant`).

Source: Stacks 0A38 (cohomology-lemma-subsheaf-of-constant-sheaf); Stacks 00A5 (sheaves-lemma-j-shriek-abelian);
Stacks 02UX third paragraph ("`j_!ℤ_U ⊂ ℤ_X`"). -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

noncomputable section

namespace TopCat.Sheaf

variable {X : TopCat.{u}}

/-- **the canonical inclusion** `c_U : j_!ℤ_U ⟶ ℤ_X` ("the section `1` of `ℤ_X` over `U`"): the morphism
induced (`extendByZeroDesc`) by the canonical isomorphism `ℤ_U ≅ (ℤ_X)|_U` -/
def constantInclusion (U : Opens X) :
    extendByZeroConstant U ⟶
      (CategoryTheory.constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift ℤ)) :=
  extendByZeroDesc U (restrictConstantSheafIso U (AddCommGrpCat.of (ULift ℤ))).inv

/-- characterisation of the canonical inclusion: `c_U ≫ η_U = (j_!ℤ_U ⟶ j_*ℤ_U) ≫ j_*(ℤ_U ≅ (ℤ_X)|_U)` -/
theorem constantInclusion_comp_restrictUnit (U : Opens X) :
    constantInclusion U ≫ restrictUnit U _ =
      extendByZeroToPushforward U _ ≫
        (TopCat.Sheaf.pushforward AddCommGrpCat.{u} (Opens.inclusion' U)).map
          (restrictConstantSheafIso U (AddCommGrpCat.of (ULift ℤ))).inv :=
  extendByZeroDesc_comp_restrictUnit U _

/-- the canonical inclusion `j_!ℤ_U ⟶ ℤ_X` is a monomorphism (stated as a theorem, not an instance). -/
theorem constantInclusion_mono (U : Opens X) : Mono (constantInclusion U) :=
  extendByZeroDesc_mono_of_isIso U _

end TopCat.Sheaf

end
