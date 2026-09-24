import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.TrivialLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorUnitIso
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesRestrictMonoidal
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorPower
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.DualSheafOld
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.LineBundleDualEvalIso

/-! # Tensor products and duals of invertible sheaves (Stacks 01CT)

Stacks 01CT: the tensor product of line bundles (invertible sheaves) is a line bundle; the dual
`Hom(L, O_X)` of a line bundle is a line bundle and the evaluation map `L ⊗ L^∨ → O_X` is an isomorphism.
Consequence: the tensor powers `L^{⊗m}` of a line bundle are line bundles (needed for the group structure
of `Pic` and for ampleness).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Shrink a trivialization on an open `U` to a smaller open `V ≤ U`. -/
def AlgebraicGeometry.Scheme.Modules.Trivialization.shrink {X : AlgebraicGeometry.Scheme.{u}}
    {M : X.Modules} (t : AlgebraicGeometry.Scheme.Modules.Trivialization M)
    {V : X.Opens} (h : V ≤ t.carrier) :
    M.restrict V.ι ≅ SheafOfModules.unit V.toScheme.ringCatSheaf :=
  (AlgebraicGeometry.Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι h).symm).app M ≪≫
    (AlgebraicGeometry.Scheme.Modules.restrictFunctorComp (X.homOfLE h) t.carrier.ι).app M ≪≫
    (AlgebraicGeometry.Scheme.Modules.restrictFunctor (X.homOfLE h)).mapIso t.iso ≪≫
    AlgebraicGeometry.Scheme.Modules.restrictUnitIso (X.homOfLE h)

/-- `O_V ⊗ O_V ≅ O_V`. -/
def AlgebraicGeometry.Scheme.Modules.unitTensorUnitIso (V : AlgebraicGeometry.Scheme.{u}) :
    CategoryTheory.MonoidalCategoryStruct.tensorObj (C := V.Modules)
        (SheafOfModules.unit V.ringCatSheaf) (SheafOfModules.unit V.ringCatSheaf) ≅
      SheafOfModules.unit V.ringCatSheaf :=
  CategoryTheory.MonoidalCategory.whiskerRightIso
      (CategoryTheory.eqToIso (AlgebraicGeometry.Scheme.Modules.unit_eq_tensorUnit V)) _ ≪≫
    CategoryTheory.MonoidalCategoryStruct.leftUnitor (C := V.Modules)
      (SheafOfModules.unit V.ringCatSheaf)

/-- The tensor product of line bundles is a line bundle (Stacks 01CT).

Proof: `restrictTensorObjIso` ("restriction to an open commutes with `⊗`") gives, for trivializing opens
`U₁`, `U₂` of `L`, `N` at `x` and `U = U₁ ⊓ U₂`, `(L ⊗ N)|_U ≅ L|_U ⊗ N|_U ≅ O_U ⊗ O_U ≅ O_U`. -/
instance SheafOfModules.IsLineBundle.tensor {X : AlgebraicGeometry.Scheme.{u}} (L N : X.Modules)
    [L.IsLineBundle] [N.IsLineBundle] :
    (AlgebraicGeometry.Scheme.Modules.tensor L N).IsLineBundle := by
  refine ⟨fun x => ?_⟩
  obtain ⟨t₁, hx₁⟩ := AlgebraicGeometry.Scheme.Modules.IsLineBundle.exists_trivialization L x
  obtain ⟨t₂, hx₂⟩ := AlgebraicGeometry.Scheme.Modules.IsLineBundle.exists_trivialization N x
  refine ⟨t₁.carrier ⊓ t₂.carrier, ⟨hx₁, hx₂⟩, ⟨?_⟩⟩
  exact (AlgebraicGeometry.Scheme.Modules.restrictFunctor (t₁.carrier ⊓ t₂.carrier).ι).mapIso
      (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj L N) ≪≫
    AlgebraicGeometry.Scheme.Modules.restrictTensorObjIso _ L N ≪≫
    CategoryTheory.MonoidalCategory.tensorIso
      (t₁.shrink inf_le_left) (t₂.shrink inf_le_right) ≪≫
    AlgebraicGeometry.Scheme.Modules.unitTensorUnitIso _

/-- Tensor powers of a line bundle are line bundles.

Induction on `m`: the inductive step is `IsLineBundle.tensor` (`tensorPow L (e+1) = tensor (tensorPow L e) L`
by definition), the base case `tensorPow L 0 = O_X` is `IsLineBundle.unit`. -/
instance SheafOfModules.IsLineBundle.tensorPow {X : AlgebraicGeometry.Scheme.{u}} (L : X.Modules)
    [L.IsLineBundle] (m : ℕ) : (AlgebraicGeometry.Scheme.Modules.tensorPow L m).IsLineBundle := by
  induction m with
  | zero => exact SheafOfModules.IsLineBundle.unit X
  | succ e ih => exact SheafOfModules.IsLineBundle.tensor _ L

/-- The dual of a line bundle is a line bundle (Stacks 01CT).

Proof: `Modules.dual L = moduleSheafDual L` is the sheafification of the dual sheaf `dualSheaf L` (defined
without sheafification), and the sheafification unit is an isomorphism here (the dual presheaf is already a
sheaf, `moduleDualPresheaf_isSheaf`), so the two are isomorphic (`dualSheafIsoOld`); a frame of `dualSheaf L`
is given explicitly by the dual frame `e^∨ = coord_e` of a frame `e` (`IsFrame.dualFrame_isFrame`), and
"has a frame ⟺ line bundle" concludes. -/
instance SheafOfModules.IsLineBundle.dual {X : AlgebraicGeometry.Scheme.{u}} (L : X.Modules)
    [L.IsLineBundle] : (AlgebraicGeometry.Scheme.Modules.dual L).IsLineBundle :=
  AlgebraicGeometry.Scheme.Modules.moduleSheafDual_isLineBundle L

/- The evaluation map `L ⊗ L^∨ → O_X` is an isomorphism: `Modules.tensor ≅ ⊗` (`tensorIsoTensorObj`), swap
   the factors (braiding), then the internal Hom evaluation `𝓗om(L, O) ⊗ L → O` (`internalHomEval`;
   `L^∨ = moduleSheafDual L` and `internalHom L O` are given by the same construction, so the evaluation
   morphism acts directly on `dual L`).

   Route: see the auxiliary module `Stacks01ct_DualEval` (`isIso_internalHomEval_unit`:
   `sheafifyTensorTo ≫ ev = L(p) ≫ ε`, where `p` is locally bijective on frame opens, hence an isomorphism
   after sheafification). -/

/-- The evaluation map `L ⊗ L^∨ → O_X` is an isomorphism (Stacks 01CT / 0B8K).

Proof: the first two factors are `hom`s of isomorphisms; `internalHomEval L O` is an isomorphism by
`isIso_internalHomEval_unit` (`sheafifyTensorTo ≫ ev = L(p) ≫ ε`, `p` locally bijective, hence an
isomorphism after sheafification). -/
theorem SheafOfModules.IsLineBundle.isIso_tensorDualEval {X : AlgebraicGeometry.Scheme.{u}} (L : X.Modules)
    [L.IsLineBundle] :
    CategoryTheory.IsIso
      ((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj L (AlgebraicGeometry.Scheme.Modules.dual L)).hom ≫
        (β_ L (AlgebraicGeometry.Scheme.Modules.dual L)).hom ≫
        AlgebraicGeometry.Scheme.Modules.internalHomEval L (SheafOfModules.unit X.ringCatSheaf)) :=
  have h := AlgebraicGeometry.Scheme.Modules.isIso_internalHomEval_dual L
  @CategoryTheory.IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance
    (@CategoryTheory.IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance h)

/-- `L ⊗ L^∨ ≅ O_X` (a consequence of the evaluation map being an isomorphism). -/
theorem SheafOfModules.IsLineBundle.tensor_dual_iso {X : AlgebraicGeometry.Scheme.{u}} (L : X.Modules)
    [L.IsLineBundle] :
    Nonempty (AlgebraicGeometry.Scheme.Modules.tensor L (AlgebraicGeometry.Scheme.Modules.dual L)
      ≅ SheafOfModules.unit X.ringCatSheaf) :=
  ⟨@CategoryTheory.asIso _ _ _ _ _ (SheafOfModules.IsLineBundle.isIso_tensorDualEval L)⟩

end
