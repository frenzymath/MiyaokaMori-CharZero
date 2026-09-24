import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.Algebra.Category.ModuleCat.Stalk
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
import Mathlib.CategoryTheory.Monoidal.Limits.Colimits
import Mathlib.CategoryTheory.Filtered.Final

/-!
# Tensor products and module stalks

The sectionwise tensor product of module presheaves commutes with passage to stalks.
The inverse sends two germs represented on the same neighbourhood to the germ of their
pure tensor. Filtered colimits of sets commute with finite products, so this construction
is independent of all representatives. No local freeness or finite generation is required.

This is the presheaf-colimit step of Stacks Project, Tag 01CB. The stalk modules use
Mathlib's canonical action of the structure-sheaf stalk. Comparison with a sheafified
tensor product is a separate construction.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite MonoidalCategory
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

universe u

set_option backward.isDefEq.respectTransparency false

attribute [local instance] IsFiltered.isSifted

variable (X : Scheme.{u})
  (M N : PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat RingCat)) (x : X)

private abbrev stalkTypesCocone
    (P : PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat RingCat)) :=
  (CategoryTheory.forget Ab).mapCocone
    (colimit.cocone ((OpenNhds.inclusion x).op ⋙ P.presheaf))

private def stalkTypesIsColimit (P : PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat RingCat)) :
    IsColimit (stalkTypesCocone X x P) :=
  isColimitOfPreserves (CategoryTheory.forget Ab) (colimit.isColimit _)

/-- A pair of module germs has representatives over one common neighbourhood. -/
theorem modulePresheafStalk_exists_pair
    (m : ↑(TopCat.Presheaf.stalk (C := Ab) M.presheaf x))
    (n : ↑(TopCat.Presheaf.stalk (C := Ab) N.presheaf x)) :
    ∃ (U : X.Opens) (hx : x ∈ U) (a : M.obj (op U)) (b : N.obj (op U)),
      TopCat.Presheaf.germ M.presheaf U x hx a = m ∧
      TopCat.Presheaf.germ N.presheaf U x hx b = n := by
  obtain ⟨U, ⟨a, b⟩, h⟩ := Types.jointly_surjective_of_isColimit
    ((stalkTypesIsColimit X x M).tensor (stalkTypesIsColimit X x N)) (m, n)
  exact ⟨U.unop.1, U.unop.2, a, b, congrArg Prod.fst h, congrArg Prod.snd h⟩

/-- Three module germs have representatives over one common neighbourhood. -/
theorem modulePresheafStalk_exists_triple
    (P : PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat RingCat))
    (m : ↑(TopCat.Presheaf.stalk (C := Ab) M.presheaf x))
    (n : ↑(TopCat.Presheaf.stalk (C := Ab) N.presheaf x))
    (p : ↑(TopCat.Presheaf.stalk (C := Ab) P.presheaf x)) :
    ∃ (U : X.Opens) (hx : x ∈ U) (a : M.obj (op U)) (b : N.obj (op U))
      (c : P.obj (op U)),
      TopCat.Presheaf.germ M.presheaf U x hx a = m ∧
      TopCat.Presheaf.germ N.presheaf U x hx b = n ∧
      TopCat.Presheaf.germ P.presheaf U x hx c = p := by
  obtain ⟨U, ⟨a, b, c⟩, h⟩ := Types.jointly_surjective_of_isColimit
    ((stalkTypesIsColimit X x M).tensor
      ((stalkTypesIsColimit X x N).tensor (stalkTypesIsColimit X x P))) (m, n, p)
  exact ⟨U.unop.1, U.unop.2, a, b, c, congrArg Prod.fst h,
    congrArg (Prod.fst ∘ Prod.snd) h, congrArg (Prod.snd ∘ Prod.snd) h⟩

private def tensorGermPairCocone :
    Cocone (((OpenNhds.inclusion x).op ⋙ M.presheaf ⋙ CategoryTheory.forget Ab) ⊗
      ((OpenNhds.inclusion x).op ⋙ N.presheaf ⋙ CategoryTheory.forget Ab)) where
  pt := ↑(TopCat.Presheaf.stalk (C := Ab)
      (PresheafOfModules.Monoidal.tensorObj (R := X.presheaf) M N).presheaf x)
  ι.app U := ↾fun ⟨m, n⟩ ↦ TopCat.Presheaf.germ
    (PresheafOfModules.Monoidal.tensorObj (R := X.presheaf) M N).presheaf
      U.unop.1 x U.unop.2 (m ⊗ₜ[X.presheaf.obj (op U.unop.1)] n)
  ι.naturality U V f := by
    ext ⟨m, n⟩
    change TopCat.Presheaf.germ (C := Ab)
      (PresheafOfModules.Monoidal.tensorObj (R := X.presheaf) M N).presheaf
      V.unop.1 x V.unop.2
      (M.map ((OpenNhds.inclusion x).op.map f) m ⊗ₜ[_]
        N.map ((OpenNhds.inclusion x).op.map f) n) = _
    erw [← PresheafOfModules.Monoidal.tensorObj_map_tmul]
    change TopCat.Presheaf.germ (C := Ab)
      (PresheafOfModules.Monoidal.tensorObj (R := X.presheaf) M N).presheaf
        V.unop.1 x V.unop.2
          ((PresheafOfModules.Monoidal.tensorObj (R := X.presheaf) M N).presheaf.map
            ((OpenNhds.inclusion x).op.map f) (m ⊗ₜ[_] n)) =
      TopCat.Presheaf.germ (C := Ab)
        (PresheafOfModules.Monoidal.tensorObj (R := X.presheaf) M N).presheaf
          U.unop.1 x U.unop.2 (m ⊗ₜ[_] n)
    exact TopCat.Presheaf.germ_res_apply' (C := Ab)
      (PresheafOfModules.Monoidal.tensorObj (R := X.presheaf) M N).presheaf
        ((OpenNhds.inclusion x).op.map f) x V.unop.2
          ((show M.obj (op U.unop.1) from m) ⊗ₜ[X.presheaf.obj (op U.unop.1)]
            (show N.obj (op U.unop.1) from n))

/-- The germ of the sectionwise pure tensor, as a function of two germs. -/
def tensorPresheafStalkPair
    (m : ↑(TopCat.Presheaf.stalk (C := Ab) M.presheaf x))
    (n : ↑(TopCat.Presheaf.stalk (C := Ab) N.presheaf x)) :
    ↑(TopCat.Presheaf.stalk (C := Ab)
      (PresheafOfModules.Monoidal.tensorObj (R := X.presheaf) M N).presheaf x) :=
  ((stalkTypesIsColimit X x M).tensor (stalkTypesIsColimit X x N)).desc
    (tensorGermPairCocone X M N x) (m, n)

/-- Pure tensors of representatives compute the stalk pairing. -/
@[simp]
theorem tensorPresheafStalkPair_germ (U : X.Opens) (hx : x ∈ U)
    (m : M.obj (op U)) (n : N.obj (op U)) :
    tensorPresheafStalkPair X M N x
      (TopCat.Presheaf.germ M.presheaf U x hx m)
      (TopCat.Presheaf.germ N.presheaf U x hx n) =
    TopCat.Presheaf.germ
      (PresheafOfModules.Monoidal.tensorObj (R := X.presheaf) M N).presheaf
        U x hx (m ⊗ₜ[X.presheaf.obj (op U)] n) :=
  congrArg (fun f ↦ f.hom' (m, n))
    (((stalkTypesIsColimit X x M).tensor (stalkTypesIsColimit X x N)).fac
      (tensorGermPairCocone X M N x) (op ⟨U, hx⟩))

/-- The stalk pairing is additive in its first variable. -/
theorem tensorPresheafStalkPair_add_left
    (m m' : ↑(TopCat.Presheaf.stalk (C := Ab) M.presheaf x))
    (n : ↑(TopCat.Presheaf.stalk (C := Ab) N.presheaf x)) :
    tensorPresheafStalkPair X M N x (m + m') n =
      tensorPresheafStalkPair X M N x m n + tensorPresheafStalkPair X M N x m' n := by
  obtain ⟨U, hx, a, a', b, rfl, rfl, rfl⟩ :=
    modulePresheafStalk_exists_triple X M M x N m m' n
  rw [← map_add, tensorPresheafStalkPair_germ, TensorProduct.add_tmul, map_add,
    tensorPresheafStalkPair_germ, tensorPresheafStalkPair_germ]

/-- The stalk pairing is additive in its second variable. -/
theorem tensorPresheafStalkPair_add_right
    (m : ↑(TopCat.Presheaf.stalk (C := Ab) M.presheaf x))
    (n n' : ↑(TopCat.Presheaf.stalk (C := Ab) N.presheaf x)) :
    tensorPresheafStalkPair X M N x m (n + n') =
      tensorPresheafStalkPair X M N x m n + tensorPresheafStalkPair X M N x m n' := by
  obtain ⟨U, hx, a, b, b', rfl, rfl, rfl⟩ :=
    modulePresheafStalk_exists_triple X M N x N m n n'
  rw [← map_add, tensorPresheafStalkPair_germ, TensorProduct.tmul_add, map_add,
    tensorPresheafStalkPair_germ, tensorPresheafStalkPair_germ]

/-- A scalar germ and two module germs can be represented on the same neighbourhood. -/
theorem modulePresheafStalk_exists_scalar_pair (r : X.presheaf.stalk x)
    (m : ↑(TopCat.Presheaf.stalk (C := Ab) M.presheaf x))
    (n : ↑(TopCat.Presheaf.stalk (C := Ab) N.presheaf x)) :
    ∃ (U : X.Opens) (hx : x ∈ U) (a : X.presheaf.obj (op U))
      (b : M.obj (op U)) (c : N.obj (op U)),
      X.presheaf.germ U x hx a = r ∧
      TopCat.Presheaf.germ M.presheaf U x hx b = m ∧
      TopCat.Presheaf.germ N.presheaf U x hx c = n := by
  obtain ⟨U, hxU, b, c, rfl, rfl⟩ := modulePresheafStalk_exists_pair X M N x m n
  obtain ⟨V, hVU, hxV, a, rfl⟩ := X.presheaf.exists_le_germ_eq r hxU
  exact ⟨V, hxV, a, M.map (homOfLE hVU).op b, N.map (homOfLE hVU).op c, rfl,
    TopCat.Presheaf.germ_res_apply M.presheaf (homOfLE hVU) x hxV b,
    TopCat.Presheaf.germ_res_apply N.presheaf (homOfLE hVU) x hxV c⟩

/-- The stalk pairing is linear over the local ring in its first variable. -/
theorem tensorPresheafStalkPair_smul_left (r : X.presheaf.stalk x)
    (m : ↑(TopCat.Presheaf.stalk (C := Ab) M.presheaf x))
    (n : ↑(TopCat.Presheaf.stalk (C := Ab) N.presheaf x)) :
    tensorPresheafStalkPair X M N x (r • m) n =
      r • tensorPresheafStalkPair X M N x m n := by
  obtain ⟨U, hx, a, b, c, rfl, rfl, rfl⟩ :=
    modulePresheafStalk_exists_scalar_pair X M N x r m n
  rw [← PresheafOfModules.germ_smul (R := X.presheaf) M,
    tensorPresheafStalkPair_germ, ← TensorProduct.smul_tmul',
    PresheafOfModules.germ_smul (R := X.presheaf), tensorPresheafStalkPair_germ]

/-- The stalk pairing is linear over the local ring in its second variable. -/
theorem tensorPresheafStalkPair_smul_right (r : X.presheaf.stalk x)
    (m : ↑(TopCat.Presheaf.stalk (C := Ab) M.presheaf x))
    (n : ↑(TopCat.Presheaf.stalk (C := Ab) N.presheaf x)) :
    tensorPresheafStalkPair X M N x m (r • n) =
      r • tensorPresheafStalkPair X M N x m n := by
  obtain ⟨U, hx, a, b, c, rfl, rfl, rfl⟩ :=
    modulePresheafStalk_exists_scalar_pair X M N x r m n
  rw [← PresheafOfModules.germ_smul (R := X.presheaf) N,
    tensorPresheafStalkPair_germ, TensorProduct.tmul_smul,
    PresheafOfModules.germ_smul (R := X.presheaf), tensorPresheafStalkPair_germ]

/-- The germ pairing is a bilinear map over the local ring. -/
def tensorPresheafStalkBilinear :
    ↑(TopCat.Presheaf.stalk (C := Ab) M.presheaf x) →ₗ[X.presheaf.stalk x]
      ↑(TopCat.Presheaf.stalk (C := Ab) N.presheaf x) →ₗ[X.presheaf.stalk x]
        ↑(TopCat.Presheaf.stalk (C := Ab)
      (PresheafOfModules.Monoidal.tensorObj (R := X.presheaf) M N).presheaf x) where
  toFun m :=
    { toFun := tensorPresheafStalkPair X M N x m
      map_add' := tensorPresheafStalkPair_add_right X M N x m
      map_smul' := fun r n ↦ tensorPresheafStalkPair_smul_right X M N x r m n }
  map_add' m m' := by
    ext n
    exact tensorPresheafStalkPair_add_left X M N x m m' n
  map_smul' r m := by
    ext n
    exact tensorPresheafStalkPair_smul_left X M N x r m n

/-- The canonical map from the tensor product of stalks to the tensor-presheaf stalk. -/
def tensorPresheafStalkFromTensor :
    (↑(TopCat.Presheaf.stalk (C := Ab) M.presheaf x) ⊗[X.presheaf.stalk x]
      ↑(TopCat.Presheaf.stalk (C := Ab) N.presheaf x)) →ₗ[X.presheaf.stalk x]
        ↑(TopCat.Presheaf.stalk (C := Ab)
      (PresheafOfModules.Monoidal.tensorObj (R := X.presheaf) M N).presheaf x) :=
  TensorProduct.lift (tensorPresheafStalkBilinear X M N x)

/-- The canonical inverse sends the tensor of two germs to the germ of their tensor. -/
@[simp]
theorem tensorPresheafStalkFromTensor_germ (U : X.Opens) (hx : x ∈ U)
    (m : M.obj (op U)) (n : N.obj (op U)) :
    tensorPresheafStalkFromTensor X M N x
      (TopCat.Presheaf.germ M.presheaf U x hx m ⊗ₜ[X.presheaf.stalk x]
        TopCat.Presheaf.germ N.presheaf U x hx n) =
      TopCat.Presheaf.germ
        (PresheafOfModules.Monoidal.tensorObj (R := X.presheaf) M N).presheaf
          U x hx (m ⊗ₜ[X.presheaf.obj (op U)] n) :=
  tensorPresheafStalkPair_germ X M N x U hx m n

/-- Taking germs in each factor gives a semilinear map on tensors of sections. -/
def tensorPresheafGermTensor (U : X.Opens) (hx : x ∈ U) :
    (M.obj (op U) ⊗[X.presheaf.obj (op U)] N.obj (op U))
      →ₛₗ[(X.presheaf.germ U x hx).hom]
      (↑(TopCat.Presheaf.stalk (C := Ab) M.presheaf x) ⊗[X.presheaf.stalk x]
        ↑(TopCat.Presheaf.stalk (C := Ab) N.presheaf x)) :=
  TensorProduct.lift
    { toFun := fun m ↦
        { toFun := fun n ↦ TopCat.Presheaf.germ M.presheaf U x hx m ⊗ₜ[_]
            TopCat.Presheaf.germ N.presheaf U x hx n
          map_add' := by intros; simp only [map_add, TensorProduct.tmul_add]
          map_smul' := by
            intro r n
            rw [PresheafOfModules.germ_smul (R := X.presheaf) N,
              TensorProduct.tmul_smul] }
      map_add' := by
        intro m m'
        ext n
        change (TopCat.Presheaf.germ M.presheaf U x hx (m + m')) ⊗ₜ[_]
          TopCat.Presheaf.germ N.presheaf U x hx n = _
        simp only [map_add, TensorProduct.add_tmul]
        rfl
      map_smul' := by
        intro r m
        ext n
        change (TopCat.Presheaf.germ M.presheaf U x hx (r • m)) ⊗ₜ[_]
          TopCat.Presheaf.germ N.presheaf U x hx n = _
        rw [PresheafOfModules.germ_smul (R := X.presheaf) M, ← TensorProduct.smul_tmul']
        rfl }

/-- The section tensor map is characterized by its action on pure tensors. -/
@[simp]
theorem tensorPresheafGermTensor_tmul (U : X.Opens) (hx : x ∈ U)
    (m : M.obj (op U)) (n : N.obj (op U)) :
    tensorPresheafGermTensor X M N x U hx (m ⊗ₜ[X.presheaf.obj (op U)] n) =
      TopCat.Presheaf.germ M.presheaf U x hx m ⊗ₜ[X.presheaf.stalk x]
        TopCat.Presheaf.germ N.presheaf U x hx n := rfl

private def tensorGermTensorCocone :
    Cocone ((OpenNhds.inclusion x).op ⋙
      (PresheafOfModules.Monoidal.tensorObj (R := X.presheaf) M N).presheaf) where
  pt := AddCommGrpCat.of (↑(TopCat.Presheaf.stalk (C := Ab) M.presheaf x) ⊗[X.presheaf.stalk x]
    ↑(TopCat.Presheaf.stalk (C := Ab) N.presheaf x))
  ι.app U := AddCommGrpCat.ofHom
    (tensorPresheafGermTensor X M N x U.unop.1 U.unop.2).toAddMonoidHom
  ι.naturality U V f := by
    ext t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul m n =>
        change (TopCat.Presheaf.germ M.presheaf V.unop.1 x V.unop.2
          (M.map ((OpenNhds.inclusion x).op.map f) m)) ⊗ₜ[X.presheaf.stalk x]
          (TopCat.Presheaf.germ N.presheaf V.unop.1 x V.unop.2
            (N.map ((OpenNhds.inclusion x).op.map f) n)) =
          (TopCat.Presheaf.germ M.presheaf U.unop.1 x U.unop.2 m) ⊗ₜ[X.presheaf.stalk x]
            (TopCat.Presheaf.germ N.presheaf U.unop.1 x U.unop.2 n)
        exact congrArg₂ (fun a b ↦ a ⊗ₜ[X.presheaf.stalk x] b)
          (TopCat.Presheaf.germ_res_apply' (C := Ab) M.presheaf
            ((OpenNhds.inclusion x).op.map f) x V.unop.2 m)
          (TopCat.Presheaf.germ_res_apply' (C := Ab) N.presheaf
            ((OpenNhds.inclusion x).op.map f) x V.unop.2 n)
    | add a b ha hb => simpa only [map_add] using congrArg₂ (· + ·) ha hb

private def tensorPresheafStalkToTensorAdd :
    ↑(TopCat.Presheaf.stalk (C := Ab)
      (PresheafOfModules.Monoidal.tensorObj (R := X.presheaf) M N).presheaf x) →+
        (↑(TopCat.Presheaf.stalk (C := Ab) M.presheaf x) ⊗[X.presheaf.stalk x]
          ↑(TopCat.Presheaf.stalk (C := Ab) N.presheaf x)) :=
  (colimit.desc _ (tensorGermTensorCocone X M N x)).hom

private theorem tensorPresheafStalkToTensorAdd_germ (U : X.Opens) (hx : x ∈ U)
    (t : M.obj (op U) ⊗[X.presheaf.obj (op U)] N.obj (op U)) :
    tensorPresheafStalkToTensorAdd X M N x
      (TopCat.Presheaf.germ
        (PresheafOfModules.Monoidal.tensorObj (R := X.presheaf) M N).presheaf U x hx t) =
      tensorPresheafGermTensor X M N x U hx t :=
  ConcreteCategory.congr_hom (colimit.ι_desc (tensorGermTensorCocone X M N x) (op ⟨U, hx⟩)) t

/-- Taking the tensor of germs descends to a local-ring linear map on the tensor stalk. -/
def tensorPresheafStalkToTensor :
    ↑(TopCat.Presheaf.stalk (C := Ab)
      (PresheafOfModules.Monoidal.tensorObj (R := X.presheaf) M N).presheaf x)
      →ₗ[X.presheaf.stalk x]
        (↑(TopCat.Presheaf.stalk (C := Ab) M.presheaf x) ⊗[X.presheaf.stalk x]
          ↑(TopCat.Presheaf.stalk (C := Ab) N.presheaf x)) where
  toFun := tensorPresheafStalkToTensorAdd X M N x
  map_add' := map_add _
  map_smul' r t := by
    let P := PresheafOfModules.Monoidal.tensorObj (R := X.presheaf) M N
    obtain ⟨U, hxU, a, rfl⟩ := X.presheaf.exists_germ_eq r
    obtain ⟨V, hVU, hxV, s, rfl⟩ := TopCat.Presheaf.exists_le_germ_eq P.presheaf t hxU
    dsimp only [P] at s ⊢
    rw [← X.presheaf.germ_res_apply (homOfLE hVU) x hxV a]
    erw [← PresheafOfModules.germ_smul (R := X.presheaf)
      (PresheafOfModules.Monoidal.tensorObj (R := X.presheaf) M N),
      tensorPresheafStalkToTensorAdd_germ X M N x V hxV,
      tensorPresheafStalkToTensorAdd_germ X M N x V hxV,
      (tensorPresheafGermTensor X M N x V hxV).map_smulₛₗ]
    rfl

/-- Taking the stalk map on a tensor of local sections gives the tensor of their germs. -/
@[simp]
theorem tensorPresheafStalkToTensor_germ_tmul (U : X.Opens) (hx : x ∈ U)
    (m : M.obj (op U)) (n : N.obj (op U)) :
    tensorPresheafStalkToTensor X M N x
      (TopCat.Presheaf.germ
        (PresheafOfModules.Monoidal.tensorObj (R := X.presheaf) M N).presheaf
          U x hx (m ⊗ₜ[X.presheaf.obj (op U)] n)) =
      TopCat.Presheaf.germ M.presheaf U x hx m ⊗ₜ[X.presheaf.stalk x]
        TopCat.Presheaf.germ N.presheaf U x hx n :=
  tensorPresheafStalkToTensorAdd_germ X M N x U hx _

/-- The tensor-presheaf stalk is canonically the tensor product over the actual local ring. -/
def tensorPresheafStalkEquiv :
    ↑(TopCat.Presheaf.stalk (C := Ab)
      (PresheafOfModules.Monoidal.tensorObj (R := X.presheaf) M N).presheaf x)
      ≃ₗ[X.presheaf.stalk x]
        (↑(TopCat.Presheaf.stalk (C := Ab) M.presheaf x) ⊗[X.presheaf.stalk x]
          ↑(TopCat.Presheaf.stalk (C := Ab) N.presheaf x)) :=
  LinearEquiv.ofLinearMap (tensorPresheafStalkToTensor X M N x)
    (tensorPresheafStalkFromTensor X M N x)
    (by
      apply TensorProduct.ext'
      intro m n
      obtain ⟨U, hx, a, b, rfl, rfl⟩ := modulePresheafStalk_exists_pair X M N x m n
      simp only [LinearMap.comp_apply, LinearMap.id_apply]
      erw [tensorPresheafStalkFromTensor_germ, tensorPresheafStalkToTensor_germ_tmul])
    (by
      ext t
      obtain ⟨U, hx, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq
        (PresheafOfModules.Monoidal.tensorObj (R := X.presheaf) M N).presheaf t
      induction s using TensorProduct.induction_on with
      | zero => simp
      | tmul m n =>
          simp only [LinearMap.comp_apply, LinearMap.id_apply]
          erw [tensorPresheafStalkToTensor_germ_tmul, tensorPresheafStalkFromTensor_germ]
          rfl
      | add a b ha hb => simpa only [map_add] using congrArg₂ (· + ·) ha hb)

/-- The canonical equivalence preserves the represented pure tensor. -/
@[simp]
theorem tensorPresheafStalkEquiv_germ_tmul (U : X.Opens) (hx : x ∈ U)
    (m : M.obj (op U)) (n : N.obj (op U)) :
    tensorPresheafStalkEquiv X M N x
      (TopCat.Presheaf.germ
        (PresheafOfModules.Monoidal.tensorObj (R := X.presheaf) M N).presheaf
          U x hx (m ⊗ₜ[X.presheaf.obj (op U)] n)) =
      TopCat.Presheaf.germ M.presheaf U x hx m ⊗ₜ[X.presheaf.stalk x]
        TopCat.Presheaf.germ N.presheaf U x hx n :=
  tensorPresheafStalkToTensor_germ_tmul X M N x U hx m n

end AlgebraicGeometry.Scheme.Modules
