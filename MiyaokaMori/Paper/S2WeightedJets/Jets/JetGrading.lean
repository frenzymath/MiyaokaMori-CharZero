import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedQcAlgebraSectionsToQcAlgebra
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.QcAlgebraSectionsRing
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.PushforwardQcAlgebra
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.PushforwardQcAlgebraMap
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedQcAlgebraSectionsRing
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.GradedQuasicoherentAlgebra
import MiyaokaMori.AlgebraicGeometry.Morphisms.GroupSchemeAction
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetCoordinateAlgebra
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetRescalingAction
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetSchemeAffineOverBase
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetWeightDefect
import MiyaokaMori.Paper.S2WeightedJets.Jets.WeightDefectSections
import MiyaokaMori.AlgebraicGeometry.Morphisms.WeightDecomposition
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.KernelSections

/-! # The grading of the jet coordinate algebra

Replacing `t` by `λt` gives the coordinate algebra of `J_k^s` a nonnegative grading `S = ⊕_{m≥0} S_m`, the index
being the weighted degree (§2 of the paper: parameter rescaling `t ↦ λt` gives weight `q` to `a_q`).

Contents (the weight defect `φ_m`, `weightPart` and `weightPart_isQuasicoherent` live in the upstream module
`JetWeightDefect`):
* the multiplication and unit of `GroupSchemeAction.weightPart α m := ker φ_m` (the `λ^m`-eigensections) are
  restricted from `π_*O_T` via `kernel.lift`; the graded algebra axioms `weightMul_one_mul` / `weightMul_assoc` /
  `weightMul_comm` reduce, after `cancel_mono (kernel.ι _)`, to those of `π_*O_T` (the last two through the
  general lemmas `kernel.lift_mul_assoc` / `kernel.lift_mul_comm`); the two conditions for `kernel.lift` are
  `weightPart_one_condition` and `weightPart_mul_condition` (from `mul_comp_unitMap` and
  `unitMul_tensor_comp_mul`);
* `GroupSchemeAction.gradedAlgebra α : S.GradedQCAlgebra`;
* `jetGradedAlgebra Z s hs r`: the case `α = jetRescalingAction`, whose sections ring on each affine piece is
  isomorphic to the jet coordinate algebra (`jetGradedAlgebra_sectionsRing_equiv`, the relative nonnegative version
  of Stacks 0EKK), obtained from the injectivity and surjectivity of `ψ_U = gradedAlgebra_sectionsToRingHom`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open scoped CategoryTheory.MonoidalCategory

/-- The product of eigensections is a `λ^{m+n}`-eigensection: `act^♯` and `pr₂^♯` are multiplicative, so
`act^♯(ab) = act^♯(a)act^♯(b) = (λ^m pr₂^♯(a))(λ^n pr₂^♯(b)) = λ^{m+n} pr₂^♯(ab)`.
At the level of sheaves: `mul_comp_actMap`, `kernelι_comp_actMap`, `lamPow_tensor_comp_mul`, `mul_comp_prMap`,
moving `⊗` past `≫` with `tensor_comp`; uses `pushforwardStructureSheaf.mul_comp_unitMap` (`g^♯` is
multiplicative) and `unitMul_tensor_comp_mul` (the multiplication is bilinear with respect to `unitMul`). -/
theorem GroupSchemeAction.weightPart_mul_condition {k : Type u} [Field k] {S : AlgebraicGeometry.Scheme.{u}}
    [S.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {T : CategoryTheory.Over S}
    [AlgebraicGeometry.IsAffineHom T.hom] (α : GmActionOver k T) (m n : ℕ) :
    ((CategoryTheory.Limits.kernel.ι (GroupSchemeAction.weightDefect α m) ⊗ₘ
          CategoryTheory.Limits.kernel.ι (GroupSchemeAction.weightDefect α n)) ≫
        (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf T.hom).mul) ≫
      GroupSchemeAction.weightDefect α (m + n) = 0 := by
  dsimp only [AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf]
  rw [GroupSchemeAction.weightDefect_eq α (m + n), CategoryTheory.Preadditive.comp_sub, sub_eq_zero]
  simp only [CategoryTheory.Category.assoc]
  rw [GroupSchemeAction.mul_comp_actMap,
    CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom_assoc,
    GroupSchemeAction.kernelι_comp_actMap α m, GroupSchemeAction.kernelι_comp_actMap α n,
    ← CategoryTheory.Category.assoc (CategoryTheory.Limits.kernel.ι (GroupSchemeAction.weightDefect α m))
      (GroupSchemeAction.prMap T) (GroupSchemeAction.lamPow T m),
    ← CategoryTheory.Category.assoc (CategoryTheory.Limits.kernel.ι (GroupSchemeAction.weightDefect α n))
      (GroupSchemeAction.prMap T) (GroupSchemeAction.lamPow T n),
    ← CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom_assoc,
    GroupSchemeAction.lamPow_tensor_comp_mul,
    ← CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom_assoc,
    ← reassoc_of% (GroupSchemeAction.mul_comp_prMap T)]

set_option backward.isDefEq.respectTransparency.types false in
/-- `1` is a `λ^0`-eigensection: `act^♯(1) = 1 = λ^0 · pr₂^♯(1)`.
Proof: `weightDefect α 0 = A − B`; `one ≫ A = unit_{act ≫ π} ≫ pushforwardCongr = unit_q`
(`unitToPushforwardObjUnit_comp_pushforward_map`, `_comp_pushforwardCongr`) and
`one ≫ B = unit_{pr₂ ≫ π} ≫ q_*(unitMul (λ^0)) = unit_q` (`pow_zero`, `unitMul_one`); the difference is `0`. -/
theorem GroupSchemeAction.weightPart_one_condition {k : Type u} [Field k] {S : AlgebraicGeometry.Scheme.{u}}
    [S.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {T : CategoryTheory.Over S}
    [AlgebraicGeometry.IsAffineHom T.hom] (α : GmActionOver k T) :
    (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf T.hom).one ≫ GroupSchemeAction.weightDefect α 0 = 0 := by
  dsimp only [AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf,
    GroupSchemeAction.weightDefect]
  rw [CategoryTheory.Preadditive.comp_sub]
  erw [reassoc_of% (SheafOfModules.unitToPushforwardObjUnit_comp_pushforward_map α.act T.hom),
    SheafOfModules.unitToPushforwardObjUnit_comp_pushforwardCongr α.act_over,
    reassoc_of% (SheafOfModules.unitToPushforwardObjUnit_comp_pushforward_map _ T.hom)]
  rw [pow_zero, AlgebraicGeometry.Scheme.Modules.unitMul_one]
  erw [CategoryTheory.Functor.map_id, CategoryTheory.Category.comp_id]
  exact sub_self _

noncomputable def GroupSchemeAction.weightMul {k : Type u} [Field k] {S : AlgebraicGeometry.Scheme.{u}}
    [S.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {T : CategoryTheory.Over S}
    [AlgebraicGeometry.IsAffineHom T.hom] (α : GmActionOver k T) (m n : ℕ) :
    GroupSchemeAction.weightPart α m ⊗ GroupSchemeAction.weightPart α n ⟶ GroupSchemeAction.weightPart α (m + n) :=
  CategoryTheory.Limits.kernel.lift (GroupSchemeAction.weightDefect α (m + n))
    ((CategoryTheory.Limits.kernel.ι (GroupSchemeAction.weightDefect α m) ⊗ₘ
        CategoryTheory.Limits.kernel.ι (GroupSchemeAction.weightDefect α n)) ≫
      (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf T.hom).mul)
    (GroupSchemeAction.weightPart_mul_condition α m n)

noncomputable def GroupSchemeAction.weightOne {k : Type u} [Field k] {S : AlgebraicGeometry.Scheme.{u}}
    [S.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {T : CategoryTheory.Over S}
    [AlgebraicGeometry.IsAffineHom T.hom] (α : GmActionOver k T) : 𝟙_ S.Modules ⟶ GroupSchemeAction.weightPart α 0 :=
  CategoryTheory.Limits.kernel.lift (GroupSchemeAction.weightDefect α 0)
    (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf T.hom).one
    (GroupSchemeAction.weightPart_one_condition α)

/-- Left unit law: `kernel.ι` is a monomorphism, so after composing both sides with `kernel.ι (φ_m)` and using
`kernel.lift_ι` this reduces to `one_mul` in `π_*O_T`. -/
theorem GroupSchemeAction.weightMul_one_mul {k : Type u} [Field k] {S : AlgebraicGeometry.Scheme.{u}}
    [S.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {T : CategoryTheory.Over S}
    [AlgebraicGeometry.IsAffineHom T.hom] (α : GmActionOver k T) (m : ℕ) :
    (GroupSchemeAction.weightOne α ▷ GroupSchemeAction.weightPart α m) ≫ GroupSchemeAction.weightMul α 0 m =
      (λ_ (GroupSchemeAction.weightPart α m)).hom ≫ eqToHom (congrArg (GroupSchemeAction.weightPart α) (Nat.zero_add m).symm) := by
  apply (cancel_mono (CategoryTheory.Limits.kernel.ι (GroupSchemeAction.weightDefect α (0 + m)))).1
  have hmul : GroupSchemeAction.weightMul α 0 m ≫
      CategoryTheory.Limits.kernel.ι (GroupSchemeAction.weightDefect α (0 + m)) =
      (CategoryTheory.Limits.kernel.ι (GroupSchemeAction.weightDefect α 0) ⊗ₘ
        CategoryTheory.Limits.kernel.ι (GroupSchemeAction.weightDefect α m)) ≫
        (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf T.hom).mul := by
    unfold GroupSchemeAction.weightMul
    apply CategoryTheory.Limits.kernel.lift_ι
  change ((MonoidalCategoryStruct.whiskerRight (GroupSchemeAction.weightOne α)
      (GroupSchemeAction.weightPart α m)) ≫ GroupSchemeAction.weightMul α 0 m) ≫
      CategoryTheory.Limits.kernel.ι (GroupSchemeAction.weightDefect α (0 + m)) = _
  rw [Category.assoc (MonoidalCategoryStruct.whiskerRight (GroupSchemeAction.weightOne α)
      (GroupSchemeAction.weightPart α m)) (GroupSchemeAction.weightMul α 0 m)
      (CategoryTheory.Limits.kernel.ι (GroupSchemeAction.weightDefect α (0 + m))), hmul]
  change (GroupSchemeAction.weightOne α ▷
      CategoryTheory.Limits.kernel (GroupSchemeAction.weightDefect α m)) ≫
      (CategoryTheory.Limits.kernel.ι (GroupSchemeAction.weightDefect α 0) ⊗ₘ
        CategoryTheory.Limits.kernel.ι (GroupSchemeAction.weightDefect α m)) ≫
      AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.mul T.hom = _
  rw [CategoryTheory.MonoidalCategory.whiskerRight_comp_tensorHom_assoc
    (GroupSchemeAction.weightOne α)
    (CategoryTheory.Limits.kernel.ι (GroupSchemeAction.weightDefect α 0))
    (CategoryTheory.Limits.kernel.ι (GroupSchemeAction.weightDefect α m))
    (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.mul T.hom)]
  have hone : GroupSchemeAction.weightOne α ≫
      CategoryTheory.Limits.kernel.ι (GroupSchemeAction.weightDefect α 0) =
      (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf T.hom).one := by
    unfold GroupSchemeAction.weightOne
    apply CategoryTheory.Limits.kernel.lift_ι
  rw [hone]
  let one : 𝟙_ S.Modules ⟶ AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.obj T.hom :=
    SheafOfModules.unitToPushforwardObjUnit T.hom.toRingCatSheafHom
  change (one ⊗ₘ
      CategoryTheory.Limits.kernel.ι (GroupSchemeAction.weightDefect α m)) ≫
      AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.mul T.hom = _
  have hunit :
      (one ⊗ₘ
          CategoryTheory.Limits.kernel.ι (GroupSchemeAction.weightDefect α m)) ≫
        AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.mul T.hom =
      (λ_ (CategoryTheory.Limits.kernel (GroupSchemeAction.weightDefect α m))).hom ≫
        CategoryTheory.Limits.kernel.ι (GroupSchemeAction.weightDefect α m) := by
    calc
      (one ⊗ₘ
          CategoryTheory.Limits.kernel.ι (GroupSchemeAction.weightDefect α m)) ≫
          AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.mul T.hom =
        (one ▷
            CategoryTheory.Limits.kernel (GroupSchemeAction.weightDefect α m)) ≫
          (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.obj T.hom ◁
            CategoryTheory.Limits.kernel.ι (GroupSchemeAction.weightDefect α m)) ≫
          AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.mul T.hom := by
            exact CategoryTheory.MonoidalCategory.tensorHom_def_assoc
              (C := S.Modules)
              one
              (CategoryTheory.Limits.kernel.ι (GroupSchemeAction.weightDefect α m))
              (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.mul T.hom)
      _ = (CategoryTheory.MonoidalCategoryStruct.whiskerLeft
          (𝟙_ S.Modules) (CategoryTheory.Limits.kernel.ι (GroupSchemeAction.weightDefect α m))) ≫
          (one ▷
            (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.obj T.hom)) ≫
          AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.mul T.hom := by
            exact (CategoryTheory.MonoidalCategory.whisker_exchange_assoc
              (C := S.Modules)
              one
              (CategoryTheory.Limits.kernel.ι (GroupSchemeAction.weightDefect α m))
              (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.mul T.hom)).symm
      _ = (CategoryTheory.MonoidalCategoryStruct.whiskerLeft
          (𝟙_ S.Modules) (CategoryTheory.Limits.kernel.ι (GroupSchemeAction.weightDefect α m))) ≫
          (λ_ (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.obj T.hom)).hom := by
            dsimp [one]
            exact congrArg
              (fun q =>
                (CategoryTheory.MonoidalCategoryStruct.whiskerLeft
                  (𝟙_ S.Modules)
                  (CategoryTheory.Limits.kernel.ι (GroupSchemeAction.weightDefect α m))) ≫ q)
              (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.one_mul T.hom).symm
      _ = (λ_ (CategoryTheory.Limits.kernel (GroupSchemeAction.weightDefect α m))).hom ≫
          CategoryTheory.Limits.kernel.ι (GroupSchemeAction.weightDefect α m) := by
            exact CategoryTheory.MonoidalCategory.leftUnitor_naturality
              (C := S.Modules)
              (CategoryTheory.Limits.kernel.ι (GroupSchemeAction.weightDefect α m))
  have hcast :
      eqToHom (congrArg (GroupSchemeAction.weightPart α) (Nat.zero_add m).symm) ≫
          CategoryTheory.Limits.kernel.ι (GroupSchemeAction.weightDefect α (0 + m)) =
        CategoryTheory.Limits.kernel.ι (GroupSchemeAction.weightDefect α m) := by
    simpa [GroupSchemeAction.weightPart] using
      (CategoryTheory.eqToHom_naturality
        (fun n => CategoryTheory.Limits.kernel.ι (GroupSchemeAction.weightDefect α n))
        (Nat.zero_add m).symm).symm
  have htransport :
      (λ_ (GroupSchemeAction.weightPart α m)).hom ≫
          eqToHom (congrArg (GroupSchemeAction.weightPart α) (Nat.zero_add m).symm) ≫
          CategoryTheory.Limits.kernel.ι (GroupSchemeAction.weightDefect α (0 + m)) =
        (λ_ (CategoryTheory.Limits.kernel (GroupSchemeAction.weightDefect α m))).hom ≫
          CategoryTheory.Limits.kernel.ι (GroupSchemeAction.weightDefect α m) := by
    simpa only [Category.assoc, GroupSchemeAction.weightPart] using
      congrArg
        (fun q => (λ_ (CategoryTheory.Limits.kernel (GroupSchemeAction.weightDefect α m))).hom ≫ q)
        hcast
  exact hunit.trans htransport.symm


/-! ## Graded multiplication on kernels: general lemmas

The next two lemmas are pure category theory: in a monoidal (braided) category with kernels, let `A` carry a
multiplication `mul` and let `φ_m : A ⟶ B_m` be a family of morphisms; if `(ι_m ⊗ ι_n) ≫ mul` lands in
`ker φ_{m+n}`, then the multiplication restricted to the kernels via `kernel.lift` inherits associativity and
commutativity from `A`. Everything is phrased with `kernel` (not `weightPart`) so that `rw` need not unfold a
`def`; `weightMul_assoc` / `weightMul_comm` are instances via `exact` (`weightPart α m` and
`kernel (weightDefect α m)` are definitionally equal at default transparency). -/

section KernelGradedLift

variable {C : Type u'} [CategoryTheory.Category.{v'} C] [CategoryTheory.MonoidalCategory C]
  [CategoryTheory.Limits.HasZeroMorphisms C] [CategoryTheory.Limits.HasKernels C]

omit [CategoryTheory.MonoidalCategory C] in
/-- Reindexing by `eqToHom` followed by `kernel.ι` is again `kernel.ι`. -/
theorem CategoryTheory.Limits.kernel.eqToHom_comp_ι {A : C} {B : ℕ → C} (φ : ∀ m, A ⟶ B m)
    {m n : ℕ} (h : m = n) :
    CategoryTheory.eqToHom (congrArg (fun i => CategoryTheory.Limits.kernel (φ i)) h) ≫
        CategoryTheory.Limits.kernel.ι (φ n) =
      CategoryTheory.Limits.kernel.ι (φ m) := by
  subst h
  rw [CategoryTheory.eqToHom_refl, CategoryTheory.Category.id_comp]

/-- The multiplication restricted to kernels inherits associativity (after `cancel_mono (kernel.ι _)` this is the
associativity `hmul` of `A`). -/
theorem CategoryTheory.Limits.kernel.lift_mul_assoc {A : C} {B : ℕ → C} (φ : ∀ m, A ⟶ B m)
    (mul : A ⊗ A ⟶ A)
    (hmul : (α_ A A A).hom ≫ (A ◁ mul) ≫ mul = (mul ▷ A) ≫ mul)
    (h : ∀ m n, ((CategoryTheory.Limits.kernel.ι (φ m) ⊗ₘ CategoryTheory.Limits.kernel.ι (φ n)) ≫ mul) ≫
      φ (m + n) = 0) (m n p : ℕ) :
    (α_ (CategoryTheory.Limits.kernel (φ m)) (CategoryTheory.Limits.kernel (φ n))
          (CategoryTheory.Limits.kernel (φ p))).hom ≫
        (CategoryTheory.Limits.kernel (φ m) ◁ CategoryTheory.Limits.kernel.lift (φ (n + p)) _ (h n p)) ≫
        CategoryTheory.Limits.kernel.lift (φ (m + (n + p))) _ (h m (n + p)) =
      (CategoryTheory.Limits.kernel.lift (φ (m + n)) _ (h m n) ▷ CategoryTheory.Limits.kernel (φ p)) ≫
        CategoryTheory.Limits.kernel.lift (φ (m + n + p)) _ (h (m + n) p) ≫
        CategoryTheory.eqToHom (congrArg (fun i => CategoryTheory.Limits.kernel (φ i)) (Nat.add_assoc m n p)) := by
  apply (CategoryTheory.cancel_mono (CategoryTheory.Limits.kernel.ι (φ (m + (n + p))))).1
  have hL : ((α_ (CategoryTheory.Limits.kernel (φ m)) (CategoryTheory.Limits.kernel (φ n))
          (CategoryTheory.Limits.kernel (φ p))).hom ≫
        (CategoryTheory.Limits.kernel (φ m) ◁ CategoryTheory.Limits.kernel.lift (φ (n + p)) _ (h n p)) ≫
        CategoryTheory.Limits.kernel.lift (φ (m + (n + p))) _ (h m (n + p))) ≫
        CategoryTheory.Limits.kernel.ι (φ (m + (n + p))) =
      ((CategoryTheory.Limits.kernel.ι (φ m) ⊗ₘ CategoryTheory.Limits.kernel.ι (φ n)) ⊗ₘ
          CategoryTheory.Limits.kernel.ι (φ p)) ≫ (mul ▷ A) ≫ mul := by
    simp only [CategoryTheory.Category.assoc]
    rw [CategoryTheory.Limits.kernel.lift_ι,
      CategoryTheory.MonoidalCategory.whiskerLeft_comp_tensorHom_assoc,
      CategoryTheory.Limits.kernel.lift_ι,
      ← CategoryTheory.MonoidalCategory.tensorHom_comp_whiskerLeft_assoc,
      ← CategoryTheory.MonoidalCategory.associator_naturality_assoc, hmul]
  have hR : ((CategoryTheory.Limits.kernel.lift (φ (m + n)) _ (h m n) ▷ CategoryTheory.Limits.kernel (φ p)) ≫
        CategoryTheory.Limits.kernel.lift (φ (m + n + p)) _ (h (m + n) p) ≫
        CategoryTheory.eqToHom (congrArg (fun i => CategoryTheory.Limits.kernel (φ i)) (Nat.add_assoc m n p))) ≫
        CategoryTheory.Limits.kernel.ι (φ (m + (n + p))) =
      ((CategoryTheory.Limits.kernel.ι (φ m) ⊗ₘ CategoryTheory.Limits.kernel.ι (φ n)) ⊗ₘ
          CategoryTheory.Limits.kernel.ι (φ p)) ≫ (mul ▷ A) ≫ mul := by
    simp only [CategoryTheory.Category.assoc]
    rw [CategoryTheory.Limits.kernel.eqToHom_comp_ι φ (Nat.add_assoc m n p),
      CategoryTheory.Limits.kernel.lift_ι,
      CategoryTheory.MonoidalCategory.whiskerRight_comp_tensorHom_assoc,
      CategoryTheory.Limits.kernel.lift_ι,
      ← CategoryTheory.MonoidalCategory.tensorHom_comp_whiskerRight_assoc]
  exact hL.trans hR.symm

/-- The multiplication restricted to kernels inherits commutativity (braided category; reduces to the
commutativity `hcomm` of `A`). -/
theorem CategoryTheory.Limits.kernel.lift_mul_comm [CategoryTheory.BraidedCategory C]
    {A : C} {B : ℕ → C} (φ : ∀ m, A ⟶ B m) (mul : A ⊗ A ⟶ A)
    (hcomm : (β_ A A).hom ≫ mul = mul)
    (h : ∀ m n, ((CategoryTheory.Limits.kernel.ι (φ m) ⊗ₘ CategoryTheory.Limits.kernel.ι (φ n)) ≫ mul) ≫
      φ (m + n) = 0) (m n : ℕ) :
    (β_ (CategoryTheory.Limits.kernel (φ m)) (CategoryTheory.Limits.kernel (φ n))).hom ≫
        CategoryTheory.Limits.kernel.lift (φ (n + m)) _ (h n m) =
      CategoryTheory.Limits.kernel.lift (φ (m + n)) _ (h m n) ≫
        CategoryTheory.eqToHom (congrArg (fun i => CategoryTheory.Limits.kernel (φ i)) (Nat.add_comm m n)) := by
  apply (CategoryTheory.cancel_mono (CategoryTheory.Limits.kernel.ι (φ (n + m)))).1
  have hL : ((β_ (CategoryTheory.Limits.kernel (φ m)) (CategoryTheory.Limits.kernel (φ n))).hom ≫
        CategoryTheory.Limits.kernel.lift (φ (n + m)) _ (h n m)) ≫
        CategoryTheory.Limits.kernel.ι (φ (n + m)) =
      (CategoryTheory.Limits.kernel.ι (φ m) ⊗ₘ CategoryTheory.Limits.kernel.ι (φ n)) ≫ mul := by
    rw [CategoryTheory.Category.assoc, CategoryTheory.Limits.kernel.lift_ι,
      ← CategoryTheory.BraidedCategory.braiding_naturality_assoc, hcomm]
  have hR : (CategoryTheory.Limits.kernel.lift (φ (m + n)) _ (h m n) ≫
        CategoryTheory.eqToHom (congrArg (fun i => CategoryTheory.Limits.kernel (φ i)) (Nat.add_comm m n))) ≫
        CategoryTheory.Limits.kernel.ι (φ (n + m)) =
      (CategoryTheory.Limits.kernel.ι (φ m) ⊗ₘ CategoryTheory.Limits.kernel.ι (φ n)) ≫ mul := by
    rw [CategoryTheory.Category.assoc, CategoryTheory.Limits.kernel.eqToHom_comp_ι φ (Nat.add_comm m n),
      CategoryTheory.Limits.kernel.lift_ι]
  exact hL.trans hR.symm

end KernelGradedLift

/-- Associativity: `kernel.lift_mul_assoc` instantiated at `φ_m = weightDefect α m` and the multiplication of
`π_*O_T`; reduces to `mul_assoc` in `π_*O_T`. -/
theorem GroupSchemeAction.weightMul_assoc {k : Type u} [Field k] {S : AlgebraicGeometry.Scheme.{u}}
    [S.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {T : CategoryTheory.Over S}
    [AlgebraicGeometry.IsAffineHom T.hom] (α : GmActionOver k T) (m n p : ℕ) :
    (α_ (GroupSchemeAction.weightPart α m) (GroupSchemeAction.weightPart α n) (GroupSchemeAction.weightPart α p)).hom ≫ (GroupSchemeAction.weightPart α m ◁ GroupSchemeAction.weightMul α n p) ≫
        GroupSchemeAction.weightMul α m (n + p) =
      (GroupSchemeAction.weightMul α m n ▷ GroupSchemeAction.weightPart α p) ≫ GroupSchemeAction.weightMul α (m + n) p ≫
        eqToHom (congrArg (GroupSchemeAction.weightPart α) (Nat.add_assoc m n p)) :=
  CategoryTheory.Limits.kernel.lift_mul_assoc (GroupSchemeAction.weightDefect α)
    (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.mul T.hom)
    (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.mul_assoc T.hom)
    (GroupSchemeAction.weightPart_mul_condition α) m n p

/-- Commutativity: `kernel.lift_mul_comm` instantiated; reduces to `mul_comm` in `π_*O_T`. -/
theorem GroupSchemeAction.weightMul_comm {k : Type u} [Field k] {S : AlgebraicGeometry.Scheme.{u}}
    [S.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {T : CategoryTheory.Over S}
    [AlgebraicGeometry.IsAffineHom T.hom] (α : GmActionOver k T) (m n : ℕ) :
    (β_ (GroupSchemeAction.weightPart α m) (GroupSchemeAction.weightPart α n)).hom ≫ GroupSchemeAction.weightMul α n m =
      GroupSchemeAction.weightMul α m n ≫ eqToHom (congrArg (GroupSchemeAction.weightPart α) (Nat.add_comm m n)) :=
  CategoryTheory.Limits.kernel.lift_mul_comm (GroupSchemeAction.weightDefect α)
    (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.mul T.hom)
    (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.mul_comm T.hom)
    (GroupSchemeAction.weightPart_mul_condition α) m n

noncomputable def GroupSchemeAction.gradedAlgebra {k : Type u} [Field k] {S : AlgebraicGeometry.Scheme.{u}}
    [S.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {T : CategoryTheory.Over S}
    [AlgebraicGeometry.IsAffineHom T.hom] (α : GmActionOver k T) : S.GradedQCAlgebra where
  part := GroupSchemeAction.weightPart α
  quasicoherent := GroupSchemeAction.weightPart_isQuasicoherent α
  mul := GroupSchemeAction.weightMul α
  one := GroupSchemeAction.weightOne α
  one_mul := GroupSchemeAction.weightMul_one_mul α
  mul_assoc := GroupSchemeAction.weightMul_assoc α
  mul_comm := GroupSchemeAction.weightMul_comm α

/-! ## The sections ring homomorphism `ψ_U : ⨁_m Γ(U, ker φ_m) ⟶ Γ(π⁻¹U, O_T)` and the relative Stacks 0EKK

Each piece of `GroupSchemeAction.gradedAlgebra α` embeds into `π_*O_T` via `kernel.ι`, compatibly with unit and
multiplication (`kernel.lift_ι`), so the general lemma `GradedQCAlgebra.sectionsToRingHom` gives a ring
homomorphism `ψ_U` on sections, compatible with restriction. On an affine open `U`, `ψ_U` is bijective; this is
the relative version of Stacks 0EKK: injectivity holds for every `𝔾_m`-action (the powers of `λ` are linearly
independent), surjectivity needs the action to be nonnegative (`IsNonnegative`: the coaction lands in `R[λ]`, so
`R = ⊕_{n≥0} R_n`). See `gradedAlgebra_sectionsToRingHom_injective` / `_surjective`. -/

section SectionsToRingHom

variable {k : Type u} [Field k] {S : AlgebraicGeometry.Scheme.{u}}
    [S.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {T : CategoryTheory.Over S}
    [AlgebraicGeometry.IsAffineHom T.hom] (α : GmActionOver k T)

/-- `S.one ≫ ι_0 = π^♯` (`weightOne` is a `kernel.lift`, recovered by composing with `kernel.ι`). -/
theorem GroupSchemeAction.gradedAlgebra_one_comp_kernelι :
    (GroupSchemeAction.gradedAlgebra α).one ≫
        CategoryTheory.Limits.kernel.ι (GroupSchemeAction.weightDefect α 0) =
      (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf T.hom).one :=
  CategoryTheory.Limits.kernel.lift_ι _ _ _

/-- `S.mul m n ≫ ι_{m+n} = (ι_m ⊗ ι_n) ≫ mul` (`weightMul` is a `kernel.lift`, recovered by composing with
`kernel.ι`). -/
theorem GroupSchemeAction.gradedAlgebra_mul_comp_kernelι (m n : ℕ) :
    (GroupSchemeAction.gradedAlgebra α).mul m n ≫
        CategoryTheory.Limits.kernel.ι (GroupSchemeAction.weightDefect α (m + n)) =
      (CategoryTheory.Limits.kernel.ι (GroupSchemeAction.weightDefect α m) ⊗ₘ
          CategoryTheory.Limits.kernel.ι (GroupSchemeAction.weightDefect α n)) ≫
        (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf T.hom).mul :=
  CategoryTheory.Limits.kernel.lift_ι _ _ _

/-- `ψ_U : ⨁_m Γ(U, ker φ_m) →+* Γ(π⁻¹U, O_T)`, given on the `m`-th summand by `kernel.ι (φ_m)` on sections. -/
noncomputable def GroupSchemeAction.gradedAlgebra_sectionsToRingHom (U : S.Opens) :
    (GroupSchemeAction.gradedAlgebra α).sectionsRing U →+*
      (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf T.hom).sectionsRing U :=
  (GroupSchemeAction.gradedAlgebra α).sectionsToRingHom
    (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf T.hom)
    (fun m => CategoryTheory.Limits.kernel.ι (GroupSchemeAction.weightDefect α m))
    (GroupSchemeAction.gradedAlgebra_one_comp_kernelι α)
    (GroupSchemeAction.gradedAlgebra_mul_comp_kernelι α) U

/-- `ψ` is compatible with restriction (an instance of the general lemma `sectionsToRingHom_restrict`). -/
theorem GroupSchemeAction.gradedAlgebra_sectionsToRingHom_restrict {U U' : S.Opens} (h : U ≤ U')
    (x : (GroupSchemeAction.gradedAlgebra α).sectionsRing U') :
    GroupSchemeAction.gradedAlgebra_sectionsToRingHom α U
        ((GroupSchemeAction.gradedAlgebra α).sectionsRestrict h x) =
      (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf T.hom).sectionsRestrict h
        (GroupSchemeAction.gradedAlgebra_sectionsToRingHom α U' x) :=
  (GroupSchemeAction.gradedAlgebra α).sectionsToRingHom_restrict _ _ _ _ h x

/-- The "direct sum" half of the relative Stacks 0EKK: `ψ_U : ⨁_m Γ(U, ker φ_m) → R := Γ(π⁻¹U, O_T)` is
injective on an affine open `U`, i.e. eigensections of different weights are linearly independent.

Notation: `W := 𝔾_m ×_k T`, `pr₂ : W → T`, `V := π⁻¹U` (affine since `π` is affine, `IsAffineOpen.preimage`),
`R := Γ(V, O_T) = (π_*O_T)(U)`; `φ_m = weightDefect α m = act^♯ − λ^m · pr₂^♯`, `ι_m := kernel.ι (φ_m)`.

Proof:
1. `ψ_U` is a ring homomorphism (`gradedAlgebra_sectionsToRingHom`), so it suffices that its kernel is `0`
   (`injective_iff_map_eq_zero`). Write `x = Σ_{m ∈ supp x} of_m(x_m)` (`DirectSum.sum_support_of`),
   `a_m := ι_m(x_m) ∈ R`; then `Σ_m a_m = ψ_U(x) = 0` (`map_sum`, `sectionsToRingHom_of`).
2. Let `y := Finsupp.onFinset (supp x) a`; then `φ_m(a_m) = 0` (`Modules.kernel_ι_app_apply_eq_zero`).
3. `GroupSchemeAction.eq_zero_of_weightDefect_eq_zero_of_sum_eq_zero`: applying the ring homomorphism `act^♯` to
   `Σ a_m = 0`, the section formula `weightDefect_val_app_apply` gives `Σ λ^m · pr₂^♯(a_m) = 0`, and
   `Gm_pullback_lambda_pow_independent` gives `y = 0`.
4. `Modules.kernel_ι_app_injective` gives `x_m = 0` for all `m`, hence `x = 0` (`DirectSum.ext`).

Technical remark: `sectionsRing` is a `def` wrapping `⨁`; write `let x : DirectSum ℕ _ := x₀; show x = 0` before
using `x m` / `x.support` / `ext`. The `Finset.sum` instances on `sectionsRing`, `⨁` and `Γ` agree only at
default transparency, so `rw [map_sum]`, `rw [Finset.sum_congr …]`, `rw [map_zero]` fail; use `Eq.trans` in term
mode instead. -/
theorem GroupSchemeAction.gradedAlgebra_sectionsToRingHom_injective (U : S.affineOpens) :
    Function.Injective (GroupSchemeAction.gradedAlgebra_sectionsToRingHom α U.1) := by
  classical
  rw [injective_iff_map_eq_zero]
  intro x₀ hx
  let x : DirectSum ℕ (fun m => (GroupSchemeAction.gradedAlgebra α).sectionsPiece U.1 m) := x₀
  show x = 0
  -- a_m := ι_m (x_m) ∈ R = Γ(π⁻¹U)
  let a : ℕ → Γ(T.left, T.hom ⁻¹ᵁ U.1) := fun m =>
    show Γ(T.left, T.hom ⁻¹ᵁ U.1) from
      ((CategoryTheory.Limits.kernel.ι (GroupSchemeAction.weightDefect α m)).val.app
        (Opposite.op U.1)).hom (x m)
  have ha0 : ∀ m, a m ≠ 0 → m ∈ x.support := by
    intro m hm
    rw [DFinsupp.mem_support_iff]
    intro hxm
    apply hm
    show ((CategoryTheory.Limits.kernel.ι (GroupSchemeAction.weightDefect α m)).val.app
      (Opposite.op U.1)).hom (x m) = 0
    rw [hxm]
    exact map_zero _
  -- `y := (m ↦ a_m)`, of finite support
  let y : ℕ →₀ Γ(T.left, T.hom ⁻¹ᵁ U.1) := Finsupp.onFinset x.support a ha0
  -- `Σ_m a_m = ψ_U x = 0` (term-mode `Eq.trans` throughout: the instances on `sectionsRing` and on `⨁` / `Γ` agree
-- only at default transparency, so `rw` fails)
  have hsum : y.sum (fun _ b => b) = 0 := by
    have hx' : GroupSchemeAction.gradedAlgebra_sectionsToRingHom α U.1
        (∑ m ∈ x.support, DirectSum.of _ m (x m) :
          DirectSum ℕ (fun m => (GroupSchemeAction.gradedAlgebra α).sectionsPiece U.1 m)) = 0 :=
      (congrArg (GroupSchemeAction.gradedAlgebra_sectionsToRingHom α U.1)
        (DirectSum.sum_support_of x)).trans hx
    have hx'' : ∑ m ∈ x.support, GroupSchemeAction.gradedAlgebra_sectionsToRingHom α U.1
        (DirectSum.of _ m (x m)) = 0 :=
      (map_sum (GroupSchemeAction.gradedAlgebra_sectionsToRingHom α U.1)
        (fun m => DirectSum.of _ m (x m)) x.support).symm.trans hx'
    have hterm : ∀ m ∈ x.support, GroupSchemeAction.gradedAlgebra_sectionsToRingHom α U.1
        (DirectSum.of _ m (x m)) = a m := fun m _ =>
      (GroupSchemeAction.gradedAlgebra α).sectionsToRingHom_of _ _ _ _ U.1 m (x m)
    have hsum' : ∑ m ∈ x.support, a m = 0 :=
      (Finset.sum_congr rfl (fun m hm => (hterm m hm).symm)).trans hx''
    exact (Finsupp.onFinset_sum ha0 (fun _ => rfl)).trans hsum'
  -- eigensections of different weights are linearly independent, so `y = 0`
  have hy : y = 0 :=
    GroupSchemeAction.eq_zero_of_weightDefect_eq_zero_of_sum_eq_zero α U.1 U.2 y
      (fun n => AlgebraicGeometry.Scheme.Modules.kernel_ι_app_apply_eq_zero
        (GroupSchemeAction.weightDefect α n) U.1 (x n)) hsum
  -- `ι_m` is injective on sections, so `x_m = 0`
  ext m
  have hm : a m = 0 := by
    have := DFunLike.congr_fun hy m
    rwa [Finsupp.onFinset_apply, Finsupp.zero_apply] at this
  refine AlgebraicGeometry.Scheme.Modules.kernel_ι_app_injective (GroupSchemeAction.weightDefect α m) U.1 ?_
  exact hm.trans (map_zero ((CategoryTheory.Limits.kernel.ι (GroupSchemeAction.weightDefect α m)).val.app
    (Opposite.op U.1)).hom).symm

/-- The "generation" half of the relative nonnegative Stacks 0EKK: for a nonnegative `𝔾_m`-action
(`α.IsNonnegative`: `act` extends to an action of the monoid `𝔸¹ = Spec k[λ]`),
`ψ_U : ⨁_m Γ(U, ker φ_m) → R := Γ(π⁻¹U, O_T)` is surjective on an affine open `U`: every `a ∈ R` is a finite
sum of eigensections.

Proof:
1. `GroupSchemeAction.exists_weight_decomposition`: `a = Σ_n y_n` with `φ_n(y_n) = 0` for every `n`. This is the
   mathematical content of 0EKK (the coaction chart on an affine piece; nonnegativity gives only nonnegative
   powers; the counit gives `Σ a_n = a`; coassociativity makes `a_n` an eigensection of weight `n`).
2. `Modules.exists_kernel_ι_app_eq`: `φ_n(y_n) = 0` gives `y_n = ι_n(x_n)` with `x_n ∈ Γ(U, ker φ_n)`.
3. `ψ_U(Σ_n of_n(x_n)) = Σ_n ι_n(x_n) = Σ_n y_n = a` (`map_sum`, `sectionsToRingHom_of`).

In the jet case the required nonnegativity is `jetRescalingAction_isNonnegative`. -/
theorem GroupSchemeAction.gradedAlgebra_sectionsToRingHom_surjective (hα : α.IsNonnegative)
    (U : S.affineOpens) :
    Function.Surjective (GroupSchemeAction.gradedAlgebra_sectionsToRingHom α U.1) := by
  intro a
  obtain ⟨y, h0, hsum⟩ := GroupSchemeAction.exists_weight_decomposition α hα U.1 U.2 a
  choose x hx using fun n => AlgebraicGeometry.Scheme.Modules.exists_kernel_ι_app_eq
    (GroupSchemeAction.weightDefect α n) U.1 (y n) (h0 n)
  refine ⟨(∑ n ∈ y.support, DirectSum.of _ n (x n) :
    DirectSum ℕ (fun m => (GroupSchemeAction.gradedAlgebra α).sectionsPiece U.1 m)), ?_⟩
  refine (map_sum (GroupSchemeAction.gradedAlgebra_sectionsToRingHom α U.1)
    (fun n => DirectSum.of _ n (x n)) y.support).trans ?_
  have hterm : ∀ n ∈ y.support, GroupSchemeAction.gradedAlgebra_sectionsToRingHom α U.1
      (DirectSum.of _ n (x n)) = y n := fun n _ =>
    ((GroupSchemeAction.gradedAlgebra α).sectionsToRingHom_of _ _ _ _ U.1 n (x n)).trans (hx n)
  exact (Finset.sum_congr rfl hterm).trans hsum

end SectionsToRingHom

/-- The relative nonnegative version of Stacks 0EKK for the jet scheme: the graded algebra `S = ⊕_m ker φ_m`
given by the `𝔾_m`-rescaling action has, on every affine open, a sections ring canonically isomorphic to that of
the jet coordinate algebra `A = π_*O_J`, compatibly with restriction.

Notation: `J := relativeJetScheme Z s hs r`, `π := J.hom : J → C` (affine, `JetSchemeAffineOverBase`),
`A := jetCoordinateAlgebra = pushforwardStructureSheaf π = π_*O_J` (by definition), `α := jetRescalingAction`,
`S := GroupSchemeAction.gradedAlgebra α`, `U ⊆ C` an affine open.

Proof:
1. `e U := RingEquiv.ofBijective (ψ_U)` with `ψ_U := GroupSchemeAction.gradedAlgebra_sectionsToRingHom α U`
   (`⨁_m Γ(U, ker φ_m) →+* Γ(π⁻¹U, O_J)`, given by `kernel.ι (φ_m)` on sections; it is a ring homomorphism by
   `kernel.lift_ι` and the general `GradedQCAlgebra.sectionsToRingHom`);
2. injectivity: `gradedAlgebra_sectionsToRingHom_injective` (for every `𝔾_m`-action);
3. surjectivity: `gradedAlgebra_sectionsToRingHom_surjective` (needs the nonnegativity
   `jetRescalingAction_isNonnegative`);
4. compatibility with restriction: `gradedAlgebra_sectionsToRingHom_restrict` (`kernel.ι` is a morphism of
   sheaves, hence commutes with restriction). -/
theorem jetGradedAlgebra_sectionsRing_equiv {k : Type u} [Field k] {C : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (Z : CategoryTheory.Over C)
    [AlgebraicGeometry.IsAffineHom Z.hom]
    (s : C ⟶ Z.left) (hs : s ≫ Z.hom = CategoryTheory.CategoryStruct.id C) (r : ℕ) :
    let S := GroupSchemeAction.gradedAlgebra (jetRescalingAction (k := k) Z s hs r)
    ∃ e : ∀ U : C.affineOpens,
            S.sectionsRing U.1 ≃+* (jetCoordinateAlgebra (k := k) Z s hs r).sectionsRing U.1,
          ∀ (U U' : C.affineOpens) (h : U.1 ≤ U'.1) (x : S.sectionsRing U'.1),
            e U (S.sectionsRestrict h x) =
              (jetCoordinateAlgebra (k := k) Z s hs r).sectionsRestrict h (e U' x) := by
  intro S
  refine ⟨fun U => RingEquiv.ofBijective
    (GroupSchemeAction.gradedAlgebra_sectionsToRingHom (jetRescalingAction (k := k) Z s hs r) U.1)
    ⟨GroupSchemeAction.gradedAlgebra_sectionsToRingHom_injective _ U,
      GroupSchemeAction.gradedAlgebra_sectionsToRingHom_surjective _
        (jetRescalingAction_isNonnegative (k := k) Z s hs r) U⟩, ?_⟩
  intro U U' h x
  exact GroupSchemeAction.gradedAlgebra_sectionsToRingHom_restrict
    (jetRescalingAction (k := k) Z s hs r) h x

/-- The graded coordinate algebra `S = ⊕_{m≥0} S_m` of the based jet scheme (§2 of the paper): the graded
quasi-coherent algebra of the `𝔾_m`-rescaling action, together with the identification of its sections ring with
the jet coordinate algebra on every affine open. -/
noncomputable def jetGradedAlgebra {k : Type u} [Field k] {C : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (Z : CategoryTheory.Over C)
    [AlgebraicGeometry.IsAffineHom Z.hom]
    (s : C ⟶ Z.left) (hs : s ≫ Z.hom = CategoryTheory.CategoryStruct.id C) (r : ℕ) :
    { S : C.GradedQCAlgebra //
        ∃ e : ∀ U : C.affineOpens,
            S.sectionsRing U.1 ≃+* (jetCoordinateAlgebra (k := k) Z s hs r).sectionsRing U.1,
          ∀ (U U' : C.affineOpens) (h : U.1 ≤ U'.1) (x : S.sectionsRing U'.1),
            e U (S.sectionsRestrict h x) =
              (jetCoordinateAlgebra (k := k) Z s hs r).sectionsRestrict h (e U' x) } :=
  ⟨GroupSchemeAction.gradedAlgebra (jetRescalingAction (k := k) Z s hs r),
    jetGradedAlgebra_sectionsRing_equiv Z s hs r⟩

end
