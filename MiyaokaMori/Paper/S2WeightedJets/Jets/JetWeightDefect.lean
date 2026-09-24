import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.PushforwardQcAlgebra
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.PushforwardQcAlgebraMap
import MiyaokaMori.AlgebraicGeometry.Morphisms.GroupSchemeAction
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.Stacks01ic

/-! # The weight defect of a `𝔾_m`-action

For a `𝔾_m`-action `α : 𝔾_m ×_k T → T` (with `T` affine over `S`), the weight-`m` defect
`φ_m := act^♯ − λ^m · pr₂^♯ : π_*O_T → q_*O_W`, the `m`-th piece `S_m := ker φ_m` (the `λ^m`-eigensections), and
general lemmas about the three-part decomposition `φ_m = act^♯ − pr₂^♯ ≫ (λ^m ·)`.

References: §2 of the paper (parameter rescaling `t ↦ λt` gives weight `q` to `a_q`); Stacks 0EKK.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open scoped CategoryTheory.MonoidalCategory

/-- The weight-`m` defect `φ_m : π_*O_T → q_*O_W`, `a ↦ act^♯(a) − λ^m · pr₂^♯(a)`, of a `𝔾_m`-action
`α : 𝔾_m ×_k T → T` (with `T` over `S`); here `W := 𝔾_m ×_k T`, `pr₂` is the second projection, `q := pr₂ ≫ π`,
and `λ ∈ Γ(𝔾_m) = k[λ^{±1}]` is the coordinate (pulled back to `W` along the first projection). `act^♯` lands in
the same target via `π_*act_* ≅ (act ≫ π)_* = (pr₂ ≫ π)_*` (`α.act_over`). -/

noncomputable def GroupSchemeAction.weightDefect {k : Type u} [Field k] {S : AlgebraicGeometry.Scheme.{u}}
    [S.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {T : CategoryTheory.Over S}
    (α : GmActionOver k T) (m : ℕ) :
    (AlgebraicGeometry.Scheme.Modules.pushforward T.hom).obj (SheafOfModules.unit T.left.ringCatSheaf) ⟶
      (AlgebraicGeometry.Scheme.Modules.pushforward
          (CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom
            (T.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) ≫ T.hom)).obj
        (SheafOfModules.unit (CategoryTheory.Limits.pullback
          ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom
          (T.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).ringCatSheaf) :=
  let pr₁ := CategoryTheory.Limits.pullback.fst ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom
    (T.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))
  let pr₂ := CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom
    (T.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))
  let lam : Γ(Gm k, ⊤) :=
    (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial k))).inv.hom (LaurentPolynomial.T 1)
  (AlgebraicGeometry.Scheme.Modules.pushforward T.hom).map
      (SheafOfModules.unitToPushforwardObjUnit α.act.toRingCatSheafHom) ≫
    (AlgebraicGeometry.Scheme.Modules.pushforwardComp α.act T.hom).hom.app _ ≫
    (AlgebraicGeometry.Scheme.Modules.pushforwardCongr α.act_over).hom.app _ -
  (AlgebraicGeometry.Scheme.Modules.pushforward T.hom).map
      (SheafOfModules.unitToPushforwardObjUnit pr₂.toRingCatSheafHom) ≫
    (AlgebraicGeometry.Scheme.Modules.pushforwardComp pr₂ T.hom).hom.app _ ≫
    (AlgebraicGeometry.Scheme.Modules.pushforward (pr₂ ≫ T.hom)).map
      (AlgebraicGeometry.Scheme.Modules.unitMul (pr₁.appTop.hom lam ^ m))

/- The graded algebra sheaf of a nonnegative `𝔾_m`-action (the construction in the relative nonnegative version of
   Stacks 0EKK): the `m`-th piece is `S_m := ker φ_m ⊆ π_*O_T` (the `λ^m`-eigensections of the coaction);
   multiplication and unit are restricted to the kernels from the algebra structure of `π_*O_T`
   (`QCAlgebra.pushforwardStructureSheaf`); that a product of eigensections is a `λ^{m+n}`-eigensection is a proof
   obligation, established in `JetGrading`. -/

/-- The `m`-th piece `S_m := ker φ_m ⊆ π_*O_T` (the `λ^m`-eigensections of the coaction). -/

noncomputable def GroupSchemeAction.weightPart {k : Type u} [Field k] {S : AlgebraicGeometry.Scheme.{u}}
    [S.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {T : CategoryTheory.Over S}
    [AlgebraicGeometry.IsAffineHom T.hom] (α : GmActionOver k T) (m : ℕ) : S.Modules :=
  CategoryTheory.Limits.kernel (GroupSchemeAction.weightDefect α m)

/-- `φ_m` is a morphism of quasi-coherent modules (`π`, `q` affine, pushforward preserves quasi-coherence), and
kernels of morphisms of quasi-coherent modules are quasi-coherent (Stacks 01LA). -/
theorem GroupSchemeAction.weightPart_isQuasicoherent {k : Type u} [Field k] {S : AlgebraicGeometry.Scheme.{u}}
    [S.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {T : CategoryTheory.Over S}
    [AlgebraicGeometry.IsAffineHom T.hom] (α : GmActionOver k T) (m : ℕ) :
    (GroupSchemeAction.weightPart α m).IsQuasicoherent := by
  letI : ((AlgebraicGeometry.Scheme.Modules.pushforward T.hom).obj
      (SheafOfModules.unit T.left.ringCatSheaf)).IsQuasicoherent :=
    AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.obj_isQuasicoherent T.hom
  let q := CategoryTheory.Limits.pullback.snd
      ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom
      (T.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) ≫ T.hom
  letI : AlgebraicGeometry.IsAffineHom q := by
    dsimp [q]
    letI : AlgebraicGeometry.IsAffine
        ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).left := by
      change AlgebraicGeometry.IsAffine (Gm k)
      unfold Gm
      exact AlgebraicGeometry.isAffine_Spec _
    letI : AlgebraicGeometry.IsAffineHom
        ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom := by
      apply AlgebraicGeometry.isAffineHom_of_isAffine
    letI : CategoryTheory.MorphismProperty.IsStableUnderBaseChange
        (@AlgebraicGeometry.IsAffineHom) :=
      AlgebraicGeometry.isAffineHom_isStableUnderBaseChange
    letI : CategoryTheory.MorphismProperty.IsStableUnderBaseChangeAlong
        (@AlgebraicGeometry.IsAffineHom)
        (T.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) := by
      constructor
      intro Z' W f' g' g pb hg
      exact CategoryTheory.MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg
    letI : AlgebraicGeometry.IsAffineHom
        (CategoryTheory.Limits.pullback.snd
          ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom
          (T.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))) :=
      CategoryTheory.MorphismProperty.pullback_snd _ _ inferInstance
    infer_instance
  letI : ((AlgebraicGeometry.Scheme.Modules.pushforward q).obj
      (SheafOfModules.unit
        (CategoryTheory.Limits.pullback
          ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom
          (T.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).ringCatSheaf)).IsQuasicoherent := by
    exact AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.obj_isQuasicoherent q
  apply (AlgebraicGeometry.Scheme.Modules.isQuasicoherent_kernel
    (GroupSchemeAction.weightDefect α m)).1

/-! ## The decomposition `φ_m = act^♯ − pr₂^♯ ≫ (λ^m ·)` of the weight defect

We name the three pieces of the definition of `weightDefect` (definitionally equal, `weightDefect_eq` is `rfl`),
so that the general lemmas of `PushforwardQcAlgebraMap` (`g^♯` is multiplicative, the multiplication is bilinear
with respect to `unitMul`) yield "a product of eigensections is an eigensection". -/

section WeightDefectDecomposition

variable {k : Type u} [Field k] {S : AlgebraicGeometry.Scheme.{u}}
    [S.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]

/-- The second projection `pr₂ : W := 𝔾_m ×_k T → T`. -/
noncomputable abbrev GroupSchemeAction.gmSnd (k : Type u) [Field k] {S : AlgebraicGeometry.Scheme.{u}}
    [S.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (T : CategoryTheory.Over S) :
    CategoryTheory.Limits.pullback ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom
        (T.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) ⟶ T.left :=
  CategoryTheory.Limits.pullback.snd _ _

/-- The coordinate `λ ∈ Γ(𝔾_m) = k[λ^{±1}]` pulled back along the first projection to a global function on
`W = 𝔾_m ×_k T`. -/
noncomputable def GroupSchemeAction.lamW (T : CategoryTheory.Over S) :
    Γ(CategoryTheory.Limits.pullback ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom
        (T.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))), ⊤) :=
  (CategoryTheory.Limits.pullback.fst ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom
    (T.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).appTop.hom
    ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial k))).inv.hom (LaurentPolynomial.T 1))

/-- `act^♯ : π_*O_T ⟶ q_*O_W` (`q = pr₂ ≫ π`; via `π_*act_* ≅ (act ≫ π)_* ≅ q_*`). -/
noncomputable def GroupSchemeAction.actMap {T : CategoryTheory.Over S} (α : GmActionOver k T) :
    AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.obj T.hom ⟶
      AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.obj (GroupSchemeAction.gmSnd k T ≫ T.hom) :=
  (AlgebraicGeometry.Scheme.Modules.pushforward T.hom).map
      (SheafOfModules.unitToPushforwardObjUnit α.act.toRingCatSheafHom) ≫
    (AlgebraicGeometry.Scheme.Modules.pushforwardComp α.act T.hom).hom.app _ ≫
    (AlgebraicGeometry.Scheme.Modules.pushforwardCongr α.act_over).hom.app _

/-- pr₂^♯ : π_*O_T ⟶ q_*O_W. -/
noncomputable def GroupSchemeAction.prMap (T : CategoryTheory.Over S) :
    AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.obj T.hom ⟶
      AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.obj (GroupSchemeAction.gmSnd k T ≫ T.hom) :=
  AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.unitMap (GroupSchemeAction.gmSnd k T) T.hom

/-- Multiplication by `λ^m`, an endomorphism of `q_*O_W`. -/
noncomputable def GroupSchemeAction.lamPow (T : CategoryTheory.Over S) (m : ℕ) :
    AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.obj (GroupSchemeAction.gmSnd k T ≫ T.hom) ⟶
      AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.obj (GroupSchemeAction.gmSnd k T ≫ T.hom) :=
  (AlgebraicGeometry.Scheme.Modules.pushforward (GroupSchemeAction.gmSnd k T ≫ T.hom)).map
    (AlgebraicGeometry.Scheme.Modules.unitMul (GroupSchemeAction.lamW (k := k) T ^ m))

/-- `weightDefect α m = act^♯ − pr₂^♯ ≫ (λ^m ·)` (by definition). -/
theorem GroupSchemeAction.weightDefect_eq {T : CategoryTheory.Over S} (α : GmActionOver k T) (m : ℕ) :
    GroupSchemeAction.weightDefect α m =
      GroupSchemeAction.actMap α - GroupSchemeAction.prMap T ≫ GroupSchemeAction.lamPow T m :=
  rfl

/-- `act^♯` is multiplicative (`mul_comp_unitMap` plus the compatibility of `pushforwardCongr`). -/
theorem GroupSchemeAction.mul_comp_actMap {T : CategoryTheory.Over S} (α : GmActionOver k T) :
    AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.mul T.hom ≫ GroupSchemeAction.actMap α =
      (GroupSchemeAction.actMap α ⊗ₘ GroupSchemeAction.actMap α) ≫
        AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.mul (GroupSchemeAction.gmSnd k T ≫ T.hom) := by
  have h1 : GroupSchemeAction.actMap α =
      AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.unitMap α.act T.hom ≫
        (AlgebraicGeometry.Scheme.Modules.pushforwardCongr α.act_over).hom.app _ :=
    (CategoryTheory.Category.assoc _ _ _).symm
  rw [h1, ← CategoryTheory.Category.assoc,
    AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.mul_comp_unitMap,
    CategoryTheory.Category.assoc,
    AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.mul_comp_pushforwardCongr,
    CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom_assoc]

/-- `pr₂^♯` is multiplicative (`mul_comp_unitMap`). -/
theorem GroupSchemeAction.mul_comp_prMap (T : CategoryTheory.Over S) :
    AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.mul T.hom ≫ GroupSchemeAction.prMap T =
      (GroupSchemeAction.prMap T ⊗ₘ GroupSchemeAction.prMap T) ≫
        AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.mul (GroupSchemeAction.gmSnd k T ≫ T.hom) :=
  AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.mul_comp_unitMap _ _

/-- `(λ^m ·) ⊗ (λ^n ·)` followed by multiplication equals multiplication followed by `(λ^{m+n} ·)`
(`unitMul_tensor_comp_mul` and `pow_add`). -/
theorem GroupSchemeAction.lamPow_tensor_comp_mul (T : CategoryTheory.Over S) (m n : ℕ) :
    (GroupSchemeAction.lamPow T m ⊗ₘ GroupSchemeAction.lamPow T n) ≫
        AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.mul (GroupSchemeAction.gmSnd k T ≫ T.hom) =
      AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.mul (GroupSchemeAction.gmSnd k T ≫ T.hom) ≫
        GroupSchemeAction.lamPow T (m + n) := by
  unfold GroupSchemeAction.lamPow
  rw [AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf.unitMul_tensor_comp_mul, ← pow_add]

/-- The kernel condition rewritten: `ι_m ≫ act^♯ = ι_m ≫ pr₂^♯ ≫ (λ^m ·)`. -/
theorem GroupSchemeAction.kernelι_comp_actMap {T : CategoryTheory.Over S} (α : GmActionOver k T) (m : ℕ) :
    CategoryTheory.Limits.kernel.ι (GroupSchemeAction.weightDefect α m) ≫ GroupSchemeAction.actMap α =
      CategoryTheory.Limits.kernel.ι (GroupSchemeAction.weightDefect α m) ≫
        GroupSchemeAction.prMap T ≫ GroupSchemeAction.lamPow T m := by
  have h : CategoryTheory.Limits.kernel.ι (GroupSchemeAction.weightDefect α m) ≫
      (GroupSchemeAction.actMap α - GroupSchemeAction.prMap T ≫ GroupSchemeAction.lamPow T m) = 0 :=
    CategoryTheory.Limits.kernel.condition _
  rw [CategoryTheory.Preadditive.comp_sub, sub_eq_zero] at h
  exact h

end WeightDefectDecomposition

end
