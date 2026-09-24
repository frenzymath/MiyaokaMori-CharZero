import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.TwistPullbackPowCore
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.PullbackTensorPowMul
import MiyaokaMori.CategoryTheory.TensorPairMul
import MiyaokaMori.CategoryTheory.TensorPowHomRec
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.TensorTripleHomExt
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.TwistMulAppAssocTransport

/-! # Block multiplicativity of `twistPullbackPow`, component form

`Ψ_e = twistPullbackPow S q Q e : (O(q) ⊗ π^*Q)^{⊗e} ⟶ O(qe) ⊗ π^*Q^{⊗e}` (`TwistPullbackPowCore`).
This module proves `twistPullbackPow_add_block`:
`Ψ_{m+n} = (tensorPowAddIso A m n).hom ≫ (Ψ_m ⊗ Ψ_n) ≫ μ_{m,n}` with `μ = twistPullbackBlockMul`
(`= τ⁻¹ ≫ twistPullbackPowMul`), by the abstract theorem `MiyaokaMori.IsTensorPowHomRec.add`
(`TensorPowHomRec.lean`) applied to:

* the recursion of `Ψ` in component form (`twistPullbackPow_zero_eq`, `twistPullbackPow_succ_eq`):
  `twistPullbackMul` is the pair product `MiyaokaMori.combMul` (`TensorPairMul.lean`) of the twist multiplication
  `twistPairMul S a b := τ⁻¹ ≫ twistMul S a b` and the pullback multiplication `pullbackPairMul π M N`
  (`PullbackTensorPowMul.lean`);
* the componentwise right unit laws: `twistPairMul_unit_right_cast` (from **`twistMul_unit_right`**, `TwistPullbackPowCore`)
  and `pullbackPowMul_unit_right`;
* the componentwise associativity steps: `twistPairMul_assoc_step_cast` (from `twistPairMul_assoc`,
  the morphism-level associativity of `twistMul`, Stacks 01MO — proved here
  from the section-level **`twistMul_app_assoc`** via the double-ext lemma `tensorObj_tensorObj_hom_ext_right`)
  and `pullbackPowMul_assoc_step`.
  and `pullbackPowMul_assoc_step`.

Implementation note: the index equalities are kept as named lemmas (`cast_mul_add_cast_eq`, …) so that the
`eqToHom` proof terms are syntactically shared, and the combination of the two components is done in the abstract
theorem `IsTensorPowHomRec.add_of_combMul` (`TensorPowHomRec.lean`): elaborating an instance of `combMul_assoc_step`
directly against the concrete combined statement (where the indices `m + (n+1)` and `m + n + 1` meet) took more than
30 s per instance, while the componentwise statements `twistPairMul_assoc_step_cast`, `pullbackPowMul_assoc_step` are
cheap.

Sources: Stacks 01MO, 01CD. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
open scoped CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalCategory

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {Y : AlgebraicGeometry.Scheme.{u}}

/-- `𝟙_ = L^{⊗0}` (`tensorPow L 0 = SheafOfModules.unit`, which is the monoidal unit by construction). -/
theorem unit_eq_tensorPow_zero (L : Y.Modules) :
    𝟙_ Y.Modules = AlgebraicGeometry.Scheme.Modules.tensorPow L 0 := rfl

/-- The recursion equations of `(tensorPowAddIso L m n).inv` (`IsTensorPowMul`), for an arbitrary module `L`
(`tensorPowAlgebra.isTensorPowMul` in `LineBundleSectionRing.lean` is the same statement under `[L.IsLineBundle]`,
which is not needed: both clauses hold by definition). -/
theorem tensorPowAddIso_isTensorPowMul (L : Y.Modules) :
    MiyaokaMori.IsTensorPowMul L (AlgebraicGeometry.Scheme.Modules.tensorPow L)
      (fun e => AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj (AlgebraicGeometry.Scheme.Modules.tensorPow L e) L)
      (CategoryTheory.eqToIso (unit_eq_tensorPow_zero L))
      (fun m n => (AlgebraicGeometry.Scheme.Modules.tensorPowAddIso L m n).inv) where
  mul_zero m := rfl
  mul_succ m n := by
    show ((_ ≫ _) ≫ _) ≫ _ = _ ≫ _ ≫ _ ≫ _
    simp only [Category.assoc]
    rfl

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.relativeProj

variable {X : AlgebraicGeometry.Scheme.{u}} (S : X.GradedQCAlgebra)

/- File-local instance attributes (they expired with the previous namespace block). -/
attribute [local instance] AlgebraicGeometry.Scheme.Modules.tensorMapHom_isIso
  AlgebraicGeometry.Scheme.Modules.tensorPowSplitHom_isIso

/-- Index arithmetic for the twist indices (kept as named lemmas so that the `eqToHom` proof terms stay small and
syntactically shared). -/
theorem cast_mul_add_cast_eq (q e : ℕ) : ((q * e : ℕ) : ℤ) + (q : ℤ) = ((q * (e + 1) : ℕ) : ℤ) := by push_cast; ring
theorem cast_mul_add_cast_mul_eq (q m n : ℕ) : ((q * m : ℕ) : ℤ) + ((q * n : ℕ) : ℤ) = ((q * (m + n) : ℕ) : ℤ) := by
  push_cast; ring

/-! ### Component form

`twistPullbackMul` is the pair product (`MiyaokaMori.combMul`, `TensorPairMul.lean`) of the twist multiplication
`twistPairMul S a b := τ⁻¹ ≫ twistMul S a b : O(a) ⊗ O(b) ⟶ O(a+b)` and the pullback multiplication
`pullbackPairMul π M N : π^*M ⊗ π^*N ⟶ π^*(M ⊗ N)` (`PullbackTensorPowMul.lean`). The recursion of `twistPullbackPow`
is then an instance of `MiyaokaMori.IsTensorPowHomRec` (`TensorPowHomRec.lean`), and its block multiplicativity follows
from the right unit law and the associativity step of the two components. -/

/-- `twistMul S a b` with domain the monoidal `O(a) ⊗ O(b)`. -/
noncomputable def twistPairMul (a b : ℤ) :
    AlgebraicGeometry.Scheme.relativeProj.twist S a ⊗ AlgebraicGeometry.Scheme.relativeProj.twist S b ⟶
      AlgebraicGeometry.Scheme.relativeProj.twist S (a + b) :=
  (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _).inv ≫ AlgebraicGeometry.Scheme.relativeProj.twistMul S a b

/-- `twistPullbackMul = τ ≫ combMul (twistPairMul a b) (pullbackPairMul π M N)`. -/
theorem twistPullbackMul_eq (a b : ℤ) (M N : X.Modules) :
    twistPullbackMul S a b M N =
      (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _).hom ≫
        MiyaokaMori.combMul AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj (twistPairMul S a b)
          (AlgebraicGeometry.Scheme.Modules.pullbackPairMul (AlgebraicGeometry.Scheme.relativeProj S).hom M N) := by
  unfold twistPullbackMul MiyaokaMori.combMul MiyaokaMori.pairMul twistPairMul
  rw [← AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj_inv_comp_pullbackTensorIso_inv]
  simp only [Category.assoc]

/-- The unit `1 ⊗ 1 : 𝟙_ ⟶ O(q·0) ⊗ π^*Q^{⊗0}` (`twistUnitSection S ⊗ pullbackUnitIso⁻¹`, then `τ⁻¹`). -/
noncomputable def twistPullbackUnit (q : ℕ) (Q : X.Modules) :
    𝟙_ (AlgebraicGeometry.Scheme.relativeProj S).left.Modules ⟶
      AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.relativeProj.twist S ((q * 0 : ℕ) : ℤ))
        ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).obj
          (AlgebraicGeometry.Scheme.Modules.tensorPow Q 0)) :=
  (λ_ (𝟙_ _)).inv ≫
    (twistUnitSection S ⊗ₘ (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso (AlgebraicGeometry.Scheme.relativeProj S).hom).inv) ≫
    (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _).inv

/-- The step multiplication `T e ⊗ A ⟶ T (e+1)`, `T e := O(qe) ⊗ π^*Q^{⊗e}`, `A := O(q) ⊗ π^*Q`:
`combMul (twistPairMul (qe) q ≫ eqToHom) (pullbackStep Q e)`. -/
noncomputable def twistPullbackStep (q : ℕ) (Q : X.Modules) (e : ℕ) :
    AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.relativeProj.twist S ((q * e : ℕ) : ℤ))
        ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).obj
          (AlgebraicGeometry.Scheme.Modules.tensorPow Q e)) ⊗
      AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.relativeProj.twist S (q : ℤ))
        ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).obj Q) ⟶
      AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.relativeProj.twist S ((q * (e + 1) : ℕ) : ℤ))
        ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).obj
          (AlgebraicGeometry.Scheme.Modules.tensorPow Q (e + 1))) :=
  MiyaokaMori.combMul AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj
    (twistPairMul S ((q * e : ℕ) : ℤ) (q : ℤ) ≫
      CategoryTheory.eqToHom (congrArg (AlgebraicGeometry.Scheme.relativeProj.twist S) (cast_mul_add_cast_eq q e)))
    (AlgebraicGeometry.Scheme.Modules.pullbackStep (AlgebraicGeometry.Scheme.relativeProj S).hom Q e)

/-- The block multiplication `T m ⊗ T n ⟶ T (m+n)` in `⊗`-form:
`combMul (twistPairMul (qm) (qn) ≫ eqToHom) (pullbackPowMul π Q m n)` (`= τ⁻¹ ≫ twistPullbackPowMul`). -/
noncomputable def twistPullbackBlockMul (q : ℕ) (Q : X.Modules) (m n : ℕ) :
    AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.relativeProj.twist S ((q * m : ℕ) : ℤ))
        ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).obj
          (AlgebraicGeometry.Scheme.Modules.tensorPow Q m)) ⊗
      AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.relativeProj.twist S ((q * n : ℕ) : ℤ))
        ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).obj
          (AlgebraicGeometry.Scheme.Modules.tensorPow Q n)) ⟶
      AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.relativeProj.twist S ((q * (m + n) : ℕ) : ℤ))
        ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).obj
          (AlgebraicGeometry.Scheme.Modules.tensorPow Q (m + n))) :=
  MiyaokaMori.combMul AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj
    (twistPairMul S ((q * m : ℕ) : ℤ) ((q * n : ℕ) : ℤ) ≫
      CategoryTheory.eqToHom (congrArg (AlgebraicGeometry.Scheme.relativeProj.twist S) (cast_mul_add_cast_mul_eq q m n)))
    (AlgebraicGeometry.Scheme.Modules.pullbackPowMul (AlgebraicGeometry.Scheme.relativeProj S).hom Q m n)

/-- `Ψ_0 = eqToHom ≫ (1 ⊗ 1)` (the `eqToHom` between `𝟙_` and `A^{⊗0} = SheafOfModules.unit` is definitionally the identity). -/
theorem twistPullbackPow_zero_eq (q : ℕ) (Q : X.Modules) :
    twistPullbackPow S q Q 0 =
      (CategoryTheory.eqToIso (AlgebraicGeometry.Scheme.Modules.unit_eq_tensorPow_zero _)).inv ≫
        twistPullbackUnit S q Q := by
  change twistPullbackPow S q Q 0 = 𝟙 (𝟙_ (AlgebraicGeometry.Scheme.relativeProj S).left.Modules) ≫ twistPullbackUnit S q Q
  rw [Category.id_comp]
  rfl

/-- The recursion of `Ψ` in component form: `Ψ_{e+1} = τ ≫ (Ψ_e ▷ A) ≫ twistPullbackStep e`. -/
theorem twistPullbackPow_succ_eq (q : ℕ) (Q : X.Modules) (e : ℕ) :
    twistPullbackPow S q Q (e + 1) =
      (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _).hom ≫
        (twistPullbackPow S q Q e ▷ _) ≫ twistPullbackStep S q Q e := by
  rw [twistPullbackPow_succ, twistPullbackMul_eq]
  unfold AlgebraicGeometry.Scheme.Modules.tensorMapHom twistPullbackStep AlgebraicGeometry.Scheme.Modules.pullbackStep
    MiyaokaMori.combMul MiyaokaMori.pairMul
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [tensorHom_comp_tensorHom_assoc (twistPairMul S _ _) _ (CategoryTheory.eqToHom _) (𝟙 _),
    tensorHom_id (twistPullbackPow S q Q e)]
  simp only [Category.comp_id]
  rfl

/-- `twistPullbackPow` is the recursively defined family out of the tensor powers of `A = O(q) ⊗ π^*Q`
(`MiyaokaMori.IsTensorPowHomRec`). -/
theorem twistPullbackPow_isTensorPowHomRec (q : ℕ) (Q : X.Modules) :
    MiyaokaMori.IsTensorPowHomRec
      (AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.relativeProj.twist S (q : ℤ))
        ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).obj Q))
      (AlgebraicGeometry.Scheme.Modules.tensorPow _)
      (fun e => AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj (AlgebraicGeometry.Scheme.Modules.tensorPow _ e) _)
      (CategoryTheory.eqToIso (AlgebraicGeometry.Scheme.Modules.unit_eq_tensorPow_zero _))
      (fun e => AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.relativeProj.twist S ((q * e : ℕ) : ℤ))
        ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).obj
          (AlgebraicGeometry.Scheme.Modules.tensorPow Q e)))
      (twistPullbackStep S q Q) (twistPullbackUnit S q Q) (twistPullbackPow S q Q) where
  zero := twistPullbackPow_zero_eq S q Q
  succ e := twistPullbackPow_succ_eq S q Q e

/-- Right unit law of `twistPairMul` at the indices `q·m`, `q·0` (the latter definitionally `0`), with the index
transport `q·m + q·0 = q·(m+0)`; from `twistMul_unit_right`. -/
theorem twistPairMul_unit_right_cast (q m : ℕ) :
    (AlgebraicGeometry.Scheme.relativeProj.twist S ((q * m : ℕ) : ℤ) ◁ twistUnitSection S) ≫
        twistPairMul S ((q * m : ℕ) : ℤ) ((q * 0 : ℕ) : ℤ) ≫
        CategoryTheory.eqToHom (congrArg (AlgebraicGeometry.Scheme.relativeProj.twist S) (cast_mul_add_cast_mul_eq q m 0)) =
      (ρ_ (AlgebraicGeometry.Scheme.relativeProj.twist S ((q * m : ℕ) : ℤ))).hom := by
  have h' : (AlgebraicGeometry.Scheme.relativeProj.twist S ((q * m : ℕ) : ℤ) ◁ twistUnitSection S) ≫
      twistPairMul S ((q * m : ℕ) : ℤ) ((q * 0 : ℕ) : ℤ) =
      (ρ_ (AlgebraicGeometry.Scheme.relativeProj.twist S ((q * m : ℕ) : ℤ))).hom ≫
        CategoryTheory.eqToHom (congrArg (AlgebraicGeometry.Scheme.relativeProj.twist S)
          (show ((q * m : ℕ) : ℤ) = ((q * m : ℕ) : ℤ) + ((q * 0 : ℕ) : ℤ) by push_cast; ring)) := by
    unfold twistPairMul
    exact twistMul_unit_right S ((q * m : ℕ) : ℤ)
  rw [← Category.assoc, h', Category.assoc, CategoryTheory.eqToHom_trans]
  exact Category.comp_id _

/-- `twistPairMul` on a section pairing: `μ_{a,b}(x ⊗ y) = twistMul (x ⊗ y)` (the `Modules.tensor` pure tensor). -/
theorem twistPairMul_app_tensorSections (a b : ℤ) (V : (AlgebraicGeometry.Scheme.relativeProj S).left.Opens)
    (x : Γ(AlgebraicGeometry.Scheme.relativeProj.twist S a, V)) (y : Γ(AlgebraicGeometry.Scheme.relativeProj.twist S b, V)) :
    (twistPairMul S a b).app V
        (AlgebraicGeometry.Scheme.Modules.tensorSections (AlgebraicGeometry.Scheme.relativeProj.twist S a)
          (AlgebraicGeometry.Scheme.relativeProj.twist S b) V x y) =
      (AlgebraicGeometry.Scheme.relativeProj.twistMul S a b).app V (AlgebraicGeometry.Scheme.Modules.moduleTensorSection x y) :=
  congrArg ((AlgebraicGeometry.Scheme.relativeProj.twistMul S a b).app V)
    (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj_inv_app_tensorSections _ _ V x y)

/-- The section-level content of `twistPairMul_assoc` (indices transported by `eqToHom`): on `x ⊗ (y ⊗ z)`, after
evaluating the whiskerings and the associator, both sides of the associativity are the two ways of multiplying
`x, y, z`; this is `twistMul_app_assoc'` (the transport form, `TwistMulAppAssocTransport`) after `subst`
of the index equalities. Kept separate from the morphism-level statement so that the rewriting happens on small
section terms. -/
theorem twistPairMul_app_assoc_sections (a b c : ℤ) {d e s : ℤ} (hd : b + c = d) (he : a + d = e) (hs : a + b = s)
    (he' : s + c = e) (V : (AlgebraicGeometry.Scheme.relativeProj S).left.Opens)
    (x : Γ(AlgebraicGeometry.Scheme.relativeProj.twist S a, V)) (y : Γ(AlgebraicGeometry.Scheme.relativeProj.twist S b, V))
    (z : Γ(AlgebraicGeometry.Scheme.relativeProj.twist S c, V)) :
    (CategoryTheory.eqToHom (congrArg (AlgebraicGeometry.Scheme.relativeProj.twist S) he)).app V
        ((twistPairMul S a d).app V
          (AlgebraicGeometry.Scheme.Modules.tensorSections (AlgebraicGeometry.Scheme.relativeProj.twist S a)
            (AlgebraicGeometry.Scheme.relativeProj.twist S d) V x
            ((CategoryTheory.eqToHom (congrArg (AlgebraicGeometry.Scheme.relativeProj.twist S) hd)).app V
              ((twistPairMul S b c).app V
                (AlgebraicGeometry.Scheme.Modules.tensorSections (AlgebraicGeometry.Scheme.relativeProj.twist S b)
                  (AlgebraicGeometry.Scheme.relativeProj.twist S c) V y z))))) =
      (CategoryTheory.eqToHom (congrArg (AlgebraicGeometry.Scheme.relativeProj.twist S) he')).app V
        ((twistPairMul S s c).app V
          (AlgebraicGeometry.Scheme.Modules.tensorSections (AlgebraicGeometry.Scheme.relativeProj.twist S s)
            (AlgebraicGeometry.Scheme.relativeProj.twist S c) V
            ((CategoryTheory.eqToHom (congrArg (AlgebraicGeometry.Scheme.relativeProj.twist S) hs)).app V
              ((twistPairMul S a b).app V
                (AlgebraicGeometry.Scheme.Modules.tensorSections (AlgebraicGeometry.Scheme.relativeProj.twist S a)
                  (AlgebraicGeometry.Scheme.relativeProj.twist S b) V x y))) z)) := by
  subst hd hs he
  rw [AlgebraicGeometry.Scheme.Modules.eqToHom_app_self', AlgebraicGeometry.Scheme.Modules.eqToHom_app_self',
    AlgebraicGeometry.Scheme.Modules.eqToHom_app_self', twistPairMul_app_tensorSections,
    twistPairMul_app_tensorSections, twistPairMul_app_tensorSections, twistPairMul_app_tensorSections]
  exact AlgebraicGeometry.Scheme.relativeProj.twistMul_app_assoc' S a b c he' V x y z

/-- **Associativity of `twistMul`, morphism level** (Stacks 01MO):
`(O(a) ◁ μ_{b,c}) ≫ μ_{a,d} = α⁻¹ ≫ (μ_{a,b} ▷ O(c)) ≫ μ_{s,c}` as morphisms `O(a) ⊗ (O(b) ⊗ O(c)) ⟶ O(e)`, where
`μ_{a,b} := twistPairMul S a b = τ⁻¹ ≫ twistMul S a b`, and the `eqToHom`s transport the indices along
`hd : b + c = d`, `he : a + d = e`, `hs : a + b = s`, `he' : s + c = e` (the plain statement is the case
`d := b + c`, `s := a + b`, `e := a + (b + c)`, where all `eqToHom`s but the last are identities and the last one is
`eqToHom (congrArg O (add_assoc a b c))`; the general form is what the applications need, and deriving it from the plain
one by `subst` costs about 20 s of elaboration in this category).

**Natural-language proof** (Stacks 01MO: the multiplication maps `O(a) ⊗ O(b) → O(a+b)` are associative):
1. Both sides are morphisms of sheaves of modules out of `O(a) ⊗ (O(b) ⊗ O(c))`. Such a morphism is determined by
   its values on the sections `x ⊗ (y ⊗ z)` (`tensorSections x (tensorSections y z)`) over all opens `V`: the tensor
   sheaf is the sheafification of the presheaf tensor product (`tensorObj_hom_ext`, `Stacks01cmTensorHom`,
   reduces to sections `x ⊗ w` with `w ∈ Γ(O(b) ⊗ O(c), V)` arbitrary), and every section `w` is locally a sum of pure
   tensors `y ⊗ z` (`exists_tensor_unit_app_eq_map`, `TwistPowerIsoSectionsGeneration`: `isLocallySurjective_toSheafify`);
   since both sides are additive and compatible with restriction and the target is a sheaf, it suffices to check on
   `x ⊗ (y ⊗ z)`. (This "double ext" lemma for `A ⊗ (B ⊗ C)` is `tensorObj_tensorObj_hom_ext_right`,
   `TensorTripleHomExt`.)
2. On `x ⊗ (y ⊗ z)`, `τ⁻¹` and the whiskerings act factorwise (`tensorHom_tensorSections`,
   `tensorIsoTensorObj_inv_app_tensorSections`), the associator acts by `associator_app_tensorSections`, and the
   `eqToHom`s only transport the indices (`eqToHom_app`); so the claim becomes the section-level identity
   `x · (y · z) = eqToHom ((x · y) · z)`, which is exactly `twistMul_app_assoc`
   (`RelativeProjTwistMulAssoc`:
   locally on `π⁻¹U` the multiplication is that of homogeneous fractions, `mul_assoc`).
3. Index bookkeeping: `subst hd hs he` first; then `he' : a + b + c = a + (b + c)` and the remaining `eqToHom`s are
   `eqToHom (congrArg O rfl) = 𝟙` (`eqToHom_refl`).

**Library facts used**: `twistMul_app_assoc`, `tensorObj_tensorObj_hom_ext_right`
(`TensorTripleHomExt`, the double-ext lemma), `whiskerLeft_app_tensorSections`, `tensorHom_tensorSections`,
`associator_app_tensorSections`, `tensorIsoTensorObj_inv_app_tensorSections`.

**Edge cases**: `a, b, c` arbitrary integers (possibly negative); no hypothesis on `S`. -/
theorem twistPairMul_assoc (a b c : ℤ) {d e s : ℤ} (hd : b + c = d) (he : a + d = e) (hs : a + b = s)
    (he' : s + c = e) :
    (AlgebraicGeometry.Scheme.relativeProj.twist S a ◁
        (twistPairMul S b c ≫ CategoryTheory.eqToHom (congrArg (AlgebraicGeometry.Scheme.relativeProj.twist S) hd))) ≫
      twistPairMul S a d ≫ CategoryTheory.eqToHom (congrArg (AlgebraicGeometry.Scheme.relativeProj.twist S) he) =
    (α_ _ _ _).inv ≫
      ((twistPairMul S a b ≫ CategoryTheory.eqToHom (congrArg (AlgebraicGeometry.Scheme.relativeProj.twist S) hs)) ▷
        AlgebraicGeometry.Scheme.relativeProj.twist S c) ≫
      twistPairMul S s c ≫ CategoryTheory.eqToHom (congrArg (AlgebraicGeometry.Scheme.relativeProj.twist S) he') := by
  apply AlgebraicGeometry.Scheme.Modules.assoc_of_app_tensorSections
  intro V x y z
  exact twistPairMul_app_assoc_sections S a b c hd he hs he' V x y z

/-- The twist component of the associativity step, at the indices `q·m`, `q·n`, `q` (from `twistPairMul_assoc`;
the codomain indices `q·(m+n+1)` and `q·(m+(n+1))` are definitionally equal). -/
theorem twistPairMul_assoc_step_cast (q m n : ℕ) :
    (AlgebraicGeometry.Scheme.relativeProj.twist S ((q * m : ℕ) : ℤ) ◁
        (twistPairMul S ((q * n : ℕ) : ℤ) (q : ℤ) ≫
          CategoryTheory.eqToHom (congrArg (AlgebraicGeometry.Scheme.relativeProj.twist S) (cast_mul_add_cast_eq q n)))) ≫
      (twistPairMul S ((q * m : ℕ) : ℤ) ((q * (n + 1) : ℕ) : ℤ) ≫
        CategoryTheory.eqToHom (congrArg (AlgebraicGeometry.Scheme.relativeProj.twist S)
          (cast_mul_add_cast_mul_eq q m (n + 1)))) =
    (α_ _ _ _).inv ≫
      ((twistPairMul S ((q * m : ℕ) : ℤ) ((q * n : ℕ) : ℤ) ≫
        CategoryTheory.eqToHom (congrArg (AlgebraicGeometry.Scheme.relativeProj.twist S) (cast_mul_add_cast_mul_eq q m n))) ▷
        AlgebraicGeometry.Scheme.relativeProj.twist S (q : ℤ)) ≫
      (twistPairMul S ((q * (m + n) : ℕ) : ℤ) (q : ℤ) ≫
        CategoryTheory.eqToHom (congrArg (AlgebraicGeometry.Scheme.relativeProj.twist S) (cast_mul_add_cast_eq q (m + n)))) :=
  twistPairMul_assoc S ((q * m : ℕ) : ℤ) ((q * n : ℕ) : ℤ) (q : ℤ)
    (d := ((q * (n + 1) : ℕ) : ℤ)) (e := ((q * (m + (n + 1)) : ℕ) : ℤ)) (s := ((q * (m + n) : ℕ) : ℤ))
    (cast_mul_add_cast_eq q n) (cast_mul_add_cast_mul_eq q m (n + 1)) (cast_mul_add_cast_mul_eq q m n)
    (cast_mul_add_cast_eq q (m + n))

/-- **Block multiplicativity of Ψ in component form**: `Ψ_{m+n} = (tensorPowAddIso A m n).hom ≫ (Ψ_m ⊗ Ψ_n) ≫ μ_{m,n}`
(`IsTensorPowHomRec.add_of_combMul` with the componentwise laws `twistPairMul_unit_right_cast` / `twistPairMul_assoc_step_cast`
on the twist side and `pullbackPowMul_unit_right` / `pullbackPowMul_assoc_step` on the pullback side). -/
theorem twistPullbackPow_add_block (q : ℕ) (Q : X.Modules) (m n : ℕ) :
    twistPullbackPow S q Q (m + n) =
      (AlgebraicGeometry.Scheme.Modules.tensorPowAddIso _ m n).hom ≫
        (twistPullbackPow S q Q m ⊗ₘ twistPullbackPow S q Q n) ≫ twistPullbackBlockMul S q Q m n :=
  MiyaokaMori.IsTensorPowHomRec.add_of_combMul AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj
    (O := fun e => AlgebraicGeometry.Scheme.relativeProj.twist S ((q * e : ℕ) : ℤ))
    (G := fun e => (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).obj
      (AlgebraicGeometry.Scheme.Modules.tensorPow Q e))
    (fun e => twistPairMul S ((q * e : ℕ) : ℤ) (q : ℤ) ≫
      CategoryTheory.eqToHom (congrArg (AlgebraicGeometry.Scheme.relativeProj.twist S) (cast_mul_add_cast_eq q e)))
    (fun e => AlgebraicGeometry.Scheme.Modules.pullbackStep (AlgebraicGeometry.Scheme.relativeProj S).hom Q e)
    (fun m n => twistPairMul S ((q * m : ℕ) : ℤ) ((q * n : ℕ) : ℤ) ≫
      CategoryTheory.eqToHom (congrArg (AlgebraicGeometry.Scheme.relativeProj.twist S) (cast_mul_add_cast_mul_eq q m n)))
    (fun m n => AlgebraicGeometry.Scheme.Modules.pullbackPowMul (AlgebraicGeometry.Scheme.relativeProj S).hom Q m n)
    (twistUnitSection S) (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso (AlgebraicGeometry.Scheme.relativeProj S).hom).inv
    (twistPairMul_unit_right_cast S q)
    (AlgebraicGeometry.Scheme.Modules.pullbackPowMul_unit_right (AlgebraicGeometry.Scheme.relativeProj S).hom Q)
    (twistPairMul_assoc_step_cast S q)
    (AlgebraicGeometry.Scheme.Modules.pullbackPowMul_assoc_step (AlgebraicGeometry.Scheme.relativeProj S).hom Q)
    (AlgebraicGeometry.Scheme.Modules.tensorPowAddIso_isTensorPowMul _) (twistPullbackPow_isTensorPowHomRec S q Q) m n

end AlgebraicGeometry.Scheme.relativeProj

end
