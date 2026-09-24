import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.TwistPullbackPowBlock
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.TwistPullbackMulAssoc

/-! # `twistPullbackPow`: the body of `splitTwistMul` at the variable level, and its block multiplicativity

Support module for the multiplicativity of the split twist multiplication (`SplitTwistMulAdd`).

* `twistPullbackMul S a b M N : (O(a) ⊗ π^*M) ⊗ (O(b) ⊗ π^*N) ⟶ O(a+b) ⊗ π^*(M ⊗ N)` — `tensorμ`, then `twistMul`
  and `pullbackTensorIso⁻¹` (Stacks 01MO, 01CD);
* `twistPullbackPow S q Q e : (O(q) ⊗ π^*Q)^{⊗e} ⟶ O(qe) ⊗ π^*Q^{⊗e}` — the `Nat.rec` inside `splitTwistMul`
  (`TwistMultiplication.lean`), with `S, q, Q` as variables; `twistPullbackPow_rec_apply` is the `rfl` bridge;
* `twistPullbackPow_add`: block multiplicativity `Ψ_{e+e'} = split ≫ (Ψ_e ⊗ Ψ_{e'}) ≫ μ_{e,e'}`, by induction from the
  named leaves `twistPullbackPow_add_zero` (needs the unit law `twistMul_unit_right`) and
  `twistPullbackPow_add_succ_of` (needs the associativity `twistPullbackMul_assoc`);
* `twistPullbackPow_mul_exists_iso(_transport)`: the target statement in general form (any global section `x`,
  indices as variables), derived from `twistPullbackPow_add`.

`IsIso` facts (`tensorMapHom_isIso`, `tensorPowSplitHom_isIso`, `tensorμ_isIso`, `twistPullbackMul_isIso`,
`twistPullbackPowMul_isIso`) are **theorems with file-local `attribute [local instance]`** — no global instance is
registered; importers needing them use `haveI`.

Module layout: `TwistPullbackPowCore` (the definitions), `TwistPullbackPowBlock` (component form, block
multiplicativity `twistPullbackPow_add_block`, `twistPairMul_assoc`), `TwistPullbackMulAssoc(Components)`
(`twistPullbackMul_assoc'`), and this file.

Sources: Stacks 01MO/01MS/01CD; the proof of Proposition 2.4 of the paper.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
open scoped CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalCategory

noncomputable section


namespace AlgebraicGeometry.Scheme.relativeProj

variable {X : AlgebraicGeometry.Scheme.{u}} (S : X.GradedQCAlgebra)

/- File-local instance attributes (they expired with the previous namespace block). -/
attribute [local instance] AlgebraicGeometry.Scheme.Modules.tensorMapHom_isIso
  AlgebraicGeometry.Scheme.Modules.tensorPowSplitHom_isIso
attribute [local instance] tensorμ_isIso twistPullbackMul_isIso twistPullbackPowMul_isIso

/-- **Associativity of `twistPullbackMul`** (Stacks 01MO + 01CD):
`μ_{a+b,c} ∘ (μ_{a,b} ⊗ 𝟙) = (eqToHom ⊗ π^*α⁻¹) ∘ μ_{a,b+c} ∘ (𝟙 ⊗ μ_{b,c}) ∘ α`
as morphisms `((O(a) ⊗ π^*M) ⊗ (O(b) ⊗ π^*N)) ⊗ (O(c) ⊗ π^*R) ⟶ O(a+b+c) ⊗ π^*((M ⊗ N) ⊗ R)`.

**Natural-language proof**:
1. Unfold `twistPullbackMul`: it is `tensorμ` (the symmetric-monoidal interchange) followed by
   `twistMul S a b ⊗ (pullbackTensorIso π M N).inv`, with `tensorIsoTensorObj` conversions between `Modules.tensor`
   and `⊗`. Cancel the conversions (`Iso.inv_hom_id_assoc`).
2. The two sides differ by (i) the coherence of `tensorμ` with the associator
   (`MonoidalCategory.tensor_associativity`: `(tensorμ ▷ _) ≫ tensorμ ≫ (α ⊗ α) = α ≫ (_ ◁ tensorμ) ≫ tensorμ`),
   (ii) the associativity of `twistMul` on the twist factors, and (iii) the associativity of `pullbackTensorObjIso.inv`
   on the pullback factors (`pullback_μ_associativity`, `ModulesPullbackMonoidal`,
   which is `LaxMonoidal.associativity` for `π^*`).
3. (ii) is the morphism-level form of `twistMul_app_assoc`
   (`RelativeProjTwistMulAssoc`: `(x·y)·z = x·(y·z)` on sections over every open `V`): two
   morphisms out of `(O(a) ⊗ O(b)) ⊗ O(c)` agree iff they agree on all sections of the form
   `tensorSections (tensorSections x y) z` over all opens (these generate the tensor presheaf and the sheafification unit
   is epi on such sections: `Presheaf.isLocallySurjective_toSheafify`, `exists_unit_app_eq_map`), and on those the
   section-level statement is exactly `twistMul_app_assoc` after `tensorHom_tensorSections` and
   `tensorIsoTensorObj_hom_app_top_sectionTensor`.
4. Assemble with `tensorHom_comp_tensorHom`, `tensorμ_natural_left/right` and `eqToHom_map`
   (the `eqToHom` transports only the index `a + (b + c) = a + b + c`).

**Library facts used**: `tensor_associativity`, `tensorμ_natural_left`, `tensorμ_natural_right`
(Mathlib `CategoryTheory/Monoidal/Braided/Basic.lean`), `pullback_μ_associativity`, `twistMul_app_assoc`.

**Edge cases**: `a, b, c` arbitrary integers; `M, N, R` arbitrary modules.

Proved as an alias of `twistPullbackMul_assoc'`
(`TwistPullbackMulAssoc`: components `twistPairMul_assoc_add_assoc` (twist side, from `twistMul_app_assoc`
via the double-ext lemma `tensorObj_tensorObj_hom_ext_right`) and `pullbackPairMul_assoc_tensorAssocIso` (pullback side,
from `pullback_μ_associativity`), combined by `combMul_assoc_conj`). -/
theorem twistPullbackMul_assoc (a b c : ℤ) (M N R : X.Modules) :
    AlgebraicGeometry.Scheme.Modules.tensorMapHom (twistPullbackMul S a b M N) (𝟙 _) ≫
        twistPullbackMul S (a + b) c (AlgebraicGeometry.Scheme.Modules.tensor M N) R =
      (AlgebraicGeometry.Scheme.Modules.tensorAssocIso _ _ _).hom ≫
        AlgebraicGeometry.Scheme.Modules.tensorMapHom (𝟙 _) (twistPullbackMul S b c N R) ≫
        twistPullbackMul S a (b + c) M (AlgebraicGeometry.Scheme.Modules.tensor N R) ≫
        AlgebraicGeometry.Scheme.Modules.tensorMapHom
          (CategoryTheory.eqToHom (congrArg (AlgebraicGeometry.Scheme.relativeProj.twist S) (add_assoc a b c).symm))
          ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).map
            (AlgebraicGeometry.Scheme.Modules.tensorAssocIso M N R).inv) :=
  twistPullbackMul_assoc' S a b c M N R

/-- `τ⁻¹ ≫ twistPullbackPowMul = twistPullbackBlockMul` (the block multiplication of the Block module in `Modules.tensor`
form); kept here rather than in the Block module for compile-time reasons (about 20 s of elaboration). -/
theorem tensorIsoTensorObj_inv_comp_twistPullbackPowMul (q : ℕ) (Q : X.Modules) (m n : ℕ) :
    (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _).inv ≫ twistPullbackPowMul S q Q m n =
      twistPullbackBlockMul S q Q m n := by
  unfold twistPullbackPowMul twistPullbackBlockMul
  rw [twistPullbackMul_eq]
  unfold AlgebraicGeometry.Scheme.Modules.tensorMapHom AlgebraicGeometry.Scheme.Modules.pullbackPowMul
    MiyaokaMori.combMul MiyaokaMori.pairMul
  simp only [Category.assoc, Iso.inv_hom_id_assoc, tensorHom_comp_tensorHom_assoc]

/-- **Block multiplicativity of Ψ, base case**:
`Ψ_{e+0} = split_{e,0} ≫ (Ψ_e ⊗ Ψ_0) ≫ μ_{e,0}`.

**Natural-language proof**: `e + 0 = e` definitionally, so the left side is `Ψ_e`. On the right,
`tensorPowSplitHom A e 0 = (ρ_ A^{⊗e}).inv ≫ (A^{⊗e} ◁ eqToHom (𝟙_ = unit)) ≫ τ⁻¹` (definition of `tensorPowAddIso _ _ 0`),
`Ψ_0 = (λ_ 𝟙_).inv ≫ (twistUnitSection S ⊗ pullbackUnitIso⁻¹) ≫ τ⁻¹` (`twistPullbackPow_zero`), and
`μ_{e,0} = twistPullbackMul S (qe) (q·0) Q^{⊗e} Q^{⊗0} ≫ (eqToHom ⊗ π^*(τ ≫ (tensorPowAddIso Q e 0)⁻¹))`.
After converting everything to the monoidal `⊗` (`tensorMapHom`, `Iso.inv_hom_id_assoc`) and applying
`tensorμ` on `(O(qe) ⊗ π^*Q^{⊗e}) ⊗ (𝟙_ ⊗ 𝟙_)` (`tensor_right_unitality`: `ρ_ (X₁ ⊗ X₂) = (X₁ ⊗ X₂) ◁ (λ_ 𝟙_).inv ≫ tensorμ ≫ (ρ_ X₁ ⊗ ρ_ X₂)`
in inverse form), the twist factor is `(O(qe) ◁ twistUnitSection S) ≫ τ⁻¹ ≫ twistMul S (qe) 0 ≫ eqToHom`, which is
`(ρ_ O(qe)).hom` by **`twistMul_unit_right`** (the two `eqToHom`s compose to the identity, `eqToHom_trans`), and the
pullback factor is `(π^*Q^{⊗e} ◁ pullbackUnitIso⁻¹) ≫ (pullbackTensorObjIso π _ 𝟙_).inv ≫ π^*((tensorPowAddIso Q e 0)⁻¹)`,
which is `(ρ_ (π^*Q^{⊗e})).hom` by `pullback_right_unitality` (`ModulesPullbackMonoidal.lean`) and the definition of
`tensorPowAddIso Q e 0` (`(ρ_ _).symm ≪≫ whiskerLeftIso _ (eqToIso _)`, whose inverse is `(_ ◁ eqToHom⁻¹) ≫ (ρ_ _).hom`).
Finally `(ρ_ A).inv ≫ (ρ_ A).hom = 𝟙` on both factors gives `Ψ_e`.

**Library facts used**: `twistMul_unit_right`, `pullback_right_unitality`, `tensor_right_unitality`
(Mathlib), `twistPullbackPow_zero`, `tensorPowAddIso` (definition), `eqToHom_trans`, `eqToHom_refl`.

**Edge cases**: `e = 0` included; `q = 0` allowed (then all twists are `O(0)`).

Estimated 80–150 lines, medium–hard (monoidal bookkeeping). -/
theorem twistPullbackPow_add_zero (q : ℕ) (Q : X.Modules) (e : ℕ) :
    twistPullbackPow S q Q (e + 0) =
      AlgebraicGeometry.Scheme.Modules.tensorPowSplitHom
          (AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.relativeProj.twist S (q : ℤ))
            ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).obj Q)) e 0 ≫
        AlgebraicGeometry.Scheme.Modules.tensorMapHom (twistPullbackPow S q Q e) (twistPullbackPow S q Q 0) ≫
        twistPullbackPowMul S q Q e 0 := by
  rw [twistPullbackPow_add_block S q Q e 0]
  unfold AlgebraicGeometry.Scheme.Modules.tensorPowSplitHom AlgebraicGeometry.Scheme.Modules.tensorMapHom
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [tensorIsoTensorObj_inv_comp_twistPullbackPowMul]

/-- **Block multiplicativity of Ψ, inductive step**:
if `Ψ_{e+e'} = split_{e,e'} ≫ (Ψ_e ⊗ Ψ_{e'}) ≫ μ_{e,e'}` then
`Ψ_{e+(e'+1)} = split_{e,e'+1} ≫ (Ψ_e ⊗ Ψ_{e'+1}) ≫ μ_{e,e'+1}`.

**Natural-language proof**: `e + (e'+1) = (e+e') + 1` definitionally, so by `twistPullbackPow_succ`
`Ψ_{e+e'+1} = (Ψ_{e+e'} ⊗ 𝟙) ≫ μ_{q(e+e'),q} ≫ (eqToHom ⊗ 𝟙)`; substitute the hypothesis for `Ψ_{e+e'}`.
Also `Ψ_{e'+1} = (Ψ_{e'} ⊗ 𝟙) ≫ μ_{qe',q} ≫ (eqToHom ⊗ 𝟙)` (`twistPullbackPow_succ`), and
`tensorPowAddIso A e (e'+1) = τ ≪≫ whiskerRightIso (tensorPowAddIso A e e') A ≪≫ α_ ≪≫ whiskerLeftIso _ τ⁻¹`
(definition), i.e. `split_{e,e'+1} = (split_{e,e'} ⊗ 𝟙) ≫ tensorAssocIso` in terms of `Modules.tensor`.
So the claim reduces to
`(μ_{e,e'} ⊗ 𝟙) ≫ μ_{q(e+e'),q} ≫ (eqToHom ⊗ 𝟙) = tensorAssocIso ≫ (𝟙 ⊗ (μ_{qe',q} ≫ (eqToHom ⊗ 𝟙))) ≫ μ_{e,e'+1}`,
which is **`twistPullbackMul_assoc`** with `a = qe`, `b = qe'`, `c = q`, `M = Q^{⊗e}`, `N = Q^{⊗e'}`, `R = Q`, after
(i) moving the `eqToHom` index transports through `twistPullbackMul` (`eqToHom` is natural: `eqToHom_map`,
`tensorMapHom` of `eqToHom`s is an `eqToHom`), and (ii) identifying the `π^*`-factors:
`π^*(τ ≫ (tensorPowAddIso Q e (e'+1))⁻¹)` versus `π^*(tensorAssocIso⁻¹) ≫ π^*((τ ≫ (tensorPowAddIso Q e e')⁻¹) ⊗ 𝟙)`,
which is again the recursive definition of `tensorPowAddIso Q e (e'+1)` (its inverse is
`whiskerLeft τ ≫ α⁻¹ ≫ whiskerRight (tensorPowAddIso Q e e')⁻¹ ≫ τ⁻¹`), plus functoriality of `π^*` (`Functor.map_comp`).

**Library facts used**: `twistPullbackPow_succ`, `twistPullbackMul_assoc`, `tensorPowAddIso` (definition),
`tensorMapHom`, `tensorAssocIso`, `eqToHom_map`, `Functor.map_comp`.

**Edge cases**: `e = 0` or `e' = 0` included.

Estimated 120–200 lines, hard (index transports through `eqToHom` are the main cost). -/
theorem twistPullbackPow_add_succ_of (q : ℕ) (Q : X.Modules) (e e' : ℕ)
    (ih : twistPullbackPow S q Q (e + e') =
      AlgebraicGeometry.Scheme.Modules.tensorPowSplitHom
          (AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.relativeProj.twist S (q : ℤ))
            ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).obj Q)) e e' ≫
        AlgebraicGeometry.Scheme.Modules.tensorMapHom (twistPullbackPow S q Q e) (twistPullbackPow S q Q e') ≫
        twistPullbackPowMul S q Q e e') :
    twistPullbackPow S q Q (e + (e' + 1)) =
      AlgebraicGeometry.Scheme.Modules.tensorPowSplitHom
          (AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.relativeProj.twist S (q : ℤ))
            ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).obj Q)) e (e' + 1) ≫
        AlgebraicGeometry.Scheme.Modules.tensorMapHom (twistPullbackPow S q Q e) (twistPullbackPow S q Q (e' + 1)) ≫
        twistPullbackPowMul S q Q e (e' + 1) := by
  clear ih
  rw [twistPullbackPow_add_block S q Q e (e' + 1)]
  unfold AlgebraicGeometry.Scheme.Modules.tensorPowSplitHom AlgebraicGeometry.Scheme.Modules.tensorMapHom
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rw [tensorIsoTensorObj_inv_comp_twistPullbackPowMul]

/-- **Block multiplicativity of Ψ**: `Ψ_{e+e'} = split_{e,e'} ≫ (Ψ_e ⊗ Ψ_{e'}) ≫ μ_{e,e'}`
(induction on `e'` from `twistPullbackPow_add_zero` and `twistPullbackPow_add_succ_of`). -/
theorem twistPullbackPow_add (q : ℕ) (Q : X.Modules) (e e' : ℕ) :
    twistPullbackPow S q Q (e + e') =
      AlgebraicGeometry.Scheme.Modules.tensorPowSplitHom
          (AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.relativeProj.twist S (q : ℤ))
            ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).obj Q)) e e' ≫
        AlgebraicGeometry.Scheme.Modules.tensorMapHom (twistPullbackPow S q Q e) (twistPullbackPow S q Q e') ≫
        twistPullbackPowMul S q Q e e' := by
  induction e' with
  | zero => exact twistPullbackPow_add_zero S q Q e
  | succ e' ih => exact twistPullbackPow_add_succ_of S q Q e e' ih

/-- **Multiplicativity of the coordinate powers, general form**: for any global section `x` of `O(q) ⊗ π^*Q`
and any `d, d'` with `twistMul S (qd) (qd')` an isomorphism, the block multiplication `μ_{d,d'}` is an isomorphism
`L_d ⊗ L_{d'} ≅ L_{d+d'}` sending `Ψ_d(x^{⊗d}) ⊗ Ψ_{d'}(x^{⊗d'})` to `Ψ_{d+d'}(x^{⊗(d+d')})`. -/
theorem twistPullbackPow_mul_exists_iso (q : ℕ) (Q : X.Modules) (d d' : ℕ)
    [IsIso (AlgebraicGeometry.Scheme.relativeProj.twistMul S ((q * d : ℕ) : ℤ) ((q * d' : ℕ) : ℤ))]
    (x : ((AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.relativeProj.twist S (q : ℤ))
      ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).obj Q)).val.obj
        (Opposite.op ⊤) : Type u)) :
    ∃ Φ : AlgebraicGeometry.Scheme.Modules.tensor
        (AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.relativeProj.twist S ((q * d : ℕ) : ℤ))
          ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).obj
            (AlgebraicGeometry.Scheme.Modules.tensorPow Q d)))
        (AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.relativeProj.twist S ((q * d' : ℕ) : ℤ))
          ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).obj
            (AlgebraicGeometry.Scheme.Modules.tensorPow Q d'))) ≅
      AlgebraicGeometry.Scheme.Modules.tensor
        (AlgebraicGeometry.Scheme.relativeProj.twist S ((q * (d + d') : ℕ) : ℤ))
        ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).obj
          (AlgebraicGeometry.Scheme.Modules.tensorPow Q (d + d'))),
      Φ.hom.app ⊤ (sectionTensor
        ((twistPullbackPow S q Q d).app ⊤ (AlgebraicGeometry.Scheme.Modules.tensorPowSection x d))
        ((twistPullbackPow S q Q d').app ⊤ (AlgebraicGeometry.Scheme.Modules.tensorPowSection x d'))) =
      (twistPullbackPow S q Q (d + d')).app ⊤ (AlgebraicGeometry.Scheme.Modules.tensorPowSection x (d + d')) := by
  refine ⟨asIso (twistPullbackPowMul S q Q d d'), ?_⟩
  rw [twistPullbackPow_add S q Q d d', ← AlgebraicGeometry.Scheme.Modules.tensorMapHom_app_top_sectionTensor,
    ← AlgebraicGeometry.Scheme.Modules.tensorPowSplitHom_app_top_tensorPowSection, asIso_hom]
  exact ((AlgebraicGeometry.Scheme.Modules.comp_app_apply_stma _ _ ⊤ _).trans
    (AlgebraicGeometry.Scheme.Modules.comp_app_apply_stma _ _ ⊤ _)).symm

/-- `twistPullbackPow S q Q e` as an explicit `Nat.rec` (definitional; used to recognise the body of
`splitTwistMul` after unfolding). -/
theorem twistPullbackPow_rec_apply (q : ℕ) (Q : X.Modules) (e : ℕ) :
    (Nat.rec (motive := fun e =>
      AlgebraicGeometry.Scheme.Modules.tensorPow
          (AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.relativeProj.twist S (q : ℤ))
            ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).obj Q)) e ⟶
        AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.relativeProj.twist S ((q * e : ℕ) : ℤ))
          ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).obj
            (AlgebraicGeometry.Scheme.Modules.tensorPow Q e)))
    ((CategoryTheory.MonoidalCategoryStruct.leftUnitor (C := (AlgebraicGeometry.Scheme.relativeProj S).left.Modules)
        (SheafOfModules.unit _)).inv ≫
      CategoryTheory.MonoidalCategoryStruct.tensorHom (C := (AlgebraicGeometry.Scheme.relativeProj S).left.Modules)
        ((AlgebraicGeometry.Scheme.Modules.pullbackUnitIso (AlgebraicGeometry.Scheme.relativeProj S).hom).inv ≫
          (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).map S.one ≫
          AlgebraicGeometry.Scheme.relativeProj.evaluation S 0)
        (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso (AlgebraicGeometry.Scheme.relativeProj S).hom).inv ≫
      (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _).inv)
    (fun e Ψe =>
      (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _).hom ≫
        CategoryTheory.MonoidalCategoryStruct.tensorHom (C := (AlgebraicGeometry.Scheme.relativeProj S).left.Modules)
          (Ψe ≫ (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _).hom)
          (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _).hom ≫
        CategoryTheory.MonoidalCategory.tensorμ (C := (AlgebraicGeometry.Scheme.relativeProj S).left.Modules) _ _ _ _ ≫
        CategoryTheory.MonoidalCategoryStruct.tensorHom (C := (AlgebraicGeometry.Scheme.relativeProj S).left.Modules)
          ((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _).inv ≫
            AlgebraicGeometry.Scheme.relativeProj.twistMul S _ _ ≫
            CategoryTheory.eqToHom (congrArg (AlgebraicGeometry.Scheme.relativeProj.twist S) (by push_cast; ring)))
          ((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _).inv ≫
            (AlgebraicGeometry.Scheme.Modules.pullbackTensorIso (AlgebraicGeometry.Scheme.relativeProj S).hom _ _).inv) ≫
        (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _).inv)
    e : _) = twistPullbackPow S q Q e := rfl

/-- **Multiplicativity of the coordinate powers, transport form**: as `twistPullbackPow_mul_exists_iso`, but with the
indices `d + d' = dsum` and the identifications `L_d = B₁`, `L_{d'} = B₂`, `L_{dsum} = B₃` as variables (so that the
concrete statement, whose objects carry `eqToHom` index transports `q(m/q) = m`, is a syntactic instance). -/
theorem twistPullbackPow_mul_exists_iso_transport (q : ℕ) (Q : X.Modules) (d d' dsum : ℕ) (hd : d + d' = dsum)
    {B₁ B₂ B₃ : (AlgebraicGeometry.Scheme.relativeProj S).left.Modules}
    (h₁ : AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.relativeProj.twist S ((q * d : ℕ) : ℤ))
      ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).obj
        (AlgebraicGeometry.Scheme.Modules.tensorPow Q d)) = B₁)
    (h₂ : AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.relativeProj.twist S ((q * d' : ℕ) : ℤ))
      ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).obj
        (AlgebraicGeometry.Scheme.Modules.tensorPow Q d')) = B₂)
    (h₃ : AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.relativeProj.twist S ((q * dsum : ℕ) : ℤ))
      ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).obj
        (AlgebraicGeometry.Scheme.Modules.tensorPow Q dsum)) = B₃)
    [IsIso (AlgebraicGeometry.Scheme.relativeProj.twistMul S ((q * d : ℕ) : ℤ) ((q * d' : ℕ) : ℤ))]
    (x : ((AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.relativeProj.twist S (q : ℤ))
      ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).obj Q)).val.obj
        (Opposite.op ⊤) : Type u)) :
    ∃ Φ : AlgebraicGeometry.Scheme.Modules.tensor B₁ B₂ ≅ B₃,
      Φ.hom.app ⊤ (sectionTensor
        (((twistPullbackPow S q Q d ≫ CategoryTheory.eqToHom h₁).val.app (Opposite.op ⊤)).hom
          (AlgebraicGeometry.Scheme.Modules.tensorPowSection x d))
        (((twistPullbackPow S q Q d' ≫ CategoryTheory.eqToHom h₂).val.app (Opposite.op ⊤)).hom
          (AlgebraicGeometry.Scheme.Modules.tensorPowSection x d'))) =
      ((twistPullbackPow S q Q dsum ≫ CategoryTheory.eqToHom h₃).val.app (Opposite.op ⊤)).hom
        (AlgebraicGeometry.Scheme.Modules.tensorPowSection x dsum) := by
  subst hd h₁ h₂ h₃
  simp only [CategoryTheory.eqToHom_refl, Category.comp_id]
  exact twistPullbackPow_mul_exists_iso S q Q d d' x

end AlgebraicGeometry.Scheme.relativeProj

end
