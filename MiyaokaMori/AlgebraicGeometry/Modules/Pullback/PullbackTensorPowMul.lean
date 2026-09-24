import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleSectionRing
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPullbackMonoidal

/-! # The pullback of the tensor-power multiplication is a graded multiplication

`π : Y ⟶ X`, `Q : X.Modules`. The pullback functor `π^*` is strong monoidal (`ModulesPullbackMonoidal.lean`:
`pullbackTensorObjIso`, `pullbackUnitIso`, and the coherence lemmas `pullback_μ_natural_left/right`,
`pullback_μ_associativity`, `pullback_right_unitality`). Everything here is written with the sheafified tensor
`Modules.tensor` on `X` (comparison `tensorIsoTensorObj : Modules.tensor M N ≅ M ⊗ N`) and the monoidal `⊗` on `Y`.

* `pullbackPairMul π M N : π^*M ⊗ π^*N ⟶ π^*(Modules.tensor M N)` (`= tensorIsoTensorObj⁻¹ ≫ pullbackTensorIso⁻¹`,
  `tensorIsoTensorObj_inv_comp_pullbackTensorIso_inv`);
* `pullbackPowMul π Q m n : π^*Q^{⊗m} ⊗ π^*Q^{⊗n} ⟶ π^*Q^{⊗(m+n)}` (`pullbackPairMul` followed by
  `π^*(tensorIsoTensorObj ≫ tensorPowAddIso⁻¹)`), the pullback of the graded multiplication of `⊕ Q^{⊗n}`;
* `pullbackPowMul_unit_right`: `(π^*Q^{⊗m} ◁ pullbackUnitIso⁻¹) ≫ pullbackPowMul m 0 = ρ_`
  (from `pullback_right_unitality`; `tensorPowAddIso Q m 0 = (ρ_)⁻¹ ≪≫ (_ ◁ eqToIso)`, and the `eqToHom` between
  `𝟙_` and `Q^{⊗0} = SheafOfModules.unit` is definitionally the identity);
* `pullbackStep π Q e := pullbackPairMul π Q^{⊗e} Q`, typed `π^*Q^{⊗e} ⊗ π^*Q ⟶ π^*Q^{⊗(e+1)}`;
* `pullbackPowMul_assoc_step`: `(π^*Q^{⊗m} ◁ pullbackStep n) ≫ pullbackPowMul m (n+1) =
  α⁻¹ ≫ (pullbackPowMul m n ▷ π^*Q) ≫ pullbackStep (m+n)` (from `pullback_μ_associativity` and the
  recursion clause of `tensorPowAddIso Q m (n+1)`; the general form `pullbackPairMul_assoc_general` has all objects
  as variables so that no `tensorPow Q (n+1) = Modules.tensor (tensorPow Q n) Q` unfolding is needed in rewriting).

These are the "pullback component" of the block multiplicativity of `twistPullbackPow`
(`Paper/S2WeightedJets/CoordinatePowerNonzeroLocus_SplitTwistMulAdd_TwistPullbackPow.lean`), the other component
being the twisting sheaf `O(n)` with `twistMul`.

Source: Stacks 01CD (pullback commutes with tensor product, compatibly with the monoidal structure).
-/
set_option autoImplicit false
set_option maxHeartbeats 400000
universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry
open scoped CategoryTheory.MonoidalCategory
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules
variable {X Y : AlgebraicGeometry.Scheme.{u}} (π : Y ⟶ X)

/-- `π^*M ⊗ π^*N ⟶ π^*(Modules.tensor M N)`: `pullbackTensorObjIso⁻¹` then `π^*(tensorIsoTensorObj⁻¹)`. -/
def pullbackPairMul (M N : X.Modules) :
    (AlgebraicGeometry.Scheme.Modules.pullback π).obj M ⊗ (AlgebraicGeometry.Scheme.Modules.pullback π).obj N ⟶
      (AlgebraicGeometry.Scheme.Modules.pullback π).obj (AlgebraicGeometry.Scheme.Modules.tensor M N) :=
  (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjIso π M N).inv ≫
    (AlgebraicGeometry.Scheme.Modules.pullback π).map (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj M N).inv

theorem tensorIsoTensorObj_inv_comp_pullbackTensorIso_inv (M N : X.Modules) :
    (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _).inv ≫
        (AlgebraicGeometry.Scheme.Modules.pullbackTensorIso π M N).inv = pullbackPairMul π M N := by
  simp only [AlgebraicGeometry.Scheme.Modules.pullbackTensorIso, Iso.trans_inv, Iso.symm_inv,
    Functor.mapIso_inv, Category.assoc, Iso.inv_hom_id_assoc, pullbackPairMul]

/-- The block multiplication on `π^*Q^{⊗•}`: `pullbackPairMul` followed by `π^*(tensorPowAddIso⁻¹)`. -/
def pullbackPowMul (Q : X.Modules) (m n : ℕ) :
    (AlgebraicGeometry.Scheme.Modules.pullback π).obj (AlgebraicGeometry.Scheme.Modules.tensorPow Q m) ⊗
      (AlgebraicGeometry.Scheme.Modules.pullback π).obj (AlgebraicGeometry.Scheme.Modules.tensorPow Q n) ⟶
      (AlgebraicGeometry.Scheme.Modules.pullback π).obj (AlgebraicGeometry.Scheme.Modules.tensorPow Q (m + n)) :=
  pullbackPairMul π _ _ ≫ (AlgebraicGeometry.Scheme.Modules.pullback π).map
    ((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _).hom ≫
      (AlgebraicGeometry.Scheme.Modules.tensorPowAddIso Q m n).inv)

theorem pullbackPowMul_eq (Q : X.Modules) (m n : ℕ) :
    pullbackPowMul π Q m n =
      (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjIso π _ _).inv ≫
        (AlgebraicGeometry.Scheme.Modules.pullback π).map (AlgebraicGeometry.Scheme.Modules.tensorPowAddIso Q m n).inv := by
  simp only [pullbackPowMul, pullbackPairMul, Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_assoc]

/-- `pullbackPairMul π Q^{⊗e} Q`, typed with codomain `π^*Q^{⊗(e+1)}` (definitionally `π^*(Modules.tensor Q^{⊗e} Q)`);
the step multiplication of the pullback component. -/
def pullbackStep (Q : X.Modules) (e : ℕ) :
    (AlgebraicGeometry.Scheme.Modules.pullback π).obj (AlgebraicGeometry.Scheme.Modules.tensorPow Q e) ⊗
      (AlgebraicGeometry.Scheme.Modules.pullback π).obj Q ⟶
      (AlgebraicGeometry.Scheme.Modules.pullback π).obj (AlgebraicGeometry.Scheme.Modules.tensorPow Q (e + 1)) :=
  pullbackPairMul π (AlgebraicGeometry.Scheme.Modules.tensorPow Q e) Q

/-- Right unit law: `(π^*Q^m ◁ pullbackUnitIso⁻¹) ≫ pullbackPowMul m 0 = ρ_`. -/
theorem pullbackPowMul_unit_right (Q : X.Modules) (m : ℕ) :
    ((AlgebraicGeometry.Scheme.Modules.pullback π).obj (AlgebraicGeometry.Scheme.Modules.tensorPow Q m) ◁
        (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso π).inv) ≫ pullbackPowMul π Q m 0 =
      (ρ_ ((AlgebraicGeometry.Scheme.Modules.pullback π).obj (AlgebraicGeometry.Scheme.Modules.tensorPow Q m))).hom := by
  rw [pullbackPowMul_eq]
  have h1 : (AlgebraicGeometry.Scheme.Modules.tensorPowAddIso Q m 0).inv = (ρ_ (AlgebraicGeometry.Scheme.Modules.tensorPow Q m)).hom := by
    show (_ ≫ _) = _
    rw [Iso.symm_inv]
    change (AlgebraicGeometry.Scheme.Modules.tensorPow Q m ◁ 𝟙 (AlgebraicGeometry.Scheme.Modules.tensorPow Q 0)) ≫ _ = _
    rw [whiskerLeft_id]
    exact Category.id_comp _
  rw [h1]
  exact (pullback_right_unitality π (AlgebraicGeometry.Scheme.Modules.tensorPow Q m)).symm

/-- `pullback_μ_associativity`, solved for `(π^*M ◁ μ) ≫ μ ≫ π^*(α⁻¹)`. -/
theorem pullback_μ_associativity_inv (M N P : X.Modules) :
    ((AlgebraicGeometry.Scheme.Modules.pullback π).obj M ◁
        (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjIso π N P).inv) ≫
      (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjIso π M (N ⊗ P)).inv ≫
      (AlgebraicGeometry.Scheme.Modules.pullback π).map (α_ M N P).inv =
    (α_ _ _ _).inv ≫
      ((AlgebraicGeometry.Scheme.Modules.pullbackTensorObjIso π M N).inv ▷
        (AlgebraicGeometry.Scheme.Modules.pullback π).obj P) ≫
      (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjIso π (M ⊗ N) P).inv := by
  rw [Iso.eq_inv_comp, ← reassoc_of% (pullback_μ_associativity π M N P), ← Functor.map_comp, Iso.hom_inv_id,
    CategoryTheory.Functor.map_id, Category.comp_id]

/-- Associativity step of `pullbackPairMul`, general form (all objects variables, `ψ : M ⊗ N ⟶ R`):
`(π^*M ◁ pairMul N P) ≫ μ⁻¹ ≫ π^*((M ◁ τ) ≫ α⁻¹ ≫ (ψ ▷ P) ≫ τ⁻¹) = α⁻¹ ≫ ((μ⁻¹ ≫ π^*ψ) ▷ π^*P) ≫ pairMul R P`. -/
theorem pullbackPairMul_assoc_general (M N P R : X.Modules) (ψ : M ⊗ N ⟶ R) :
    ((AlgebraicGeometry.Scheme.Modules.pullback π).obj M ◁ pullbackPairMul π N P) ≫
      (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjIso π M (AlgebraicGeometry.Scheme.Modules.tensor N P)).inv ≫
      (AlgebraicGeometry.Scheme.Modules.pullback π).map
        ((M ◁ (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj N P).hom) ≫ (α_ M N P).inv ≫ (ψ ▷ P) ≫
          (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj R P).inv) =
    (α_ _ _ _).inv ≫
      (((AlgebraicGeometry.Scheme.Modules.pullbackTensorObjIso π M N).inv ≫
        (AlgebraicGeometry.Scheme.Modules.pullback π).map ψ) ▷ (AlgebraicGeometry.Scheme.Modules.pullback π).obj P) ≫
      pullbackPairMul π R P := by
  unfold pullbackPairMul
  simp only [Functor.map_comp, whiskerLeft_comp, Category.assoc, comp_whiskerRight]
  rw [reassoc_of% (pullback_μ_natural_right π M (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj N P).inv),
    ← Functor.map_comp_assoc, ← whiskerLeft_comp, Iso.inv_hom_id, whiskerLeft_id, CategoryTheory.Functor.map_id,
    Category.id_comp, reassoc_of% (pullback_μ_associativity_inv π M N P),
    ← reassoc_of% (pullback_μ_natural_left π ψ P)]

/-- Associativity step: `(π^*Q^m ◁ pullbackStep n) ≫ pullbackPowMul m (n+1) =
α⁻¹ ≫ (pullbackPowMul m n ▷ π^*Q) ≫ pullbackStep (m+n)`. -/
theorem pullbackPowMul_assoc_step (Q : X.Modules) (m n : ℕ) :
    ((AlgebraicGeometry.Scheme.Modules.pullback π).obj (AlgebraicGeometry.Scheme.Modules.tensorPow Q m) ◁
        pullbackStep π Q n) ≫ pullbackPowMul π Q m (n + 1) =
      (α_ _ _ _).inv ≫ (pullbackPowMul π Q m n ▷ (AlgebraicGeometry.Scheme.Modules.pullback π).obj Q) ≫
        pullbackStep π Q (m + n) := by
  have h1 : (AlgebraicGeometry.Scheme.Modules.tensorPowAddIso Q m (n + 1)).inv =
      (AlgebraicGeometry.Scheme.Modules.tensorPow Q m ◁ (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _).hom) ≫
        (α_ _ _ _).inv ≫ ((AlgebraicGeometry.Scheme.Modules.tensorPowAddIso Q m n).inv ▷ Q) ≫
        (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _).inv := by
    show ((_ ≫ _) ≫ _) ≫ _ = _
    simp only [Category.assoc]
    rfl
  unfold pullbackStep
  rw [pullbackPowMul_eq, pullbackPowMul_eq, h1]
  exact pullbackPairMul_assoc_general π _ _ Q _ (AlgebraicGeometry.Scheme.Modules.tensorPowAddIso Q m n).inv

end AlgebraicGeometry.Scheme.Modules
end
