import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Blowup.BlowupReesLiftMaps
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.InvertibleIdealPowToUnitMono

/-! # The `map_mul` field of the Rees lift data

The `map_mul` field of the Rees lift data: graded maps `Ψ_n : f^*(Iⁿ) ⟶ J^{⊗n}` with `Ψ_n ≫ μ_n = θ_n`
(`J := I.comap f` invertible) are automatically multiplicative, i.e. compatible with `Iᵐ ⊗ Iⁿ → I^{m+n}` and
`J^{⊗m} ⊗ J^{⊗n} ≅ J^{⊗(m+n)}`.

Source: Stacks 01O4 (multiplicativity of a graded map into `⊕ L^{⊗n}`); Stacks 0806.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open scoped CategoryTheory.MonoidalCategory

/-! ## Abstract monoidal lemma

Stated for an arbitrary oplax monoidal functor `F : C ⥤ D` and applied with `exact`, so that no rewriting has to
see through `monoidalPow` / `monoidalPowCat` / `𝟙_ Y.Modules = SheafOfModules.unit`. -/

namespace AlgebraicGeometry.Scheme.ReesLiftMapMulAux

open CategoryTheory.MonoidalCategory CategoryTheory.Functor.OplaxMonoidal

variable {C : Type u'} [Category.{v'} C] [MonoidalCategory C]
variable {D : Type w} [Category.{v} D] [MonoidalCategory D]
variable (F : C ⥤ D) [F.OplaxMonoidal]

/-- Unit compatibility of an oplax monoidal functor in the form
`F(λ_ 𝟙_) ≫ η = δ ≫ (η ⊗ₘ η) ≫ (λ_ 𝟙_).hom` (`left_unitality_hom` at `X = 𝟙_ C`, then `tensorHom_def` and the
naturality of `λ_`). -/
theorem map_leftUnitor_unit_comp_η :
    F.map (λ_ (𝟙_ C)).hom ≫ η F = δ F (𝟙_ C) (𝟙_ C) ≫ (η F ⊗ₘ η F) ≫ (λ_ (𝟙_ D)).hom := by
  rw [← left_unitality_hom, tensorHom_def]
  simp only [Category.assoc]
  rw [leftUnitor_naturality]

/-- **Multiplicativity after cancelling a mono.** Let `a, b, r` be "inclusions" into `𝟙_ C`, `mult : P ⊗ Q ⟶ R`
multiplicative for them (`mult ≫ r = (a ⊗ₘ b) ≫ λ_`), let `u, v, w` be maps into `𝟙_ D` with `w` a monomorphism and
`c : A ⊗ B ⟶ E` multiplicative for them (`c ≫ w = (u ⊗ₘ v) ≫ λ_`), and let `x, y, z` be lifts
(`x ≫ u = F a ≫ η`, etc.). Then `F(mult) ≫ z = δ ≫ (x ⊗ₘ y) ≫ c`. Proof: compose with `w`; both sides become
`δ ≫ ((F a ≫ η) ⊗ₘ (F b ≫ η)) ≫ λ_` by `map_leftUnitor_unit_comp_η` and the naturality of `δ`
(`projBundle.MonoidalPowAux.map_tensorHom_δ_comp`). -/
theorem map_mul_of_cancel_mono {P Q R : C} {A B E : D}
    (a : P ⟶ 𝟙_ C) (b : Q ⟶ 𝟙_ C) (r : R ⟶ 𝟙_ C) (mult : P ⊗ Q ⟶ R)
    (hmult : mult ≫ r = (a ⊗ₘ b) ≫ (λ_ (𝟙_ C)).hom)
    (x : F.obj P ⟶ A) (y : F.obj Q ⟶ B) (z : F.obj R ⟶ E)
    (u : A ⟶ 𝟙_ D) (v : B ⟶ 𝟙_ D) (w : E ⟶ 𝟙_ D) [Mono w]
    (c : A ⊗ B ⟶ E) (hc : c ≫ w = (u ⊗ₘ v) ≫ (λ_ (𝟙_ D)).hom)
    (hx : x ≫ u = F.map a ≫ η F) (hy : y ≫ v = F.map b ≫ η F) (hz : z ≫ w = F.map r ≫ η F) :
    F.map mult ≫ z = δ F P Q ≫ (x ⊗ₘ y) ≫ c := by
  rw [← cancel_mono w, Category.assoc]
  calc F.map mult ≫ z ≫ w = F.map mult ≫ F.map r ≫ η F := by rw [hz]
    _ = F.map (a ⊗ₘ b) ≫ F.map (λ_ (𝟙_ C)).hom ≫ η F := by
        rw [← Category.assoc, ← F.map_comp, hmult, F.map_comp, Category.assoc]
    _ = F.map (a ⊗ₘ b) ≫ δ F (𝟙_ C) (𝟙_ C) ≫ (η F ⊗ₘ η F) ≫ (λ_ (𝟙_ D)).hom := by
        rw [map_leftUnitor_unit_comp_η]
    _ = δ F P Q ≫ ((F.map a ≫ η F) ⊗ₘ (F.map b ≫ η F)) ≫ (λ_ (𝟙_ D)).hom :=
        AlgebraicGeometry.Scheme.projBundle.MonoidalPowAux.map_tensorHom_δ_comp F a b (η F) (η F) _
    _ = δ F P Q ≫ ((x ≫ u) ⊗ₘ (y ≫ v)) ≫ (λ_ (𝟙_ D)).hom := by rw [hx, hy]
    _ = δ F P Q ≫ (x ⊗ₘ y) ≫ c ≫ w := by rw [← tensorHom_comp_tensorHom_assoc, hc]
    _ = (δ F P Q ≫ (x ⊗ₘ y) ≫ c) ≫ w := by simp only [Category.assoc]

end AlgebraicGeometry.Scheme.ReesLiftMapMulAux

/-! ## The two bridging lemmas (where `𝟙_ Y.Modules` and `SheafOfModules.unit` meet) -/

set_option backward.isDefEq.respectTransparency.types false in
/-- `pb ≫ ε_Y⁻¹ = f^*(ε_X⁻¹) ≫ η`, with `pb = (pullbackUnitIso f).hom`, `ε = monoidalUnitIso`, `η` the counit of
the oplax monoidal structure of `f^*` (`= pb` by `pullback_η`). Both `ε`'s are `eqToHom`s of the definitional
equality `𝟙_ = SheafOfModules.unit`, so after `eqToHom_map` both sides are `pb` (`with_unfolding_all rfl`; the
statement mixes `𝟙_` and `unit`, hence the `Eq.trans` chain instead of `rw`, cf. `blowup_reesLiftMaps_map_one`). -/
theorem AlgebraicGeometry.Scheme.Modules.pullbackUnitIso_hom_monoidalUnitIso_inv
    {X Y : AlgebraicGeometry.Scheme.{u}} (f : Y ⟶ X) :
    (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso f).hom ≫
        (AlgebraicGeometry.Scheme.IdealSheafData.monoidalUnitIso Y).inv =
      (AlgebraicGeometry.Scheme.Modules.pullback f).map
          (AlgebraicGeometry.Scheme.IdealSheafData.monoidalUnitIso X).inv ≫
        CategoryTheory.Functor.OplaxMonoidal.η (AlgebraicGeometry.Scheme.Modules.pullback f)
          (self := AlgebraicGeometry.Scheme.Modules.pullbackOplaxMonoidal f) := by
  refine Eq.trans ?_ (congrArg (fun t => (AlgebraicGeometry.Scheme.Modules.pullback f).map
    (AlgebraicGeometry.Scheme.IdealSheafData.monoidalUnitIso X).inv ≫ t)
    (AlgebraicGeometry.Scheme.Modules.pullback_η f).symm)
  show (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso f).hom ≫
      (AlgebraicGeometry.Scheme.IdealSheafData.monoidalUnitIso Y).inv =
    (AlgebraicGeometry.Scheme.Modules.pullback f).map
      (AlgebraicGeometry.Scheme.IdealSheafData.monoidalUnitIso X).inv ≫
      (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso f).hom
  simp only [AlgebraicGeometry.Scheme.IdealSheafData.monoidalUnitIso, eqToIso.inv, eqToHom_map]
  with_unfolding_all rfl

set_option backward.isDefEq.respectTransparency.types false in
/-- `μ_k ≫ ε_Y⁻¹ = monoidalPowMap ι k ≫ unitPowCollapse Y k` (definition of `monoidalPowToUnit`, `Iso.hom_inv_id`). -/
theorem AlgebraicGeometry.Scheme.IdealSheafData.monoidalPowToUnit_comp_monoidalUnitIso_inv
    {Y : AlgebraicGeometry.Scheme.{u}} (J : Y.IdealSheafData) (k : ℕ) :
    J.monoidalPowToUnit k ≫ (AlgebraicGeometry.Scheme.IdealSheafData.monoidalUnitIso Y).inv =
      AlgebraicGeometry.Scheme.Modules.monoidalPowMap (AlgebraicGeometry.Scheme.EffCartier.idealIncl J) k ≫
        AlgebraicGeometry.Scheme.Modules.unitPowCollapse Y k := by
  unfold AlgebraicGeometry.Scheme.IdealSheafData.monoidalPowToUnit
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency.types false in
/-- `cat_J(m,n) ≫ (μ_{m+n} ≫ ε_Y⁻¹) = ((μ_m ≫ ε_Y⁻¹) ⊗ₘ (μ_n ≫ ε_Y⁻¹)) ≫ (λ_ 𝟙_).hom`: by
`monoidalPowToUnit_comp_monoidalUnitIso_inv`, `projBundle.monoidalPowCat_monoidalPowMap` (for `ι = idealIncl J`)
and `projBundle.unitPowCollapse_monoidalPowCat`. -/
theorem AlgebraicGeometry.Scheme.IdealSheafData.monoidalPowCat_monoidalPowToUnit
    {Y : AlgebraicGeometry.Scheme.{u}} (J : Y.IdealSheafData) (m n : ℕ) :
    (AlgebraicGeometry.Scheme.Modules.monoidalPowCat J.toModules m n).hom ≫
        (J.monoidalPowToUnit (m + n) ≫ (AlgebraicGeometry.Scheme.IdealSheafData.monoidalUnitIso Y).inv) =
      ((J.monoidalPowToUnit m ≫ (AlgebraicGeometry.Scheme.IdealSheafData.monoidalUnitIso Y).inv) ⊗ₘ
          (J.monoidalPowToUnit n ≫ (AlgebraicGeometry.Scheme.IdealSheafData.monoidalUnitIso Y).inv)) ≫
        (λ_ (𝟙_ Y.Modules)).hom := by
  rw [J.monoidalPowToUnit_comp_monoidalUnitIso_inv, J.monoidalPowToUnit_comp_monoidalUnitIso_inv,
    J.monoidalPowToUnit_comp_monoidalUnitIso_inv]
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun t => t ≫ AlgebraicGeometry.Scheme.Modules.unitPowCollapse Y (m + n))
    (AlgebraicGeometry.Scheme.projBundle.monoidalPowCat_monoidalPowMap
      (AlgebraicGeometry.Scheme.EffCartier.idealIncl J) m n).symm).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun t => (AlgebraicGeometry.Scheme.Modules.monoidalPowMap
      (AlgebraicGeometry.Scheme.EffCartier.idealIncl J) m ⊗ₘ
    AlgebraicGeometry.Scheme.Modules.monoidalPowMap (AlgebraicGeometry.Scheme.EffCartier.idealIncl J) n) ≫ t)
    (AlgebraicGeometry.Scheme.projBundle.unitPowCollapse_monoidalPowCat Y m n)).trans ?_
  exact CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom_assoc (C := Y.Modules)
    (AlgebraicGeometry.Scheme.Modules.monoidalPowMap (AlgebraicGeometry.Scheme.EffCartier.idealIncl J) m)
    (AlgebraicGeometry.Scheme.Modules.monoidalPowMap (AlgebraicGeometry.Scheme.EffCartier.idealIncl J) n)
    (AlgebraicGeometry.Scheme.Modules.unitPowCollapse Y m) (AlgebraicGeometry.Scheme.Modules.unitPowCollapse Y n)
    (λ_ (𝟙_ Y.Modules)).hom

set_option backward.isDefEq.respectTransparency.types false in
/-- `powMul m n ≫ (powι (m+n) ≫ ε_X⁻¹) = ((powι m ≫ ε_X⁻¹) ⊗ₘ (powι n ≫ ε_X⁻¹)) ≫ (λ_ 𝟙_).hom`: the Rees
multiplication followed by the inclusion is `powMulToUnit = (powι ⊗ₘ powι) ≫ (ε_X⁻¹ ⊗ₘ ε_X⁻¹) ≫ (λ_ 𝟙_).hom ≫ ε_X`
(`powMul_powι`), then `Iso.hom_inv_id` and `tensorHom_comp_tensorHom`. -/
theorem AlgebraicGeometry.Scheme.IdealSheafData.powMul_comp_powι_monoidalUnitIso_inv
    {X : AlgebraicGeometry.Scheme.{u}} (I : X.IdealSheafData) (m n : ℕ) :
    I.powMul m n ≫ (I.powι (m + n) ≫ (AlgebraicGeometry.Scheme.IdealSheafData.monoidalUnitIso X).inv) =
      ((I.powι m ≫ (AlgebraicGeometry.Scheme.IdealSheafData.monoidalUnitIso X).inv) ⊗ₘ
        (I.powι n ≫ (AlgebraicGeometry.Scheme.IdealSheafData.monoidalUnitIso X).inv)) ≫
        (λ_ (𝟙_ X.Modules)).hom := by
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun t => t ≫ (AlgebraicGeometry.Scheme.IdealSheafData.monoidalUnitIso X).inv)
    (I.powMul_powι m n)).trans ?_
  unfold AlgebraicGeometry.Scheme.IdealSheafData.powMulToUnit
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  exact CategoryTheory.MonoidalCategory.tensorHom_comp_tensorHom_assoc _ _ _ _ _

set_option backward.isDefEq.respectTransparency.types false in
/-- A lift `Ψ_k : f^*(Iᵏ) ⟶ J^{⊗k}` with `Ψ_k ≫ μ_k = θ_k` satisfies `Ψ_k ≫ (μ_k ≫ ε_Y⁻¹) = f^*(powι k ≫ ε_X⁻¹) ≫ η`
(unfold `θ_k = f^*(powι k) ≫ pb`, then `pullbackUnitIso_hom_monoidalUnitIso_inv`). -/
theorem AlgebraicGeometry.Scheme.IdealSheafData.reesLift_comp_monoidalPowToUnit_monoidalUnitIso_inv
    {X : AlgebraicGeometry.Scheme.{u}} (I : X.IdealSheafData) {Y : AlgebraicGeometry.Scheme.{u}} (f : Y ⟶ X)
    {k : ℕ} (Ψk : (AlgebraicGeometry.Scheme.Modules.pullback f).obj (I.reesAlgebra.part k) ⟶
        AlgebraicGeometry.Scheme.Modules.monoidalPow (I.comap f).toModules k)
    (hΨk : Ψk ≫ (I.comap f).monoidalPowToUnit k = I.reesPullbackToUnit f k) :
    Ψk ≫ ((I.comap f).monoidalPowToUnit k ≫ (AlgebraicGeometry.Scheme.IdealSheafData.monoidalUnitIso Y).inv) =
      (AlgebraicGeometry.Scheme.Modules.pullback f).map
          (I.powι k ≫ (AlgebraicGeometry.Scheme.IdealSheafData.monoidalUnitIso X).inv) ≫
        CategoryTheory.Functor.OplaxMonoidal.η (AlgebraicGeometry.Scheme.Modules.pullback f)
          (self := AlgebraicGeometry.Scheme.Modules.pullbackOplaxMonoidal f) := by
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun t => t ≫ (AlgebraicGeometry.Scheme.IdealSheafData.monoidalUnitIso Y).inv) hΨk).trans ?_
  show ((AlgebraicGeometry.Scheme.Modules.pullback f).map (I.powι k) ≫
      (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso f).hom) ≫
      (AlgebraicGeometry.Scheme.IdealSheafData.monoidalUnitIso Y).inv = _
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun t => (AlgebraicGeometry.Scheme.Modules.pullback f).map (I.powι k) ≫ t)
    (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso_hom_monoidalUnitIso_inv f)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  exact congrArg (fun t => t ≫ CategoryTheory.Functor.OplaxMonoidal.η (AlgebraicGeometry.Scheme.Modules.pullback f)
    (self := AlgebraicGeometry.Scheme.Modules.pullbackOplaxMonoidal f)) (Functor.map_comp _ _ _).symm

/-! ## Assembly -/

/-- **Multiplicativity of the Rees lift data** (the `map_mul` field of `relativeProj.LiftData`):
`f^*(mul m n) ≫ Ψ_{m+n} = δ ≫ (Ψ_m ⊗ Ψ_n) ≫ cat_J(m,n)`, where `δ = pullbackTensorObjHom f` and
`cat_J(m,n) = (monoidalPowCat J.toModules m n).hom : J^{⊗m} ⊗ J^{⊗n} ≅ J^{⊗(m+n)}`.

Proof. Write `θ_k := I.reesPullbackToUnit f k`, `μ_k := J.monoidalPowToUnit k`,
`ε_X := monoidalUnitIso X`, `ε_Y := monoidalUnitIso Y`, `pb := (pullbackUnitIso f).hom`, `ι := idealIncl J`.

0. **Cancel the mono.** `μ_{m+n}` is a monomorphism (`monoidalPowToUnit_mono`, needs `hf`), hence so is `w := μ_{m+n} ≫ ε_Y⁻¹`; it suffices to prove the identity after composing with `w`.
   This and the comparison of step 4 are the abstract lemma `ReesLiftMapMulAux.map_mul_of_cancel_mono`, applied to
   `F = f^*` (oplax structure `pullbackOplaxMonoidal f`), `a_k := powι k ≫ ε_X⁻¹`, `mult := powMul m n`,
   `x, y, z := Ψ_m, Ψ_n, Ψ_{m+n}`, `u_k := μ_k ≫ ε_Y⁻¹`, `c := cat_J(m,n)`.
1. **Left side.** `powMul m n ≫ a_{m+n} = (a_m ⊗ₘ a_n) ≫ (λ_ 𝟙_).hom` (`powMul_comp_powι_monoidalUnitIso_inv`:
   `powMul_powι`, definition of `powMulToUnit = (powι m ⊗ₘ powι n) ≫ (ε_X⁻¹ ⊗ₘ ε_X⁻¹) ≫ (λ_ 𝟙_).hom ≫ ε_X`,
   `tensorHom_comp_tensorHom`).
2. **Right side, monoidal powers.** `cat_J(m,n) ≫ u_{m+n} = (u_m ⊗ₘ u_n) ≫ (λ_ 𝟙_).hom`
   (`monoidalPowCat_monoidalPowToUnit`: `projBundle.monoidalPowCat_monoidalPowMap`, `projBundle.unitPowCollapse_monoidalPowCat`).
3. **Lifts.** `Ψ_k ≫ u_k = f^*(a_k) ≫ η` (`reesLift_comp_monoidalPowToUnit_monoidalUnitIso_inv`): by `hΨ k`,
   `θ_k = f^*(powι k) ≫ pb` and the `eqToHom` identity `pb ≫ ε_Y⁻¹ = f^*(ε_X⁻¹) ≫ η`
   (`pullbackUnitIso_hom_monoidalUnitIso_inv`, using `pullback_η`).
4. **Compare** (inside `map_mul_of_cancel_mono`): both sides composed with `w` become
   `δ ≫ ((f^*(a_m) ≫ η) ⊗ₘ (f^*(a_n) ≫ η)) ≫ (λ_ 𝟙_).hom`, by the naturality of `δ` (`map_tensorHom_δ_comp`) and
   the unit compatibility `f^*((λ_ 𝟙_).hom) ≫ η = δ ≫ (η ⊗ₘ η) ≫ (λ_ 𝟙_).hom` (`left_unitality_hom`). ∎

Edge cases: `m = 0` or `n = 0` are covered by the same computation (`cat_J(m,0) = ρ_`); `Y = ∅` trivial. -/
theorem AlgebraicGeometry.Scheme.blowup_reesLiftMaps_map_mul {X : AlgebraicGeometry.Scheme.{u}}
    (I : X.IdealSheafData) {Y : AlgebraicGeometry.Scheme.{u}} (f : Y ⟶ X)
    (hf : MiyaokaMori.Statement.IsInvertibleIdeal (I.comap f))
    (Ψ : ∀ n : ℕ, (AlgebraicGeometry.Scheme.Modules.pullback f).obj (I.reesAlgebra.part n) ⟶
        AlgebraicGeometry.Scheme.Modules.monoidalPow (I.comap f).toModules n)
    (hΨ : ∀ n : ℕ, Ψ n ≫ (I.comap f).monoidalPowToUnit n = I.reesPullbackToUnit f n) (m n : ℕ) :
    (AlgebraicGeometry.Scheme.Modules.pullback f).map (I.reesAlgebra.mul m n) ≫ Ψ (m + n) =
      AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom f (I.reesAlgebra.part m) (I.reesAlgebra.part n) ≫
        CategoryTheory.MonoidalCategoryStruct.tensorHom (C := Y.Modules) (Ψ m) (Ψ n) ≫
        (AlgebraicGeometry.Scheme.Modules.monoidalPowCat (I.comap f).toModules m n).hom := by
  have hμ : Mono ((I.comap f).monoidalPowToUnit (m + n)) := (I.comap f).monoidalPowToUnit_mono hf (m + n)
  have hε' : IsIso (AlgebraicGeometry.Scheme.IdealSheafData.monoidalUnitIso Y).inv := Iso.isIso_inv _
  have hε : Mono (AlgebraicGeometry.Scheme.IdealSheafData.monoidalUnitIso Y).inv := IsIso.mono_of_iso _
  have hw : Mono ((I.comap f).monoidalPowToUnit (m + n) ≫
      (AlgebraicGeometry.Scheme.IdealSheafData.monoidalUnitIso Y).inv) := mono_comp _ _
  exact AlgebraicGeometry.Scheme.ReesLiftMapMulAux.map_mul_of_cancel_mono
    (AlgebraicGeometry.Scheme.Modules.pullback f) _ _ _ (I.powMul m n) (I.powMul_comp_powι_monoidalUnitIso_inv m n)
    (Ψ m) (Ψ n) (Ψ (m + n)) _ _ _ _ ((I.comap f).monoidalPowCat_monoidalPowToUnit m n)
    (I.reesLift_comp_monoidalPowToUnit_monoidalUnitIso_inv f (Ψ m) (hΨ m))
    (I.reesLift_comp_monoidalPowToUnit_monoidalUnitIso_inv f (Ψ n) (hΨ n))
    (I.reesLift_comp_monoidalPowToUnit_monoidalUnitIso_inv f (Ψ (m + n)) (hΨ (m + n)))

end
