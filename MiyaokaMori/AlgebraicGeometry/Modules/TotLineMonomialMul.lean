import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesProjectionFormulaHom
import MiyaokaMori.CategoryTheory.ProjectionFormulaHomMul
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.AlgebraMapToPushforwardMorphismLevel
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.JetNeighborhoodToTotalSpaceLemmas
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotLineCoefficientMonomial

/-! # Multiplicativity of the monomial maps on the total space of a line bundle

**Multiplicativity of the monomial maps on `Tot(L)`**, the morphism-level content of the product rule
`(c·ξ^a)·(c'·ξ^b) = (c ⊗ c')·ξ^{a+b}` (`xiSectionMul_xiMonomial_xiMonomial`).
Notation: `p : Tot(L) → X`, `S := Sym(L^∨)`, `σ := relativeSpec.structureHom S.total`, `Θ_q := tensorPowerToSymPart L q`,
`ι_q := S.totalIncl q`, `u_q := Θ_q ≫ ι_q ≫ σ : T_q ⟶ p_*O_Tot` (`T_q = (L^∨)^{⊗q}`), `pw_q := monoidalPowIsoTensorPower`.

1. `totalSpace.monomialUnit_mul`: `(u_a ⊗ u_b) ≫ pushforwardUnitMul p = W ≫ u_{a+b}` with
   `W := (pw_a⁻¹ ⊗ pw_b⁻¹) ≫ monoidalPowCat.hom ≫ pw_{a+b}` — the graded multiplication of `Sym(L^∨)` is the concatenation
   of tensor powers: `σ` is an algebra map (`mul_comp_eq_of_isAlgebraMap_mul`, Stacks 01LQ), `(ι_a ⊗ ι_b) ≫ totalMul = S.mul ≫ ι_{a+b}`
   (`tensor_ι_comp_totalMul`), and `(Θ_a ⊗ Θ_b) ≫ S.mul a b = W ≫ Θ_{a+b}` (`mul_comp_symPartToMonoidalPow` +
   `tensorPowerToSymPart_symPartToTensorPower`).
2. `Modules.projectionFormulaHom_mul_general`: the instance of the abstract `Adjunction.projFormulaHom_mul_general`
   for `f^* ⊣ f_*`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- `Θ'_q ≫ Θ_q = 𝟙` (`symPartToTensorPower ≫ tensorPowerToSymPart`); same proof as
`symPartToTensorPower_tensorPowerToSymPart` in `TotSectionsPolynomial` (which is downstream of this file). -/
theorem totalSpace.symPartToTensorPower_comp_tensorPowerToSymPart (L : X.Modules) [L.IsLineBundle] (q : ℕ) :
    totalSpace.symPartToTensorPower L q ≫ totalSpace.tensorPowerToSymPart L q = 𝟙 _ := by
  have hq : (Modules.dual L).IsQuasicoherent := inferInstance
  unfold totalSpace.symPartToTensorPower totalSpace.tensorPowerToSymPart Modules.symPartToMonoidalPow
  rw [Category.assoc, Iso.hom_inv_id_assoc]
  generalize_proofs _ _ pf3 pf4 pf5 pf6
  have hS : Modules.symGradedAlgebra (Modules.dual L) = Modules.symGradedAlgebraOfQC (Modules.dual L) hq := by
    delta Modules.symGradedAlgebra
    exact dif_pos hq
  change (pf4 pf3).mpr (@CategoryTheory.inv _ _ _ _ (Modules.symPowπ (Modules.dual L) q) (pf5 pf3)) ≫
    (pf6 pf3).mpr (Modules.symPowπ (Modules.dual L) q) = 𝟙 _
  generalize Modules.symGradedAlgebra (Modules.dual L) = S at hS pf4 pf6 ⊢
  subst hS
  exact CategoryTheory.IsIso.inv_hom_id (Modules.symPowπ (Modules.dual L) q)

/-- `Θ_q ≫ symPartToMonoidalPow q = pw_q⁻¹` (from `Θ_q ≫ Θ'_q = 𝟙`). -/
theorem totalSpace.tensorPowerToSymPart_comp_symPartToMonoidalPow (L : X.Modules) [L.IsLineBundle] (q : ℕ) :
    totalSpace.tensorPowerToSymPart L q ≫ Modules.symPartToMonoidalPow (Modules.dual L) q =
      (Modules.monoidalPowIsoTensorPower (Modules.dual L) q).inv := by
  rw [← Iso.comp_hom_eq_id, Category.assoc]
  exact totalSpace.tensorPowerToSymPart_symPartToTensorPower L q

/-- `(Θ_a ⊗ Θ_b) ≫ S.mul a b = ((pw_a⁻¹ ⊗ pw_b⁻¹) ≫ monoidalPowCat.hom ≫ pw_{a+b}) ≫ Θ_{a+b}`. -/
theorem totalSpace.tensorHom_tensorPowerToSymPart_comp_symMul (L : X.Modules) [L.IsLineBundle] (a b : ℕ) :
    (totalSpace.tensorPowerToSymPart L a ⊗ₘ totalSpace.tensorPowerToSymPart L b) ≫
        (Modules.symGradedAlgebra (Modules.dual L)).mul a b =
      (((Modules.monoidalPowIsoTensorPower (Modules.dual L) a).inv ⊗ₘ
          (Modules.monoidalPowIsoTensorPower (Modules.dual L) b).inv) ≫
        (Modules.monoidalPowCat (Modules.dual L) a b).hom ≫
        (Modules.monoidalPowIsoTensorPower (Modules.dual L) (a + b)).hom) ≫
      totalSpace.tensorPowerToSymPart L (a + b) := by
  have h1 : (totalSpace.tensorPowerToSymPart L a ⊗ₘ totalSpace.tensorPowerToSymPart L b) ≫
      (Modules.symGradedAlgebra (Modules.dual L)).mul a b ≫ totalSpace.symPartToTensorPower L (a + b) =
      ((Modules.monoidalPowIsoTensorPower (Modules.dual L) a).inv ⊗ₘ
          (Modules.monoidalPowIsoTensorPower (Modules.dual L) b).inv) ≫
        (Modules.monoidalPowCat (Modules.dual L) a b).hom ≫
        (Modules.monoidalPowIsoTensorPower (Modules.dual L) (a + b)).hom := by
    unfold totalSpace.symPartToTensorPower
    rw [reassoc_of% (Modules.mul_comp_symPartToMonoidalPow (Modules.dual L) a b), ← Category.assoc,
      tensorHom_comp_tensorHom, totalSpace.tensorPowerToSymPart_comp_symPartToMonoidalPow,
      totalSpace.tensorPowerToSymPart_comp_symPartToMonoidalPow]
  calc (totalSpace.tensorPowerToSymPart L a ⊗ₘ totalSpace.tensorPowerToSymPart L b) ≫
        (Modules.symGradedAlgebra (Modules.dual L)).mul a b
      = ((totalSpace.tensorPowerToSymPart L a ⊗ₘ totalSpace.tensorPowerToSymPart L b) ≫
          (Modules.symGradedAlgebra (Modules.dual L)).mul a b ≫ totalSpace.symPartToTensorPower L (a + b)) ≫
          totalSpace.tensorPowerToSymPart L (a + b) := by
        rw [Category.assoc, Category.assoc, totalSpace.symPartToTensorPower_comp_tensorPowerToSymPart,
          Category.comp_id]
    _ = _ := by rw [h1]

/-- Variable-level bridge for `monomialUnit_mul`: `σ` multiplicative, `ι` multiplicative, `Θ` multiplicative ⇒
`((Θa ≫ ιa ≫ σ) ⊗ (Θb ≫ ιb ≫ σ)) ≫ m = W ≫ Θab ≫ ιab ≫ σ`. (Stated with variables so that `rw` is not blocked by
the `ringCatSheaf` instance-transparency mismatch.) -/
theorem Modules.comp_mul_bridge {𝒞 : Type*} [Category 𝒞] [MonoidalCategory 𝒞]
    {Ta Tb Tab Sa Sb Sab Cc P : 𝒞} (Θa : Ta ⟶ Sa) (Θb : Tb ⟶ Sb) (Θab : Tab ⟶ Sab) (ιa : Sa ⟶ Cc) (ιb : Sb ⟶ Cc)
    (ιab : Sab ⟶ Cc) (σ : Cc ⟶ P) (mulC : Cc ⊗ Cc ⟶ Cc) (mulS : Sa ⊗ Sb ⟶ Sab) (m : P ⊗ P ⟶ P) (W : Ta ⊗ Tb ⟶ Tab)
    (hσ : mulC ≫ σ = (σ ⊗ₘ σ) ≫ m) (hι : (ιa ⊗ₘ ιb) ≫ mulC = mulS ≫ ιab) (hΘ : (Θa ⊗ₘ Θb) ≫ mulS = W ≫ Θab) :
    ((Θa ≫ ιa ≫ σ) ⊗ₘ (Θb ≫ ιb ≫ σ)) ≫ m = W ≫ Θab ≫ ιab ≫ σ := by
  rw [← tensorHom_comp_tensorHom, ← tensorHom_comp_tensorHom, Category.assoc, Category.assoc, ← hσ,
    reassoc_of% hι, reassoc_of% hΘ]

/-- **The monomial unit maps are multiplicative**: `(u_a ⊗ u_b) ≫ pushforwardUnitMul p = W ≫ u_{a+b}`. -/
theorem totalSpace.monomialUnit_mul (L : X.Modules) [L.IsLineBundle] (a b : ℕ) :
    ((totalSpace.tensorPowerToSymPart L a ≫ (Modules.symGradedAlgebra (Modules.dual L)).totalIncl a ≫
        relativeSpec.structureHom (Modules.symGradedAlgebra (Modules.dual L)).total) ⊗ₘ
      (totalSpace.tensorPowerToSymPart L b ≫ (Modules.symGradedAlgebra (Modules.dual L)).totalIncl b ≫
        relativeSpec.structureHom (Modules.symGradedAlgebra (Modules.dual L)).total)) ≫
      Modules.pushforwardUnitMul (totalSpace L).hom =
    (((Modules.monoidalPowIsoTensorPower (Modules.dual L) a).inv ⊗ₘ
        (Modules.monoidalPowIsoTensorPower (Modules.dual L) b).inv) ≫
      (Modules.monoidalPowCat (Modules.dual L) a b).hom ≫
      (Modules.monoidalPowIsoTensorPower (Modules.dual L) (a + b)).hom) ≫
      (totalSpace.tensorPowerToSymPart L (a + b) ≫ (Modules.symGradedAlgebra (Modules.dual L)).totalIncl (a + b) ≫
        relativeSpec.structureHom (Modules.symGradedAlgebra (Modules.dual L)).total) :=
  Modules.comp_mul_bridge _ _ _ _ _ _ _ _ _ _ _
    (QCAlgebra.mul_comp_eq_of_isAlgebraMap_mul _ _ _
      (relativeSpecHomEquiv (Modules.symGradedAlgebra (Modules.dual L)).total
        (relativeSpec (Modules.symGradedAlgebra (Modules.dual L)).total) (CategoryTheory.CategoryStruct.id _)).2.1)
    (GradedQCAlgebra.tensor_ι_comp_totalMul _ a b)
    (totalSpace.tensorHom_tensorPowerToSymPart_comp_symMul L a b)

/-- The instance of `Adjunction.projFormulaHom_mul_general` for `f^* ⊣ f_*` on sheaves of modules
(`G` lax monoidal through `pushforwardLaxMonoidal`, `hμ := homEquiv_pullbackTensorObjHom`). -/
theorem Modules.projectionFormulaHom_mul_general {T Y : AlgebraicGeometry.Scheme.{u}} (f : T ⟶ Y)
    {M M' N T₁ T₂ T₃ : Y.Modules} (τ : N ≅ M ⊗ M')
    (u : T₁ ⟶ (Modules.pushforward f).obj (SheafOfModules.unit T.ringCatSheaf))
    (v : T₂ ⟶ (Modules.pushforward f).obj (SheafOfModules.unit T.ringCatSheaf))
    (W : T₁ ⊗ T₂ ⟶ T₃) (u'' : T₃ ⟶ (Modules.pushforward f).obj (SheafOfModules.unit T.ringCatSheaf))
    (hW : (u ⊗ₘ v) ≫ Modules.pushforwardUnitMul f = W ≫ u'') :
    letI := Modules.pushforwardLaxMonoidal f
    (((M ◁ u) ≫ Modules.projectionFormulaHom f M (SheafOfModules.unit T.ringCatSheaf) ≫
          (Modules.pushforward f).map (ρ_ ((Modules.pullback f).obj M)).hom) ⊗ₘ
        ((M' ◁ v) ≫ Modules.projectionFormulaHom f M' (SheafOfModules.unit T.ringCatSheaf) ≫
          (Modules.pushforward f).map (ρ_ ((Modules.pullback f).obj M')).hom)) ≫
      Functor.LaxMonoidal.μ (Modules.pushforward f) ((Modules.pullback f).obj M) ((Modules.pullback f).obj M') ≫
      (Modules.pushforward f).map ((Modules.pullbackTensorObjIso f M M').inv ≫ (Modules.pullback f).map τ.inv) =
    tensorμ M _ M' _ ≫ (τ.inv ⊗ₘ W) ≫ (N ◁ u'') ≫
      Modules.projectionFormulaHom f N (SheafOfModules.unit T.ringCatSheaf) ≫
      (Modules.pushforward f).map (ρ_ ((Modules.pullback f).obj N)).hom := by
  let _ := Modules.pushforwardLaxMonoidal f
  exact (Modules.pullbackPushforwardAdjunction f).projFormulaHom_mul_general
    (fun A B => Modules.homEquiv_pullbackTensorObjHom f A B) τ u v W u'' hW

end AlgebraicGeometry.Scheme

end
