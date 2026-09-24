import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.FiberPolynomialExtensionDegreeFiberSectionsPolynomialFrameCoordinateMonomialFramePureTensor
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotLineMonomialZeroUnit
import MiyaokaMori.AlgebraicGeometry.Modules.TotLineMonomialMul
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.JetWeightComponentEqCoefficient
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.SymCoeffHomMulHomogeneousAux
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.JetProjectivize
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedAlgebraTotalComponent

/-! # `σ(t^{⊗q}) = σ(t)^q` for the monomial unit maps

Notation: `L` a line bundle on `X`, `p : Tot(L) → X`, `S := Sym(L^∨)`, `σ : S.total ⟶ p_*O_Tot` the structure
map of the relative `Spec`, `Θ_q : (L^∨)^{⊗q} ⟶ Sym^q L^∨` (`tensorPowerToSymPart`), `ι_q` the inclusion of the
`q`-th graded piece, `u_q := Θ_q ≫ ι_q ≫ σ` (`totalSpace.monomialUnit L q`, the second factor of the monomial map),
`t ∈ Γ(V, L^∨)`, `t^{⊗q} := moduleTensorPowerSection t q`.

* `totalSpace.frameCoordinate L V t := u_1(t ⊗ 1) ∈ Γ(p⁻¹V, O_Tot)`: the fiber coordinate attached to `t`
  ("`x = σ(t)`"; for `t = ε^∨` the dual of a frame `ε` of `L` this is the coordinate with `ξ = x·p^*ε`, see the
  sibling module `…MonomialFrameTautological`).
* **Main** `totalSpace.monomialUnit_app_moduleTensorPowerSection`: `u_q(t^{⊗q}) = x^q`.
  Proof: `σ` is an algebra map (`relativeSpec.structureHom_isAlgebraMap`), the multiplication of `S.total` on the
  graded pieces is `S.mul m n` (`GradedQCAlgebra.total_mul_component`), and on a line bundle `S.mul m n` is the
  concatenation `monoidalPowCat` under the comparison isomorphisms `Φ_m = symPartToMonoidalPow`
  (`symGradedAlgebra_mul_symPartToMonoidalPow`), with `Θ_m ≫ Φ_m = powIso_m⁻¹`
  (`tensorPowerToSymPart_symPartToMonoidalPow`). Hence (`tensorHom_tensorPowerToSymPart_comp_mul`, morphism level,
  by cancelling the isomorphism `Φ_{m+n}`) `(Θ_m ⊗ Θ_n) ≫ S.mul m n = (powIso_m⁻¹ ⊗ powIso_n⁻¹) ≫ cat ≫
  powIso_{m+n} ≫ Θ_{m+n}`, and on sections `u_{m+n}(a ⋆ b) = u_m(a) · u_n(b)` for the concatenation
  `a ⋆ b := powIso_{m+n}(cat(powIso_m⁻¹ a ⊗ powIso_n⁻¹ b))` (`monomialUnit_app_concat`). Finally
  `t^{⊗q} ⋆ (t ⊗ 1) = t^{⊗(q+1)}` (`powIso_hom_monoidalPowCat_moduleTensorPowerSection`: unwinding the recursive
  definitions of `monoidalPowIsoTensorPower` — braiding, whiskering, `tensorIsoTensorObj` — and of
  `monoidalPowCat _ q 1 = α⁻¹ ≫ (ρ ▷ _)` on pure tensors), so induction on `q` gives `u_q(t^{⊗q}) = x^q`; the case
  `q = 0` is `u_0(1) = σ(S.one(1)) = 1` (`tensorPowerToSymPart_zero_eq_one`, `structureHom_isAlgebraMap.2`).

`totalSpace.tensorHom_tensorPowerToSymPart_comp_mul` is a one-line consequence of
`totalSpace.tensorHom_tensorPowerToSymPart_comp_symMul` (`TotLineMonomialMul`, the same equation up to
reassociation); the section instance `[(Modules.dual L).IsLineBundle]` is not needed by its proof but is kept
in the statement (with `linter.unusedSectionVars` silenced for this one declaration).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry CategoryTheory.MonoidalCategory

noncomputable section

namespace AlgebraicGeometry.Scheme

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- The fiber coordinate attached to `t ∈ Γ(V, L^∨)`: `x := u_1(t ⊗ 1) ∈ Γ(p⁻¹V, O_{Tot(L)})`
("`x = σ(t)`", the linear function of `t` on the total space). -/
def totalSpace.frameCoordinate (L : X.Modules) [L.IsLineBundle] (V : X.Opens)
    (t : Γ(Modules.dual L, V)) : Γ((totalSpace L).left, (totalSpace L).hom ⁻¹ᵁ V) :=
  (totalSpace.monomialUnit L 1).app V (AlgebraicGeometry.Scheme.Modules.moduleTensorPowerSection t 1)

/-- Braiding inverse on a pure tensor: `(β_ A B)⁻¹(b ⊗ a) = a ⊗ b`. -/
private theorem braiding_inv_app_tensorSections (A B : X.Modules) (U : X.Opens) (a : Γ(A, U)) (b : Γ(B, U)) :
    (β_ A B).inv.app U (Modules.tensorSections B A U b a) = Modules.tensorSections A B U a b := by
  rw [← SymmetricCategory.braiding_swap_eq_inv_braiding]
  exact Modules.braiding_app_tensorSections B A U b a

/-- Right whiskering on a pure tensor: `(f ▷ C)(a ⊗ c) = f a ⊗ c`. -/
private theorem whiskerRight_app_tensorSections_mf {A A' : X.Modules} (f : A ⟶ A') (C : X.Modules) (U : X.Opens)
    (a : Γ(A, U)) (c : Γ(C, U)) :
    (f ▷ C).app U (Modules.tensorSections A C U a c) = Modules.tensorSections A' C U (f.app U a) c := by
  rw [← CategoryTheory.MonoidalCategory.tensorHom_id]
  exact Modules.tensorHom_tensorSections f (𝟙 C) U a c

/-- Associator inverse on a pure tensor: `α⁻¹(a ⊗ (b ⊗ c)) = (a ⊗ b) ⊗ c`. -/
private theorem associator_inv_app_tensorSections (A B C : X.Modules) (U : X.Opens)
    (a : Γ(A, U)) (b : Γ(B, U)) (c : Γ(C, U)) :
    (α_ A B C).inv.app U (Modules.tensorSections A (B ⊗ C) U a (Modules.tensorSections B C U b c)) =
      Modules.tensorSections (A ⊗ B) C U (Modules.tensorSections A B U a b) c := by
  rw [← Modules.associator_app_tensorSections]
  exact Modules.modIso_inv_app_hom_app (α_ A B C) U _

/-- **The comparison isomorphism `powIso_{n+1}⁻¹` on a pure tensor**: `powIso_{n+1}⁻¹(v ⊗ w) = powIso_n⁻¹(w) ⊗ v`
(recursive definition of `monoidalPowIsoTensorPower`: braiding, whiskering, `tensorIsoTensorObj`). -/
theorem Modules.monoidalPowIsoTensorPower_succ_inv_app (Vm : X.Modules) (n : ℕ) (U : X.Opens) (v : Γ(Vm, U))
    (w : Γ(AlgebraicGeometry.Scheme.Modules.moduleTensorPower Vm n, U)) :
    (Modules.monoidalPowIsoTensorPower Vm (n + 1)).inv.app U (AlgebraicGeometry.Scheme.Modules.moduleTensorSection v w) =
      Modules.tensorSections (Modules.monoidalPow Vm n) Vm U ((Modules.monoidalPowIsoTensorPower Vm n).inv.app U w) v := by
  change (β_ (Modules.monoidalPow Vm n) Vm).inv.app U
    ((Vm ◁ (Modules.monoidalPowIsoTensorPower Vm n).inv).app U
      ((Modules.tensorIsoTensorObj Vm (AlgebraicGeometry.Scheme.Modules.moduleTensorPower Vm n)).hom.app U
        (AlgebraicGeometry.Scheme.Modules.moduleTensorSection v w))) = _
  rw [Modules.tensorIsoTensorObj_hom_app_moduleTensorSection, Modules.whiskerLeft_app_tensorSections,
    braiding_inv_app_tensorSections]

/-- `powIso_1⁻¹(t ⊗ 1) = 1 ⊗ t`. -/
theorem Modules.monoidalPowIsoTensorPower_one_inv_app (Vm : X.Modules) (U : X.Opens) (t : Γ(Vm, U)) :
    (Modules.monoidalPowIsoTensorPower Vm 1).inv.app U (AlgebraicGeometry.Scheme.Modules.moduleTensorPowerSection t 1) =
      Modules.tensorSections (Modules.monoidalPow Vm 0) Vm U (1 : Γ(X, U)) t := by
  change (Modules.monoidalPowIsoTensorPower Vm (0 + 1)).inv.app U
    (AlgebraicGeometry.Scheme.Modules.moduleTensorSection t (AlgebraicGeometry.Scheme.Modules.moduleTensorPowerSection t 0)) = _
  rw [Modules.monoidalPowIsoTensorPower_succ_inv_app]
  rfl

/-- **The concatenation `monoidalPowCat _ q 1` on a pure tensor**: `x ⊗ (1 ⊗ v) ↦ x ⊗ v`. -/
theorem Modules.monoidalPowCat_one_hom_app (Vm : X.Modules) (q : ℕ) (U : X.Opens)
    (x : Γ(Modules.monoidalPow Vm q, U)) (v : Γ(Vm, U)) :
    (Modules.monoidalPowCat Vm q 1).hom.app U
        (Modules.tensorSections (Modules.monoidalPow Vm q) (Modules.monoidalPow Vm 1) U x
          (Modules.tensorSections (Modules.monoidalPow Vm 0) Vm U (1 : Γ(X, U)) v)) =
      Modules.tensorSections (Modules.monoidalPow Vm q) Vm U x v := by
  have h1 := associator_inv_app_tensorSections (Modules.monoidalPow Vm q) (Modules.monoidalPow Vm 0) Vm U x
    (1 : Γ(X, U)) v
  have h2 := whiskerRight_app_tensorSections_mf (ρ_ (Modules.monoidalPow Vm q)).hom Vm U
    (Modules.tensorSections (Modules.monoidalPow Vm q) (Modules.monoidalPow Vm 0) U x (1 : Γ(X, U))) v
  have h3 : (ρ_ (Modules.monoidalPow Vm q)).hom.app U
      (Modules.tensorSections (Modules.monoidalPow Vm q) (Modules.monoidalPow Vm 0) U x (1 : Γ(X, U))) = x :=
    (Modules.rightUnitor_app_tensorSections (Modules.monoidalPow Vm q) U x (1 : Γ(X, U))).trans (one_smul _ x)
  change ((ρ_ (Modules.monoidalPow Vm q)).hom ▷ Vm).app U
    ((α_ (Modules.monoidalPow Vm q) (Modules.monoidalPow Vm 0) Vm).inv.app U
      (Modules.tensorSections (Modules.monoidalPow Vm q) (Modules.monoidalPow Vm 0 ⊗ Vm) U x
        (Modules.tensorSections (Modules.monoidalPow Vm 0) Vm U (1 : Γ(X, U)) v))) = _
  exact (congrArg (fun z => ((ρ_ (Modules.monoidalPow Vm q)).hom ▷ Vm).app U z) h1).trans
    (h2.trans (congrArg (fun z => Modules.tensorSections (Modules.monoidalPow Vm q) Vm U z v) h3))

/-- **Concatenation of tensor powers of a section**: `t^{⊗q} ⋆ (t ⊗ 1) = t^{⊗(q+1)}`, where
`a ⋆ b := powIso_{m+n}(cat(powIso_m⁻¹ a ⊗ powIso_n⁻¹ b))`. -/
theorem Modules.monoidalPowIsoTensorPower_hom_monoidalPowCat_moduleTensorPowerSection (Vm : X.Modules)
    (U : X.Opens) (t : Γ(Vm, U)) (q : ℕ) :
    (Modules.monoidalPowIsoTensorPower Vm (q + 1)).hom.app U
        ((Modules.monoidalPowCat Vm q 1).hom.app U
          (Modules.tensorSections (Modules.monoidalPow Vm q) (Modules.monoidalPow Vm 1) U
            ((Modules.monoidalPowIsoTensorPower Vm q).inv.app U (AlgebraicGeometry.Scheme.Modules.moduleTensorPowerSection t q))
            ((Modules.monoidalPowIsoTensorPower Vm 1).inv.app U (AlgebraicGeometry.Scheme.Modules.moduleTensorPowerSection t 1)))) =
      AlgebraicGeometry.Scheme.Modules.moduleTensorPowerSection t (q + 1) := by
  rw [Modules.monoidalPowIsoTensorPower_one_inv_app, Modules.monoidalPowCat_one_hom_app,
    ← Modules.monoidalPowIsoTensorPower_succ_inv_app Vm q U t (AlgebraicGeometry.Scheme.Modules.moduleTensorPowerSection t q)]
  exact Modules.modIso_hom_app_inv_app (Modules.monoidalPowIsoTensorPower Vm (q + 1)) U _

section Multiplicativity

variable (L : X.Modules) [L.IsLineBundle] [(Modules.dual L).IsLineBundle]

-- The section instance `[(Modules.dual L).IsLineBundle]` is not used by this proof (the upstream lemma does not
-- need it) but is kept in the statement.
set_option linter.unusedSectionVars false in
/-- **Multiplicativity of `Θ` (morphism level)**: `(Θ_m ⊗ Θ_n) ≫ S.mul m n = (powIso_m⁻¹ ⊗ powIso_n⁻¹) ≫ cat ≫
powIso_{m+n} ≫ Θ_{m+n}` (cancel the isomorphism `Φ_{m+n} = symPartToMonoidalPow`;
`symGradedAlgebra_mul_symPartToMonoidalPow`, `tensorPowerToSymPart_symPartToMonoidalPow`).
The reassociation of `tensorHom_tensorPowerToSymPart_comp_symMul` (`TotLineMonomialMul`). -/
theorem totalSpace.tensorHom_tensorPowerToSymPart_comp_mul (m n : ℕ) :
    (totalSpace.tensorPowerToSymPart L m ⊗ₘ totalSpace.tensorPowerToSymPart L n) ≫
        (Modules.symGradedAlgebra (Modules.dual L)).mul m n =
      ((Modules.monoidalPowIsoTensorPower (Modules.dual L) m).inv ⊗ₘ
          (Modules.monoidalPowIsoTensorPower (Modules.dual L) n).inv) ≫
        (Modules.monoidalPowCat (Modules.dual L) m n).hom ≫
        (Modules.monoidalPowIsoTensorPower (Modules.dual L) (m + n)).hom ≫
        totalSpace.tensorPowerToSymPart L (m + n) :=
  (totalSpace.tensorHom_tensorPowerToSymPart_comp_symMul L m n).trans (by simp only [Category.assoc])

/-- **`u_{m+n}(a ⋆ b) = u_m(a) · u_n(b)`** for the concatenation `a ⋆ b := powIso_{m+n}(cat(powIso_m⁻¹ a ⊗ powIso_n⁻¹ b))`
(`σ` is an algebra map, `total_mul_component`, and the previous lemma). -/
theorem totalSpace.monomialUnit_app_concat (m n : ℕ) (V : X.Opens)
    (a : Γ(AlgebraicGeometry.Scheme.Modules.moduleTensorPower (Modules.dual L) m, V))
    (b : Γ(AlgebraicGeometry.Scheme.Modules.moduleTensorPower (Modules.dual L) n, V)) :
    (show Γ((totalSpace L).left, (totalSpace L).hom ⁻¹ᵁ V) from
      (totalSpace.monomialUnit L (m + n)).app V
        ((Modules.monoidalPowIsoTensorPower (Modules.dual L) (m + n)).hom.app V
          ((Modules.monoidalPowCat (Modules.dual L) m n).hom.app V
            (Modules.tensorSections (Modules.monoidalPow (Modules.dual L) m) (Modules.monoidalPow (Modules.dual L) n) V
              ((Modules.monoidalPowIsoTensorPower (Modules.dual L) m).inv.app V a)
              ((Modules.monoidalPowIsoTensorPower (Modules.dual L) n).inv.app V b))))) =
      (show Γ((totalSpace L).left, (totalSpace L).hom ⁻¹ᵁ V) from (totalSpace.monomialUnit L m).app V a) *
        (show Γ((totalSpace L).left, (totalSpace L).hom ⁻¹ᵁ V) from (totalSpace.monomialUnit L n).app V b) := by
  have halg := (relativeSpec.structureHom_isAlgebraMap (Modules.symGradedAlgebra (Modules.dual L)).total).1 V
    (((Modules.symGradedAlgebra (Modules.dual L)).totalIncl m).app V ((totalSpace.tensorPowerToSymPart L m).app V a))
    (((Modules.symGradedAlgebra (Modules.dual L)).totalIncl n).app V ((totalSpace.tensorPowerToSymPart L n).app V b))
  refine Eq.trans ?_ halg
  have E : (totalSpace.tensorPowerToSymPart L m ⊗ₘ totalSpace.tensorPowerToSymPart L n) ≫
      (Modules.symGradedAlgebra (Modules.dual L)).mul m n ≫
        (Modules.symGradedAlgebra (Modules.dual L)).totalIncl (m + n) =
      ((Modules.monoidalPowIsoTensorPower (Modules.dual L) m).inv ⊗ₘ
          (Modules.monoidalPowIsoTensorPower (Modules.dual L) n).inv) ≫
        (Modules.monoidalPowCat (Modules.dual L) m n).hom ≫
        (Modules.monoidalPowIsoTensorPower (Modules.dual L) (m + n)).hom ≫
        totalSpace.tensorPowerToSymPart L (m + n) ≫
        (Modules.symGradedAlgebra (Modules.dual L)).totalIncl (m + n) := by
    rw [← Category.assoc, totalSpace.tensorHom_tensorPowerToSymPart_comp_mul L m n]
    simp only [Category.assoc]
  have E' : (totalSpace.tensorPowerToSymPart L m ⊗ₘ totalSpace.tensorPowerToSymPart L n) ≫
      ((Modules.symGradedAlgebra (Modules.dual L)).totalIncl m ⊗ₘ
        (Modules.symGradedAlgebra (Modules.dual L)).totalIncl n) ≫
        (Modules.symGradedAlgebra (Modules.dual L)).total.mul =
      (totalSpace.tensorPowerToSymPart L m ⊗ₘ totalSpace.tensorPowerToSymPart L n) ≫
        (Modules.symGradedAlgebra (Modules.dual L)).mul m n ≫
        (Modules.symGradedAlgebra (Modules.dual L)).totalIncl (m + n) := by
    change (totalSpace.tensorPowerToSymPart L m ⊗ₘ totalSpace.tensorPowerToSymPart L n) ≫
      (Sigma.ι (Modules.symGradedAlgebra (Modules.dual L)).part m ⊗ₘ
        Sigma.ι (Modules.symGradedAlgebra (Modules.dual L)).part n) ≫
        (Modules.symGradedAlgebra (Modules.dual L)).total.mul =
      (totalSpace.tensorPowerToSymPart L m ⊗ₘ totalSpace.tensorPowerToSymPart L n) ≫
        (Modules.symGradedAlgebra (Modules.dual L)).mul m n ≫
        Sigma.ι (Modules.symGradedAlgebra (Modules.dual L)).part (m + n)
    rw [(Modules.symGradedAlgebra (Modules.dual L)).total_mul_component m n]
    rfl
  have h1 := congrArg (fun g => (relativeSpec.structureHom (Modules.symGradedAlgebra (Modules.dual L)).total).app V
    (g.app V (Modules.tensorSections _ _ V a b))) (E.symm.trans E'.symm)
  have hL : (Modules.tensorSections (Modules.monoidalPow (Modules.dual L) m) (Modules.monoidalPow (Modules.dual L) n) V
      ((Modules.monoidalPowIsoTensorPower (Modules.dual L) m).inv.app V a)
      ((Modules.monoidalPowIsoTensorPower (Modules.dual L) n).inv.app V b)) =
      ((Modules.monoidalPowIsoTensorPower (Modules.dual L) m).inv ⊗ₘ
        (Modules.monoidalPowIsoTensorPower (Modules.dual L) n).inv).app V (Modules.tensorSections _ _ V a b) :=
    (Modules.tensorHom_tensorSections _ _ V a b).symm
  have t1 : (totalSpace.tensorPowerToSymPart L m ⊗ₘ totalSpace.tensorPowerToSymPart L n).app V
      (Modules.tensorSections _ _ V a b) =
      Modules.tensorSections _ _ V ((totalSpace.tensorPowerToSymPart L m).app V a)
        ((totalSpace.tensorPowerToSymPart L n).app V b) :=
    Modules.tensorHom_tensorSections _ _ V a b
  have t2 : ((Modules.symGradedAlgebra (Modules.dual L)).totalIncl m ⊗ₘ
        (Modules.symGradedAlgebra (Modules.dual L)).totalIncl n).app V
      (Modules.tensorSections _ _ V ((totalSpace.tensorPowerToSymPart L m).app V a)
        ((totalSpace.tensorPowerToSymPart L n).app V b)) =
      Modules.tensorSections _ _ V
        (((Modules.symGradedAlgebra (Modules.dual L)).totalIncl m).app V ((totalSpace.tensorPowerToSymPart L m).app V a))
        (((Modules.symGradedAlgebra (Modules.dual L)).totalIncl n).app V ((totalSpace.tensorPowerToSymPart L n).app V b)) :=
    Modules.tensorHom_tensorSections _ _ V _ _
  have hR : Modules.tensorSections _ _ V
      (((Modules.symGradedAlgebra (Modules.dual L)).totalIncl m).app V ((totalSpace.tensorPowerToSymPart L m).app V a))
      (((Modules.symGradedAlgebra (Modules.dual L)).totalIncl n).app V ((totalSpace.tensorPowerToSymPart L n).app V b)) =
      ((Modules.symGradedAlgebra (Modules.dual L)).totalIncl m ⊗ₘ
        (Modules.symGradedAlgebra (Modules.dual L)).totalIncl n).app V
        ((totalSpace.tensorPowerToSymPart L m ⊗ₘ totalSpace.tensorPowerToSymPart L n).app V
          (Modules.tensorSections _ _ V a b)) :=
    t2.symm.trans (congrArg (((Modules.symGradedAlgebra (Modules.dual L)).totalIncl m ⊗ₘ
        (Modules.symGradedAlgebra (Modules.dual L)).totalIncl n).app V) t1.symm)
  refine Eq.trans ?_ (h1.trans ?_)
  · exact congrArg (fun z => (relativeSpec.structureHom (Modules.symGradedAlgebra (Modules.dual L)).total).app V
      (((Modules.symGradedAlgebra (Modules.dual L)).totalIncl (m + n)).app V
        ((totalSpace.tensorPowerToSymPart L (m + n)).app V
          ((Modules.monoidalPowIsoTensorPower (Modules.dual L) (m + n)).hom.app V
            ((Modules.monoidalPowCat (Modules.dual L) m n).hom.app V z))))) hL
  · exact congrArg (fun z => (relativeSpec.structureHom (Modules.symGradedAlgebra (Modules.dual L)).total).app V
      ((Modules.symGradedAlgebra (Modules.dual L)).total.mul.app V z)) hR.symm

omit [(Modules.dual L).IsLineBundle] in
/-- `u_0(1) = 1`: `Θ_0 = S.one` (`tensorPowerToSymPart_zero_eq_one`) and `σ` preserves the unit. -/
theorem totalSpace.monomialUnit_zero_app_one (V : X.Opens) :
    (show Γ((totalSpace L).left, (totalSpace L).hom ⁻¹ᵁ V) from
      (totalSpace.monomialUnit L 0).app V
        (AlgebraicGeometry.Scheme.Modules.moduleTensorPowerSection (M := Modules.dual L) (U := V) 0 0)) = 1 := by
  have h2 := (relativeSpec.structureHom_isAlgebraMap
    (Modules.symGradedAlgebra (Modules.dual L)).total).2 V
  refine Eq.trans ?_ h2
  change ((totalSpace.tensorPowerToSymPart L 0 ≫ (Modules.symGradedAlgebra (Modules.dual L)).totalIncl 0 ≫
    relativeSpec.structureHom (Modules.symGradedAlgebra (Modules.dual L)).total).app V (1 : Γ(X, V))) = _
  rw [totalSpace.tensorPowerToSymPart_zero_eq_one]
  rfl

/-- **`σ(t^{⊗q}) = σ(t)^q`**: the second factor `u_q = Θ_q ≫ ι_q ≫ σ` of the monomial map sends the `q`-th tensor
power of `t` to the `q`-th power of the fiber coordinate `x = u_1(t ⊗ 1)`. -/
theorem totalSpace.monomialUnit_app_moduleTensorPowerSection
    (V : X.Opens) (t : Γ(Modules.dual L, V)) (q : ℕ) :
    (show Γ((totalSpace L).left, (totalSpace L).hom ⁻¹ᵁ V) from
      (totalSpace.monomialUnit L q).app V (AlgebraicGeometry.Scheme.Modules.moduleTensorPowerSection t q)) =
    totalSpace.frameCoordinate L V t ^ q := by
  induction q with
  | zero =>
    rw [pow_zero]
    exact totalSpace.monomialUnit_zero_app_one L V
  | succ q ih =>
    rw [pow_succ, ← ih]
    have h := totalSpace.monomialUnit_app_concat L q 1 V (AlgebraicGeometry.Scheme.Modules.moduleTensorPowerSection t q)
      (AlgebraicGeometry.Scheme.Modules.moduleTensorPowerSection t 1)
    rw [Modules.monoidalPowIsoTensorPower_hom_monoidalPowCat_moduleTensorPowerSection] at h
    exact h

end Multiplicativity

end AlgebraicGeometry.Scheme

end
