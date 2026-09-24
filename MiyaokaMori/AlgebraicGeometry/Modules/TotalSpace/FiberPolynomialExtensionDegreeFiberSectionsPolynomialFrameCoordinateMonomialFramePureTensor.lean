import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotSectionsPolynomial
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.TensorPowIsoSection
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotLineMonomialZeroSection

/-! # The monomial map on pure tensors

Glue for the restriction of the monomials `c·ξ^q` to a fibre. The first lemma is at the variable
level (any `f : X ⟶ Y`). The projection formula on pure tensors over an open (`θ_{M,N}(m ⊗ n) = (f^*m) ⊗ n`)
is `projectionFormulaHom_app_tensorSections` (`TotLineMonomialZeroSection`), reused here.

* `rightUnitor_projectionFormulaHom_whiskerLeft_tensorSections` (**the monomial map on a pure tensor**): for
  `v : N ⟶ f_*O_X` and `m ∈ Γ(M, U)`, `n ∈ Γ(N, U)`: `ρ(θ((M ◁ v)(m ⊗ n))) = v(n) • f^*m` in `Γ(f^*M, f⁻¹U)`.
* `totalSpace.monomialUnit L q := Θ_q ≫ ι_q ≫ σ : (L^∨)^{⊗q} ⟶ p_*O_{Tot}` (the second factor of
  `monomialHom`, `monomialHom_eq`), and `xiMonomial_res`: the restriction of `xiMonomial L M q c` to
  `p⁻¹V` is `ρ(θ((monomialHom).app V (c'|_V)))` computed on `V` (naturality of the three sheaf morphisms
  under restriction, `Hom.app_res`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry CategoryTheory.MonoidalCategory

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : AlgebraicGeometry.Scheme.{u}}

/-- A morphism of sheaves of modules commutes with restriction (element form; private copy of
`ModuleSheafFrameIso.Hom.app_res`). -/
private theorem app_res_mf {M N : X.Modules} (φ : M ⟶ N) {W W' : X.Opens} (h : W' ≤ W) (x : Γ(M, W)) :
    φ.app W' (M.res h x) = N.res h (φ.app W x) :=
  ConcreteCategory.congr_hom (φ.mapPresheaf.naturality (homOfLE h).op) x

/-- **The monomial map on a pure tensor**: for `v : N ⟶ f_*O_X`, `ρ(θ((M ◁ v)(m ⊗ n))) = v(n) • f^*m`. -/
theorem rightUnitor_projectionFormulaHom_whiskerLeft_tensorSections (f : X ⟶ Y) (M N : Y.Modules)
    (v : N ⟶ (pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)) (U : Y.Opens)
    (m : Γ(M, U)) (n : Γ(N, U)) :
    (ρ_ ((pullback f).obj M)).hom.app (f ⁻¹ᵁ U)
        (show Γ((pullback f).obj M ⊗ SheafOfModules.unit X.ringCatSheaf, f ⁻¹ᵁ U) from
          (projectionFormulaHom f M (SheafOfModules.unit X.ringCatSheaf)).app U
            ((M ◁ v).app U (tensorSections M N U m n))) =
      (show Γ(X, f ⁻¹ᵁ U) from v.app U n) •
        (show Γ((pullback f).obj M, f ⁻¹ᵁ U) from ((pullbackPushforwardAdjunction f).unit.app M).app U m) := by
  have h1 := whiskerLeft_app_tensorSections M v U m n
  have h2 := projectionFormulaHom_app_tensorSections f M (SheafOfModules.unit X.ringCatSheaf) U m
    (show Γ((pushforward f).obj (SheafOfModules.unit X.ringCatSheaf), U) from v.app U n)
  have h3 := rightUnitor_app_tensorSections ((pullback f).obj M) (f ⁻¹ᵁ U)
    (show Γ((pullback f).obj M, f ⁻¹ᵁ U) from ((pullbackPushforwardAdjunction f).unit.app M).app U m)
    (show Γ(X, f ⁻¹ᵁ U) from v.app U n)
  refine (congrArg (fun z => (ρ_ ((pullback f).obj M)).hom.app (f ⁻¹ᵁ U)
    (show Γ((pullback f).obj M ⊗ SheafOfModules.unit X.ringCatSheaf, f ⁻¹ᵁ U) from
      (projectionFormulaHom f M (SheafOfModules.unit X.ringCatSheaf)).app U z)) h1).trans ?_
  refine (congrArg (fun z => (ρ_ ((pullback f).obj M)).hom.app (f ⁻¹ᵁ U)
    (show Γ((pullback f).obj M ⊗ SheafOfModules.unit X.ringCatSheaf, f ⁻¹ᵁ U) from z)) h2).trans ?_
  exact h3

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- The second factor of the monomial map: `Θ_q ≫ ι_q ≫ σ : (L^∨)^{⊗q} ⟶ p_*O_{Tot(L)}` (`Θ_q` the comparison
with the `q`-th symmetric power, `ι_q` the inclusion of the `q`-th graded piece, `σ` the structure map of the
relative `Spec`). -/
def totalSpace.monomialUnit (L : X.Modules) [L.IsLineBundle] (q : ℕ) :
    AlgebraicGeometry.Scheme.Modules.moduleTensorPower (Modules.dual L) q ⟶
      (Modules.pushforward (totalSpace L).hom).obj (SheafOfModules.unit (totalSpace L).left.ringCatSheaf) :=
  totalSpace.tensorPowerToSymPart L q ≫ (Modules.symGradedAlgebra (Modules.dual L)).totalIncl q ≫
    relativeSpec.structureHom (Modules.symGradedAlgebra (Modules.dual L)).total

theorem totalSpace.monomialHom_eq (L M : X.Modules) [L.IsLineBundle] (q : ℕ) :
    totalSpace.monomialHom L M q =
      (Modules.tensorIsoTensorObj M (AlgebraicGeometry.Scheme.Modules.moduleTensorPower (Modules.dual L) q)).hom ≫
        (M ◁ totalSpace.monomialUnit L q) := rfl

end AlgebraicGeometry.Scheme

/-- **The restriction of `xiMonomial L M q c` to `p⁻¹V`** is computed on `V`: it is
`ρ(θ((monomialHom L M q).app V (c'|_V)))`, `c' = (coefficientModuleIso q)⁻¹ c`. (Naturality of the three
sheaf morphisms under restriction.) -/
theorem xiMonomial_res {k : Type u} [Field k] {C : SmoothProjectiveCurve k} (L M : LineBundle C.toVariety)
    (q : ℕ) (c : ((((M.zpow 1).tensor (L.zpow (-(q : ℤ)))).toModules.val.obj (Opposite.op ⊤)) : Type u))
    (V : C.toScheme.Opens) :
    ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        M.toModules).res (le_top : (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ V ≤ ⊤)
        (xiMonomial L M q c) =
      (ρ_ ((AlgebraicGeometry.Scheme.Modules.pullback
          (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj M.toModules)).hom.app
        ((AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ V)
        (show Γ((AlgebraicGeometry.Scheme.Modules.pullback
            (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj M.toModules ⊗
            SheafOfModules.unit (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.ringCatSheaf,
            (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ V) from
          (AlgebraicGeometry.Scheme.Modules.projectionFormulaHom
            (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom M.toModules
            (SheafOfModules.unit (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.ringCatSheaf)).app V
            ((AlgebraicGeometry.Scheme.totalSpace.monomialHom L.toModules M.toModules q).app V
              ((AlgebraicGeometry.Scheme.Modules.coefficientLineModule M.toModules L.toModules q).res (le_top : V ≤ ⊤)
                ((L.coefficientModuleIso M q).inv.app ⊤ c)))) := by
  let p := (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom
  let PM := (AlgebraicGeometry.Scheme.Modules.pullback p).obj M.toModules
  let O := SheafOfModules.unit (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.ringCatSheaf
  let θ := AlgebraicGeometry.Scheme.Modules.projectionFormulaHom p M.toModules O
  let μ := AlgebraicGeometry.Scheme.totalSpace.monomialHom L.toModules M.toModules q
  let c' : Γ(AlgebraicGeometry.Scheme.Modules.coefficientLineModule M.toModules L.toModules q, ⊤) := (L.coefficientModuleIso M q).inv.app ⊤ c
  have e1 : μ.app V ((AlgebraicGeometry.Scheme.Modules.coefficientLineModule M.toModules L.toModules q).res (le_top : V ≤ ⊤) c') =
      (M.toModules ⊗ (AlgebraicGeometry.Scheme.Modules.pushforward p).obj O).res (le_top : V ≤ ⊤) (μ.app ⊤ c') :=
    AlgebraicGeometry.Scheme.Modules.app_res_mf μ (le_top : V ≤ ⊤) c'
  have e2 : (show Γ(PM ⊗ O, p ⁻¹ᵁ V) from θ.app V
        ((M.toModules ⊗ (AlgebraicGeometry.Scheme.Modules.pushforward p).obj O).res (le_top : V ≤ ⊤) (μ.app ⊤ c'))) =
      (PM ⊗ O).res (le_top : p ⁻¹ᵁ V ≤ ⊤) (show Γ(PM ⊗ O, ⊤) from θ.app ⊤ (μ.app ⊤ c')) :=
    AlgebraicGeometry.Scheme.Modules.app_res_mf θ (le_top : V ≤ ⊤) (μ.app ⊤ c')
  have e3 : (ρ_ PM).hom.app (p ⁻¹ᵁ V) ((PM ⊗ O).res (le_top : p ⁻¹ᵁ V ≤ ⊤) (show Γ(PM ⊗ O, ⊤) from θ.app ⊤ (μ.app ⊤ c'))) =
      PM.res (le_top : p ⁻¹ᵁ V ≤ ⊤) ((ρ_ PM).hom.app ⊤ (show Γ(PM ⊗ O, ⊤) from θ.app ⊤ (μ.app ⊤ c'))) :=
    AlgebraicGeometry.Scheme.Modules.app_res_mf (ρ_ PM).hom (le_top : p ⁻¹ᵁ V ≤ ⊤) _
  exact ((congrArg (fun z => (ρ_ PM).hom.app (p ⁻¹ᵁ V) (show Γ(PM ⊗ O, p ⁻¹ᵁ V) from θ.app V z)) e1).trans
    ((congrArg (fun z => (ρ_ PM).hom.app (p ⁻¹ᵁ V) z) e2).trans e3)).symm

end
