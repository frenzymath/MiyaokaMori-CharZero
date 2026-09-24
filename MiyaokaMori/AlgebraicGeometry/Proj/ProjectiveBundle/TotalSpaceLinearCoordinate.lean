import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.RelativeSpecStructureIso
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModulesDualMap
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModulesDual
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.ModulesPow
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.RelativeSpec
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotalSpaceVectorBundle
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedSymGenerator
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedAlgebraTotalProjection

/-! # Linear coordinate functions on the total space of a vector bundle

On the total space `Tot(V) = Spec_X Sym(V^∨)` of a vector bundle, a section `ξ` of `V^∨` over an open
`U` gives the **linear function** `totalSpace.linearFunction V U ξ ∈ Γ(Tot(V), π⁻¹U)`. In particular,
for `V = A^{⊕(N+1)}` a dual frame `α ∈ Γ(A^∨, U)` of `A` on `U` gives the `ℓ`-th linear coordinate
function `x_ℓ^α = totalSpace.coordinateFunction A (N+1) ℓ U α` (the function of the section `α ∘ pr_ℓ`
of `V^∨`); pulling back along any morphism `j : Y ⟶ Tot(V)` (in the paper, the closed immersion of the
twisted affine cone `𝒵`) gives `totalSpace.coordinateFunctionOn`, the paper's `x_ℓ^a|_𝒵`.

`BasedJet.coneCoordinate` gives, via `totalSpaceHomEquiv`, a section of a sheaf morphism (a global
section of `ρ^*A`), not a function on `Tot`; this module isolates the chain "inclusion of the generators
of Sym + graded inclusion + structure map of `relativeSpec`" (also used by
`totalSpace.tautologicalFunctional`) at the level of sections, producing functions.

Source: §1 and §4 of the paper (`Tot(A^{⊕(N+1)}) = Spec Sym`; the coordinates `x_ℓ^a` and the
polynomials `P_ℓ^{(k)}` of the twisted affine cone).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- `V^∨ ⟶ π_*O_{Tot(V)}`: dual sections viewed as fiberwise linear functions on `Tot(V)`.
The chain is `V^∨ →(symGen) Sym^1(V^∨) →(totalIncl 1) ⊕_m Sym^m(V^∨) →(structureHom) π_*O_{Tot(V)}`. -/

noncomputable def AlgebraicGeometry.Scheme.totalSpace.linearFunctionHom
    {X : AlgebraicGeometry.Scheme.{u}} (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType] :
    AlgebraicGeometry.Scheme.Modules.dual V ⟶
      (AlgebraicGeometry.Scheme.Modules.pushforward (AlgebraicGeometry.Scheme.totalSpace V).hom).obj
        (SheafOfModules.unit (AlgebraicGeometry.Scheme.totalSpace V).left.ringCatSheaf) :=
  AlgebraicGeometry.Scheme.Modules.symGen (AlgebraicGeometry.Scheme.Modules.dual V) ≫
    (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
      (AlgebraicGeometry.Scheme.Modules.dual V)).totalIncl 1 ≫
    AlgebraicGeometry.Scheme.relativeSpec.structureHom
      (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
        (AlgebraicGeometry.Scheme.Modules.dual V)).total

/-- The linear function on `π⁻¹U ⊆ Tot(V)` of a section `ξ ∈ Γ(V^∨, U)`. -/

noncomputable def AlgebraicGeometry.Scheme.totalSpace.linearFunction
    {X : AlgebraicGeometry.Scheme.{u}} (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType]
    (U : X.Opens) (ξ : ((AlgebraicGeometry.Scheme.Modules.dual V).val.obj (Opposite.op U) : Type u)) :
    Γ((AlgebraicGeometry.Scheme.totalSpace V).left,
      (AlgebraicGeometry.Scheme.totalSpace V).hom ⁻¹ᵁ U) :=
  ((AlgebraicGeometry.Scheme.totalSpace.linearFunctionHom V).val.app (Opposite.op U)).hom ξ

/-- The `ℓ`-th linear coordinate function for `V = A^{⊕n}`: the section `α` of `A^∨` is dualized along
the `ℓ`-th projection to a section of `V^∨` (`Modules.dualMap (biproduct.π _ ℓ)`), and its linear
function is taken. When `α` is the dual frame of a frame `a` of `A` on `U`, this is the paper's `x_ℓ^a`. -/

noncomputable def AlgebraicGeometry.Scheme.totalSpace.coordinateFunction
    {X : AlgebraicGeometry.Scheme.{u}} (A : X.Modules) (n : ℕ)
    [(AlgebraicGeometry.Scheme.Modules.pow A n).IsLocallyFree]
    [(AlgebraicGeometry.Scheme.Modules.pow A n).IsFiniteType]
    (ℓ : Fin n) (U : X.Opens)
    (α : ((AlgebraicGeometry.Scheme.Modules.dual A).val.obj (Opposite.op U) : Type u)) :
    Γ((AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A n)).left,
      (AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A n)).hom ⁻¹ᵁ U) :=
  AlgebraicGeometry.Scheme.totalSpace.linearFunction (AlgebraicGeometry.Scheme.Modules.pow A n) U
    (((AlgebraicGeometry.Scheme.Modules.dualMap
      (CategoryTheory.Limits.biproduct.π (fun _ : Fin n => A) ℓ)).val.app
        (Opposite.op U)).hom α)

/-- The coordinate function pulled back along `j : Y ⟶ Tot(V)` (in the paper, `j` is the closed immersion
`𝒵 ↪ Tot(A^{⊕(N+1)})` of the twisted affine cone, and the result is the `ℓ`-th coordinate function
restricted to `𝒵`, `b = x_ℓ^a|_𝒵 ∈ Γ(𝒵, π⁻¹U)`). -/

noncomputable def AlgebraicGeometry.Scheme.totalSpace.coordinateFunctionOn
    {X Y : AlgebraicGeometry.Scheme.{u}} (A : X.Modules) (n : ℕ)
    [(AlgebraicGeometry.Scheme.Modules.pow A n).IsLocallyFree]
    [(AlgebraicGeometry.Scheme.Modules.pow A n).IsFiniteType]
    (ℓ : Fin n) (U : X.Opens)
    (α : ((AlgebraicGeometry.Scheme.Modules.dual A).val.obj (Opposite.op U) : Type u))
    (j : Y ⟶ (AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A n)).left)
    (UY : Y.Opens)
    (hle : UY ≤ j ⁻¹ᵁ
      ((AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A n)).hom ⁻¹ᵁ U)) :
    Γ(Y, UY) :=
  (j.appLE _ _ hle).hom
    (AlgebraicGeometry.Scheme.totalSpace.coordinateFunction A n ℓ U α)

end
