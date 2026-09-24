import MiyaokaMori.Prelude
import MiyaokaMori.CategoryTheory.ModulesProjectionFormulaHomAbstract
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPullbackMonoidal
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.TensorRightInvertibleEquivalence
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.SheafOfModulesMonoidal

/-! # The projection formula morphism

The comparison morphism `M ⊗ f_*N → f_*(f^*M ⊗ N)` of the projection formula, an isomorphism
when `M` is a line bundle (Stacks 01E8).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open scoped CategoryTheory.MonoidalCategory

/-- The comparison morphism `M ⊗ f_*N → f_*(f^*M ⊗ N)` of the projection formula: the adjoint of
`f^*(M ⊗ f_*N) → f^*M ⊗ f^*f_*N` (`pullbackTensorObjHom`) followed by the counit
`f^*f_*N → N`. -/
noncomputable def AlgebraicGeometry.Scheme.Modules.projectionFormulaHom {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) (M : Y.Modules) (N : X.Modules) :
    M ⊗ (AlgebraicGeometry.Scheme.Modules.pushforward f).obj N ⟶
      (AlgebraicGeometry.Scheme.Modules.pushforward f).obj
        ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M ⊗ N) :=
  (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f).homEquiv _ _
    (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom f M
        ((AlgebraicGeometry.Scheme.Modules.pushforward f).obj N) ≫
      ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M ◁
        (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f).counit.app N))

/-- `projectionFormulaHom` is the abstract projection-formula map
`CategoryTheory.Adjunction.projFormulaHom` of the monoidal adjunction `f^* ⊣ f_*`
(`ModulesProjectionFormulaHomAbstract`), for the oplax structure
`pullbackOplaxMonoidal f` on `f^*` (definitional unfolding). -/
theorem AlgebraicGeometry.Scheme.Modules.projectionFormulaHom_eq_projFormulaHom
    {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules) (N : X.Modules) :
    AlgebraicGeometry.Scheme.Modules.projectionFormulaHom f M N =
      (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f).projFormulaHom
        (instF := AlgebraicGeometry.Scheme.Modules.pullbackOplaxMonoidal f) M N := rfl

/-- **Projection formula (Stacks 01E8, the `q = 0` part)**: for a line bundle `M` the comparison
morphism `θ_M` is an isomorphism.

Reference: Stacks 01E8 `lemma-projection-formula`, which reduces the general case to
"$f_*(f^*\mathcal E \otimes \mathcal F) = \mathcal E \otimes_{\mathcal O_Y} f_*\mathcal F$ …
This is clear when $\mathcal E = \mathcal O_Y^{\oplus n}$, and follows in general by working
locally on $Y$." Here only the line bundle case (`n = 1`) is stated. Stacks assumes `E` finite
locally free; `[M.IsLineBundle]` (locally free of rank 1) is stronger; no extra hypotheses on `f`
or `N` are needed, and the direction of the comparison morphism agrees with the canonical map.

---
## Proof (no base change needed)

Write `θ_{M,N} := projectionFormulaHom f M N`. It is the abstract map
`Adjunction.projFormulaHom` for the adjunction `f^* ⊣ f_*` with `f^*` oplax monoidal
(`projectionFormulaHom_eq_projFormulaHom`, `rfl`). The abstract file
`ModulesProjectionFormulaHomAbstract.lean` proves, for any adjunction `F ⊣ G` with `F` oplax
monoidal (`δ`, `η`), purely from the adjunction and monoidal axioms:

1. `θ` is natural in `M` and in `N` (`projFormulaHom_naturality_left/right`).
2. `θ` is multiplicative in `M` (`projFormulaHom_tensor`):
   `θ_{M⊗M'} ≫ G(δ_{M,M'} ▷ N) ≫ G(α) = α ≫ (M ◁ θ_{M'}) ≫ θ_{M, F M' ⊗ N}`
   (transpose; use `δ_natural_right`, `whisker_exchange`, associator naturality and the oplax
   associativity of `F`).
3. Unit case (`projFormulaHom_unit_eq`): if `η` is an iso then
   `θ_𝟙 = (λ_ (G N)).hom ≫ G((λ_ N).inv ≫ (η⁻¹ ▷ N))` (oplax left unitality, `whisker_exchange`,
   left-unitor naturality, and the triangle identity), so `θ_𝟙` is an iso.
4. `isIso_projFormulaHom_of_invertible`: if `e : M ⊗ M' ≅ 𝟙`, `e' : M' ⊗ M ≅ 𝟙`, and
   `η`, `δ_{M,M'}`, `δ_{M',M}` are isos, then `θ_{M,N}` is an iso for all `N`:
   by 1 and 3, `θ_{M⊗M'}` and `θ_{M'⊗M}` are isos; by 2, `(M ◁ θ_{M',N}) ≫ θ_{M,FM'⊗N}` and
   `(M' ◁ θ_{M,N}) ≫ θ_{M',FM⊗N}` are isos, so `θ_{M,FM'⊗N₀}` is a split epi and `M' ◁ θ_{M,N}`
   is a split mono; whiskering with `M'` is injective (conjugate by `e`), so `θ_{M,N}` is mono;
   transporting along `N ≅ F M' ⊗ (F M ⊗ N)` (built from `δ_{M',M}⁻¹`, `F e'`, `η`) by the
   naturality in `N` makes `θ_{M,N}` a split epi; a split epi which is mono is an iso.

Concrete inputs for `f^* ⊣ f_*`:
* `η = (pullbackUnitIso f).hom` is an iso: `pullback_η_isIso`;
* `δ = pullbackTensorObjHom` is an iso for all `M, M'`: `pullbackTensorObjHom_isIso` (Stacks 01CD);
* `M ⊗ M^∨ ≅ 𝟙` for a line bundle: `nonempty_tensorObj_dual_iso_tensorUnit`, which rests on
  `SheafOfModules.IsLineBundle.tensor_dual_iso` (Stacks 01CT: the evaluation `L ⊗ L^∨ → O` of a
  line bundle is an iso), and `M^∨ ⊗ M ≅ 𝟙` by the braiding. -/
instance AlgebraicGeometry.Scheme.Modules.projectionFormulaHom_isIso {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) (M : Y.Modules) [M.IsLineBundle] (N : X.Modules) :
    CategoryTheory.IsIso (AlgebraicGeometry.Scheme.Modules.projectionFormulaHom f M N) := by
  obtain ⟨e⟩ := AlgebraicGeometry.Scheme.Modules.nonempty_tensorObj_dual_iso_tensorUnit M
  have e' : (AlgebraicGeometry.Scheme.Modules.dual M ⊗ M) ≅ 𝟙_ Y.Modules := β_ _ _ ≪≫ e
  have hη : CategoryTheory.IsIso (CategoryTheory.Functor.OplaxMonoidal.η
      (AlgebraicGeometry.Scheme.Modules.pullback f)
      (self := AlgebraicGeometry.Scheme.Modules.pullbackOplaxMonoidal f)) :=
    AlgebraicGeometry.Scheme.Modules.pullback_η_isIso f
  have h₁ : CategoryTheory.IsIso (CategoryTheory.Functor.OplaxMonoidal.δ
      (AlgebraicGeometry.Scheme.Modules.pullback f)
      (self := AlgebraicGeometry.Scheme.Modules.pullbackOplaxMonoidal f)
      M (AlgebraicGeometry.Scheme.Modules.dual M)) :=
    AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom_isIso f M _
  have h₂ : CategoryTheory.IsIso (CategoryTheory.Functor.OplaxMonoidal.δ
      (AlgebraicGeometry.Scheme.Modules.pullback f)
      (self := AlgebraicGeometry.Scheme.Modules.pullbackOplaxMonoidal f)
      (AlgebraicGeometry.Scheme.Modules.dual M) M) :=
    AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom_isIso f _ M
  rw [AlgebraicGeometry.Scheme.Modules.projectionFormulaHom_eq_projFormulaHom]
  exact (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction f).isIso_projFormulaHom_of_invertible
    (instF := AlgebraicGeometry.Scheme.Modules.pullbackOplaxMonoidal f) e e' N

noncomputable def AlgebraicGeometry.Scheme.Modules.projectionFormulaIso {X Y : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) (M : Y.Modules) [M.IsLineBundle] (N : X.Modules) :
    M ⊗ (AlgebraicGeometry.Scheme.Modules.pushforward f).obj N ≅
      (AlgebraicGeometry.Scheme.Modules.pushforward f).obj
        ((AlgebraicGeometry.Scheme.Modules.pullback f).obj M ⊗ N) :=
  CategoryTheory.asIso (AlgebraicGeometry.Scheme.Modules.projectionFormulaHom f M N)

end
