import MiyaokaMori.Prelude

/-! # The sections functor preserves limits

Statement: `X` a scheme, `V` an open. The sections functor `Γ(-, V) : X.Modules ⥤ Ab` preserves limits, hence:
  (a) `sections_pi_ext`: a section of a product `∏ P_k` over `V` is determined by its components;
  (b) `sections_pi_exists`: for any family `t_k ∈ Γ(P_k, V)` there is `x ∈ Γ(∏ P_k, V)` with components `t_k`;
  (c) `sections_kernel_ι_injective`: the map on sections over `V` of `kernel.ι f` is injective;
  (d) `sections_kernel_exists`: if `x ∈ Γ(A, V)` satisfies `f(x) = 0`, then `x` comes from `Γ(kernel f, V)`.

Proof:
1. `sectionsFunctor V = toPresheaf X ⋙ (evaluation at op V)`. `toPresheaf X` preserves limits (instance for
   `Scheme.Modules`), evaluation functors on functor categories preserve limits (`evaluationPreservesLimits`),
   and composites preserve limits (`comp_preservesLimits`); it is additive by definition.
2. (a) is `Concrete.Pi.map_ext` (componentwise extensionality for product-preserving functors into concrete
   categories).
3. (b): `PreservesProduct.iso` gives `Γ(∏ P, V) ≅ ∏ Γ(P_k, V)`, and elements of a product in `Ab` are
   described by `Concrete.productEquiv`; the component equalities are `piComparison_comp_π` and
   `productEquiv_symm_apply_π`.
4. (c): a functor preserving finite limits preserves monomorphisms, and monomorphisms in `Ab` are injective
   maps (`AddCommGrpCat.mono_iff_injective`).
5. (d): the kernel sequence `0 → ker f → A → B` is exact (`ShortComplex.kernelSequence_exact`), a functor
   preserving kernels preserves its exactness (`ShortComplex.Exact.map_of_mono_of_preservesKernel`), and
   exactness in `Ab` is described elementwise (`ShortComplex.ab_exact_iff`).
-/

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.Modules

noncomputable section

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- The sections functor `Γ(-, V) : X.Modules ⥤ Ab` (the composite of `toPresheaf` with evaluation); it
preserves limits. -/
abbrev sectionsFunctor (V : X.Opens) : X.Modules ⥤ Ab.{u} :=
  toPresheaf X ⋙ (CategoryTheory.evaluation _ _).obj (op V)

instance (V : X.Opens) : PreservesLimits (sectionsFunctor (X := X) V) := by
  have h1 : PreservesLimits (toPresheaf X) := inferInstance
  have h2 : PreservesLimits ((CategoryTheory.evaluation (TopologicalSpace.Opens X)ᵒᵖ Ab.{u}).obj (op V)) :=
    inferInstance
  exact comp_preservesLimits _ _

instance (V : X.Opens) : (sectionsFunctor (X := X) V).Additive where
  map_add := rfl

theorem sections_pi_ext {κ : Type u} (P : κ → X.Modules) (V : X.Opens) (x y : Γ(∏ᶜ P, V))
    (h : ∀ k, (Pi.π P k).app V x = (Pi.π P k).app V y) : x = y :=
  Concrete.Pi.map_ext P (sectionsFunctor V) x y h

theorem sections_pi_exists {κ : Type u} (P : κ → X.Modules) (V : X.Opens) (t : ∀ k, Γ(P k, V)) :
    ∃ x : Γ(∏ᶜ P, V), ∀ k, (Pi.π P k).app V x = t k := by
  let G := sectionsFunctor (X := X) V
  let y : ToType (∏ᶜ fun k => G.obj (P k)) := (Concrete.productEquiv (fun k => G.obj (P k))).symm t
  refine ⟨(PreservesProduct.iso G P).inv y, fun k => ?_⟩
  have h1 : G.map (Pi.π P k) = (PreservesProduct.iso G P).hom ≫ Pi.π _ k := by
    rw [PreservesProduct.iso_hom, piComparison_comp_π]
  change G.map (Pi.π P k) ((PreservesProduct.iso G P).inv y) = t k
  rw [h1, ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply (PreservesProduct.iso G P).inv,
    Iso.inv_hom_id, ConcreteCategory.id_apply]
  exact Concrete.productEquiv_symm_apply_π (fun k => G.obj (P k)) t k

theorem sections_kernel_ι_injective {A B : X.Modules} (f : A ⟶ B) (V : X.Opens) :
    Function.Injective ((kernel.ι f).app V) := by
  have : Mono ((sectionsFunctor V).map (kernel.ι f)) := inferInstance
  exact (AddCommGrpCat.mono_iff_injective _).mp this

theorem sections_kernel_exists {A B : X.Modules} (f : A ⟶ B) (V : X.Opens) (x : Γ(A, V))
    (hx : f.app V x = 0) : ∃ s : Γ(kernel f, V), (kernel.ι f).app V s = x := by
  have hex := (ShortComplex.kernelSequence_exact f).map_of_mono_of_preservesKernel
    (sectionsFunctor V) inferInstance inferInstance
  exact (ShortComplex.ab_exact_iff _).mp hex x hx

end

end AlgebraicGeometry.Scheme.Modules
