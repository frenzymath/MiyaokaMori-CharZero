import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.Cech.CechPullbackMap
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPullbackQuasicoherent
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.QcPullbackAffineSections
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Algebra.DirectSum.Module

/-! # Auxiliary facts for the base change of the Čech complex

Small facts used in the base change of the Čech complex: finite intersections of affine opens are
affine (separated case), a finite product of flat modules is flat, the Čech terms vanish in high
degrees, the base change square commutes on global sections, and the base change of an affine
morphism is affine.

Source: Stacks 01XD, 01U4, 01I9, 02KG/02KH; Hartshorne II Ex. 4.3, III.9.3.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

/-- Separated over an affine base ⇒ the diagonal is affine (hence intersections of affine opens are
affine, Mathlib `IsAffineOpen.inf`). -/
theorem isAffineHom_diagonal_of_isSeparated_over_affine {A : CommRingCat.{u}}
    {X : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ AlgebraicGeometry.Spec A)
    [AlgebraicGeometry.IsSeparated f] :
    AlgebraicGeometry.IsAffineHom (pullback.diagonal (terminal.from X)) := by
  haveI : AlgebraicGeometry.IsSeparated (terminal.from X) := by
    rw [← terminal.comp_from f]
    infer_instance
  infer_instance

/-- Hartshorne II Ex. 4.3: on a separated scheme, a nonempty finite intersection of affine opens is
affine. -/
theorem isAffineOpen_iInf_of_isSeparated {A : CommRingCat.{u}}
    {X : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ AlgebraicGeometry.Spec A)
    [AlgebraicGeometry.IsSeparated f] {m : ℕ} (W : Fin (m + 1) → X.Opens)
    (hW : ∀ k, AlgebraicGeometry.IsAffineOpen (W k)) :
    AlgebraicGeometry.IsAffineOpen (⨅ k, W k) := by
  haveI := isAffineHom_diagonal_of_isSeparated_over_affine f
  induction m with
  | zero =>
    have : (⨅ k, W k) = W 0 := by
      apply le_antisymm (iInf_le _ 0)
      exact le_iInf fun k => le_of_eq (congrArg W (Fin.fin_one_eq_zero k).symm)
    rw [this]
    exact hW 0
  | succ m ih =>
    have : (⨅ k, W k) = W 0 ⊓ ⨅ k : Fin (m + 1), W k.succ := by
      apply le_antisymm
      · exact le_inf (iInf_le _ 0) (le_iInf fun k => iInf_le _ k.succ)
      · refine le_iInf fun k => ?_
        refine Fin.cases inf_le_left (fun j => inf_le_right.trans (iInf_le _ j)) k
    rw [this]
    exact (hW 0).inf (ih (fun k => W k.succ) fun k => hW k.succ)

/-- The base change `X_{A'} → X` of the affine morphism `Spec A' → Spec A` is affine. -/
theorem isAffineHom_pullback_fst_spec {A A' : CommRingCat.{u}} {X : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ AlgebraicGeometry.Spec A) (φ : A ⟶ A') :
    AlgebraicGeometry.IsAffineHom (Limits.pullback.fst f (AlgebraicGeometry.Spec.map φ)) :=
  MorphismProperty.of_isPullback (P := @AlgebraicGeometry.IsAffineHom)
    (IsPullback.of_hasPullback f (AlgebraicGeometry.Spec.map φ)).flip inferInstance

/-- If a strictly increasing tuple would need more indices than available, the term is zero (the
alternating Čech complex is nonzero only in degrees `0..n−1`). -/
theorem cechTermAlt_isZero_of_le {X : AlgebraicGeometry.Scheme.{u}} {n : ℕ} (U : Fin n → X.Opens)
    (M : X.Modules) (q : ℕ) (hq : n ≤ q) : IsZero (cechTermAlt U M q) := by
  haveI : IsEmpty (Fin (q + 1) ↪o Fin n) := ⟨fun σ => by
    have := Fintype.card_le_of_embedding σ.toEmbedding
    simp only [Fintype.card_fin] at this
    omega⟩
  haveI : Subsingleton ↑(cechTermAlt U M q) :=
    (pi_family_bijective (fun σ : Fin (q + 1) ↪o Fin n =>
      M.sectionsOverTop (⨅ k, U (σ k)))).1.subsingleton
  exact ModuleCat.isZero_of_subsingleton _

/-- A finite product of flat modules is flat (viewed as `A`-modules by restriction of scalars).

Proof: take the linear isomorphism `(∏ᶜ Z)_A ≃ₗ[A] Π_i (Z_i)_A`, `x ↦ (π_i x)_i` (bijective by
`pi_family_bijective`, `A`-linear since the `π_i` are `B`-linear); for finite `ι`,
`Π_i N_i ≃ₗ ⨁_i N_i` (`DirectSum.linearEquivFunOnFintype`), a direct sum of flat modules is flat
(`Module.Flat.directSum`), and flatness transports along linear isomorphisms
(`Module.Flat.of_linearEquiv`).
Source: Stacks 05UT (direct sums of flat modules are flat).

Edge case: for empty `ι` the product is the zero module, which is flat. -/
theorem flat_restrictScalars_pi {A B : Type u} [CommRing A] [CommRing B] (a : A →+* B)
    {ι : Type} [Finite ι] (Z : ι → ModuleCat.{u} B)
    (h : ∀ i, Module.Flat A ((ModuleCat.restrictScalars a).obj (Z i))) :
    Module.Flat A ((ModuleCat.restrictScalars a).obj (∏ᶜ Z)) := by
  classical
  haveI := Fintype.ofFinite ι
  -- `x ↦ (π_i x)_i` is an `A`-linear bijection `(∏ᶜ Z)_A ≃ Π_i (Z_i)_A`
  let ev : ↑((ModuleCat.restrictScalars a).obj (∏ᶜ Z)) →ₗ[A]
      (∀ i, ↑((ModuleCat.restrictScalars a).obj (Z i))) :=
    LinearMap.pi fun i => ((ModuleCat.restrictScalars a).map (Pi.π Z i)).hom
  have hev : Function.Bijective ev := pi_family_bijective Z
  haveI : ∀ i, Module.Flat A ↑((ModuleCat.restrictScalars a).obj (Z i)) := h
  haveI : Module.Flat A (∀ i, ↑((ModuleCat.restrictScalars a).obj (Z i))) :=
    Module.Flat.of_linearEquiv (DirectSum.linearEquivFunOnFintype A ι _).symm
  exact Module.Flat.of_linearEquiv (LinearEquiv.ofBijective ev hev)

/-- The base change square commutes on global sections: `g'^♯ ∘ a = a' ∘ φ` (`a`, `a'` the
structure homomorphisms `A → Γ(X)`, `A' → Γ(X_{A'})`). -/
theorem appTop_comp_structure_eq {A A' : CommRingCat.{u}} {X : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ AlgebraicGeometry.Spec A) (φ : A ⟶ A') :
    (pullback.fst f (AlgebraicGeometry.Spec.map φ)).appTop.hom.comp
        ((AlgebraicGeometry.Scheme.ΓSpecIso A).inv ≫ f.appTop).hom =
      ((AlgebraicGeometry.Scheme.ΓSpecIso A').inv ≫
        (pullback.snd f (AlgebraicGeometry.Spec.map φ)).appTop).hom.comp φ.hom := by
  have h1 : f.appTop ≫ (pullback.fst f (AlgebraicGeometry.Spec.map φ)).appTop =
      (AlgebraicGeometry.Spec.map φ).appTop ≫
        (pullback.snd f (AlgebraicGeometry.Spec.map φ)).appTop := by
    rw [← AlgebraicGeometry.Scheme.Hom.comp_appTop, ← AlgebraicGeometry.Scheme.Hom.comp_appTop,
      pullback.condition]
  have h2 : ((AlgebraicGeometry.Scheme.ΓSpecIso A).inv ≫ f.appTop) ≫
      (pullback.fst f (AlgebraicGeometry.Spec.map φ)).appTop =
      φ ≫ ((AlgebraicGeometry.Scheme.ΓSpecIso A').inv ≫
        (pullback.snd f (AlgebraicGeometry.Spec.map φ)).appTop) := by
    rw [Category.assoc, h1, ← Category.assoc, ← Category.assoc,
      AlgebraicGeometry.Scheme.ΓSpecIso_inv_naturality]
  exact congrArg CommRingCat.Hom.hom h2

end AlgebraicGeometry.Scheme.Modules

end
