import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.SectionTensor
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleSectionRing
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorMonoidalIso
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorSectionsCoherence
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorUnitIso
import MiyaokaMori.AlgebraicGeometry.Modules.NonvanishingLocusTensorSection
import MiyaokaMori.AlgebraicGeometry.Modules.Stacks0892_TensorPowIsos

/-! # Rearrangement isomorphisms of tensor powers on section powers

**The values of the rearrangement isomorphisms of tensor powers on `tensorPowSection`** (the
section-level form of the compatibility of the multiplication of `Γ_*` with powers of sections in
Stacks 01MM).

`tensorPow L (e+1) = Modules.tensor (tensorPow L e) L` (right-multiplication recursion) and
`tensorPowSection s (e+1) = s^{⊗e} ⊗ s` (`AlgebraicGeometry.Scheme.Modules.moduleTensorSection`). This file proves:
* `tensorIsoTensorObj.inv` (`A ⊗ B ≅ Modules.tensor A B`) sends `tensorSections a b` back to
  `moduleTensorSection a b` (the forward direction `tensorIsoTensorObj_hom_app_moduleTensorSection` is
  `rfl`, see `CoordinatePowerNonzeroLocus_TensorNonvanishing`);
* `tensorBraidIso : Modules.tensor A B ≅ Modules.tensor B A` (via the braiding `β_`) sends `a ⊗ b` to
  `b ⊗ a` (the same construction as `tensorCommIso` in `Stacks0ber` and `tensorSymmIso` in
  `ModuleTensorPowerIsoTensorPow`);
* `tensorPowAddIso L m k : L^{⊗(m+k)} ≅ L^{⊗m} ⊗ L^{⊗k}` sends `s^{⊗(m+k)}` to `s^{⊗m} ⊗ s^{⊗k}`
 (induction on `k`: `k = 0` uses the formula for the right unitor on section pairings, `k+1` the
  associator formula and the induction hypothesis);
* `tensorPowMulIso L k n : (L^{⊗k})^{⊗n} ≅ L^{⊗(k·n)}` sends `(s^{⊗k})^{⊗n}` to `s^{⊗(k·n)}`
 (induction on `n`, the inductive step using the inverse of the previous item).

Sources: Stacks 01MM, 01CA; monoidal coherence (`ModulesTensorSectionsCoherence`:
`rightUnitor_app_tensorSections`, `associator_app_tensorSections`, `braiding_app_tensorSections`).
Used for the uniform extension of sections of ample line bundles.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
open scoped CategoryTheory.MonoidalCategory

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- `tensorIsoTensorObj.inv` sends the section pairing `tensorSections a b` to the pure tensor
`moduleTensorSection a b`. -/
theorem tensorIsoTensorObj_inv_app_tensorSections (A B : X.Modules) (U : X.Opens)
    (a : Γ(A, U)) (b : Γ(B, U)) :
    (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj A B).inv.app U
        (AlgebraicGeometry.Scheme.Modules.tensorSections A B U a b) =
      AlgebraicGeometry.Scheme.Modules.moduleTensorSection a b := by
  have h := congrArg (fun φ : AlgebraicGeometry.Scheme.Modules.tensor A B ⟶ _ =>
      φ.app U (AlgebraicGeometry.Scheme.Modules.moduleTensorSection a b))
    (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj A B).hom_inv_id
  exact h

/-- Right whiskering on section pairings: `(f ▷ C)(a ⊗ c) = f a ⊗ c`. -/
private theorem whiskerRight_app_tensorSections {A A' : X.Modules} (f : A ⟶ A') (C : X.Modules) (U : X.Opens)
    (a : Γ(A, U)) (c : Γ(C, U)) :
    (f ▷ C).app U (AlgebraicGeometry.Scheme.Modules.tensorSections A C U a c) =
      AlgebraicGeometry.Scheme.Modules.tensorSections A' C U (f.app U a) c := by
  rw [← CategoryTheory.MonoidalCategory.tensorHom_id]
  exact AlgebraicGeometry.Scheme.Modules.tensorHom_tensorSections f (𝟙 C) U a c

/-- Left whiskering on section pairings: `(A ◁ g)(a ⊗ b) = a ⊗ g b`. -/
theorem whiskerLeft_app_tensorSections (A : X.Modules) {B B' : X.Modules} (g : B ⟶ B') (U : X.Opens)
    (a : Γ(A, U)) (b : Γ(B, U)) :
    (A ◁ g).app U (AlgebraicGeometry.Scheme.Modules.tensorSections A B U a b) =
      AlgebraicGeometry.Scheme.Modules.tensorSections A B' U a (g.app U b) := by
  rw [← CategoryTheory.MonoidalCategory.id_tensorHom]
  exact AlgebraicGeometry.Scheme.Modules.tensorHom_tensorSections (𝟙 A) g U a b

/-- The inverse right unitor on sections: `(ρ_ A).inv a = a ⊗ 1`. -/
theorem rightUnitor_inv_app_eq_tensorSections (A : X.Modules) (U : X.Opens) (a : Γ(A, U)) :
    (ρ_ A).inv.app U a =
      AlgebraicGeometry.Scheme.Modules.tensorSections A (𝟙_ X.Modules) U a (1 : Γ(X, U)) := by
  have h1 : (ρ_ A).hom.app U
      (AlgebraicGeometry.Scheme.Modules.tensorSections A (𝟙_ X.Modules) U a (1 : Γ(X, U))) = a := by
    rw [AlgebraicGeometry.Scheme.Modules.rightUnitor_app_tensorSections, one_smul]
  have h2 := congrArg (fun φ : (A ⊗ 𝟙_ X.Modules) ⟶ _ =>
      φ.app U (AlgebraicGeometry.Scheme.Modules.tensorSections A (𝟙_ X.Modules) U a (1 : Γ(X, U))))
    (ρ_ A).hom_inv_id
  simp only [Hom.comp_app, Hom.id_app] at h2
  change (ρ_ A).inv.app U ((ρ_ A).hom.app U _) = _ at h2
  rw [h1] at h2
  exact h2.trans rfl

/-- `eqToHom (𝟙_ = L^{⊗0})` is the identity on sections (the two objects are literally equal). -/
theorem eqToHom_tensorPow_zero_app (L : X.Modules) (U : X.Opens)
    (h : 𝟙_ X.Modules = AlgebraicGeometry.Scheme.Modules.tensorPow L 0) (r : Γ(X, U)) :
    (CategoryTheory.eqToHom h).app U r = r := by
  with_unfolding_all rfl

/-- `(P ◁ eqToHom h) ∘ (ρ_ P).inv` on sections: `x ↦ x ⊗ (eqToHom h) 1` (by `subst` on `h`). -/
theorem whiskerLeft_eqToHom_rightUnitor_inv_app (P : X.Modules) {Q : X.Modules}
    (h : 𝟙_ X.Modules = Q) (U : X.Opens) (x : Γ(P, U)) :
    (P ◁ CategoryTheory.eqToHom h).app U ((ρ_ P).inv.app U x) =
      AlgebraicGeometry.Scheme.Modules.tensorSections P Q U x
        ((CategoryTheory.eqToHom h).app U (1 : Γ(X, U))) := by
  subst h
  rw [CategoryTheory.eqToHom_refl, CategoryTheory.MonoidalCategory.whiskerLeft_id, Hom.id_app,
    rightUnitor_inv_app_eq_tensorSections]
  rfl

/-- The commutativity isomorphism `Modules.tensor A B ≅ Modules.tensor B A` (via `tensorIsoTensorObj` and
the braiding `β_`). -/
noncomputable def tensorBraidIso (A B : X.Modules) :
    AlgebraicGeometry.Scheme.Modules.tensor A B ≅ AlgebraicGeometry.Scheme.Modules.tensor B A :=
  AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj A B ≪≫ β_ A B ≪≫
    (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj B A).symm

/-- The commutativity isomorphism on pure tensors: `a ⊗ b ↦ b ⊗ a`. -/
theorem tensorBraidIso_hom_app_moduleTensorSection (A B : X.Modules) (U : X.Opens)
    (a : Γ(A, U)) (b : Γ(B, U)) :
    (AlgebraicGeometry.Scheme.Modules.tensorBraidIso A B).hom.app U (AlgebraicGeometry.Scheme.Modules.moduleTensorSection a b) =
      AlgebraicGeometry.Scheme.Modules.moduleTensorSection b a := by
  change (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj B A).inv.app U
    ((β_ A B).hom.app U ((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj A B).hom.app U
      (AlgebraicGeometry.Scheme.Modules.moduleTensorSection a b))) = _
  rw [tensorIsoTensorObj_hom_app_moduleTensorSection,
    AlgebraicGeometry.Scheme.Modules.braiding_app_tensorSections,
    tensorIsoTensorObj_inv_app_tensorSections]

/-- **`tensorPowAddIso` on `tensorPowSection`**: `L^{⊗(m+k)} ≅ L^{⊗m} ⊗ L^{⊗k}` sends `s^{⊗(m+k)}` to
`s^{⊗m} ⊗ s^{⊗k}`. -/
theorem tensorPowAddIso_app_top_tensorPowSection (L : X.Modules) (s : Γ(L, ⊤)) (m : ℕ) :
    ∀ k : ℕ,
    (AlgebraicGeometry.Scheme.Modules.tensorPowAddIso L m k).hom.app ⊤
        (AlgebraicGeometry.Scheme.Modules.tensorPowSection s (m + k)) =
      AlgebraicGeometry.Scheme.Modules.tensorSections
        (AlgebraicGeometry.Scheme.Modules.tensorPow L m) (AlgebraicGeometry.Scheme.Modules.tensorPow L k) ⊤
        (AlgebraicGeometry.Scheme.Modules.tensorPowSection s m)
        (AlgebraicGeometry.Scheme.Modules.tensorPowSection s k)
  | 0 => by
    refine (whiskerLeft_eqToHom_rightUnitor_inv_app (AlgebraicGeometry.Scheme.Modules.tensorPow L m)
      (show 𝟙_ X.Modules = AlgebraicGeometry.Scheme.Modules.tensorPow L 0 from
        (AlgebraicGeometry.Scheme.Modules.unit_eq_tensorUnit X).symm) ⊤
      (AlgebraicGeometry.Scheme.Modules.tensorPowSection s m)).trans ?_
    rw [eqToHom_tensorPow_zero_app]
    rfl
  | k + 1 => by
    -- Notation: `P = L^{⊗m}`, `Q = L^{⊗k}`, `A = tensorPowAddIso L m k`, `ι = tensorIsoTensorObj`.
    -- `(tensorPowAddIso L m (k+1)).hom = ι.hom ≫ (A.hom ▷ L) ≫ (α_ P Q L).hom ≫ (P ◁ ι.inv)` (by definition).
    have e1 := tensorIsoTensorObj_hom_app_moduleTensorSection
      (AlgebraicGeometry.Scheme.Modules.tensorPow L (m + k)) L ⊤
      (AlgebraicGeometry.Scheme.Modules.tensorPowSection s (m + k)) s
    have e2 := whiskerRight_app_tensorSections
      (AlgebraicGeometry.Scheme.Modules.tensorPowAddIso L m k).hom L ⊤
      (AlgebraicGeometry.Scheme.Modules.tensorPowSection s (m + k)) s
    have e3 := tensorPowAddIso_app_top_tensorPowSection L s m k
    have e4 := AlgebraicGeometry.Scheme.Modules.associator_app_tensorSections
      (AlgebraicGeometry.Scheme.Modules.tensorPow L m) (AlgebraicGeometry.Scheme.Modules.tensorPow L k) L ⊤
      (AlgebraicGeometry.Scheme.Modules.tensorPowSection s m)
      (AlgebraicGeometry.Scheme.Modules.tensorPowSection s k) s
    have e5 := whiskerLeft_app_tensorSections (AlgebraicGeometry.Scheme.Modules.tensorPow L m)
      (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj
        (AlgebraicGeometry.Scheme.Modules.tensorPow L k) L).inv ⊤
      (AlgebraicGeometry.Scheme.Modules.tensorPowSection s m)
      (AlgebraicGeometry.Scheme.Modules.tensorSections
        (AlgebraicGeometry.Scheme.Modules.tensorPow L k) L ⊤
        (AlgebraicGeometry.Scheme.Modules.tensorPowSection s k) s)
    have e6 := tensorIsoTensorObj_inv_app_tensorSections
      (AlgebraicGeometry.Scheme.Modules.tensorPow L k) L ⊤
      (AlgebraicGeometry.Scheme.Modules.tensorPowSection s k) s
    -- rewrite step by step
    let F3 := ((AlgebraicGeometry.Scheme.Modules.tensorPow L m) ◁
      (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj
        (AlgebraicGeometry.Scheme.Modules.tensorPow L k) L).inv).app ⊤
    let F2 := (α_ (AlgebraicGeometry.Scheme.Modules.tensorPow L m)
      (AlgebraicGeometry.Scheme.Modules.tensorPow L k) L).hom.app ⊤
    let F1 := ((AlgebraicGeometry.Scheme.Modules.tensorPowAddIso L m k).hom ▷ L).app ⊤
    refine Eq.trans (congrArg (fun y => F3 (F2 (F1 y))) e1) ?_
    refine Eq.trans (congrArg (fun y => F3 (F2 y)) e2) ?_
    refine Eq.trans (congrArg (fun z => F3 (F2 (AlgebraicGeometry.Scheme.Modules.tensorSections
      (AlgebraicGeometry.Scheme.Modules.tensorPow L m ⊗ AlgebraicGeometry.Scheme.Modules.tensorPow L k) L ⊤
      z s))) e3) ?_
    refine Eq.trans (congrArg F3 e4) ?_
    refine Eq.trans e5 ?_
    exact congrArg (AlgebraicGeometry.Scheme.Modules.tensorSections
      (AlgebraicGeometry.Scheme.Modules.tensorPow L m)
      (AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.Modules.tensorPow L k) L) ⊤
      (AlgebraicGeometry.Scheme.Modules.tensorPowSection s m)) e6

/-- The inverse of `tensorPowAddIso` on section pairings: `s^{⊗m} ⊗ s^{⊗k} ↦ s^{⊗(m+k)}`. -/
theorem tensorPowAddIso_inv_app_top_tensorSections (L : X.Modules) (s : Γ(L, ⊤)) (m k : ℕ) :
    (AlgebraicGeometry.Scheme.Modules.tensorPowAddIso L m k).inv.app ⊤
        (AlgebraicGeometry.Scheme.Modules.tensorSections
          (AlgebraicGeometry.Scheme.Modules.tensorPow L m) (AlgebraicGeometry.Scheme.Modules.tensorPow L k) ⊤
          (AlgebraicGeometry.Scheme.Modules.tensorPowSection s m)
          (AlgebraicGeometry.Scheme.Modules.tensorPowSection s k)) =
      AlgebraicGeometry.Scheme.Modules.tensorPowSection s (m + k) := by
  rw [← tensorPowAddIso_app_top_tensorPowSection L s m k]
  have h := congrArg (fun φ : AlgebraicGeometry.Scheme.Modules.tensorPow L (m + k) ⟶ _ =>
      φ.app ⊤ (AlgebraicGeometry.Scheme.Modules.tensorPowSection s (m + k)))
    (AlgebraicGeometry.Scheme.Modules.tensorPowAddIso L m k).hom_inv_id
  exact h

/-- **`tensorPowMulIso` on `tensorPowSection`**: `(L^{⊗k})^{⊗n} ≅ L^{⊗(k·n)}` sends `(s^{⊗k})^{⊗n}` to
`s^{⊗(k·n)}`. -/
theorem tensorPowMulIso_app_top_tensorPowSection (L : X.Modules) (s : Γ(L, ⊤)) (k : ℕ) :
    ∀ n : ℕ,
    (AlgebraicGeometry.Scheme.Modules.tensorPowMulIso L k n).hom.app ⊤
        (AlgebraicGeometry.Scheme.Modules.tensorPowSection
          (AlgebraicGeometry.Scheme.Modules.tensorPowSection s k) n) =
      AlgebraicGeometry.Scheme.Modules.tensorPowSection s (k * n)
  | 0 => rfl
  | n + 1 => by
    -- `(tensorPowMulIso L k (n+1)).hom = ι.hom ≫ ((tensorPowMulIso L k n).hom ▷ L^{⊗k}) ≫ (tensorPowAddIso L (k n) k).inv`.
    have e1 := tensorIsoTensorObj_hom_app_moduleTensorSection
      (AlgebraicGeometry.Scheme.Modules.tensorPow (AlgebraicGeometry.Scheme.Modules.tensorPow L k) n)
      (AlgebraicGeometry.Scheme.Modules.tensorPow L k) ⊤
      (AlgebraicGeometry.Scheme.Modules.tensorPowSection
        (AlgebraicGeometry.Scheme.Modules.tensorPowSection s k) n)
      (AlgebraicGeometry.Scheme.Modules.tensorPowSection s k)
    have e2 := whiskerRight_app_tensorSections
      (AlgebraicGeometry.Scheme.Modules.tensorPowMulIso L k n).hom
      (AlgebraicGeometry.Scheme.Modules.tensorPow L k) ⊤
      (AlgebraicGeometry.Scheme.Modules.tensorPowSection
        (AlgebraicGeometry.Scheme.Modules.tensorPowSection s k) n)
      (AlgebraicGeometry.Scheme.Modules.tensorPowSection s k)
    have e3 := tensorPowMulIso_app_top_tensorPowSection L s k n
    have e4 := tensorPowAddIso_inv_app_top_tensorSections L s (k * n) k
    let F2 := (AlgebraicGeometry.Scheme.Modules.tensorPowAddIso L (k * n) k).inv.app ⊤
    let F1 := ((AlgebraicGeometry.Scheme.Modules.tensorPowMulIso L k n).hom ▷
      AlgebraicGeometry.Scheme.Modules.tensorPow L k).app ⊤
    refine Eq.trans (congrArg (fun y => F2 (F1 y)) e1) ?_
    refine Eq.trans (congrArg (fun y => F2 y) e2) ?_
    refine Eq.trans (congrArg (fun z => F2 (AlgebraicGeometry.Scheme.Modules.tensorSections
      (AlgebraicGeometry.Scheme.Modules.tensorPow L (k * n))
      (AlgebraicGeometry.Scheme.Modules.tensorPow L k) ⊤ z
      (AlgebraicGeometry.Scheme.Modules.tensorPowSection s k))) e3) ?_
    exact e4

end AlgebraicGeometry.Scheme.Modules

end
