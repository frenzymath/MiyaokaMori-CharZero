import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle

/-! # Constants on a scheme-theoretic fibre, and "two trivializations differ by a unit"

Glue for the coordinate computation of the `ξ`-monomials on a fibre of a total space.

* `Scheme.Hom.fiberResidueConstants f y : κ(y) →+* Γ(f.fiber y, O)`: the constants on the fiber, i.e. the
  structure map `f.fiberToSpecResidueField y : f.fiber y → Spec κ(y)` on global sections (composed with
  Mathlib's `ΓSpecIso : Γ(Spec κ(y), O) ≅ κ(y)`).
* `Modules.unitSectionAsFunction`: a global section of `O_X` as a module, read as a function in `Γ(X, ⊤)`
  (definitionally the identity; it only fixes the elaborated type so that `*`, `^`, `1` are found).
* `Modules.exists_isUnit_app_top_eq_mul`: two trivializations `τ, τ' : N ≅ O_X` of a module differ on
  global sections by a unit `u ∈ Γ(X, O)`: `τ(s) = u · τ'(s)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The constants on the scheme-theoretic fiber `f.fiber y`: the ring homomorphism
`κ(y) → Γ(f.fiber y, O)` given by the structure map `f.fiberToSpecResidueField y : f.fiber y → Spec κ(y)`
on global sections (composed with `ΓSpecIso : Γ(Spec κ(y), O) ≅ κ(y)`). -/
def AlgebraicGeometry.Scheme.Hom.fiberResidueConstants {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
    (y : Y) : (Y.residueField y : Type u) →+* Γ(f.fiber y, ⊤) :=
  ((AlgebraicGeometry.Scheme.ΓSpecIso (Y.residueField y)).inv ≫ (f.fiberToSpecResidueField y).appTop).hom

/-- A global section of the structure sheaf regarded as a module (`SheafOfModules.unit X.ringCatSheaf`),
read as a function in `Γ(X, ⊤)`. Definitionally the identity (the two types are the same carrier); it only
fixes the elaborated type, so that `*`, `^` and `1` are found (on `Γ(SheafOfModules.unit _, ⊤)` the scalar
ring is spelled `X.ringCatSheaf.obj.obj _`, and `*` between it and `Γ(X, ⊤)` does not elaborate). -/
def AlgebraicGeometry.Scheme.Modules.unitSectionAsFunction {X : AlgebraicGeometry.Scheme.{u}}
    (z : Γ(SheafOfModules.unit X.ringCatSheaf, ⊤)) : Γ(X, ⊤) := z

/-- **Two trivializations of a line bundle differ by a unit.** For `τ τ' : N ≅ O_X` there is a unit
`u ∈ Γ(X, O)` with `τ(s) = u · τ'(s)` on global sections. Proof: `α := τ'⁻¹ ≫ τ : O_X → O_X` is `O_X`-linear,
so `α(x) = α(x · 1) = x · α(1)` (`Hom.app_smul`); `u := α(1)` is a unit because `β := τ⁻¹ ≫ τ'` satisfies
`α ≫ β = 𝟙`, so `1 = β(α(1)) = α(1) · β(1)`; and `τ(s) = α(τ'(s)) = τ'(s) · u`. -/
theorem AlgebraicGeometry.Scheme.Modules.exists_isUnit_app_top_eq_mul {X : AlgebraicGeometry.Scheme.{u}}
    {N : X.Modules} (τ τ' : N ≅ SheafOfModules.unit X.ringCatSheaf) :
    ∃ u : Γ(X, ⊤), IsUnit u ∧ ∀ s : Γ(N, ⊤),
      AlgebraicGeometry.Scheme.Modules.unitSectionAsFunction (τ.hom.app ⊤ s) =
        u * AlgebraicGeometry.Scheme.Modules.unitSectionAsFunction (τ'.hom.app ⊤ s) := by
  let uS := @AlgebraicGeometry.Scheme.Modules.unitSectionAsFunction X
  let α := τ'.inv ≫ τ.hom
  let β := τ.inv ≫ τ'.hom
  have hα : ∀ x : Γ(X, ⊤), uS (α.app ⊤ x) = x * uS (α.app ⊤ (1 : Γ(X, ⊤))) := fun x =>
    (congrArg (fun z : Γ(X, ⊤) => uS (α.app ⊤ z)) (mul_one x).symm).trans
      (congrArg uS (AlgebraicGeometry.Scheme.Modules.Hom.app_smul α x (1 : Γ(X, ⊤))))
  have hβ : ∀ x : Γ(X, ⊤), uS (β.app ⊤ x) = x * uS (β.app ⊤ (1 : Γ(X, ⊤))) := fun x =>
    (congrArg (fun z : Γ(X, ⊤) => uS (β.app ⊤ z)) (mul_one x).symm).trans
      (congrArg uS (AlgebraicGeometry.Scheme.Modules.Hom.app_smul β x (1 : Γ(X, ⊤))))
  have hαβ : α ≫ β = 𝟙 _ :=
    calc α ≫ β = τ'.inv ≫ (τ.hom ≫ τ.inv ≫ τ'.hom) := Category.assoc _ _ _
      _ = τ'.inv ≫ τ'.hom := congrArg (fun g => τ'.inv ≫ g) (Iso.hom_inv_id_assoc τ τ'.hom)
      _ = 𝟙 _ := Iso.inv_hom_id τ'
  have hone : uS (α.app ⊤ (1 : Γ(X, ⊤))) * uS (β.app ⊤ (1 : Γ(X, ⊤))) = 1 := by
    have h1 : uS (β.app ⊤ (α.app ⊤ (1 : Γ(X, ⊤)))) = uS ((α ≫ β).app ⊤ (1 : Γ(X, ⊤))) := rfl
    have h2 : uS ((α ≫ β).app ⊤ (1 : Γ(X, ⊤))) = 1 := by
      have h := congrArg (fun ψ => uS (ψ.app ⊤ (1 : Γ(X, ⊤)))) hαβ
      exact h
    exact (hβ _).symm.trans (h1.trans h2)
  refine ⟨uS (α.app ⊤ (1 : Γ(X, ⊤))),
    isUnit_iff_exists.mpr ⟨uS (β.app ⊤ (1 : Γ(X, ⊤))), hone, (mul_comm _ _).trans hone⟩, fun s => ?_⟩
  have h : uS (α.app ⊤ (τ'.hom.app ⊤ s)) = uS (τ.hom.app ⊤ s) :=
    congrArg (fun g : N ⟶ SheafOfModules.unit X.ringCatSheaf => uS (g.app ⊤ s)) (Iso.hom_inv_id_assoc τ' τ.hom)
  exact h.symm.trans ((hα (uS (τ'.hom.app ⊤ s))).trans (mul_comm _ _))

end
