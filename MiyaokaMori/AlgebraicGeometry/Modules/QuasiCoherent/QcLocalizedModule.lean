import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.QcSectionsBasicOpenLocalization

/-! # Sections of a quasi-coherent sheaf on a basic open as a localized module

"A quasi-coherent sheaf on an affine open commutes with localization at a basic open", stated with
Mathlib's `IsLocalizedModule`.

`QcSectionsBasicOpenLocalization` gives the two elementwise facts (surjectivity in
`exists_pow_smul_eq_map_basicOpen`, the kernel in `exists_pow_smul_eq_zero_of_map_basicOpen_eq_zero`),
but not as a Mathlib class. This module packages them, together with the third condition `map_units`,
into

`IsLocalizedModule (Submonoid.powers f) g`,

where `g : Γ(M, U) →ₗ[Γ(X,U)] Γ(M, D f)` is the restriction map and the `Γ(X,U)`-module structure on
`Γ(M, D f)` is given by the restriction ring homomorphism (`Module.compHom`).

**Interface**: the module structure and the linear map are passed as **parameters**, required only to
satisfy the two equations `hsmul` and `hg`. A caller can then use the instance it has itself
introduced with `letI`, and instance search hits directly, without any `convert` / `show`; if this
module registered its own `Module.compHom` instance, the instance in the caller's goal would be a
different term and `exact` would fail.

Uses: `affineUnit_coequifibered` in `OfGradedQCAlgebra` (piecewise, then `IsLocalizedModule.directSum`);
the field `Scheme.AffineModule.isLocalizedModule` in `SymAffineAlgebra` (needed whenever an
`AffineModule` is built from a quasi-coherent `X.Modules`).

Source: Stacks 01I8 / 01IB.
-/

set_option autoImplicit false

universe u

open CategoryTheory Opposite

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (M : X.Modules) [M.IsQuasicoherent] {U : X.Opens}

/-- **Quasi-coherent ⟹ restriction to a basic open is the localization away from `f`** (Stacks 01I8 in
`IsLocalizedModule` form).

The `Γ(X,U)`-module structure on `Γ(M, D f)` and the restriction linear map are supplied by the caller,
subject to `hsmul` (the scalar action goes through the restriction ring homomorphism) and `hg` (the
linear map is the restriction of the sheaf). -/
theorem isLocalizedModule_basicOpen (hU : IsAffineOpen U) (f : Γ(X, U))
    [Module Γ(X, U) Γ(M, X.basicOpen f)]
    (hsmul : ∀ (r : Γ(X, U)) (x : Γ(M, X.basicOpen f)),
      r • x = (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom r • x)
    (g : Γ(M, U) →ₗ[Γ(X, U)] Γ(M, X.basicOpen f))
    (hg : ∀ x, g x = M.presheaf.map (homOfLE (X.basicOpen_le f)).op x) :
    IsLocalizedModule (Submonoid.powers f) g where
  map_units := by
    have hfu : IsUnit ((X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom f) :=
      X.toRingedSpace.isUnit_res_basicOpen f
    obtain ⟨u, hu⟩ := hfu
    have key : ∀ n : ℕ,
        IsUnit (algebraMap Γ(X, U) (Module.End Γ(X, U) Γ(M, X.basicOpen f)) (f ^ n)) := by
      intro n
      rw [Module.End.isUnit_iff]
      have hact : ∀ x : Γ(M, X.basicOpen f),
          (algebraMap Γ(X, U) (Module.End Γ(X, U) Γ(M, X.basicOpen f)) (f ^ n)) x
            = ((u : Γ(X, X.basicOpen f)) ^ n) • x := by
        intro x
        rw [Module.algebraMap_end_apply, hsmul, map_pow, hu]
      refine Function.bijective_iff_has_inverse.mpr
        ⟨fun x => ((↑u⁻¹ : Γ(X, X.basicOpen f)) ^ n) • x, fun x => ?_, fun x => ?_⟩
      · simp only [hact, smul_smul, ← mul_pow, u.inv_mul, one_pow, one_smul]
      · simp only [hact, smul_smul, ← mul_pow, u.mul_inv, one_pow, one_smul]
    rintro ⟨-, n, rfl⟩
    exact key n
  surj := by
    intro y
    obtain ⟨n, t, ht⟩ := Scheme.Modules.exists_pow_smul_eq_map_basicOpen M hU f y
    refine ⟨⟨t, ⟨f ^ n, n, rfl⟩⟩, ?_⟩
    show (f ^ n : Γ(X, U)) • y = g t
    rw [hg, hsmul, map_pow]
    exact ht.symm
  exists_of_eq := by
    intro x₁ x₂ h
    have h0 : M.presheaf.map (homOfLE (X.basicOpen_le f)).op (x₁ - x₂) = 0 := by
      rw [map_sub, ← hg, ← hg, h, sub_self]
    obtain ⟨n, hn⟩ :=
      Scheme.Modules.exists_pow_smul_eq_zero_of_map_basicOpen_eq_zero M hU f (x₁ - x₂) h0
    refine ⟨⟨f ^ n, n, rfl⟩, ?_⟩
    show (f ^ n : Γ(X, U)) • x₁ = (f ^ n : Γ(X, U)) • x₂
    exact sub_eq_zero.mp ((smul_sub (f ^ n) x₁ x₂).symm.trans hn)

end AlgebraicGeometry.Scheme.Modules

end
