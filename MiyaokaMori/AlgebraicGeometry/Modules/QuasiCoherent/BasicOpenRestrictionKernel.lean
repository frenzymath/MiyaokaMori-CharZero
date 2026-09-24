import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.Algebra.Module.Torsion.Basic

/-!
# The restriction kernel on an affine basic open

On an affine open `V`, restriction to the actual basic open of a section `a` is
localization away from `a`. Its kernel is the existing submodule of sections
annihilated by some power of `a`, regarded as an ideal of the same section ring.
The section `a` may be zero or a zero divisor; no reduction is taken.

This is the principal-ideal case of the supported-sections calculation in Stacks
Tag 07ZP, used in the strict-transform definition of Tag 080D and in the paper's blowup
construction. Identifying the ideal with the strict-transform
closure model and proving the blowup property of Tag 080E are separate steps.
-/

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules.BasicOpenRestrictionKernel

universe u

/-- The actual restriction kernel on an affine basic open is its power-torsion ideal. -/
theorem ker_restriction_eq_powerTorsion
    (X : Scheme.{u}) (V : X.affineOpens) (a : Γ(X, V))
    (W : X.Opens) (hWV : W ≤ V.1) (hW : W = X.basicOpen a) :
    RingHom.ker (X.presheaf.map (CategoryTheory.homOfLE hWV).op).hom =
      (Submodule.torsion' Γ(X, V) Γ(X, V) ↥(Submonoid.powers a) : Ideal Γ(X, V)) := by
  let : Algebra Γ(X, V) Γ(X, W) := (X.presheaf.map (CategoryTheory.homOfLE hWV).op).hom.toAlgebra
  have : IsLocalization.Away a Γ(X, W) :=
    V.2.isLocalization_of_eq_basicOpen a (CategoryTheory.homOfLE hWV) hW
  ext s
  change algebraMap Γ(X, V) Γ(X, W) s = 0 ↔
    ∃ m : Submonoid.powers a, (m : Γ(X, V)) * s = 0
  exact IsLocalization.map_eq_zero_iff (Submonoid.powers a) Γ(X, W) s

/-- A section restricts to zero on the basic open exactly when a power annihilates it. -/
theorem mem_ker_restriction_iff_pow_mul_eq_zero
    (X : Scheme.{u}) (V : X.affineOpens) (a : Γ(X, V))
    (W : X.Opens) (hWV : W ≤ V.1) (hW : W = X.basicOpen a) (s : Γ(X, V)) :
    s ∈ RingHom.ker (X.presheaf.map (CategoryTheory.homOfLE hWV).op).hom ↔
      ∃ n : ℕ, a ^ n * s = 0 := by
  rw [ker_restriction_eq_powerTorsion X V a W hWV hW]
  change (∃ m : Submonoid.powers a, (m : Γ(X, V)) * s = 0) ↔ _
  constructor
  · rintro ⟨⟨m, hm⟩, hms⟩
    obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff m a).mp hm
    exact ⟨n, hms⟩
  · rintro ⟨n, hn⟩
    exact ⟨⟨a ^ n, (Submonoid.mem_powers_iff _ a).mpr ⟨n, rfl⟩⟩, hn⟩

end AlgebraicGeometry.Scheme.Modules.BasicOpenRestrictionKernel
