import Mathlib.LinearAlgebra.ExteriorPower.Basic

namespace MiyaokaMori.Algebra

universe u v w

/-- The exterior-power map preserves bijectivity for every degree, including degree zero. -/
theorem exteriorPower_map_bijective {R : Type u} [CommRing R]
    {M : Type v} {N : Type w} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (n : ℕ) (g : M →ₗ[R] N)
    (hg : Function.Bijective g) :
    Function.Bijective (exteriorPower.map n g) := by
  let e : M ≃ₗ[R] N := LinearEquiv.ofBijective g hg
  have he : e.toLinearMap = g := by
    ext x
    exact LinearEquiv.ofBijective_apply g x
  have hleft : e.symm.toLinearMap ∘ₗ g = LinearMap.id := by
    apply LinearMap.ext
    intro x
    change e.symm (g x) = x
    rw [← he]
    exact e.symm_apply_apply x
  exact ⟨exteriorPower.map_injective e.symm.toLinearMap hleft,
    exteriorPower.map_surjective hg.2⟩

end MiyaokaMori.Algebra
