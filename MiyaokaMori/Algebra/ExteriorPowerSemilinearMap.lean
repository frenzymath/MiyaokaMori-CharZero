import Mathlib.LinearAlgebra.ExteriorPower.Basic

/-!
# Exterior powers of semilinear maps

Mathlib's `exteriorPower.map` is only defined for linear maps over one ring. Stalk comparisons
(restriction to an open subscheme, germs of sections) are semilinear over a ring map, so this
file provides the exterior power of a semilinear map, its formula on wedge generators, and its
bijectivity when the map has a semilinear inverse. It also contains the generator-extension
principle `semilinear_ext_of_span` used to move inductions over wedge generators out of the
presheaf layer.

Everything is stated for variable rings and modules: no presheaf or stalk occurs, so every
`isDefEq` here is cheap (same design as `semilinear_pairing_ext`).

Sources: Stacks Project, `algebra.tex`, `lemma-colimit-tensor-algebra` (functoriality of
exterior powers under base ring change); consumers are `ExteriorPowerStalk` and
`ExteriorPowerRestrictionStalk`.
-/

noncomputable section
namespace MiyaokaMori.Algebra


theorem semilinear_ext_of_span {R S E P : Type*} [CommRing R] [CommRing S]
    [AddCommGroup E] [Module R E] [AddCommGroup P] [Module S P]
    (ρ : R →+* S) (g₁ g₂ : E → P)
    (h₁_add : ∀ x y, g₁ (x + y) = g₁ x + g₁ y) (h₁_smul : ∀ (r : R) x, g₁ (r • x) = ρ r • g₁ x)
    (h₂_add : ∀ x y, g₂ (x + y) = g₂ x + g₂ y) (h₂_smul : ∀ (r : R) x, g₂ (r • x) = ρ r • g₂ x)
    {s : Set E} (hs : Submodule.span R s = ⊤) (h : ∀ a ∈ s, g₁ a = g₂ a) (α : E) :
    g₁ α = g₂ α := by
  have h10 : g₁ 0 = 0 := by simpa using h₁_smul 0 0
  have h20 : g₂ 0 = 0 := by simpa using h₂_smul 0 0
  have hα : α ∈ Submodule.span R s := hs ▸ Submodule.mem_top
  induction hα using Submodule.span_induction with
  | mem a ha => exact h a ha
  | zero => rw [h10, h20]
  | add x y _ _ hx hy => rw [h₁_add, h₂_add, hx, hy]
  | smul r x _ hx => rw [h₁_smul, h₂_smul, hx]

variable {R S M N : Type*} [CommRing R] [CommRing S]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]

/-- The alternating map `v ↦ ⋀ (e ∘ v)` of a semilinear map, with the target regarded as an
`R`-module through the ring map. -/
def exteriorPowerMapSLAlternating (σ : R →+* S) (e : M →ₛₗ[σ] N) (n : ℕ) :
    letI : Module R (⋀[S]^n N) := Module.compHom _ σ
    M [⋀^Fin n]→ₗ[R] (⋀[S]^n N) :=
  letI : Module R (⋀[S]^n N) := Module.compHom _ σ
  { toFun := fun v ↦ exteriorPower.ιMulti S n (e ∘ v)
    map_update_add' := fun v i a b ↦ by
      simp only [Function.comp_update, map_add, AlternatingMap.map_update_add]
    map_update_smul' := fun v i r a ↦ by
      simp only [Function.comp_update, LinearMap.map_smulₛₗ, AlternatingMap.map_update_smul]
      rfl
    map_eq_zero_of_eq' := fun v i j h hij ↦
      (exteriorPower.ιMulti S n).map_eq_zero_of_eq _ (congrArg e h) hij }

/-- The exterior power of a semilinear map. -/
def exteriorPowerMapSL (σ : R →+* S) (e : M →ₛₗ[σ] N) (n : ℕ) :
    ⋀[R]^n M →ₛₗ[σ] ⋀[S]^n N :=
  letI : Module R (⋀[S]^n N) := Module.compHom _ σ
  { toFun := exteriorPower.alternatingMapLinearEquiv (exteriorPowerMapSLAlternating σ e n)
    map_add' := map_add _
    map_smul' := fun r a ↦
      (exteriorPower.alternatingMapLinearEquiv (exteriorPowerMapSLAlternating σ e n)).map_smul r a }

@[simp]
theorem exteriorPowerMapSL_ιMulti (σ : R →+* S) (e : M →ₛₗ[σ] N) (n : ℕ) (v : Fin n → M) :
    exteriorPowerMapSL σ e n (exteriorPower.ιMulti R n v) =
      exteriorPower.ιMulti S n (e ∘ v) :=
  letI : Module R (⋀[S]^n N) := Module.compHom _ σ
  exteriorPower.alternatingMapLinearEquiv_apply_ιMulti (exteriorPowerMapSLAlternating σ e n) v

theorem exteriorPowerMapSL_leftInverse (σ : R →+* S) (τ : S →+* R) (hτσ : ∀ r, τ (σ r) = r)
    (e : M →ₛₗ[σ] N) (e' : N →ₛₗ[τ] M) (h : ∀ m, e' (e m) = m) (n : ℕ) (a : ⋀[R]^n M) :
    exteriorPowerMapSL τ e' n (exteriorPowerMapSL σ e n a) = a := by
  refine semilinear_ext_of_span (RingHom.id R)
    (fun a ↦ exteriorPowerMapSL τ e' n (exteriorPowerMapSL σ e n a)) (fun a ↦ a)
    (fun x y ↦ by simp only [map_add]) (fun r x ↦ by
      simp only [LinearMap.map_smulₛₗ, hτσ, RingHom.id_apply])
    (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) (exteriorPower.ιMulti_span R n M) ?_ a
  rintro _ ⟨v, rfl⟩
  simp only [exteriorPowerMapSL_ιMulti]
  exact congrArg _ (funext fun i ↦ h (v i))

/-- The exterior power of a semilinear bijection with a semilinear inverse is bijective. -/
theorem exteriorPowerMapSL_bijective (σ : R →+* S) (τ : S →+* R)
    (hτσ : ∀ r, τ (σ r) = r) (hστ : ∀ s, σ (τ s) = s)
    (e : M →ₛₗ[σ] N) (e' : N →ₛₗ[τ] M) (h₁ : ∀ m, e' (e m) = m) (h₂ : ∀ y, e (e' y) = y)
    (n : ℕ) : Function.Bijective (exteriorPowerMapSL σ e n) :=
  Function.bijective_iff_has_inverse.mpr ⟨exteriorPowerMapSL τ e' n,
    exteriorPowerMapSL_leftInverse σ τ hτσ e e' h₁ n,
    exteriorPowerMapSL_leftInverse τ σ hστ e' e h₂ n⟩

end MiyaokaMori.Algebra
