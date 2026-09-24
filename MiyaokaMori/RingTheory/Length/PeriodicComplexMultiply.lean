import MiyaokaMori.RingTheory.Length.PeriodicComplexLength

/-! # Multiplying one differential of a periodic complex by an endomorphism

Let `R` be a ring, `(M, N, φ, ψ)` a `2`-periodic complex, `I = Im φ ⊂ N`, and `χ : N → N` linear with
`χ(I) ⊂ I` (e.g. `R` commutative and `χ` = multiplication by `x`). Then `(M, N, χφ, ψ)` is again a complex,
and unconditionally in `ℕ∞`
  `l H⁰(χφ, ψ) = l H⁰(φ, ψ) + l Ker(χ|I)`,  `l H¹(χφ, ψ) = l H¹(φ, ψ) + l Coker(χ|I)`.
Hence, as soon as the cohomology of `(φ, ψ)` and `Ker(χ|I)`, `Coker(χ|I)` have finite length, Stacks 0EAC
holds: `e(M, χφ, ψ) = e(M, φ, ψ) − e(I, 0, χ|I)`, and symmetrically
`e(M, φ, χψ) = e(M, φ, ψ) + e(Im ψ, 0, χ|Im ψ)`. (This is more general than Stacks 0EAC: no need for `R`
Noetherian local, `M` finite, `dim Supp(M/xM) ≤ 0`, nor for the reduction to the `x`-power-torsion-free
case.)

Proof:
1. `H¹`: the chain `χI ≤ I ≤ Ker ψ` and additivity of relative lengths along chains
   (`PeriodicComplexLength`) give `l(Ker ψ/χI) = l(I/χI) + l(Ker ψ/I)`, and `l(I/χI) = l Coker(χ|I)`.
2. `H⁰`: the chain `Im ψ ≤ Ker φ ≤ Ker(χφ) = φ⁻¹(Ker χ)`, and
   `l(φ⁻¹(Ker χ)/φ⁻¹(0)) = l(Ker χ ∩ I)` (the `comap` formula) `= l Ker(χ|I)`.
3. The formula for `e`: take `toNat` of 1 and 2 and subtract; `e(I, 0, χ|I) = l Coker − l Ker`
   (`herbrand_zero_left`). The second formula follows by exchanging `φ` and `ψ`.

Reference: Stacks 0EAC (chow-lemma-multiply-period-length); a direct lattice argument replacing the torsion
reduction of the original.
-/

set_option autoImplicit false

open Submodule

namespace PeriodicComplex

variable {R : Type*} [Ring R]
variable {M : Type*} [AddCommGroup M] [Module R M] {N : Type*} [AddCommGroup N] [Module R N]

/-- The restriction of `χ` to `I = Im φ`. -/
abbrev restrictRange (φ : M →ₗ[R] N) (χ : N →ₗ[R] N)
    (hχ : LinearMap.range φ ≤ (LinearMap.range φ).comap χ) :
    ↥(LinearMap.range φ) →ₗ[R] ↥(LinearMap.range φ) := χ.restrict hχ

variable (φ : M →ₗ[R] N) (ψ : N →ₗ[R] M) (χ : N →ₗ[R] N)

theorem length_H_comp_left (hφψ : φ ∘ₗ ψ = 0)
    (hχ : LinearMap.range φ ≤ (LinearMap.range φ).comap χ) :
    Module.length R (H (χ ∘ₗ φ) ψ) =
      Module.length R (H φ ψ) + Module.length R (LinearMap.ker (restrictRange φ χ hχ)) := by
  have hle : LinearMap.range ψ ≤ LinearMap.ker φ := LinearMap.range_le_ker_iff.mpr hφψ
  have hle2 : LinearMap.ker φ ≤ LinearMap.ker (χ ∘ₗ φ) := LinearMap.ker_le_ker_comp φ χ
  rw [length_H, length_H, relLength_add hle hle2]
  congr 1
  have e0 : LinearMap.ker φ = (⊥ : Submodule R N).comap φ := rfl
  rw [LinearMap.ker_comp, e0, relLength_comap φ bot_le, bot_inf_eq, ← relLength_bot,
    ← relLength_map_of_injective (LinearMap.range φ).subtype (Submodule.subtype_injective _) bot_le,
    Submodule.map_bot]
  congr 1
  rw [LinearMap.ker_restrict, Submodule.map_comap_eq, Submodule.range_subtype, inf_comm]

theorem length_H_comp_right (hψφ : ψ ∘ₗ φ = 0)
    (hχ : LinearMap.range φ ≤ (LinearMap.range φ).comap χ) :
    Module.length R (H ψ (χ ∘ₗ φ)) =
      Module.length R (H ψ φ) +
        Module.length R (↥(LinearMap.range φ) ⧸ LinearMap.range (restrictRange φ χ hχ)) := by
  have hle : LinearMap.range φ ≤ LinearMap.ker ψ := LinearMap.range_le_ker_iff.mpr hψφ
  have hle1 : LinearMap.range (χ ∘ₗ φ) ≤ LinearMap.range φ := by
    rw [LinearMap.range_comp]; exact Submodule.map_le_iff_le_comap.mpr hχ
  rw [length_H, length_H, relLength_add hle1 hle, add_comm]
  congr 1
  refine (length_eq_relLength (LinearMap.range (restrictRange φ χ hχ)).mkQ
    (Submodule.mkQ_surjective _) ?_).symm
  rw [Submodule.ker_mkQ]
  ext y
  simp only [LinearMap.mem_range, Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply,
    LinearMap.comp_apply]
  constructor
  · rintro ⟨z, rfl⟩
    obtain ⟨m, hm⟩ := z.2
    exact ⟨m, by rw [hm]; rfl⟩
  · rintro ⟨m, hm⟩
    exact ⟨⟨φ m, m, rfl⟩, Subtype.ext hm⟩

theorem comp_left_isComplex (hφψ : φ ∘ₗ ψ = 0) : (χ ∘ₗ φ) ∘ₗ ψ = 0 := by
  rw [LinearMap.comp_assoc, hφψ, LinearMap.comp_zero]

theorem comp_left_isComplex' (hψφ : ψ ∘ₗ φ = 0)
    (hχ : LinearMap.range φ ≤ (LinearMap.range φ).comap χ) : ψ ∘ₗ (χ ∘ₗ φ) = 0 := by
  ext m
  obtain ⟨m', hm'⟩ : χ (φ m) ∈ LinearMap.range φ := hχ ⟨m, rfl⟩
  rw [LinearMap.comp_apply, LinearMap.comp_apply, ← hm']
  exact LinearMap.congr_fun hψφ m'

/-- Stacks 0EAC (first formula): `e(M, χφ, ψ) = e(M, φ, ψ) − e(Im φ, 0, χ|Im φ)`. -/
theorem herbrand_comp_left (hφψ : φ ∘ₗ ψ = 0) (hψφ : ψ ∘ₗ φ = 0)
    (hχ : LinearMap.range φ ≤ (LinearMap.range φ).comap χ) (hfin : FiniteCohomology φ ψ)
    (hχfin : FiniteCohomology (0 : ↥(LinearMap.range φ) →ₗ[R] ↥(LinearMap.range φ))
      (restrictRange φ χ hχ)) :
    FiniteCohomology (χ ∘ₗ φ) ψ ∧
      herbrand (χ ∘ₗ φ) ψ = herbrand φ ψ -
        herbrand (0 : ↥(LinearMap.range φ) →ₗ[R] ↥(LinearMap.range φ)) (restrictRange φ χ hχ) := by
  have h0 := length_H_comp_left φ ψ χ hφψ hχ
  have h1 := length_H_comp_right φ ψ χ hψφ hχ
  obtain ⟨hC, hK⟩ := (finiteCohomology_zero_left_iff _).mp hχfin
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [h0]; exact WithTop.add_ne_top.mpr ⟨hfin.1, hK⟩
  · rw [h1]; exact WithTop.add_ne_top.mpr ⟨hfin.2, hC⟩
  · rw [herbrand_zero_left]
    unfold herbrand
    rw [h0, h1, ENat.toNat_add hfin.1 hK, ENat.toNat_add hfin.2 hC]
    push_cast
    ring

/-- Stacks 0EAC (second formula): `e(M, φ, χψ) = e(M, φ, ψ) + e(Im ψ, 0, χ|Im ψ)` (`χ : M → M` preserving `Im ψ`). -/
theorem herbrand_comp_right (χ' : M →ₗ[R] M) (hφψ : φ ∘ₗ ψ = 0) (hψφ : ψ ∘ₗ φ = 0)
    (hχ : LinearMap.range ψ ≤ (LinearMap.range ψ).comap χ') (hfin : FiniteCohomology φ ψ)
    (hχfin : FiniteCohomology (0 : ↥(LinearMap.range ψ) →ₗ[R] ↥(LinearMap.range ψ))
      (restrictRange ψ χ' hχ)) :
    FiniteCohomology φ (χ' ∘ₗ ψ) ∧
      herbrand φ (χ' ∘ₗ ψ) = herbrand φ ψ +
        herbrand (0 : ↥(LinearMap.range ψ) →ₗ[R] ↥(LinearMap.range ψ)) (restrictRange ψ χ' hχ) := by
  obtain ⟨h1, h2⟩ := herbrand_comp_left ψ φ χ' hψφ hφψ hχ hfin.symm hχfin
  refine ⟨h1.symm, ?_⟩
  rw [herbrand_symm, h2, herbrand_symm ψ φ]
  ring

end PeriodicComplex
