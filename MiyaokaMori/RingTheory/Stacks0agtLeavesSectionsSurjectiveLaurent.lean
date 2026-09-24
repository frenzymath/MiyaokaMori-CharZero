import MiyaokaMori.Prelude

/-! # Laurent splitting on two charts: the pure algebra behind the two-chart Čech computation

Setting (the two affine charts `U₁ = Spec B₁`, `U₂ = Spec B₂` of a scheme over `Spec A`, with
affine overlap `U₁₂ = Spec C`): ring maps `φ₁ : A → B₁`, `φ₂ : A → B₂` (structure maps) and
`r₁ : B₁ → C`, `r₂ : B₂ → C` (restrictions) with `r₁ ∘ φ₁ = r₂ ∘ φ₂`.

* `exists_eq_add_of_localization_of_eval₂_surjective` (**Laurent splitting**): if `B₁ = A[u]`
  (every element is a polynomial in `u` over `φ₁(A)`), `C` is generated over `r₁(B₁)` by `1/r₁(u)`
  (every `z ∈ C` satisfies `z · r₁(u)ⁿ ∈ r₁(B₁)` for some `n`) and `r₁(u) · r₂(v) = 1` for some
  `v ∈ B₂`, then `C = r₁(B₁) + r₂(B₂)`. (`A[u, u⁻¹] = A[u] + A[u⁻¹]`: a Laurent polynomial
  `Σ aₖ uᵏ`, `k ∈ ℤ`, splits into its parts with `k ≥ 0` and `k < 0`.)
* `exists_mem_map_add_of_forall_exists_eq_add` (**Čech `H¹` of `I·O_X` vanishes**): if
  `C = r₁(B₁) + r₂(B₂)` then `I·C = r₁(I·B₁) + r₂(I·B₂)` for every ideal `I ⊆ A`, i.e. every
  element of `I.map (r₁ ∘ φ₁)` is `r₁ c₁ + r₂ c₂` with `c₁ ∈ I.map φ₁`, `c₂ ∈ I.map φ₂`.

Source: Stacks 0AGS(3) / 0AGT proof, second paragraph, in Čech form (surjectivity of the
sections of the blowup onto the quotient families); Hartshorne III.4 (Čech cohomology for a
two-element affine cover).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

open Polynomial

namespace MiyaokaMori.LaurentSplitting

variable {A B₁ B₂ C : Type*} [CommRing A] [CommRing B₁] [CommRing B₂] [CommRing C]

/-- **Laurent splitting.** With `r₁ ∘ φ₁ = r₂ ∘ φ₂`, `r₁ u · r₂ v = 1`, `B₁` generated over
`φ₁(A)` by `u` and `C` generated over `r₁(B₁)` by `r₁(u)⁻¹`, every `z ∈ C` is `r₁ b₁ + r₂ b₂`.

Proof: `z = r₁(b) · r₂(v)ⁿ` with `b = Σ φ₁(aᵢ) uⁱ`; the term `r₁(φ₁ aᵢ) · r₁(u)ⁱ · r₂(v)ⁿ` equals
`r₁(φ₁ aᵢ · u^(i-n))` if `i ≥ n` and `r₂(φ₂ aᵢ · v^(n-i))` if `i < n`, using `r₁ u · r₂ v = 1`. -/
theorem exists_eq_add_of_localization_of_eval₂_surjective
    (φ₁ : A →+* B₁) (φ₂ : A →+* B₂) (r₁ : B₁ →+* C) (r₂ : B₂ →+* C)
    (hφ : r₁.comp φ₁ = r₂.comp φ₂) (u : B₁) (v : B₂) (huv : r₁ u * r₂ v = 1)
    (hgen : ∀ b : B₁, ∃ p : A[X], p.eval₂ φ₁ u = b)
    (hloc : ∀ z : C, ∃ (b : B₁) (n : ℕ), z * r₁ u ^ n = r₁ b) (z : C) :
    ∃ (b₁ : B₁) (b₂ : B₂), z = r₁ b₁ + r₂ b₂ := by
  obtain ⟨b, n, hb⟩ := hloc z
  obtain ⟨p, rfl⟩ := hgen b
  have hz : z = r₁ (p.eval₂ φ₁ u) * r₂ v ^ n := by
    rw [← hb, mul_assoc, ← mul_pow, huv, one_pow, mul_one]
  let S : AddSubmonoid C :=
    { carrier := {z | ∃ (b₁ : B₁) (b₂ : B₂), z = r₁ b₁ + r₂ b₂}
      zero_mem' := ⟨0, 0, by simp⟩
      add_mem' := by
        rintro _ _ ⟨a₁, a₂, rfl⟩ ⟨b₁, b₂, rfl⟩
        exact ⟨a₁ + b₁, a₂ + b₂, by rw [map_add, map_add]; ring⟩ }
  have hmul : ∀ (a : A) (w : C), w ∈ S → r₁ (φ₁ a) * w ∈ S := by
    rintro a _ ⟨b₁, b₂, rfl⟩
    refine ⟨φ₁ a * b₁, φ₂ a * b₂, ?_⟩
    rw [map_mul, map_mul, mul_add, ← RingHom.comp_apply r₁ φ₁, hφ, RingHom.comp_apply]
  have key : ∀ i : ℕ, r₁ u ^ i * r₂ v ^ n ∈ S := by
    intro i
    rcases le_or_gt n i with hni | hin
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hni
      refine ⟨u ^ k, 0, ?_⟩
      rw [map_zero, add_zero, pow_add, mul_right_comm, ← mul_pow, huv, one_pow, one_mul, map_pow]
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hin.le
      refine ⟨0, v ^ k, ?_⟩
      rw [map_zero, zero_add, pow_add, ← mul_assoc, ← mul_pow, huv, one_pow, one_mul, map_pow]
  suffices hS : z ∈ S by
    obtain ⟨b₁, b₂, hz'⟩ := hS
    exact ⟨b₁, b₂, hz'⟩
  rw [hz, Polynomial.eval₂_eq_sum_range, map_sum, Finset.sum_mul]
  refine AddSubmonoid.sum_mem _ fun i _ => ?_
  rw [map_mul, map_pow, mul_assoc]
  exact hmul _ _ (key i)

/-- **`I·C = r₁(I·B₁) + r₂(I·B₂)` when `C = r₁(B₁) + r₂(B₂)`.** Proof: as `A`-submodules of `C`
(via `r₁ ∘ φ₁`), `I·C = I • ⊤ = I • (range r₁ ⊔ range r₂) = I • range r₁ ⊔ I • range r₂ =
map r₁ (I • ⊤) ⊔ map r₂ (I • ⊤)` (`Ideal.smul_top_eq_map`, `Submodule.smul_sup`,
`Submodule.map_smul''`). -/
theorem exists_mem_map_add_of_forall_exists_eq_add
    (φ₁ : A →+* B₁) (φ₂ : A →+* B₂) (r₁ : B₁ →+* C) (r₂ : B₂ →+* C)
    (hφ : r₁.comp φ₁ = r₂.comp φ₂)
    (hsum : ∀ z : C, ∃ (b₁ : B₁) (b₂ : B₂), z = r₁ b₁ + r₂ b₂) (I : Ideal A) (z : C)
    (hz : z ∈ I.map (r₁.comp φ₁)) :
    ∃ c₁ ∈ I.map φ₁, ∃ c₂ ∈ I.map φ₂, z = r₁ c₁ + r₂ c₂ := by
  let _ : Algebra A B₁ := φ₁.toAlgebra
  let _ : Algebra A B₂ := φ₂.toAlgebra
  let _ : Algebra A C := (r₁.comp φ₁).toAlgebra
  let ρ₁ : B₁ →ₗ[A] C :=
    { toFun := r₁
      map_add' := map_add r₁
      map_smul' := fun a b => by
        simp only [Algebra.smul_def, RingHom.algebraMap_toAlgebra, map_mul, RingHom.comp_apply,
          RingHom.id_apply] }
  let ρ₂ : B₂ →ₗ[A] C :=
    { toFun := r₂
      map_add' := map_add r₂
      map_smul' := fun a b => by
        simp only [Algebra.smul_def, RingHom.algebraMap_toAlgebra, map_mul, RingHom.id_apply]
        rw [hφ, RingHom.comp_apply] }
  have htop : (⊤ : Submodule A C) ≤ LinearMap.range ρ₁ ⊔ LinearMap.range ρ₂ := by
    intro w _
    obtain ⟨b₁, b₂, rfl⟩ := hsum w
    exact Submodule.add_mem _ (Submodule.mem_sup_left ⟨b₁, rfl⟩)
      (Submodule.mem_sup_right ⟨b₂, rfl⟩)
  have hz' : z ∈ Submodule.map ρ₁ (I • (⊤ : Submodule A B₁)) ⊔
      Submodule.map ρ₂ (I • (⊤ : Submodule A B₂)) := by
    rw [Submodule.map_smul'', Submodule.map_smul'', Submodule.map_top, Submodule.map_top,
      ← Submodule.smul_sup]
    refine smul_mono_right I htop ?_
    rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem]
    exact hz
  obtain ⟨z₁, hz₁, z₂, hz₂, rfl⟩ := Submodule.mem_sup.1 hz'
  obtain ⟨c₁, hc₁, rfl⟩ := Submodule.mem_map.1 hz₁
  obtain ⟨c₂, hc₂, rfl⟩ := Submodule.mem_map.1 hz₂
  rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem, RingHom.algebraMap_toAlgebra] at hc₁ hc₂
  exact ⟨c₁, hc₁, c₂, hc₂, rfl⟩

end MiyaokaMori.LaurentSplitting
