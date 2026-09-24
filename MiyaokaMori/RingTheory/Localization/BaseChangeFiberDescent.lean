import MiyaokaMori.Prelude

/-! # Descent of the fibre along a local homomorphism

Let `φ : A → B` be a local homomorphism of local rings, `M` an `A`-module and `m ∈ M`. If the extended
element `1 ⊗ m` lies in `𝔪_B·(B ⊗_A M)`, then `m` already lies in `𝔪_A·M`. (That is, "taking the fibre"
along a local homomorphism is faithful: `M ⊗ κ(A) → (B ⊗_A M) ⊗ κ(B)` is injective.)

Proof:
1. By contradiction: if `m ∉ 𝔪_A·M`, the image `w` of `m` in the `κ(A)`-vector space `W := M ⧸ 𝔪_A·M` is
   nonzero.
2. `κ(B)` becomes a `κ(A)`-vector space via `IsLocalRing.ResidueField.map φ` (this uses that `φ` is local).
   Mathlib's `LinearMap.exists_extend_of_notMem` for vector spaces (subspace `⊥`, functional `0`, prescribing
   `w ↦ 1`) gives a `κ(A)`-linear `λ : W → κ(B)` with `λ w = 1`.
3. The composite `g : M → W → κ(B)` is `A`-linear (`A` acts on `κ(B)` through `residue_B ∘ φ`; use
   `ResidueField.map_residue`) and vanishes on `𝔪_A·M`. Extending scalars gives a `B`-linear
   `G : B ⊗_A M → κ(B)`, `G(b ⊗ x) = b·g(x)` (`TensorProduct.AlgebraTensorModule.lift`).
4. `G` sends `𝔪_B·(B ⊗_A M)` to `0` (`𝔪_B` acts as zero on `κ(B)`, `Submodule.smul_induction_on`), while
   `G(1 ⊗ m) = g m = λ w = 1 ≠ 0`, contradicting the assumption.

Reference: elementary (comparison of fibres along a field extension; the Nakayama-type facts for local rings
in Matsumura). Used to show that a pulled-back section is nonzero at a point.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open scoped TensorProduct

namespace MiyaokaMori.BaseChangeFiberDescent

universe u

/-- Extending scalars along a local homomorphism does not create new elements in the maximal-ideal multiples:
`1 ⊗ m ∈ 𝔪_B·(B ⊗_A M) ⇒ m ∈ 𝔪_A·M`. -/
theorem mem_maximalIdeal_smul_of_one_tmul
    {A B M : Type u} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    [AddCommGroup M] [Module A M] (φ : A →+* B) [IsLocalHom φ] (m : M)
    (h : letI := φ.toAlgebra
      (1 : B) ⊗ₜ[A] m ∈
        (IsLocalRing.maximalIdeal B) • (⊤ : Submodule B (B ⊗[A] M))) :
    m ∈ (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A M) := by
  letI := φ.toAlgebra
  by_contra hm
  -- `κ(B)` as a `κ(A)`-vector space and as an `A`-algebra
  letI : Algebra (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) :=
    (IsLocalRing.ResidueField.map φ).toAlgebra
  letI : Algebra A (IsLocalRing.ResidueField B) :=
    ((IsLocalRing.residue B).comp φ).toAlgebra
  haveI : IsScalarTower A B (IsLocalRing.ResidueField B) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  -- the `κ(A)`-structure on the fibre `W = M ⧸ 𝔪_A·M`
  letI : Module (IsLocalRing.ResidueField A)
      (M ⧸ (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A M)) :=
    inferInstanceAs (Module (A ⧸ IsLocalRing.maximalIdeal A) _)
  have hne : (Submodule.Quotient.mk m :
      M ⧸ (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A M)) ∉
      (⊥ : Submodule (IsLocalRing.ResidueField A)
        (M ⧸ (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A M))) := by
    simp only [Submodule.mem_bot]
    exact fun hz ↦ hm ((Submodule.Quotient.mk_eq_zero _).mp hz)
  obtain ⟨lam, -, hlam⟩ :=
    LinearMap.exists_extend_of_notMem
      (K := IsLocalRing.ResidueField A)
      (V := M ⧸ (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A M))
      (V' := IsLocalRing.ResidueField B)
      (p := ⊥) 0 hne 1
  -- the `A`-linear functional `g : M → κ(B)`, vanishing on `𝔪_A·M`
  let g : M →ₗ[A] IsLocalRing.ResidueField B :=
    { toFun := fun x ↦ lam (Submodule.Quotient.mk x)
      map_add' := fun x y ↦ by
        simp only [Submodule.Quotient.mk_add, map_add]
      map_smul' := fun a x ↦ by
        have h1 : (Submodule.Quotient.mk (a • x) :
            M ⧸ (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A M)) =
            IsLocalRing.residue A a • Submodule.Quotient.mk x := rfl
        have h2 := lam.map_smul (IsLocalRing.residue A a)
          (Submodule.Quotient.mk x : M ⧸ (IsLocalRing.maximalIdeal A) • (⊤ : Submodule A M))
        show lam (Submodule.Quotient.mk (a • x)) = a • lam (Submodule.Quotient.mk x)
        rw [h1, h2]
        show IsLocalRing.ResidueField.map φ (IsLocalRing.residue A a) *
            lam (Submodule.Quotient.mk x) = _
        rw [IsLocalRing.ResidueField.map_residue]
        rfl }
  -- extend scalars to a `B`-linear `G`
  let G : (B ⊗[A] M) →ₗ[B] IsLocalRing.ResidueField B :=
    TensorProduct.AlgebraTensorModule.lift
      { toFun := fun b ↦ b • g
        map_add' := fun b c ↦ by ext x; simp [add_smul]
        map_smul' := fun b c ↦ by ext x; simp [mul_smul] }
  -- `G` sends `𝔪_B·(B ⊗_A M)` to `0`
  have hzero : G ((1 : B) ⊗ₜ[A] m) = 0 := by
    refine Submodule.smul_induction_on h ?_ ?_
    · intro r hr n _
      rw [map_smul, Algebra.smul_def]
      have : (algebraMap B (IsLocalRing.ResidueField B)) r = 0 :=
        Ideal.Quotient.eq_zero_iff_mem.mpr hr
      rw [this, zero_mul]
    · intro a b ha hb
      rw [map_add, ha, hb, add_zero]
  -- but `G(1 ⊗ m) = g m = 1`
  have hone : G ((1 : B) ⊗ₜ[A] m) = 1 := by
    show ((1 : B) • g) m = 1
    rw [LinearMap.smul_apply, one_smul]
    exact hlam
  rw [hone] at hzero
  exact one_ne_zero hzero

end MiyaokaMori.BaseChangeFiberDescent

end
