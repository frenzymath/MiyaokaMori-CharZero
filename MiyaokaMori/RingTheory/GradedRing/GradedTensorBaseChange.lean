import Mathlib.LinearAlgebra.TensorProduct.Decomposition
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.TensorProduct.Maps

/-! # Base change of a graded algebra: the ring-level core

Let `R` be a commutative ring, `A` an `R`-algebra with an internal grading `𝒜 : ℕ → Submodule R A`
(`GradedAlgebra 𝒜`), and `B` any `R`-algebra. Then `A ⊗[R] B` carries the internal grading
`tensorGrading 𝒜 B m := DirectSum.decomposeTensor 𝒜 B m` (`= ((𝒜 m).subtype.rTensor B).range`, the
image of `𝒜 m ⊗ B` in `A ⊗ B`), and:

* `GradedAlgebra (tensorGrading 𝒜 B)` (the `instance` of this file):
  - the decomposition data `DirectSum.Decomposition` are taken directly from Mathlib's
    `DirectSum.tensorDecomposition`, built from `TensorProduct.directSumLeft`
    (`(⨁ᵢMᵢ) ⊗ N ≃ ⨁ᵢ(Mᵢ ⊗ N)`), which needs no flatness of `B`;
  - `SetLike.GradedMonoid` (`1 ∈` piece `0`, piece `i` `*` piece `j` `⊆` piece `i+j`) is proved here,
    using `Algebra.TensorProduct.tmul_mul_tmul` and one `TensorProduct.induction_on`.
* Functoriality `GradedBaseChange.map φ ψ χ hψ hχ : A ⊗[R] B →+* A' ⊗[R'] B'`, where **the base ring
  may change** (`φ : R →+* R'`, `ψ : A →+* A'`, `χ : B →+* B'`, with two compatibilities with
  `algebraMap`). Uniqueness `GradedBaseChange.ringHom_ext` (equality on pure tensors suffices)
  reduces `map_id` / `map_comp` to two lines.
* `GradedBaseChange.map_mem`: if `ψ` preserves the grading, then `map` preserves `tensorGrading`.

Motivation: graded algebras are encoded as presheaves of rings on the small affine Zariski site, where
**the base ring `Γ(X,U)` differs on every affine open `U`**, so the restriction maps of the base-change
presheaf `U ↦ S(U) ⊗_{Γ(X,U)} B(U)` are tensor product maps with a change of base ring; Mathlib's
`Algebra.TensorProduct.map` requires a common base and does not apply. Both the "tensor product map with
change of base ring" and the "grading on the tensor product" are isolated here as pure algebra without
any scheme data, so that the geometric side (`AffineAlgebraBaseChange`) only has to substitute
`Γ(X,U)`, `S(U)`, `B(U)`.

Why base change rather than pullback: the pullback of a graded algebra along an arbitrary morphism
does not carry a grading in this encoding (`GradedRing.decompose'` is data, and choosing it with
`Classical.choice` would make the definition hollow). Base change makes the grading constructive: the
decomposition data of `decomposeTensor` are the explicit linear isomorphism `directSumLeft`.

Sources: Mathlib `LinearAlgebra/TensorProduct/Decomposition.lean` (`decomposeTensor`,
`tensorDecomposition`), `RingTheory/TensorProduct/Maps.lean` (`Algebra.TensorProduct.lift`).
-/

set_option autoImplicit false

universe u

open TensorProduct DirectSum

namespace GradedBaseChange

/-! ## Extensionality for ring homomorphisms out of a tensor product -/

section Ext

variable {R A B C : Type*} [CommRing R] [CommRing A] [CommRing B] [Semiring C]
  [Algebra R A] [Algebra R B]

/-- Two ring homomorphisms out of `A ⊗[R] B` that agree on pure tensors are equal. -/
theorem ringHom_ext {F G : A ⊗[R] B →+* C}
    (h : ∀ (a : A) (b : B), F (a ⊗ₜ[R] b) = G (a ⊗ₜ[R] b)) : F = G := by
  refine RingHom.ext fun x => ?_
  induction x using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul a b => exact h a b
  | add x y hx hy => rw [map_add, map_add, hx, hy]

end Ext

/-! ## The tensor product map with change of base ring -/

section Map

variable {R R' R'' A A' A'' B B' B'' : Type*}
  [CommRing R] [CommRing R'] [CommRing R''] [CommRing A] [CommRing A'] [CommRing A'']
  [CommRing B] [CommRing B'] [CommRing B'']
  [Algebra R A] [Algebra R B] [Algebra R' A'] [Algebra R' B'] [Algebra R'' A''] [Algebra R'' B'']

/-- **The tensor product map with change of base ring**: `a ⊗ b ↦ ψ a ⊗ χ b`.
`φ : R →+* R'` is the map of base rings; `hψ`, `hχ` say that `ψ`, `χ` are compatible with the structure
maps. -/
noncomputable def map (φ : R →+* R') (ψ : A →+* A') (χ : B →+* B')
    (hψ : ∀ r : R, ψ (algebraMap R A r) = algebraMap R' A' (φ r))
    (hχ : ∀ r : R, χ (algebraMap R B r) = algebraMap R' B' (φ r)) :
    A ⊗[R] B →+* A' ⊗[R'] B' :=
  letI : Algebra R (A' ⊗[R'] B') :=
    ((algebraMap R' (A' ⊗[R'] B')).comp φ).toAlgebra
  have hAlg : ∀ r : R, algebraMap R (A' ⊗[R'] B') r = algebraMap R' (A' ⊗[R'] B') (φ r) :=
    fun _ => rfl
  (Algebra.TensorProduct.lift
      ({ toFun := fun a => ψ a ⊗ₜ[R'] (1 : B')
         map_one' := by rw [map_one]; rfl
         map_mul' := fun a b => by
           rw [map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
         map_zero' := by rw [map_zero]; exact TensorProduct.zero_tmul _ _
         map_add' := fun a b => by rw [map_add]; exact TensorProduct.add_tmul _ _ _
         commutes' := fun r => by
           rw [hψ, hAlg, Algebra.TensorProduct.algebraMap_apply] } : A →ₐ[R] A' ⊗[R'] B')
      ({ toFun := fun b => (1 : A') ⊗ₜ[R'] χ b
         map_one' := by rw [map_one]; rfl
         map_mul' := fun a b => by
           rw [map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
         map_zero' := by rw [map_zero]; exact TensorProduct.tmul_zero _ _
         map_add' := fun a b => by rw [map_add]; exact TensorProduct.tmul_add _ _ _
         commutes' := fun r => by
           rw [hχ, hAlg, Algebra.TensorProduct.algebraMap_apply'] } : B →ₐ[R] A' ⊗[R'] B')
      fun _ _ => Commute.all _ _).toRingHom

@[simp] theorem map_tmul (φ : R →+* R') (ψ : A →+* A') (χ : B →+* B')
    (hψ : ∀ r : R, ψ (algebraMap R A r) = algebraMap R' A' (φ r))
    (hχ : ∀ r : R, χ (algebraMap R B r) = algebraMap R' B' (φ r)) (a : A) (b : B) :
    map φ ψ χ hψ hχ (a ⊗ₜ[R] b) = ψ a ⊗ₜ[R'] χ b := by
  show (ψ a ⊗ₜ[R'] (1 : B')) * ((1 : A') ⊗ₜ[R'] χ b) = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]

/-- The base change of the identity maps is the identity. -/
theorem map_id (h₁ : ∀ r : R, (RingHom.id A) (algebraMap R A r) = algebraMap R A ((RingHom.id R) r))
    (h₂ : ∀ r : R, (RingHom.id B) (algebraMap R B r) = algebraMap R B ((RingHom.id R) r)) :
    map (RingHom.id R) (RingHom.id A) (RingHom.id B) h₁ h₂ = RingHom.id (A ⊗[R] B) :=
  ringHom_ext fun a b => by rw [map_tmul]; rfl

/-- Base change is compatible with composition. -/
theorem map_comp (φ : R →+* R') (ψ : A →+* A') (χ : B →+* B')
    (hψ : ∀ r : R, ψ (algebraMap R A r) = algebraMap R' A' (φ r))
    (hχ : ∀ r : R, χ (algebraMap R B r) = algebraMap R' B' (φ r))
    (φ' : R' →+* R'') (ψ' : A' →+* A'') (χ' : B' →+* B'')
    (hψ' : ∀ r : R', ψ' (algebraMap R' A' r) = algebraMap R'' A'' (φ' r))
    (hχ' : ∀ r : R', χ' (algebraMap R' B' r) = algebraMap R'' B'' (φ' r))
    (hψ'' : ∀ r : R, (ψ'.comp ψ) (algebraMap R A r) = algebraMap R'' A'' ((φ'.comp φ) r))
    (hχ'' : ∀ r : R, (χ'.comp χ) (algebraMap R B r) = algebraMap R'' B'' ((φ'.comp φ) r)) :
    (map φ' ψ' χ' hψ' hχ').comp (map φ ψ χ hψ hχ) =
      map (φ'.comp φ) (ψ'.comp ψ) (χ'.comp χ) hψ'' hχ'' :=
  ringHom_ext fun a b => by
    rw [RingHom.comp_apply, map_tmul, map_tmul, map_tmul]; rfl

end Map

/-! ## The grading on the tensor product -/

section Grading

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
  (𝒜 : ℕ → Submodule R A)

/-- The `m`-th piece of `A ⊗[R] B`: the image of `𝒜 m ⊗ B` in `A ⊗ B`. -/
abbrev tensorGrading (m : ℕ) : Submodule R (A ⊗[R] B) := DirectSum.decomposeTensor 𝒜 B m

theorem mem_tensorGrading {m : ℕ} {x : A ⊗[R] B} :
    x ∈ tensorGrading 𝒜 (B := B) m ↔
      ∃ y : (𝒜 m) ⊗[R] B, ((𝒜 m).subtype.rTensor B) y = x := Iff.rfl

theorem tmul_mem_tensorGrading {m : ℕ} {a : A} (ha : a ∈ 𝒜 m) (b : B) :
    a ⊗ₜ[R] b ∈ tensorGrading 𝒜 (B := B) m :=
  (mem_tensorGrading 𝒜).2 ⟨(⟨a, ha⟩ : 𝒜 m) ⊗ₜ[R] b, by rw [LinearMap.rTensor_tmul]; rfl⟩

variable [GradedAlgebra 𝒜]

instance tensorGrading_gradedMonoid :
    SetLike.GradedMonoid (fun m => tensorGrading 𝒜 (B := B) m) where
  one_mem := by
    have h : (1 : A ⊗[R] B) = (1 : A) ⊗ₜ[R] (1 : B) := rfl
    rw [h]
    exact tmul_mem_tensorGrading 𝒜 (SetLike.GradedOne.one_mem (A := 𝒜)) 1
  mul_mem := by
    intro i j x y hx hy
    obtain ⟨u, rfl⟩ := (mem_tensorGrading 𝒜).1 hx
    obtain ⟨v, rfl⟩ := (mem_tensorGrading 𝒜).1 hy
    clear hx hy
    induction u using TensorProduct.induction_on with
    | zero => rw [map_zero, zero_mul]; exact Submodule.zero_mem _
    | add u₁ u₂ h₁ h₂ => rw [map_add, add_mul]; exact Submodule.add_mem _ h₁ h₂
    | tmul a b =>
      induction v using TensorProduct.induction_on with
      | zero => rw [map_zero, mul_zero]; exact Submodule.zero_mem _
      | add v₁ v₂ h₁ h₂ => rw [map_add, mul_add]; exact Submodule.add_mem _ h₁ h₂
      | tmul a' b' =>
        rw [LinearMap.rTensor_tmul, LinearMap.rTensor_tmul,
          Algebra.TensorProduct.tmul_mul_tmul]
        exact tmul_mem_tensorGrading 𝒜
          (SetLike.GradedMul.mul_mem (A := 𝒜) a.2 a'.2) _

/-- **The graded algebra structure on the tensor product**: the decomposition data come from Mathlib's
`DirectSum.tensorDecomposition` (built from `TensorProduct.directSumLeft`, no flatness needed), and
multiplicativity is given by the instance above. -/
noncomputable instance tensorGradedAlgebra : GradedAlgebra (fun m => tensorGrading 𝒜 (B := B) m) :=
  { tensorGrading_gradedMonoid 𝒜 (B := B), DirectSum.tensorDecomposition 𝒜 B with }

end Grading

/-! ## Base change preserves the grading -/

section MapMem

variable {R R' A A' B B' : Type*}
  [CommRing R] [CommRing R'] [CommRing A] [CommRing A'] [CommRing B] [CommRing B']
  [Algebra R A] [Algebra R B] [Algebra R' A'] [Algebra R' B']

theorem map_mem (φ : R →+* R') (ψ : A →+* A') (χ : B →+* B')
    (hψ : ∀ r : R, ψ (algebraMap R A r) = algebraMap R' A' (φ r))
    (hχ : ∀ r : R, χ (algebraMap R B r) = algebraMap R' B' (φ r))
    (𝒜 : ℕ → Submodule R A) (𝒜' : ℕ → Submodule R' A')
    (hgr : ∀ (m : ℕ) (a : A), a ∈ 𝒜 m → ψ a ∈ 𝒜' m)
    {m : ℕ} {x : A ⊗[R] B} (hx : x ∈ tensorGrading 𝒜 (B := B) m) :
    map φ ψ χ hψ hχ x ∈ tensorGrading 𝒜' (B := B') m := by
  obtain ⟨u, rfl⟩ := (mem_tensorGrading 𝒜).1 hx
  clear hx
  induction u using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]; exact Submodule.zero_mem _
  | add u₁ u₂ h₁ h₂ => rw [map_add, map_add]; exact Submodule.add_mem _ h₁ h₂
  | tmul a b =>
    rw [LinearMap.rTensor_tmul, map_tmul]
    exact tmul_mem_tensorGrading 𝒜' (hgr m a a.2) _

end MapMem

end GradedBaseChange
