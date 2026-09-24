import MiyaokaMori.Prelude

/-! # Maximal ideals of a polynomial ring over a field have height `n`

Let `k` be a field and `n` a natural number. Every maximal ideal `𝔪` of the polynomial ring
`k[x_1,…,x_n]` (`MvPolynomial (Fin n) k`) has height `n`.

Proof:
1. Induction on `n`. For `n = 0`, `k[∅]` has Krull dimension `0` (Mathlib
   `MvPolynomial.ringKrullDim_of_isNoetherianRing` and `ringKrullDim_eq_zero_of_field`), and the
   height of a prime is at most the dimension of the ring (`Ideal.height_le_ringKrullDim_of_isPrime`),
   so `height 𝔪 = 0`.
2. `n → n+1`: via `MvPolynomial.finSuccEquiv`, `k[x_0..x_n] ≅ R[X]` with `R = k[x_1..x_n]`; ring
   isomorphisms preserve heights (`RingEquiv.height_map`) and maximality, so it suffices to show
   `height 𝔐 = n+1` for a maximal ideal `𝔐` of `R[X]`.
3. `R` is a Jacobson ring (a polynomial ring over a field; Mathlib instance), so `𝔭 = 𝔐 ∩ R` is a
   maximal ideal of `R` (`Polynomial.isMaximal_comap_C_of_isJacobsonRing`); by induction
   `height 𝔭 = n`.
4. `R` is Noetherian and `𝔐` is a maximal ideal of `R[X]` lying over `𝔭`, so
   `height 𝔐 = height 𝔭 + 1 = n + 1` (Mathlib `Polynomial.height_eq_height_add_one`).

Reference: Stacks 00OP (algebra-lemma-dim-affine-space).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

noncomputable section

theorem MvPolynomial.height_eq_of_isMaximal {k : Type u} [Field k] (n : ℕ)
    (m : Ideal (MvPolynomial (Fin n) k)) [m.IsMaximal] : m.height = n := by
  induction n with
  | zero =>
    have h0 : ringKrullDim (MvPolynomial (Fin 0) k) = 0 := by
      rw [MvPolynomial.ringKrullDim_of_isNoetherianRing]; simp
    have h1 : (m.height : WithBot ℕ∞) ≤ 0 := h0 ▸ Ideal.height_le_ringKrullDim_of_isPrime
    have h2 : m.height ≤ 0 := by exact_mod_cast h1
    simpa using h2
  | succ n ih =>
    let R := MvPolynomial (Fin n) k
    let e : MvPolynomial (Fin (n + 1)) k ≃+* Polynomial R :=
      (MvPolynomial.finSuccEquiv k n).toRingEquiv
    have hM : (m.map e).IsMaximal := Ideal.map_isMaximal_of_equiv e
    have hp : ((m.map e).comap (Polynomial.C : R →+* Polynomial R)).IsMaximal :=
      Polynomial.isMaximal_comap_C_of_isJacobsonRing (m.map e)
    have hlo : (m.map e).LiesOver ((m.map e).comap (Polynomial.C : R →+* Polynomial R)) := ⟨rfl⟩
    rw [← e.height_map m,
      Polynomial.height_eq_height_add_one ((m.map e).comap (Polynomial.C : R →+* Polynomial R))
        (m.map e), ih _]
    simp

end
