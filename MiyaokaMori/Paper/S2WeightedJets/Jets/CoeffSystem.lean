import MiyaokaMori.Paper.S2WeightedJets.Jets.JetAlgebraGrading

/-! # Coefficient systems: the universal property of the based jet algebra

The universal property of the based jet algebra `J = J_r(B, ε)` in terms of coefficients (truncated
Hasse–Schmidt derivations). A coefficient system of order `r` with values in a commutative ring `G`
(`BasedJetAlgebra.CoeffSystem ε r ρ G`, with `ρ : R →+* G`) is a family of maps `c_n : B → G` (`n ∈ ℕ`) with
`c_0 = ρ ∘ ε` which, for `n ≤ r`, are additive and `R`-semilinear, satisfy `c_n(1) = 0` for `n ≥ 1`, and obey
the Leibniz rule `c_n(bb') = Σ_{i+j=n} c_i(b) c_j(b')`. It induces a ring homomorphism `CoeffSystem.lift : J →+* G`
with `lift (D_n b) = c_n b` for `n ≤ r` and `lift ∘ algebraMap = ρ`; if `G` is `ℕ`-graded with `c_n b ∈ 𝒢_n` and
`ρ(R) ⊆ 𝒢_0`, then `lift` preserves the grading (`lift_mem`: the `m`-th piece of `J` maps into `𝒢_m`).

This unifies the two encodings of the coefficient of order `q` of a jet: (a) the `q`-th component of a cone
coordinate under the truncated decomposition `Γ(C̃_(κ)(L), p^*M) ≃ ⊕_q H^0(M ⊗ L^{-q})`, and (b) the weight
decomposition `S_m → (L^∨)^{⊗m}` of the image under the algebra map. With `G = ⊕_m L^{-m}(V)` graded, (a) is
`c_q` itself and (b) is the restriction of `lift` to `S_m`; `lift_coeffClass` compares the two and `lift_mem` is
"weight `m` goes to `L^{-m}`". The untwisted case (`G = S`, `c_n` the `n`-th coefficient of `ψ`,
`CoeffSystem.ofTruncated`) recovers the plain lift `BasedJetAlgebra.lift`; `G = J[λ]`, `c_n b = D_n b · λ^n`
recovers the coaction. The weight convention lives in one place: `BasedJetAlgebra.weight` (the weight of
`d_q b` is `q + 1`, its order).

References: §2 and §3 of the paper (based jets and their coefficients of order `q`); Vojta, "Jets via
Hasse–Schmidt derivations", Def. 1.3–Thm. 1.6 (the universal property of `HS^r_{B/R}`).
-/

set_option autoImplicit false

universe u

noncomputable section

namespace BasedJetAlgebra

variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]

/-- A coefficient system of order `r` with values in `G` (a truncated Hasse–Schmidt derivation whose constant
term is fixed to `ρ ∘ ε`). -/
structure CoeffSystem (ε : B →ₐ[R] R) (r : ℕ) {G : Type u} [CommRing G] (ρ : R →+* G) where
  /-- The coefficient of order `n`. -/
  coeff : ℕ → B → G
  coeff_zero : ∀ b, coeff 0 b = ρ (ε b)
  coeff_add : ∀ n, n ≤ r → ∀ b b', coeff n (b + b') = coeff n b + coeff n b'
  coeff_smul : ∀ n, n ≤ r → ∀ (a : R) (b : B), coeff n (a • b) = ρ a * coeff n b
  coeff_one : ∀ n, 0 < n → n ≤ r → coeff n 1 = 0
  coeff_mul : ∀ n, n ≤ r → ∀ b b', coeff n (b * b') =
    ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal (A := ℕ) n, coeff ij.1 b * coeff ij.2 b'

namespace CoeffSystem

variable {ε : B →ₐ[R] R} {r : ℕ} {G : Type u} [CommRing G] {ρ : R →+* G} (c : CoeffSystem ε r ρ)

/-- The image of the generators: `d_q b ↦ c_{q+1} b`. -/
def genImage : Fin r × B → G := fun qb => c.coeff (qb.1.1 + 1) qb.2

theorem eval_symbol (n : ℕ) (hn : n ≤ r) (b : B) :
    MvPolynomial.eval₂Hom ρ c.genImage (symbol ε r n b) = c.coeff n b := by
  unfold symbol
  rcases n with _ | m
  · rw [if_pos rfl, MvPolynomial.eval₂Hom_C, c.coeff_zero]
  · have h : m + 1 - 1 < r := by omega
    rw [if_neg (Nat.succ_ne_zero m), dif_pos h, MvPolynomial.eval₂Hom_X']
    rfl

theorem wellDefined : ∀ a ∈ relations ε r, MvPolynomial.eval₂Hom ρ c.genImage a = 0 := by
  intro a ha
  have hle : relations ε r ≤ RingHom.ker (MvPolynomial.eval₂Hom ρ c.genImage) := by
    unfold relations
    rw [Ideal.span_le]
    rintro x (((⟨q, b, b', rfl⟩ | ⟨q, a, b, rfl⟩) | ⟨q, rfl⟩) | ⟨q, b, b', rfl⟩)
    · rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_sub, MvPolynomial.eval₂Hom_X',
        MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X']
      show c.coeff (q.1 + 1) (b + b') - c.coeff (q.1 + 1) b - c.coeff (q.1 + 1) b' = 0
      rw [c.coeff_add _ (Nat.succ_le_of_lt q.2)]; ring
    · rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_mul, MvPolynomial.eval₂Hom_X',
        MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_C]
      show c.coeff (q.1 + 1) (a • b) - ρ a * c.coeff (q.1 + 1) b = 0
      rw [c.coeff_smul _ (Nat.succ_le_of_lt q.2)]; ring
    · rw [SetLike.mem_coe, RingHom.mem_ker, MvPolynomial.eval₂Hom_X']
      exact c.coeff_one _ (Nat.succ_pos _) (Nat.succ_le_of_lt q.2)
    · rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_sum, MvPolynomial.eval₂Hom_X']
      show c.coeff (q.1 + 1) (b * b') - _ = 0
      rw [c.coeff_mul _ (Nat.succ_le_of_lt q.2), sub_eq_zero]
      refine Finset.sum_congr rfl fun ij hij => ?_
      have := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
      have h1 : ij.1 ≤ r := by have := q.2; omega
      have h2 : ij.2 ≤ r := by have := q.2; omega
      rw [map_mul, c.eval_symbol _ h1, c.eval_symbol _ h2]
  exact hle ha

/-- The universal property in coefficient form: a coefficient system induces a ring homomorphism
`J_r(B, ε) → G`. -/
def lift : BasedJetAlgebra ε r →+* G :=
  Ideal.Quotient.lift (relations ε r) (MvPolynomial.eval₂Hom ρ c.genImage) c.wellDefined

@[simp] theorem lift_mk (p : MvPolynomial (Fin r × B) R) :
    c.lift (Ideal.Quotient.mk (relations ε r) p) = MvPolynomial.eval₂Hom ρ c.genImage p := rfl

/-- Comparison lemma: `lift` sends the coefficient class `D_n b` of order `n` to `c_n b`. -/
@[simp] theorem lift_coeffClass (n : ℕ) (hn : n ≤ r) (b : B) :
    c.lift (coeffClass ε r n b) = c.coeff n b :=
  c.eval_symbol n hn b

@[simp] theorem lift_algebraMap (a : R) :
    c.lift (algebraMap R (BasedJetAlgebra ε r) a) = ρ a := by
  show MvPolynomial.eval₂Hom ρ c.genImage (MvPolynomial.C a) = ρ a
  rw [MvPolynomial.eval₂Hom_C]

/-- Two ring homomorphisms out of `J` that agree on the coefficient ring and on all `D_n b` (`1 ≤ n ≤ r`) are
equal. -/
theorem _root_.BasedJetAlgebra.ringHom_ext {G : Type u} [CommRing G]
    {φ ψ : BasedJetAlgebra ε r →+* G}
    (h₀ : ∀ a : R, φ (algebraMap R _ a) = ψ (algebraMap R _ a))
    (h : ∀ (n : ℕ) (_ : n ≤ r) (b : B), φ (coeffClass ε r n b) = ψ (coeffClass ε r n b)) :
    φ = ψ := by
  refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun a => h₀ a) fun qb => ?_)
  obtain ⟨q, b⟩ := qb
  have := h (q.1 + 1) (Nat.succ_le_of_lt q.2) b
  rwa [coeffClass_succ ε r q.1 q.2 b] at this

/-- Uniqueness: there is only one ring homomorphism satisfying `lift_coeffClass` and `lift_algebraMap`. -/
theorem lift_unique (φ : BasedJetAlgebra ε r →+* G)
    (h₀ : ∀ a : R, φ (algebraMap R _ a) = ρ a)
    (h : ∀ (n : ℕ) (_ : n ≤ r) (b : B), φ (coeffClass ε r n b) = c.coeff n b) : φ = c.lift :=
  BasedJetAlgebra.ringHom_ext (fun a => (h₀ a).trans (c.lift_algebraMap a).symm)
    fun n hn b => (h n hn b).trans (c.lift_coeffClass n hn b).symm

/-- Weight `m` goes to `𝒢_m`: if `G` is `ℕ`-graded, `c_n b ∈ 𝒢_n` and `ρ(R) ⊆ 𝒢_0`, then `lift` sends the `m`-th
piece of `J` into `𝒢_m`. -/
theorem lift_mem {σ : Type*} [SetLike σ G] [AddSubmonoidClass σ G] (𝒢 : ℕ → σ)
    [SetLike.GradedMonoid 𝒢] (hρ : ∀ a : R, ρ a ∈ 𝒢 0)
    (hc : ∀ (n : ℕ) (_ : n ≤ r) (b : B), c.coeff n b ∈ 𝒢 n)
    {m : ℕ} {x : BasedJetAlgebra ε r} (hx : x ∈ grading ε r m) : c.lift x ∈ 𝒢 m := by
  obtain ⟨p, hp, rfl⟩ := (mem_grading_iff ε r m x).mp hx
  rw [lift_mk]
  clear hx
  induction hp using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => rw [map_zero]; exact zero_mem _
  | add p q _ _ ihp ihq => rw [map_add]; exact add_mem ihp ihq
  | monomial d a hd =>
    rw [MvPolynomial.eval₂Hom_monomial]
    have hprod : (d.prod fun i k => c.genImage i ^ k) ∈ 𝒢 (Finsupp.weight (weight r B) d) := by
      rw [Finsupp.weight_apply, Finsupp.sum, Finsupp.prod]
      refine SetLike.prod_mem_graded _ _ _ fun i _ => ?_
      have hi : c.genImage i ∈ 𝒢 (weight r B i) :=
        hc (i.1.1 + 1) (Nat.succ_le_of_lt i.1.2) i.2
      simpa [smul_eq_mul] using SetLike.pow_mem_graded (d i) hi
    have := SetLike.mul_mem_graded (hρ a) hprod
    rwa [zero_add, hd] at this

end CoeffSystem

end BasedJetAlgebra

end
