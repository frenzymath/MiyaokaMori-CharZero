import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.EvaluateHomogeneousAtSections
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveBundle.ProjectiveBundleUniversalProperty

/-! # The based jet algebra

The coordinate algebra of based `r`-jets (a presentation-free construction of Hasse–Schmidt type): for an
`R`-algebra `B` with augmentation `ε : B → R`, `J_r(B, ε) := R[d_q b | q < r, b ∈ B]/(linearity, d_q 1 = 0,
Leibniz relations)`. We also provide the universal jet `B → J_r(B,ε)[t]/(t^{r+1})`, coefficient extraction in the
truncated ring, the lift `lift`, the representability bijection `homEquiv` (whose right-hand side is
`BasedAffineJet.Point`) and functoriality `map` in `(R, B, ε)`.

References: §2 of the paper (the based jet scheme); Ein–Mustață, Prop. 2.2 (the coordinate algebra in the affine
case); Vojta, "Jets via Hasse–Schmidt derivations", §1.

Implementation note: `TruncatedJetRing` is `AdjoinRoot (X^(r+1))`; representatives are taken with
`jetProjection_surjective` (so that `rw` sees `jetProjection … p`, not `Ideal.Quotient.mk (span …) p`), and
`Ideal.Quotient.lift_mk` is rewritten with `erw` (it matches only up to unfolding `AdjoinRoot`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/- The coordinate algebra of based jets (presentation-free, Hasse–Schmidt type). For an `R`-algebra `B` with
   augmentation `ε : B → R` (the comorphism of the section `s`), `J_r(B, ε) := R[d_q b | q < r, b ∈ B] / (relations)`,
   where `d_q b` is the coefficient of order `q + 1` of `b` along the universal jet and the coefficient of order `0`
   is fixed to `ε b`. Relations: `d_q` is `R`-linear in `b`, `d_q 1 = 0`, and Leibniz
   `D_n(bb') = Σ_{i+j=n} D_i b · D_j b'` (with `D_0 := ε`).
   A presentation-dependent construction (`B` as a literal quotient `R[x_1..x_n]/I`) would not be functorial in the
   sections rings `Γ(Z, π⁻¹U)`, which have no canonical presentation; this version is functorial in `(R, B, ε)`
   (`BasedJetAlgebra.map`) and can be fed directly to Mathlib's `AffineZariskiSite.relativeGluingData` to glue a
   scheme over `C`. It represents the functor `BasedAffineJet.Point` (`homEquiv`). -/

/-- The coefficient symbol `D_n b` of order `n`: `D_0 b = ε b`, for `1 ≤ n ≤ r` it is the generator `d_{n-1} b`,
and for `n > r` it is `0`. -/

noncomputable def BasedJetAlgebra.symbol {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    (ε : B →ₐ[R] R) (r : ℕ) (n : ℕ) (b : B) : MvPolynomial (Fin r × B) R :=
  if n = 0 then MvPolynomial.C (ε b)
  else if h : n - 1 < r then MvPolynomial.X (⟨n - 1, h⟩, b) else 0

/-- The ideal of relations. -/

noncomputable def BasedJetAlgebra.relations {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    (ε : B →ₐ[R] R) (r : ℕ) : Ideal (MvPolynomial (Fin r × B) R) :=
  Ideal.span
    ({p | ∃ (q : Fin r) (b b' : B), p = MvPolynomial.X (q, b + b') - MvPolynomial.X (q, b) - MvPolynomial.X (q, b')} ∪
     {p | ∃ (q : Fin r) (a : R) (b : B), p = MvPolynomial.X (q, a • b) - MvPolynomial.C a * MvPolynomial.X (q, b)} ∪
     {p | ∃ q : Fin r, p = MvPolynomial.X (q, (1 : B))} ∪
     {p | ∃ (q : Fin r) (b b' : B), p = MvPolynomial.X (q, b * b') -
        ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal (A := ℕ) (q.1 + 1),
          BasedJetAlgebra.symbol ε r ij.1 b * BasedJetAlgebra.symbol ε r ij.2 b'})

/-- The coordinate algebra of based `r`-jets. -/

abbrev BasedJetAlgebra {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    (ε : B →ₐ[R] R) (r : ℕ) : Type u :=
  MvPolynomial (Fin r × B) R ⧸ BasedJetAlgebra.relations ε r

/-- The class of `D_n b` in the quotient. -/

noncomputable def BasedJetAlgebra.coeffClass {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    (ε : B →ₐ[R] R) (r : ℕ) (n : ℕ) (b : B) : BasedJetAlgebra ε r :=
  Ideal.Quotient.mk _ (BasedJetAlgebra.symbol ε r n b)

/- The five proof obligations of the universal jet: first linearity, scalars, `D_n 1` and Leibniz for `D_n`
   (`coeffClass_*`, which are exactly the four families of relations), then compare coefficients order by order
   in the truncated ring (`jetProjection_eq_of_coeff`). -/

section UniversalJetAux
variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B] (ε : B →ₐ[R] R) (r : ℕ)

theorem BasedJetAlgebra.coeffClass_zero_order (b : B) :
    BasedJetAlgebra.coeffClass ε r 0 b = Ideal.Quotient.mk _ (MvPolynomial.C (ε b)) := by
  unfold BasedJetAlgebra.coeffClass BasedJetAlgebra.symbol
  rw [if_pos rfl]

theorem BasedJetAlgebra.coeffClass_succ (m : ℕ) (hm : m < r) (b : B) :
    BasedJetAlgebra.coeffClass ε r (m + 1) b =
      Ideal.Quotient.mk (BasedJetAlgebra.relations ε r) (MvPolynomial.X (⟨m, hm⟩, b)) := by
  unfold BasedJetAlgebra.coeffClass BasedJetAlgebra.symbol
  rw [if_neg (Nat.succ_ne_zero m), dif_pos (show m + 1 - 1 < r by omega)]
  rfl

theorem BasedJetAlgebra.coeffClass_add (n : ℕ) (hn : n ≤ r) (b b' : B) :
    BasedJetAlgebra.coeffClass ε r n (b + b') =
      BasedJetAlgebra.coeffClass ε r n b + BasedJetAlgebra.coeffClass ε r n b' := by
  rcases n with _ | m
  · rw [BasedJetAlgebra.coeffClass_zero_order, BasedJetAlgebra.coeffClass_zero_order, BasedJetAlgebra.coeffClass_zero_order, map_add, map_add, map_add]
  · have hm : m < r := hn
    rw [BasedJetAlgebra.coeffClass_succ ε r m hm, BasedJetAlgebra.coeffClass_succ ε r m hm, BasedJetAlgebra.coeffClass_succ ε r m hm, ← map_add,
      Ideal.Quotient.eq]
    exact Ideal.subset_span (Or.inl (Or.inl (Or.inl ⟨⟨m, hm⟩, b, b', (sub_sub _ _ _).symm⟩)))

theorem BasedJetAlgebra.coeffClass_smul (n : ℕ) (hn : n ≤ r) (a : R) (b : B) :
    BasedJetAlgebra.coeffClass ε r n (a • b) =
      Ideal.Quotient.mk _ (MvPolynomial.C a) * BasedJetAlgebra.coeffClass ε r n b := by
  rcases n with _ | m
  · rw [BasedJetAlgebra.coeffClass_zero_order, BasedJetAlgebra.coeffClass_zero_order, map_smul, smul_eq_mul, map_mul, map_mul]
  · have hm : m < r := hn
    rw [BasedJetAlgebra.coeffClass_succ ε r m hm, BasedJetAlgebra.coeffClass_succ ε r m hm, ← map_mul, Ideal.Quotient.eq]
    exact Ideal.subset_span (Or.inl (Or.inl (Or.inr ⟨⟨m, hm⟩, a, b, rfl⟩)))

theorem BasedJetAlgebra.coeffClass_one (n : ℕ) (hn : n ≤ r) :
    BasedJetAlgebra.coeffClass ε r n (1 : B) = if n = 0 then 1 else 0 := by
  rcases n with _ | m
  · rw [BasedJetAlgebra.coeffClass_zero_order, map_one, if_pos rfl]; rfl
  · have hm : m < r := hn
    rw [BasedJetAlgebra.coeffClass_succ ε r m hm, if_neg (Nat.succ_ne_zero m), Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span (Or.inl (Or.inr ⟨⟨m, hm⟩, rfl⟩))

theorem BasedJetAlgebra.coeffClass_mul (n : ℕ) (hn : n ≤ r) (b b' : B) :
    BasedJetAlgebra.coeffClass ε r n (b * b') =
      ∑ ij ∈ Finset.HasAntidiagonal.antidiagonal (A := ℕ) n,
        BasedJetAlgebra.coeffClass ε r ij.1 b * BasedJetAlgebra.coeffClass ε r ij.2 b' := by
  rcases n with _ | m
  · rw [Finset.Nat.antidiagonal_zero, Finset.sum_singleton, BasedJetAlgebra.coeffClass_zero_order, BasedJetAlgebra.coeffClass_zero_order, BasedJetAlgebra.coeffClass_zero_order,
      map_mul, map_mul, map_mul]
  · have hm : m < r := hn
    rw [BasedJetAlgebra.coeffClass_succ ε r m hm]
    unfold BasedJetAlgebra.coeffClass
    simp only [← map_mul, ← map_sum]
    rw [Ideal.Quotient.eq]
    exact Ideal.subset_span (Or.inr ⟨⟨m, hm⟩, b, b', rfl⟩)

/-- The polynomial representative of the universal jet. -/
theorem BasedJetAlgebra.universalJet_poly_coeff (b : B) (n : ℕ) (hn : n ≤ r) :
    (∑ m ∈ Finset.range (r + 1),
      Polynomial.monomial m (BasedJetAlgebra.coeffClass ε r m b)).coeff n =
      BasedJetAlgebra.coeffClass ε r n b := by
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial]
  rw [Finset.sum_ite_eq' (Finset.range (r + 1)) n, if_pos (Finset.mem_range.mpr (by omega))]

theorem BasedJetAlgebra.universalJet_map_one :
    MiyaokaMori.Jet.jetProjection (BasedJetAlgebra ε r) r
      (∑ n ∈ Finset.range (r + 1), Polynomial.monomial n (BasedJetAlgebra.coeffClass ε r n (1 : B))) = 1 := by
  show _ = MiyaokaMori.Jet.jetProjection (BasedJetAlgebra ε r) r 1
  apply MiyaokaMori.Jet.jetProjection_eq_of_coeff
  intro n hn
  rw [BasedJetAlgebra.universalJet_poly_coeff ε r _ n hn, BasedJetAlgebra.coeffClass_one ε r n hn, Polynomial.coeff_one]

theorem BasedJetAlgebra.universalJet_map_mul (b b' : B) :
    MiyaokaMori.Jet.jetProjection (BasedJetAlgebra ε r) r
      (∑ n ∈ Finset.range (r + 1), Polynomial.monomial n (BasedJetAlgebra.coeffClass ε r n (b * b'))) =
    MiyaokaMori.Jet.jetProjection (BasedJetAlgebra ε r) r
      (∑ n ∈ Finset.range (r + 1), Polynomial.monomial n (BasedJetAlgebra.coeffClass ε r n b)) *
    MiyaokaMori.Jet.jetProjection (BasedJetAlgebra ε r) r
      (∑ n ∈ Finset.range (r + 1), Polynomial.monomial n (BasedJetAlgebra.coeffClass ε r n b')) := by
  rw [← map_mul]
  apply MiyaokaMori.Jet.jetProjection_eq_of_coeff
  intro n hn
  rw [BasedJetAlgebra.universalJet_poly_coeff ε r _ n hn, BasedJetAlgebra.coeffClass_mul ε r n hn, Polynomial.coeff_mul]
  refine Finset.sum_congr rfl fun ij hij => ?_
  have := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  rw [BasedJetAlgebra.universalJet_poly_coeff ε r _ _ (by omega), BasedJetAlgebra.universalJet_poly_coeff ε r _ _ (by omega)]

theorem BasedJetAlgebra.universalJet_map_add (b b' : B) :
    MiyaokaMori.Jet.jetProjection (BasedJetAlgebra ε r) r
      (∑ n ∈ Finset.range (r + 1), Polynomial.monomial n (BasedJetAlgebra.coeffClass ε r n (b + b'))) =
    MiyaokaMori.Jet.jetProjection (BasedJetAlgebra ε r) r
      (∑ n ∈ Finset.range (r + 1), Polynomial.monomial n (BasedJetAlgebra.coeffClass ε r n b)) +
    MiyaokaMori.Jet.jetProjection (BasedJetAlgebra ε r) r
      (∑ n ∈ Finset.range (r + 1), Polynomial.monomial n (BasedJetAlgebra.coeffClass ε r n b')) := by
  rw [← map_add]
  apply MiyaokaMori.Jet.jetProjection_eq_of_coeff
  intro n hn
  rw [Polynomial.coeff_add,
    BasedJetAlgebra.universalJet_poly_coeff ε r _ n hn, BasedJetAlgebra.universalJet_poly_coeff ε r _ n hn, BasedJetAlgebra.universalJet_poly_coeff ε r _ n hn, BasedJetAlgebra.coeffClass_add ε r n hn]

theorem BasedJetAlgebra.universalJet_map_zero :
    MiyaokaMori.Jet.jetProjection (BasedJetAlgebra ε r) r
      (∑ n ∈ Finset.range (r + 1), Polynomial.monomial n (BasedJetAlgebra.coeffClass ε r n (0 : B))) = 0 := by
  have h := BasedJetAlgebra.universalJet_map_add ε r 0 0
  rw [add_zero] at h
  exact left_eq_add.mp h

theorem BasedJetAlgebra.universalJet_commutes (a : R) :
    MiyaokaMori.Jet.jetProjection (BasedJetAlgebra ε r) r
      (∑ n ∈ Finset.range (r + 1), Polynomial.monomial n
        (BasedJetAlgebra.coeffClass ε r n (algebraMap R B a))) =
    algebraMap R (MiyaokaMori.Jet.TruncatedJetRing (BasedJetAlgebra ε r) r) a := by
  show _ = MiyaokaMori.Jet.jetProjection (BasedJetAlgebra ε r) r
    (Polynomial.C (Ideal.Quotient.mk (BasedJetAlgebra.relations ε r) (MvPolynomial.C a)))
  apply MiyaokaMori.Jet.jetProjection_eq_of_coeff
  intro n hn
  rw [BasedJetAlgebra.universalJet_poly_coeff ε r _ n hn, Algebra.algebraMap_eq_smul_one,
    BasedJetAlgebra.coeffClass_smul ε r n hn, BasedJetAlgebra.coeffClass_one ε r n hn, Polynomial.coeff_C]
  split_ifs <;> simp
end UniversalJetAux

/-- The universal jet `b ↦ Σ_{n ≤ r} (D_n b) t^n ∈ J_r(B, ε)[t]/(t^{r+1})` (the truncated ring is
`Jet.TruncatedJetRing`). Multiplicativity is exactly the Leibniz relation; additivity and scalars are the linearity
relations. -/

noncomputable def BasedJetAlgebra.universalJet {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    (ε : B →ₐ[R] R) (r : ℕ) : B →ₐ[R] MiyaokaMori.Jet.TruncatedJetRing (BasedJetAlgebra ε r) r where
  toFun b := MiyaokaMori.Jet.jetProjection (BasedJetAlgebra ε r) r
    (∑ n ∈ Finset.range (r + 1), Polynomial.monomial n (BasedJetAlgebra.coeffClass ε r n b))
  map_one' := BasedJetAlgebra.universalJet_map_one ε r
  map_mul' := BasedJetAlgebra.universalJet_map_mul ε r
  map_zero' := BasedJetAlgebra.universalJet_map_zero ε r
  map_add' := BasedJetAlgebra.universalJet_map_add ε r
  commutes' := BasedJetAlgebra.universalJet_commutes ε r


theorem BasedJetAlgebra.lift_eval_symbol {R B S : Type u} [CommRing R] [CommRing B] [Algebra R B] [CommRing S]
    (ε : B →ₐ[R] R) (r : ℕ) (ρ : R →+* S) (ψ : B →+* MiyaokaMori.Jet.TruncatedJetRing S r)
    (hε : ∀ b : B, MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.epsilon r (ψ b) = ρ (ε b))
    (n : ℕ) (hn : n ≤ r) (b : B) :
    MvPolynomial.eval₂Hom ρ (fun qb : Fin r × B =>
      MiyaokaMori.Jet.TruncatedJetRing.coeff r (qb.1.1 + 1) (Nat.succ_le_of_lt qb.1.2) (ψ qb.2))
      (BasedJetAlgebra.symbol ε r n b) = MiyaokaMori.Jet.TruncatedJetRing.coeff r n hn (ψ b) := by
  unfold BasedJetAlgebra.symbol
  rcases n with _ | m
  · rw [if_pos rfl, MvPolynomial.eval₂Hom_C, ← hε]
    obtain ⟨p, hp⟩ := MiyaokaMori.Jet.jetProjection_surjective _ _ (ψ b)
    rw [← hp]
    exact (Polynomial.coeff_zero_eq_eval_zero p).symm
  · have h : m + 1 - 1 < r := by omega
    rw [if_neg (Nat.succ_ne_zero m), dif_pos h, MvPolynomial.eval₂Hom_X']
    rfl

/-- Well-definedness of `lift`: `d_q b ↦` the coefficient of order `q + 1` of `ψ(b)` sends all four families of
relations to `0`. Linearity, scalars (via `hψ`) and `d_q 1 = 0` are checked on polynomial representatives coefficient
by coefficient; Leibniz uses `Polynomial.coeff_mul`, with the order-`0` term given by `hε` (`lift_eval_symbol`). -/
theorem BasedJetAlgebra.lift_wellDefined {R B S : Type u} [CommRing R] [CommRing B] [Algebra R B] [CommRing S]
    (ε : B →ₐ[R] R) (r : ℕ) (ρ : R →+* S) (ψ : B →+* MiyaokaMori.Jet.TruncatedJetRing S r)
    (hψ : ∀ (a : R) (b : B), ψ (a • b) = MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.eta r (ρ a) * ψ b)
    (hε : ∀ b : B, MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.epsilon r (ψ b) = ρ (ε b)) :
    ∀ a ∈ BasedJetAlgebra.relations ε r,
      MvPolynomial.eval₂Hom ρ (fun qb : Fin r × B =>
        MiyaokaMori.Jet.TruncatedJetRing.coeff r (qb.1.1 + 1) (Nat.succ_le_of_lt qb.1.2) (ψ qb.2)) a = 0 := by
  intro a ha
  have hle : BasedJetAlgebra.relations ε r ≤ RingHom.ker (MvPolynomial.eval₂Hom ρ
      (fun qb : Fin r × B =>
        MiyaokaMori.Jet.TruncatedJetRing.coeff r (qb.1.1 + 1) (Nat.succ_le_of_lt qb.1.2) (ψ qb.2))) := by
    unfold BasedJetAlgebra.relations
    rw [Ideal.span_le]
    rintro x (((⟨q, b, b', rfl⟩ | ⟨q, a, b, rfl⟩) | ⟨q, rfl⟩) | ⟨q, b, b', rfl⟩)
    · rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_sub, MvPolynomial.eval₂Hom_X',
        MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X']
      obtain ⟨p, hp⟩ := MiyaokaMori.Jet.jetProjection_surjective _ _ (ψ b)
      obtain ⟨p', hp'⟩ := MiyaokaMori.Jet.jetProjection_surjective _ _ (ψ b')
      show MiyaokaMori.Jet.TruncatedJetRing.coeff r _ _ (ψ (b + b')) -
        MiyaokaMori.Jet.TruncatedJetRing.coeff r _ _ (ψ b) -
        MiyaokaMori.Jet.TruncatedJetRing.coeff r _ _ (ψ b') = 0
      rw [map_add, ← hp, ← hp', ← map_add]
      show (p + p').coeff _ - p.coeff _ - p'.coeff _ = 0
      rw [Polynomial.coeff_add]; ring
    · rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_mul, MvPolynomial.eval₂Hom_X',
        MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_C]
      obtain ⟨p, hp⟩ := MiyaokaMori.Jet.jetProjection_surjective _ _ (ψ b)
      show MiyaokaMori.Jet.TruncatedJetRing.coeff r _ _ (ψ (a • b)) -
        ρ a * MiyaokaMori.Jet.TruncatedJetRing.coeff r _ _ (ψ b) = 0
      rw [hψ, ← hp]
      show (Polynomial.C (ρ a) * p).coeff _ - ρ a * p.coeff _ = 0
      rw [Polynomial.coeff_C_mul]; ring
    · rw [SetLike.mem_coe, RingHom.mem_ker, MvPolynomial.eval₂Hom_X']
      show MiyaokaMori.Jet.TruncatedJetRing.coeff r _ _ (ψ 1) = 0
      rw [map_one]
      show (1 : Polynomial S).coeff (q.1 + 1) = 0
      rw [Polynomial.coeff_one, if_neg (Nat.succ_ne_zero _)]
    · rw [SetLike.mem_coe, RingHom.mem_ker, map_sub, map_sum, MvPolynomial.eval₂Hom_X']
      have hsum : ∀ ij ∈ Finset.HasAntidiagonal.antidiagonal (A := ℕ) (q.1 + 1),
          (MvPolynomial.eval₂Hom ρ (fun qb : Fin r × B =>
            MiyaokaMori.Jet.TruncatedJetRing.coeff r (qb.1.1 + 1) (Nat.succ_le_of_lt qb.1.2) (ψ qb.2)))
            (BasedJetAlgebra.symbol ε r ij.1 b * BasedJetAlgebra.symbol ε r ij.2 b') =
          (if h : ij.1 ≤ r then MiyaokaMori.Jet.TruncatedJetRing.coeff r ij.1 h (ψ b) else 0) *
          (if h : ij.2 ≤ r then MiyaokaMori.Jet.TruncatedJetRing.coeff r ij.2 h (ψ b') else 0) := by
        intro ij hij
        have := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
        have h1 : ij.1 ≤ r := by have := q.2; omega
        have h2 : ij.2 ≤ r := by have := q.2; omega
        rw [map_mul, BasedJetAlgebra.lift_eval_symbol ε r ρ ψ hε _ h1, BasedJetAlgebra.lift_eval_symbol ε r ρ ψ hε _ h2, dif_pos h1,
          dif_pos h2]
      rw [Finset.sum_congr rfl hsum]
      obtain ⟨p, hp⟩ := MiyaokaMori.Jet.jetProjection_surjective _ _ (ψ b)
      obtain ⟨p', hp'⟩ := MiyaokaMori.Jet.jetProjection_surjective _ _ (ψ b')
      show MiyaokaMori.Jet.TruncatedJetRing.coeff r _ _ (ψ (b * b')) - _ = 0
      rw [map_mul, ← hp, ← hp', ← map_mul]
      show (p * p').coeff (q.1 + 1) - _ = 0
      rw [Polynomial.coeff_mul, sub_eq_zero]
      refine Finset.sum_congr rfl fun ij hij => ?_
      have := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
      have h1 : ij.1 ≤ r := by have := q.2; omega
      have h2 : ij.2 ≤ r := by have := q.2; omega
      rw [dif_pos h1, dif_pos h2]
      rfl
  exact hle ha

/-- The lift at the level of ring homomorphisms: given `ρ : R → S` and `ψ : B → S[t]/(t^{r+1})` compatible with `ρ`
(`hψ`) and with constant term `ρ ∘ ε` (`hε`), `d_q b ↦` the coefficient of order `q + 1` of `ψ(b)` defines
`J_r(B, ε) → S`. -/

noncomputable def BasedJetAlgebra.lift {R B S : Type u} [CommRing R] [CommRing B] [Algebra R B] [CommRing S]
    (ε : B →ₐ[R] R) (r : ℕ) (ρ : R →+* S) (ψ : B →+* MiyaokaMori.Jet.TruncatedJetRing S r)
    (hψ : ∀ (a : R) (b : B), ψ (a • b) = MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.eta r (ρ a) * ψ b)
    (hε : ∀ b : B, MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.epsilon r (ψ b) = ρ (ε b)) :
    BasedJetAlgebra ε r →+* S :=
  Ideal.Quotient.lift (BasedJetAlgebra.relations ε r)
    (MvPolynomial.eval₂Hom ρ (fun qb : Fin r × B =>
      MiyaokaMori.Jet.TruncatedJetRing.coeff r (qb.1.1 + 1) (Nat.succ_le_of_lt qb.1.2) (ψ qb.2)))
    (BasedJetAlgebra.lift_wellDefined ε r ρ ψ hψ hε)

/- The proof obligations of `homEquiv`: the constant-term condition, the two hypotheses of `lift`, `commutes`, and
   the inverse laws; all reduce to `universalJet_poly_coeff` (the coefficient of order `n` of the universal jet is
   `D_n b`) and `lift_coeffClass` (`lift` sends `D_n b` to the coefficient of order `n` of `ψ b`). -/

section HomEquivAux
variable {R B S : Type u} [CommRing R] [CommRing B] [Algebra R B]
    [CommRing S] [Algebra R S] (ε : B →ₐ[R] R) (r : ℕ)

theorem BasedJetAlgebra.homEquiv_toFun_augmentation (φ : BasedJetAlgebra ε r →ₐ[R] S) (b : B) :
    MiyaokaMori.BasedAffineJet.augmentation S r
      (((MiyaokaMori.BasedAffineJet.mapTruncated r φ).comp (BasedJetAlgebra.universalJet ε r)) b) =
      algebraMap R S (ε b) := by
  show MiyaokaMori.BasedAffineJet.augmentation S r
      (MiyaokaMori.BasedAffineJet.mapTruncated r φ (BasedJetAlgebra.universalJet ε r b)) = _
  rw [MiyaokaMori.BasedAffineJet.augmentation_mapTruncated]
  show φ (Polynomial.eval 0 _) = _
  rw [← Polynomial.coeff_zero_eq_eval_zero,
    BasedJetAlgebra.universalJet_poly_coeff ε r b 0 (Nat.zero_le r),
    BasedJetAlgebra.coeffClass_zero_order]
  exact φ.commutes (ε b)

theorem BasedJetAlgebra.homEquiv_invFun_smul (j : MiyaokaMori.BasedAffineJet.Point ε S r) (a : R) (b : B) :
    j.1.toRingHom (a • b) =
      MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.eta r (algebraMap R S a) * j.1.toRingHom b := by
  show j.1 (a • b) = _
  rw [map_smul]
  exact Algebra.smul_def a (j.1 b)

theorem BasedJetAlgebra.homEquiv_invFun_epsilon (j : MiyaokaMori.BasedAffineJet.Point ε S r) (b : B) :
    MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.epsilon r (j.1.toRingHom b) = algebraMap R S (ε b) := by
  rw [← j.2 b]
  show _ = MiyaokaMori.BasedAffineJet.augmentation S r (j.1.toRingHom b)
  obtain ⟨p, hp⟩ := MiyaokaMori.Jet.jetProjection_surjective _ _ (j.1.toRingHom b)
  rw [← hp]
  rfl

theorem BasedJetAlgebra.homEquiv_invFun_commutes (j : MiyaokaMori.BasedAffineJet.Point ε S r) (a : R) :
    BasedJetAlgebra.lift ε r (algebraMap R S) j.1.toRingHom (BasedJetAlgebra.homEquiv_invFun_smul ε r j) (BasedJetAlgebra.homEquiv_invFun_epsilon ε r j)
      (algebraMap R (BasedJetAlgebra ε r) a) = algebraMap R S a := by
  show MvPolynomial.eval₂Hom _ _ (MvPolynomial.C a) = _
  rw [MvPolynomial.eval₂Hom_C]

theorem BasedJetAlgebra.lift_coeffClass {S : Type u} [CommRing S] (ρ : R →+* S)
    (ψ : B →+* MiyaokaMori.Jet.TruncatedJetRing S r)
    (hψ : ∀ (a : R) (b : B), ψ (a • b) = MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.eta r (ρ a) * ψ b)
    (hε : ∀ b : B, MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.epsilon r (ψ b) = ρ (ε b))
    (n : ℕ) (hn : n ≤ r) (b : B) :
    BasedJetAlgebra.lift ε r ρ ψ hψ hε (BasedJetAlgebra.coeffClass ε r n b) =
      MiyaokaMori.Jet.TruncatedJetRing.coeff r n hn (ψ b) :=
  BasedJetAlgebra.lift_eval_symbol ε r ρ ψ hε n hn b

theorem BasedJetAlgebra.homEquiv_left_inv_apply (φ : BasedJetAlgebra ε r →ₐ[R] S) (x : BasedJetAlgebra ε r) :
    BasedJetAlgebra.lift ε r (algebraMap R S)
      ((MiyaokaMori.BasedAffineJet.mapTruncated r φ).comp (BasedJetAlgebra.universalJet ε r)).toRingHom
      (BasedJetAlgebra.homEquiv_invFun_smul ε r ⟨_, BasedJetAlgebra.homEquiv_toFun_augmentation ε r φ⟩) (BasedJetAlgebra.homEquiv_invFun_epsilon ε r ⟨_, BasedJetAlgebra.homEquiv_toFun_augmentation ε r φ⟩) x = φ x := by
  suffices h : BasedJetAlgebra.lift ε r (algebraMap R S)
      ((MiyaokaMori.BasedAffineJet.mapTruncated r φ).comp (BasedJetAlgebra.universalJet ε r)).toRingHom
      (BasedJetAlgebra.homEquiv_invFun_smul ε r ⟨_, BasedJetAlgebra.homEquiv_toFun_augmentation ε r φ⟩) (BasedJetAlgebra.homEquiv_invFun_epsilon ε r ⟨_, BasedJetAlgebra.homEquiv_toFun_augmentation ε r φ⟩) = φ.toRingHom from
    congrArg (fun f => f x) h
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro a
    show MvPolynomial.eval₂Hom _ _ (MvPolynomial.C a) = φ (algebraMap R _ a)
    rw [MvPolynomial.eval₂Hom_C, φ.commutes]
  · rintro ⟨q, b⟩
    show MvPolynomial.eval₂Hom _ _ (MvPolynomial.X (q, b)) = φ (Ideal.Quotient.mk _ (MvPolynomial.X (q, b)))
    rw [MvPolynomial.eval₂Hom_X']
    show (Polynomial.map φ.toRingHom _).coeff (q.1 + 1) = _
    rw [Polynomial.coeff_map, BasedJetAlgebra.universalJet_poly_coeff ε r b _ (Nat.succ_le_of_lt q.2),
      BasedJetAlgebra.coeffClass_succ ε r q.1 q.2]
    rfl

theorem BasedJetAlgebra.homEquiv_right_inv_apply (j : MiyaokaMori.BasedAffineJet.Point ε S r) (b : B) :
    MiyaokaMori.BasedAffineJet.mapTruncated r
      ({ toRingHom := BasedJetAlgebra.lift ε r (algebraMap R S) j.1.toRingHom
          (BasedJetAlgebra.homEquiv_invFun_smul ε r j) (BasedJetAlgebra.homEquiv_invFun_epsilon ε r j)
         commutes' := BasedJetAlgebra.homEquiv_invFun_commutes ε r j } : BasedJetAlgebra ε r →ₐ[R] S)
      (BasedJetAlgebra.universalJet ε r b) = j.1 b := by
  obtain ⟨p, hp⟩ := MiyaokaMori.Jet.jetProjection_surjective _ _ (j.1 b)
  rw [← hp]
  show MiyaokaMori.Jet.jetProjection S r (Polynomial.map _ _) = MiyaokaMori.Jet.jetProjection S r p
  apply MiyaokaMori.Jet.jetProjection_eq_of_coeff
  intro n hn
  rw [Polynomial.coeff_map, BasedJetAlgebra.universalJet_poly_coeff ε r b n hn]
  show BasedJetAlgebra.lift ε r (algebraMap R S) j.1.toRingHom (BasedJetAlgebra.homEquiv_invFun_smul ε r j) (BasedJetAlgebra.homEquiv_invFun_epsilon ε r j)
    (BasedJetAlgebra.coeffClass ε r n b) = _
  rw [BasedJetAlgebra.lift_coeffClass ε r _ _ _ _ n hn]
  show MiyaokaMori.Jet.TruncatedJetRing.coeff r n hn (j.1 b) = _
  rw [← hp]
  rfl
end HomEquivAux

/-- `J_r(B, ε)` represents based jets: `R`-algebra homomorphisms `J_r(B, ε) → S` correspond to
`BasedAffineJet.Point ε S r` (`R`-algebra homomorphisms `B → S[t]/(t^{r+1})` with constant term `ε`). Forward:
change coefficients along `φ` after the universal jet; backward: take coefficients. -/

noncomputable def BasedJetAlgebra.homEquiv {R B S : Type u} [CommRing R] [CommRing B] [Algebra R B]
    [CommRing S] [Algebra R S] (ε : B →ₐ[R] R) (r : ℕ) :
    (BasedJetAlgebra ε r →ₐ[R] S) ≃ MiyaokaMori.BasedAffineJet.Point ε S r where
  toFun φ := ⟨(MiyaokaMori.BasedAffineJet.mapTruncated r φ).comp (BasedJetAlgebra.universalJet ε r),
    BasedJetAlgebra.homEquiv_toFun_augmentation ε r φ⟩
  invFun j :=
    { toRingHom := BasedJetAlgebra.lift ε r (algebraMap R S) j.1.toRingHom
        (BasedJetAlgebra.homEquiv_invFun_smul ε r j) (BasedJetAlgebra.homEquiv_invFun_epsilon ε r j)
      commutes' := BasedJetAlgebra.homEquiv_invFun_commutes ε r j }
  left_inv φ := AlgHom.ext (BasedJetAlgebra.homEquiv_left_inv_apply ε r φ)
  right_inv j := Subtype.ext (AlgHom.ext (BasedJetAlgebra.homEquiv_right_inv_apply ε r j))

theorem BasedJetAlgebra.map_eval_symbol {R B R' B' : Type u} [CommRing R] [CommRing B] [Algebra R B]
    [CommRing R'] [CommRing B'] [Algebra R' B'] (ε : B →ₐ[R] R) (ε' : B' →ₐ[R'] R') (r : ℕ)
    (ρ : R →+* R') (β : B →+* B') (hε : ∀ b : B, ε' (β b) = ρ (ε b)) (n : ℕ) (b : B) :
    MvPolynomial.eval₂Hom (MvPolynomial.C.comp ρ)
        (fun qb : Fin r × B => MvPolynomial.X (R := R') (qb.1, β qb.2))
        (BasedJetAlgebra.symbol ε r n b) = BasedJetAlgebra.symbol ε' r n (β b) := by
  unfold BasedJetAlgebra.symbol
  split_ifs with h0 h1
  · rw [MvPolynomial.eval₂Hom_C, hε]; rfl
  · rw [MvPolynomial.eval₂Hom_X']
  · rw [map_zero]

/-- Well-definedness of `map`: `d_q b ↦ d_q (β b)` sends the four families of relations of `(R,B,ε)` into the ideal
of relations of `(R',B',ε')`. Check family by family that the image is a generator of the same type (linearity via
`map_add`, scalars via `hβ`, `d_q 1` via `map_one`, Leibniz via `map_mul` and `map_eval_symbol`, whose order-`0`
term uses `hε`). -/
theorem BasedJetAlgebra.map_wellDefined {R B R' B' : Type u} [CommRing R] [CommRing B] [Algebra R B]
    [CommRing R'] [CommRing B'] [Algebra R' B'] (ε : B →ₐ[R] R) (ε' : B' →ₐ[R'] R') (r : ℕ)
    (ρ : R →+* R') (β : B →+* B')
    (hβ : ∀ (a : R) (b : B), β (a • b) = ρ a • β b) (hε : ∀ b : B, ε' (β b) = ρ (ε b)) :
    ∀ a ∈ BasedJetAlgebra.relations ε r,
      ((Ideal.Quotient.mk (BasedJetAlgebra.relations ε' r)).comp
        (MvPolynomial.eval₂Hom (MvPolynomial.C.comp ρ)
          (fun qb : Fin r × B => MvPolynomial.X (qb.1, β qb.2)))) a = 0 := by
  intro a ha
  have hle : BasedJetAlgebra.relations ε r ≤ RingHom.ker
      ((Ideal.Quotient.mk (BasedJetAlgebra.relations ε' r)).comp
        (MvPolynomial.eval₂Hom (MvPolynomial.C.comp ρ)
          (fun qb : Fin r × B => MvPolynomial.X (qb.1, β qb.2)))) := by
    unfold BasedJetAlgebra.relations
    rw [Ideal.span_le]
    rintro x (((⟨q, b, b', rfl⟩ | ⟨q, a, b, rfl⟩) | ⟨q, rfl⟩) | ⟨q, b, b', rfl⟩)
    · rw [SetLike.mem_coe, RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem,
        map_sub, map_sub, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X',
        MvPolynomial.eval₂Hom_X']
      exact Ideal.subset_span (Or.inl (Or.inl (Or.inl ⟨q, β b, β b', by rw [map_add]⟩)))
    · rw [SetLike.mem_coe, RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem,
        map_sub, map_mul, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_X',
        MvPolynomial.eval₂Hom_C]
      exact Ideal.subset_span (Or.inl (Or.inl (Or.inr ⟨q, ρ a, β b, by rw [hβ]; rfl⟩)))
    · rw [SetLike.mem_coe, RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem,
        MvPolynomial.eval₂Hom_X']
      exact Ideal.subset_span (Or.inl (Or.inr ⟨q, by rw [map_one]⟩))
    · rw [SetLike.mem_coe, RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem,
        map_sub, map_sum, MvPolynomial.eval₂Hom_X']
      refine Ideal.subset_span (Or.inr ⟨q, β b, β b', ?_⟩)
      rw [map_mul]
      congr 1
      refine Finset.sum_congr rfl fun ij _ => ?_
      rw [map_mul, BasedJetAlgebra.map_eval_symbol ε ε' r ρ β hε, BasedJetAlgebra.map_eval_symbol ε ε' r ρ β hε]
  exact hle ha

/-- Functoriality in `(R, B, ε)`: for `ρ : R → R'` and `β : B → B'` compatible with the scalar actions and the
augmentations, `d_q b ↦ d_q (β b)`. -/

noncomputable def BasedJetAlgebra.map {R B R' B' : Type u} [CommRing R] [CommRing B] [Algebra R B]
    [CommRing R'] [CommRing B'] [Algebra R' B'] (ε : B →ₐ[R] R) (ε' : B' →ₐ[R'] R') (r : ℕ)
    (ρ : R →+* R') (β : B →+* B')
    (hβ : ∀ (a : R) (b : B), β (a • b) = ρ a • β b) (hε : ∀ b : B, ε' (β b) = ρ (ε b)) :
    BasedJetAlgebra ε r →+* BasedJetAlgebra ε' r :=
  Ideal.Quotient.lift (BasedJetAlgebra.relations ε r)
    ((Ideal.Quotient.mk (BasedJetAlgebra.relations ε' r)).comp
      (MvPolynomial.eval₂Hom (MvPolynomial.C.comp ρ)
        (fun qb : Fin r × B => MvPolynomial.X (qb.1, β qb.2))))
    (BasedJetAlgebra.map_wellDefined ε ε' r ρ β hβ hε)

theorem BasedJetAlgebra.map_id {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    (ε : B →ₐ[R] R) (r : ℕ) :
    BasedJetAlgebra.map ε ε r (RingHom.id R) (RingHom.id B) (fun _ _ => rfl) (fun _ => rfl) =
      RingHom.id _ := by
  apply Ideal.Quotient.ringHom_ext
  apply MvPolynomial.ringHom_ext
  · intro a
    show Ideal.Quotient.mk _ (MvPolynomial.eval₂Hom _ _ (MvPolynomial.C a)) = _
    rw [MvPolynomial.eval₂Hom_C]
    rfl
  · intro i
    show Ideal.Quotient.mk _ (MvPolynomial.eval₂Hom _ _ (MvPolynomial.X i)) = _
    rw [MvPolynomial.eval₂Hom_X']
    rfl

end
