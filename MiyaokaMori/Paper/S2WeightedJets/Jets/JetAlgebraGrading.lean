import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S2WeightedJets.Jets.BasedJetAlgebra
import MiyaokaMori.Paper.S2WeightedJets.Jets.BasedAffineJetQuotientGrading

/-! # The weighted grading of the based jet algebra

The based jet algebra `J_r(B, ε) = R[d_q b]/(relations)` (`BasedJetAlgebra`, of Hasse–Schmidt type) carries a
weighted grading: the generator `d_q b` (`q : Fin r`) has weight `q + 1` by definition (`BasedJetAlgebra.weight`),
the ideal of relations is homogeneous for this weight (`relations_isHomogeneous`), so the quotient algebra is a
`GradedAlgebra (BasedJetAlgebra.grading ε r)` whose `m`-th piece is the image of the submodule of polynomials of
weight `m`. We also show that `D_n b` lies in the `n`-th piece, that the coefficient ring `R` lies in the `0`-th
piece, that the `0`-th piece is exactly the image of `R` (`S_0 = O_C`), and that the functorial map
`BasedJetAlgebra.map` in `(R, B, ε)` preserves the grading.

The grading is given directly at the level of rings, so that the data is entirely constructive (the decomposition
of the quotient descends from that of the polynomial ring) and the weight convention is a `def`. Its relation to
the geometric `𝔾_m`-action is established in the module on the jet algebra coaction (the coaction on the `m`-th
piece is multiplication by `λ^m`).

References: §2 of the paper (the coordinate algebra of `J_k^s` is graded by parameter rescaling, the coefficient of
order `q` having weight `q`); Ein–Mustață, Prop. 2.2; Vojta, "Jets via Hasse–Schmidt derivations", §1.
Uses Mathlib's `MvPolynomial.weightedGradedAlgebra` and `BasedAffineJetQuotientGrading.HomogeneousQuotient`
(the grading of the quotient by a homogeneous ideal).
-/

set_option autoImplicit false

universe u

noncomputable section

open MiyaokaMori.BasedAffineJetQuotientGrading

attribute [local instance] MvPolynomial.weightedGradedAlgebra

/-- Substituting for each variable `i` a `w'`-homogeneous polynomial `g i` of weight `w i` (and transforming the
coefficients along `ρ`) preserves weighted homogeneity. -/
theorem MvPolynomial.IsWeightedHomogeneous.eval₂Hom_C_comp {R R' σ τ : Type*} [CommSemiring R]
    [CommSemiring R'] (ρ : R →+* R') {w : σ → ℕ} {w' : τ → ℕ} (g : σ → MvPolynomial τ R')
    (hg : ∀ i, (g i).IsWeightedHomogeneous w' (w i)) {p : MvPolynomial σ R} {n : ℕ}
    (hp : p.IsWeightedHomogeneous w n) :
    (MvPolynomial.eval₂Hom (MvPolynomial.C.comp ρ) g p).IsWeightedHomogeneous w' n := by
  induction hp using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => rw [map_zero]; exact MvPolynomial.isWeightedHomogeneous_zero _ _ _
  | add p q _ _ ihp ihq => rw [map_add]; exact ihp.add ihq
  | monomial d c hd =>
    rw [MvPolynomial.eval₂Hom_monomial, RingHom.comp_apply]
    refine (MvPolynomial.IsWeightedHomogeneous.C_mul ?_ _)
    rw [← hd, Finsupp.weight_apply, Finsupp.prod, Finsupp.sum]
    exact MvPolynomial.IsWeightedHomogeneous.prod _ _ _ fun i _ => by
      simpa [smul_eq_mul] using (hg i).pow (d i)

namespace BasedJetAlgebra

/-- The weight convention: the generator `d_q b` (the coefficient of order `q + 1` of `b` along the universal
jet) has weight `q + 1`, independently of `b`. -/
def weight (r : ℕ) (B : Type u) : Fin r × B → ℕ := fun qb => qb.1.1 + 1

@[simp] theorem weight_apply {r : ℕ} {B : Type u} (q : Fin r) (b : B) : weight r B (q, b) = q.1 + 1 := rfl

theorem weight_ne_zero {r : ℕ} {B : Type u} (qb : Fin r × B) : weight r B qb ≠ 0 := Nat.succ_ne_zero _

variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B] (ε : B →ₐ[R] R) (r : ℕ)

/-- The coefficient symbol `D_n b` of order `n` is a homogeneous polynomial of weight `n`. -/
theorem symbol_isWeightedHomogeneous (n : ℕ) (b : B) :
    (symbol ε r n b).IsWeightedHomogeneous (weight r B) n := by
  unfold symbol
  split_ifs with h0 h
  · subst h0; exact MvPolynomial.isWeightedHomogeneous_C _ _
  · have := MvPolynomial.isWeightedHomogeneous_X R (weight r B) ((⟨n - 1, h⟩ : Fin r), b)
    rw [weight_apply] at this
    have hn : n - 1 + 1 = n := Nat.sub_add_cancel (Nat.pos_of_ne_zero h0)
    simpa [hn] using this
  · exact MvPolynomial.isWeightedHomogeneous_zero _ _ _

/-- The ideal of relations is homogeneous for `weight`: each of the four families of relations consists of
homogeneous elements of weight `q + 1`. -/
theorem relations_isHomogeneous :
    (relations ε r).IsHomogeneous (MvPolynomial.weightedHomogeneousSubmodule R (weight r B)) := by
  refine Ideal.homogeneous_span _ _ fun p hp => ?_
  have hX : ∀ (q : Fin r) (b : B),
      (MvPolynomial.X (q, b) : MvPolynomial (Fin r × B) R).IsWeightedHomogeneous (weight r B) (q.1 + 1) :=
    fun q b => MvPolynomial.isWeightedHomogeneous_X R (weight r B) (q, b)
  rcases hp with ((⟨q, b, b', rfl⟩ | ⟨q, a, b, rfl⟩) | ⟨q, rfl⟩) | ⟨q, b, b', rfl⟩
  · exact ⟨q.1 + 1, ((hX q _).sub (hX q _)).sub (hX q _)⟩
  · exact ⟨q.1 + 1, (hX q _).sub ((hX q _).C_mul a)⟩
  · exact ⟨q.1 + 1, hX q _⟩
  · refine ⟨q.1 + 1, (hX q _).sub (MvPolynomial.IsWeightedHomogeneous.sum _ _ _ fun ij hij => ?_)⟩
    have h := (symbol_isWeightedHomogeneous ε r ij.1 b).mul (symbol_isWeightedHomogeneous ε r ij.2 b')
    rwa [Finset.HasAntidiagonal.mem_antidiagonal.mp hij] at h

/-- The `m`-th graded piece of the jet algebra: the image of the polynomials of weight `m`. -/
def grading : ℕ → Submodule R (BasedJetAlgebra ε r) :=
  HomogeneousQuotient.component (MvPolynomial.weightedHomogeneousSubmodule R (weight r B))
    (relations ε r)

instance gradedAlgebra : GradedAlgebra (grading ε r) :=
  HomogeneousQuotient.grading _ _ (relations_isHomogeneous ε r)

theorem mem_grading_iff (m : ℕ) (x : BasedJetAlgebra ε r) :
    x ∈ grading ε r m ↔ ∃ p : MvPolynomial (Fin r × B) R,
      p.IsWeightedHomogeneous (weight r B) m ∧ Ideal.Quotient.mk (relations ε r) p = x :=
  Submodule.mem_map

theorem mk_mem_grading {m : ℕ} {p : MvPolynomial (Fin r × B) R}
    (hp : p.IsWeightedHomogeneous (weight r B) m) :
    Ideal.Quotient.mk (relations ε r) p ∈ grading ε r m :=
  (mem_grading_iff ε r m _).mpr ⟨p, hp, rfl⟩

/-- `D_n b` lies in the `n`-th piece (for `n = 0` it is the constant `ε b`, for `n > r` it is `0`). -/
theorem coeffClass_mem_grading (n : ℕ) (b : B) : coeffClass ε r n b ∈ grading ε r n :=
  mk_mem_grading ε r (symbol_isWeightedHomogeneous ε r n b)

/-- The coefficient ring lies in the `0`-th piece. -/
theorem algebraMap_mem_grading_zero (a : R) :
    algebraMap R (BasedJetAlgebra ε r) a ∈ grading ε r 0 :=
  mk_mem_grading ε r (MvPolynomial.isWeightedHomogeneous_C _ a)

/-- `S_0 = R`: the `0`-th piece is exactly the image of the coefficient ring (all generators have positive
weight). -/
theorem grading_zero : grading ε r 0 = 1 := by
  refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
  · obtain ⟨p, hp, rfl⟩ := (mem_grading_iff ε r 0 x).mp hx
    have h1 := MvPolynomial.IsWeightedHomogeneous.weightedHomogeneousComponent_same hp
    rw [MvPolynomial.weightedHomogeneousComponent_zero (hw := weight_ne_zero)] at h1
    rw [← h1]
    exact Submodule.mem_one.mpr ⟨MvPolynomial.coeff 0 p, rfl⟩
  · obtain ⟨a, rfl⟩ := Submodule.mem_one.mp hx
    exact algebraMap_mem_grading_zero ε r a

/-- The functorial map preserves the grading. -/
theorem map_mem_grading {R' B' : Type u} [CommRing R'] [CommRing B'] [Algebra R' B']
    (ε' : B' →ₐ[R'] R') (ρ : R →+* R') (β : B →+* B')
    (hβ : ∀ (a : R) (b : B), β (a • b) = ρ a • β b) (hε : ∀ b : B, ε' (β b) = ρ (ε b))
    {m : ℕ} {x : BasedJetAlgebra ε r} (hx : x ∈ grading ε r m) :
    BasedJetAlgebra.map ε ε' r ρ β hβ hε x ∈ grading ε' r m := by
  obtain ⟨p, hp, rfl⟩ := (mem_grading_iff ε r m x).mp hx
  show Ideal.Quotient.mk (relations ε' r) (MvPolynomial.eval₂Hom (MvPolynomial.C.comp ρ)
    (fun qb : Fin r × B => MvPolynomial.X (qb.1, β qb.2)) p) ∈ grading ε' r m
  refine mk_mem_grading ε' r ?_
  have hg : ∀ qb : Fin r × B, (MvPolynomial.X (qb.1, β qb.2) :
      MvPolynomial (Fin r × B') R').IsWeightedHomogeneous (weight r B') (weight r B qb) := fun qb =>
    MvPolynomial.isWeightedHomogeneous_X R' (weight r B') (qb.1, β qb.2)
  exact MvPolynomial.IsWeightedHomogeneous.eval₂Hom_C_comp (w := weight r B) (w' := weight r B') ρ
    (fun qb : Fin r × B => MvPolynomial.X (qb.1, β qb.2)) hg hp

end BasedJetAlgebra

end
