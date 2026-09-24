import MiyaokaMori.Paper.S2WeightedJets.Jets.CoeffSystemInstances

/-! # The based jet algebra of a polynomial algebra is a weighted polynomial algebra

Statement (the affine-space case of Ein–Mustaţă, *Jet schemes and singularities*, §2, at the level
of rings): if `B` is isomorphic as an `R`-algebra to `MvPolynomial ι R` (via `β`, with an arbitrary
augmentation `ε`), then

    `BasedJetAlgebra.mvPolynomialEquiv : J_r(B, ε) ≃+* MvPolynomial (Fin r × ι) R`,

which sends the structure map to the constants `C` (`mvPolynomialEquiv_algebraMap`) and matches the
grading pieces with the weighted homogeneous components
(`mem_grading_iff_isWeightedHomogeneous`: `x ∈ grading ε r m ↔ (equiv x).IsWeightedHomogeneous (weight r ι) m`,
with the weight convention `BasedJetAlgebra.weight`: the generator `x_{q,i} = D_{q+1}(β⁻¹ X i)` has
weight `q+1`).

This is the ring isomorphism on each chart of the weighted polynomial atlas of the jet graded
algebra (`JetAlgebraLocallyWeightedPolynomial`): on a chart `Z|_U ≅ 𝔸^{n+1}_U`,
`J_r(Γ(Z, π⁻¹U), ε_U) ≅ Γ(C, U)[x_{i,q}]`. It is purely algebraic — no sheaves, no
quasi-coherence, no dependence on `jetGradedAlgebra` — and is proved entirely from the universal
property of coefficient systems.

Proof (four constructive steps):
1. The forward map comes from a coefficient system: `polyJetHom` sends the generator `X i` to
   `ε(X i) + Σ_{q<r} x_{q,i} t^{q+1}` in the truncated ring, `CoeffSystem.ofTruncated` turns it
   into a coefficient system, and `CoeffSystem.lift` gives `toMvPolynomial`.
2. The inverse is the universal property of the polynomial ring: `x_{q,i} ↦ D_{q+1}(β⁻¹ X i)`
   (`ofMvPolynomial`).
3. `toMvPolynomial ∘ ofMvPolynomial = id` is checked on generators;
   `ofMvPolynomial ∘ toMvPolynomial = id` uses `BasedJetAlgebra.ringHom_ext`, whose obligation
   "the inverse map sends the `n`-th coefficient of `ψ` back to `D_n b`" is proved by
   `MvPolynomial.induction_on` on `b` (addition via `coeffTotal_add`; for multiplication the Cauchy
   product of `coeffTotal_mul` matches the Leibniz rule `coeffClass_mul`).
4. Grading: forward via `CoeffSystem.lift_mem` (the obligation "the `n`-th coefficient of `ψ` is
   weighted homogeneous of weight `n`" is the same induction); backward directly by
   `IsWeightedHomogeneous.induction_on` on weighted homogeneous polynomials, monomial by monomial
   with `SetLike.prod_mem_graded` + `coeffClass_mem_grading`. Given the backward direction, the
   `⟸` of the `iff` follows from step 3.

References: §2.2 of the paper; Ein–Mustaţă, *Jet schemes and singularities*, §2 (the jet scheme
of `𝔸^n` is `𝔸^{nr}`); Vojta, *Jets via Hasse–Schmidt derivations*, §1.
-/

set_option autoImplicit false
universe u
noncomputable section

open MiyaokaMori.Jet MiyaokaMori.Jet.TruncatedJetRing

namespace BasedJetAlgebra

variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B] {ι : Type u}
  (ε : B →ₐ[R] R) (r : ℕ) (β : B ≃ₐ[R] MvPolynomial ι R)

/-- The `n`-th coefficient of the universal jet of the generator `X i`. -/
def polyGenCoeff (n : ℕ) (i : ι) : MvPolynomial (Fin r × ι) R :=
  if n = 0 then MvPolynomial.C (ε (β.symm (MvPolynomial.X i)))
  else if h : n - 1 < r then MvPolynomial.X (⟨n - 1, h⟩, i) else 0

theorem polyGenCoeff_isWeightedHomogeneous (n : ℕ) (i : ι) :
    (polyGenCoeff ε r β n i).IsWeightedHomogeneous (weight r ι) n := by
  unfold polyGenCoeff
  split_ifs with h0 h
  · subst h0; exact MvPolynomial.isWeightedHomogeneous_C _ _
  · have := MvPolynomial.isWeightedHomogeneous_X R (weight r ι) ((⟨n - 1, h⟩ : Fin r), i)
    rw [weight_apply] at this
    have hn : n - 1 + 1 = n := Nat.sub_add_cancel (Nat.pos_of_ne_zero h0)
    simpa [hn] using this
  · exact MvPolynomial.isWeightedHomogeneous_zero _ _ _

/-- A polynomial representative of the universal jet of a generator. -/
def polyGenPoly (i : ι) : Polynomial (MvPolynomial (Fin r × ι) R) :=
  ∑ n ∈ Finset.range (r + 1), Polynomial.monomial n (polyGenCoeff ε r β n i)

theorem polyGenPoly_coeff (n : ℕ) (hn : n ≤ r) (i : ι) :
    (polyGenPoly ε r β i).coeff n = polyGenCoeff ε r β n i := by
  rw [polyGenPoly, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial]
  rw [Finset.sum_ite_eq' (Finset.range (r + 1)) n, if_pos (Finset.mem_range.mpr (by omega))]

/-- The universal jet on the polynomial algebra: `X i ↦ ε(X i) + Σ_{q<r} x_{q,i} t^{q+1}`. -/
def polyJetHom : MvPolynomial ι R →+*
    TruncatedJetRing (MvPolynomial (Fin r × ι) R) r :=
  MvPolynomial.eval₂Hom
    ((MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.eta r).comp
      (MvPolynomial.C : R →+* MvPolynomial (Fin r × ι) R))
    (fun i => jetProjection _ r (polyGenPoly ε r β i))

@[simp] theorem polyJetHom_C (a : R) :
    polyJetHom ε r β (MvPolynomial.C a) =
      MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.eta r (MvPolynomial.C a) :=
  MvPolynomial.eval₂Hom_C _ _ a

@[simp] theorem polyJetHom_X (i : ι) :
    polyJetHom ε r β (MvPolynomial.X i) = jetProjection _ r (polyGenPoly ε r β i) :=
  MvPolynomial.eval₂Hom_X' _ _ i

/-- The universal jet transported back to `B` along `β`. -/
def polyJet : B →+* TruncatedJetRing (MvPolynomial (Fin r × ι) R) r :=
  (polyJetHom ε r β).comp (β : B →ₐ[R] MvPolynomial ι R).toRingHom

theorem polyJet_apply (b : B) : polyJet ε r β b = polyJetHom ε r β (β b) := rfl

theorem polyJet_smul (a : R) (b : B) :
    polyJet ε r β (a • b) =
      MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.eta r (MvPolynomial.C a) * polyJet ε r β b := by
  rw [polyJet_apply, polyJet_apply, map_smul, MvPolynomial.smul_eq_C_mul, map_mul, polyJetHom_C]

theorem polyJetHom_epsilon (p : MvPolynomial ι R) :
    MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.epsilon r (polyJetHom ε r β p) =
      MvPolynomial.C (ε (β.symm p)) := by
  have h : (MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.epsilon r).comp (polyJetHom ε r β) =
      (MvPolynomial.C : R →+* MvPolynomial (Fin r × ι) R).comp
        ((ε : B →ₐ[R] R).toRingHom.comp (β.symm : MvPolynomial ι R →ₐ[R] B).toRingHom) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
    · show MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.epsilon r (polyJetHom ε r β (MvPolynomial.C a)) =
        MvPolynomial.C (ε (β.symm (MvPolynomial.C a)))
      have hb : ε (β.symm (MvPolynomial.C a)) = a := by
        rw [← MvPolynomial.algebraMap_eq, AlgEquiv.commutes, AlgHom.commutes]; rfl
      rw [hb, polyJetHom_C]
      show (Polynomial.C (MvPolynomial.C a : MvPolynomial (Fin r × ι) R)).eval 0 = _
      exact Polynomial.eval_C
    · show MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.epsilon r (polyJetHom ε r β (MvPolynomial.X i)) =
        MvPolynomial.C (ε (β.symm (MvPolynomial.X i)))
      rw [polyJetHom_X]
      show (polyGenPoly ε r β i).eval 0 = _
      rw [← Polynomial.coeff_zero_eq_eval_zero, polyGenPoly_coeff ε r β 0 (Nat.zero_le r),
        polyGenCoeff, if_pos rfl]
  exact DFunLike.congr_fun h p


theorem polyJet_epsilon (b : B) :
    MiyaokaMori.RingTheory.GlobalTruncatedParameterAPI.epsilon r (polyJet ε r β b) = MvPolynomial.C (ε b) := by
  rw [polyJet_apply, polyJetHom_epsilon, AlgEquiv.symm_apply_apply]

/-- The coefficient system on the polynomial algebra (an instance of `CoeffSystem.ofTruncated`, with
values in `MvPolynomial (Fin r × ι) R`). -/
def polyCoeffSystem :
    CoeffSystem ε r (MvPolynomial.C : R →+* MvPolynomial (Fin r × ι) R) :=
  CoeffSystem.ofTruncated ε r MvPolynomial.C (polyJet ε r β)
    (polyJet_smul ε r β) (polyJet_epsilon ε r β)

theorem polyCoeffSystem_coeff (n : ℕ) (b : B) :
    (polyCoeffSystem ε r β).coeff n b = coeffTotal r n (polyJetHom ε r β (β b)) := rfl

/-- **The forward map** `J_r(B, ε) → R[x_{q,i}]`. -/
def toMvPolynomial : BasedJetAlgebra ε r →+* MvPolynomial (Fin r × ι) R :=
  (polyCoeffSystem ε r β).lift

/-- **The inverse map** `x_{q,i} ↦ D_{q+1}(β⁻¹ X i)`. -/
def ofMvPolynomial : MvPolynomial (Fin r × ι) R →+* BasedJetAlgebra ε r :=
  MvPolynomial.eval₂Hom (algebraMap R (BasedJetAlgebra ε r))
    (fun qi : Fin r × ι => coeffClass ε r (qi.1.1 + 1) (β.symm (MvPolynomial.X qi.2)))

@[simp] theorem ofMvPolynomial_C (a : R) :
    ofMvPolynomial ε r β (MvPolynomial.C a) = algebraMap R (BasedJetAlgebra ε r) a :=
  MvPolynomial.eval₂Hom_C _ _ a

@[simp] theorem ofMvPolynomial_X (qi : Fin r × ι) :
    ofMvPolynomial ε r β (MvPolynomial.X qi) =
      coeffClass ε r (qi.1.1 + 1) (β.symm (MvPolynomial.X qi.2)) :=
  MvPolynomial.eval₂Hom_X' _ _ qi

theorem ofMvPolynomial_polyGenCoeff (n : ℕ) (hn : n ≤ r) (i : ι) :
    ofMvPolynomial ε r β (polyGenCoeff ε r β n i) =
      coeffClass ε r n (β.symm (MvPolynomial.X i)) := by
  unfold polyGenCoeff
  split_ifs with h0 h
  · subst h0
    rw [ofMvPolynomial_C, coeffClass_zero_order]
    rfl
  · rw [ofMvPolynomial_X]
    have hn1 : n - 1 + 1 = n := Nat.sub_add_cancel (Nat.pos_of_ne_zero h0)
    simp only [hn1]
  · exact absurd hn (by omega)

/-- **The key induction**: the inverse map sends the `n`-th coefficient of `ψ` back to `D_n`. -/
theorem ofMvPolynomial_coeffTotal (p : MvPolynomial ι R) :
    ∀ n ≤ r, ofMvPolynomial ε r β (coeffTotal r n (polyJetHom ε r β p)) =
      coeffClass ε r n (β.symm p) := by
  refine MvPolynomial.induction_on
    (motive := fun p => ∀ n ≤ r, ofMvPolynomial ε r β (coeffTotal r n (polyJetHom ε r β p)) =
      coeffClass ε r n (β.symm p)) p ?_ ?_ ?_
  · intro a n hn
    have hb : β.symm (MvPolynomial.C a) = algebraMap R B a := by
      rw [← MvPolynomial.algebraMap_eq, AlgEquiv.commutes]
    rw [hb, Algebra.algebraMap_eq_smul_one, coeffClass_smul ε r n hn, coeffClass_one ε r n hn,
      polyJetHom_C]
    show ofMvPolynomial ε r β
      (coeffTotal r n (jetProjection _ r (Polynomial.C (MvPolynomial.C a)))) = _
    rw [coeffTotal_mk r hn, Polynomial.coeff_C]
    split_ifs with h
    · rw [ofMvPolynomial_C, mul_one]; rfl
    · rw [map_zero, mul_zero]
  · intro p q ihp ihq n hn
    rw [map_add, coeffTotal_add r hn, map_add, map_add, ihp n hn, ihq n hn,
      coeffClass_add ε r n hn]
  · intro p i ih n hn
    rw [map_mul, coeffTotal_mul r hn, map_sum, map_mul, coeffClass_mul ε r n hn]
    refine Finset.sum_congr rfl fun ij hij => ?_
    have h := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
    rw [map_mul, ih ij.1 (by omega)]
    congr 1
    rw [polyJetHom_X, coeffTotal_mk r (by omega), polyGenPoly_coeff ε r β ij.2 (by omega),
      ofMvPolynomial_polyGenCoeff ε r β ij.2 (by omega)]


theorem ofMvPolynomial_toMvPolynomial (x : BasedJetAlgebra ε r) :
    ofMvPolynomial ε r β (toMvPolynomial ε r β x) = x := by
  have h : (ofMvPolynomial ε r β).comp (toMvPolynomial ε r β) = RingHom.id _ := by
    refine BasedJetAlgebra.ringHom_ext (fun a => ?_) (fun n hn b => ?_)
    · show ofMvPolynomial ε r β (toMvPolynomial ε r β (algebraMap R _ a)) = _
      rw [toMvPolynomial, CoeffSystem.lift_algebraMap, ofMvPolynomial_C]
      rfl
    · show ofMvPolynomial ε r β (toMvPolynomial ε r β (coeffClass ε r n b)) = _
      rw [toMvPolynomial, CoeffSystem.lift_coeffClass _ n hn, polyCoeffSystem_coeff]
      have hb := ofMvPolynomial_coeffTotal ε r β (β b) n hn
      rw [AlgEquiv.symm_apply_apply] at hb
      exact hb
  exact DFunLike.congr_fun h x

theorem toMvPolynomial_ofMvPolynomial (p : MvPolynomial (Fin r × ι) R) :
    toMvPolynomial ε r β (ofMvPolynomial ε r β p) = p := by
  have h : (toMvPolynomial ε r β).comp (ofMvPolynomial ε r β) = RingHom.id _ := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun qi => ?_)
    · show toMvPolynomial ε r β (ofMvPolynomial ε r β (MvPolynomial.C a)) = _
      rw [ofMvPolynomial_C, toMvPolynomial, CoeffSystem.lift_algebraMap]
      rfl
    · show toMvPolynomial ε r β (ofMvPolynomial ε r β (MvPolynomial.X qi)) = _
      have hq : qi.1.1 + 1 ≤ r := Nat.succ_le_of_lt qi.1.2
      rw [ofMvPolynomial_X, toMvPolynomial, CoeffSystem.lift_coeffClass _ _ hq,
        polyCoeffSystem_coeff, AlgEquiv.apply_symm_apply, polyJetHom_X,
        coeffTotal_mk r hq, polyGenPoly_coeff ε r β _ hq, polyGenCoeff,
        if_neg (Nat.succ_ne_zero _), dif_pos (show qi.1.1 + 1 - 1 < r from qi.1.2)]
      rfl
  exact DFunLike.congr_fun h p

/-- **The based jet algebra of a polynomial algebra is a weighted polynomial algebra**:
    `J_r(B, ε) ≃+* R[x_{q,i} ; q < r, i ∈ ι]`, with generators `x_{q,i} = D_{q+1}(β⁻¹ X i)`. -/
def mvPolynomialEquiv : BasedJetAlgebra ε r ≃+* MvPolynomial (Fin r × ι) R where
  toFun := toMvPolynomial ε r β
  invFun := ofMvPolynomial ε r β
  left_inv := ofMvPolynomial_toMvPolynomial ε r β
  right_inv := toMvPolynomial_ofMvPolynomial ε r β
  map_mul' := map_mul _
  map_add' := map_add _

@[simp] theorem mvPolynomialEquiv_algebraMap (a : R) :
    mvPolynomialEquiv ε r β (algebraMap R (BasedJetAlgebra ε r) a) = MvPolynomial.C a :=
  CoeffSystem.lift_algebraMap _ a

/-! ## Compatibility with the gradings -/

theorem polyJetHom_coeffTotal_isWeightedHomogeneous (p : MvPolynomial ι R) :
    ∀ n ≤ r, (coeffTotal r n (polyJetHom ε r β p)).IsWeightedHomogeneous (weight r ι) n := by
  refine MvPolynomial.induction_on (motive := fun p => ∀ n ≤ r,
    (coeffTotal r n (polyJetHom ε r β p)).IsWeightedHomogeneous (weight r ι) n) p ?_ ?_ ?_
  · intro a n hn
    rw [polyJetHom_C]
    show (coeffTotal r n (jetProjection _ r
      (Polynomial.C (MvPolynomial.C a)))).IsWeightedHomogeneous _ _
    rw [coeffTotal_mk r hn, Polynomial.coeff_C]
    split_ifs with h
    · subst h; exact MvPolynomial.isWeightedHomogeneous_C _ _
    · exact MvPolynomial.isWeightedHomogeneous_zero _ _ _
  · intro p q ihp ihq n hn
    rw [map_add, coeffTotal_add r hn]
    exact (ihp n hn).add (ihq n hn)
  · intro p i ih n hn
    rw [map_mul, coeffTotal_mul r hn]
    refine MvPolynomial.IsWeightedHomogeneous.sum _ _ _ fun ij hij => ?_
    have h := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
    have h2 : (coeffTotal r ij.2
        (polyJetHom ε r β (MvPolynomial.X i))).IsWeightedHomogeneous (weight r ι) ij.2 := by
      rw [polyJetHom_X, coeffTotal_mk r (by omega), polyGenPoly_coeff ε r β ij.2 (by omega)]
      exact polyGenCoeff_isWeightedHomogeneous ε r β ij.2 i
    have hm := (ih ij.1 (by omega)).mul h2
    rwa [h] at hm

attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem toMvPolynomial_isWeightedHomogeneous {m : ℕ} {x : BasedJetAlgebra ε r}
    (hx : x ∈ grading ε r m) :
    (toMvPolynomial ε r β x).IsWeightedHomogeneous (weight r ι) m :=
  (polyCoeffSystem ε r β).lift_mem
    (MvPolynomial.weightedHomogeneousSubmodule R (weight r ι))
    (fun a => MvPolynomial.isWeightedHomogeneous_C _ _)
    (fun n hn b => by
      rw [polyCoeffSystem_coeff]
      exact polyJetHom_coeffTotal_isWeightedHomogeneous ε r β (β b) n hn) hx

theorem ofMvPolynomial_mem_grading {m : ℕ} {p : MvPolynomial (Fin r × ι) R}
    (hp : p.IsWeightedHomogeneous (weight r ι) m) :
    ofMvPolynomial ε r β p ∈ grading ε r m := by
  induction hp using MvPolynomial.IsWeightedHomogeneous.induction_on with
  | zero => rw [map_zero]; exact zero_mem _
  | add p q _ _ ihp ihq => rw [map_add]; exact add_mem ihp ihq
  | monomial d a hd =>
    have hmon : ofMvPolynomial ε r β (MvPolynomial.monomial d a) =
        algebraMap R (BasedJetAlgebra ε r) a *
          d.prod fun i k => (coeffClass ε r (i.1.1 + 1) (β.symm (MvPolynomial.X i.2))) ^ k :=
      MvPolynomial.eval₂Hom_monomial _ _ _ _
    rw [hmon]
    have hprod : (d.prod fun i k =>
        (coeffClass ε r (i.1.1 + 1) (β.symm (MvPolynomial.X i.2))) ^ k)
        ∈ grading ε r (Finsupp.weight (weight r ι) d) := by
      rw [Finsupp.weight_apply, Finsupp.sum, Finsupp.prod]
      refine SetLike.prod_mem_graded _ _ _ fun i _ => ?_
      have hi : coeffClass ε r (i.1.1 + 1) (β.symm (MvPolynomial.X i.2)) ∈
          grading ε r (weight r ι i) := coeffClass_mem_grading ε r _ _
      simpa [smul_eq_mul] using SetLike.pow_mem_graded (d i) hi
    have hz := SetLike.mul_mem_graded (algebraMap_mem_grading_zero ε r a) hprod
    rwa [zero_add, hd] at hz

/-- **Compatibility with the gradings**: the `m`-th piece of `J` corresponds exactly to the weighted
homogeneous polynomials of weight `m` (weight = order: `x_{q,i}` has weight `q+1`). -/
theorem mem_grading_iff_isWeightedHomogeneous (m : ℕ) (x : BasedJetAlgebra ε r) :
    x ∈ grading ε r m ↔
      (mvPolynomialEquiv ε r β x).IsWeightedHomogeneous (weight r ι) m := by
  refine ⟨toMvPolynomial_isWeightedHomogeneous ε r β, fun h => ?_⟩
  have hx := ofMvPolynomial_mem_grading ε r β h
  rwa [show mvPolynomialEquiv ε r β x = toMvPolynomial ε r β x from rfl,
    ofMvPolynomial_toMvPolynomial] at hx

end BasedJetAlgebra
end
