import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.LaurentCechComplex

/-! # Laurent monomial basis of the localizations `R[T]_{T_I}`

Purely algebraic, `R` any commutative ring. Let `L = R[ℤ^{N+1}]` (`LaurentRing`, the Laurent polynomial
ring, implemented as `AddMonoidAlgebra R (Fin (N+1) → ℤ)`).
1. `toLaurent : R[T_0..T_N] →ₐ[R] L` (`mapDomain` along `ℕ ↪ ℤ`) is injective and sends
   `monomial m r` to `single m r`;
2. for every `I ⊆ {0..N}`, `emb I : R[T]_{T_I} →ₐ[R] L` is injective, `emb I ∘ algebraMap = toLaurent`,
   and `emb T ∘ locRes = emb S`;
3. **image description**: `emb I ((R[T]_{T_I})_d) = supported {e : ℤ^{N+1} | NEG(e) ⊆ I ∧ Σ e = d}`
   (`map_degPiece`), where `NEG(e) = {k | e_k < 0}` (the set `good I d`);
4. consequences: `S → S_{T_I}` is injective; the image of `polyPiece` is bounded by
   `supported {e ≥ 0, Σ e = d}` (`exists_polyPiece_toLaurent_eq`).

Proof: `T_I ↦ single (1_I) 1` is invertible in `L` (inverse `single (−1_I) 1`), so
`IsLocalization.Away.liftAlgHom` gives `emb`; `a/T_I^j ↦ toLaurent a · single (−j·1_I) 1` (`emb_mk`),
with coefficients shifted by `coeff_mul_single_apply`; conversely `single e r` (`e ∈ good I d`) is the
image of `monomial (e + j·1_I) r / T_I^j` with `j = Σ|e_k|`.

Source: the first paragraph of the proof of Stacks 01XT (the `R`-basis of `S_{T_{i_0}⋯T_{i_p}}` is
`T^e` with `e_k ≥ 0` for `k ∉ {i_0..i_p}`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

noncomputable section

namespace LaurentCech

variable (R : Type u) [CommRing R] (N : ℕ)

/-- The Laurent polynomial ring `R[ℤ^{N+1}]`. -/
abbrev LaurentRing : Type u := AddMonoidAlgebra R (Fin (N + 1) → ℤ)

/-- The embedding of exponents `ℕ^{N+1} → ℤ^{N+1}`. -/
def castExp : (Fin (N + 1) →₀ ℕ) →+ (Fin (N + 1) → ℤ) where
  toFun m := fun k => (m k : ℤ)
  map_zero' := by ext; simp
  map_add' := by intros; ext; simp

theorem castExp_apply (m : Fin (N + 1) →₀ ℕ) (k : Fin (N + 1)) : castExp N m k = (m k : ℤ) := rfl

theorem castExp_injective : Function.Injective (castExp N) := by
  intro m m' h
  ext k
  have := congrFun h k
  rw [castExp_apply, castExp_apply] at this
  exact_mod_cast this

theorem sum_castExp (m : Fin (N + 1) →₀ ℕ) : ∑ k, castExp N m k = (m.degree : ℤ) := by
  rw [Finsupp.degree_eq_sum]
  push_cast
  rfl

/-- `R[T_0..T_N] → R[ℤ^{N+1}]`. -/
def toLaurent : MvPolynomial (Fin (N + 1)) R →ₐ[R] LaurentRing R N :=
  AddMonoidAlgebra.mapDomainAlgHom R R (castExp N)

theorem toLaurent_apply (a : MvPolynomial (Fin (N + 1)) R) :
    toLaurent R N a = AddMonoidAlgebra.mapDomain (castExp N) a := rfl

theorem toLaurent_monomial (m : Fin (N + 1) →₀ ℕ) (r : R) :
    toLaurent R N (MvPolynomial.monomial m r) = AddMonoidAlgebra.single (castExp N m) r := by
  rw [toLaurent_apply, ← MvPolynomial.single_eq_monomial, AddMonoidAlgebra.mapDomain_single]

theorem toLaurent_injective : Function.Injective (toLaurent R N) :=
  fun _ _ h => AddMonoidAlgebra.mapDomain_injective (castExp_injective N) h

theorem coeff_toLaurent (a : MvPolynomial (Fin (N + 1)) R) :
    (toLaurent R N a).coeff = Finsupp.mapDomain (castExp N) (AddMonoidAlgebra.coeff a) := rfl

/-- Every exponent in the support of `toLaurent a` comes from a monomial of `a`. -/
theorem exists_of_coeff_toLaurent_ne_zero (a : MvPolynomial (Fin (N + 1)) R)
    (e : Fin (N + 1) → ℤ) (h : (toLaurent R N a).coeff e ≠ 0) :
    ∃ m, MvPolynomial.coeff m a ≠ 0 ∧ castExp N m = e := by
  classical
  rw [coeff_toLaurent] at h
  have hmem : e ∈ (Finsupp.mapDomain (castExp N) (AddMonoidAlgebra.coeff a)).support :=
    Finsupp.mem_support_iff.2 h
  rw [Finsupp.mapDomain_support_of_injective (castExp_injective N)] at hmem
  obtain ⟨m, hm, rfl⟩ := Finset.mem_image.1 hmem
  exact ⟨m, Finsupp.mem_support_iff.1 hm, rfl⟩

/-- `1_I ∈ ℤ^{N+1}`: the indicator vector of `I` (as `castExp (∑_{i∈I} single i 1)`). -/
def expI (I : Finset (Fin (N + 1))) : Fin (N + 1) → ℤ :=
  castExp N (∑ i ∈ I, Finsupp.single i 1)

theorem expI_apply (I : Finset (Fin (N + 1))) (k : Fin (N + 1)) :
    expI N I k = if k ∈ I then 1 else 0 := by
  classical
  simp [expI, castExp_apply, Finsupp.finsetSum_apply, Finsupp.single_apply, eq_comm]

theorem sum_expI (I : Finset (Fin (N + 1))) : ∑ k, expI N I k = I.card := by
  classical
  simp [expI_apply]

theorem prodX_eq_monomial (I : Finset (Fin (N + 1))) :
    prodX R N I = MvPolynomial.monomial (∑ i ∈ I, Finsupp.single i 1) 1 := by
  rw [prodX, MvPolynomial.monomial_sum_one]
  rfl

theorem toLaurent_prodX (I : Finset (Fin (N + 1))) :
    toLaurent R N (prodX R N I) = AddMonoidAlgebra.single (expI N I) 1 := by
  rw [prodX_eq_monomial, toLaurent_monomial]
  rfl

theorem toLaurent_prodX_pow (I : Finset (Fin (N + 1))) (j : ℕ) :
    toLaurent R N (prodX R N I ^ j) = AddMonoidAlgebra.single (j • expI N I) 1 := by
  rw [map_pow, toLaurent_prodX, AddMonoidAlgebra.single_pow, one_pow]

theorem isUnit_single (e : Fin (N + 1) → ℤ) :
    IsUnit (AddMonoidAlgebra.single e (1 : R) : LaurentRing R N) :=
  isUnit_iff_exists_inv.2 ⟨AddMonoidAlgebra.single (-e) 1, by
    rw [AddMonoidAlgebra.single_mul_single, add_neg_cancel, mul_one]
    rfl⟩

theorem isUnit_toLaurent_prodX (I : Finset (Fin (N + 1))) :
    IsUnit (toLaurent R N (prodX R N I)) := by
  rw [toLaurent_prodX]
  exact isUnit_single R N _

/-- `R[T]_{T_I} → R[ℤ^{N+1}]`. -/
def emb (I : Finset (Fin (N + 1))) : Loc R N I →ₐ[R] LaurentRing R N :=
  IsLocalization.Away.liftAlgHom (A := R) (x := prodX R N I) (f := toLaurent R N)
    (isUnit_toLaurent_prodX R N I)

theorem emb_algebraMap (I : Finset (Fin (N + 1))) (a : MvPolynomial (Fin (N + 1)) R) :
    emb R N I (algebraMap _ (Loc R N I) a) = toLaurent R N a := by
  show IsLocalization.Away.lift (prodX R N I) (isUnit_toLaurent_prodX R N I) _ = _
  rw [IsLocalization.Away.lift_eq]
  rfl

theorem emb_injective (I : Finset (Fin (N + 1))) : Function.Injective (emb R N I) := by
  have := (IsLocalization.injective_iff_map_algebraMap_eq (Submonoid.powers (prodX R N I))
    (emb R N I).toRingHom).2
  refine this fun x y => ⟨fun h => by rw [h], fun h => ?_⟩
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, emb_algebraMap] at h
  rw [toLaurent_injective R N h]

/-- `S → S_{T_I}` is injective (via `toLaurent = emb ∘ algebraMap`). -/
theorem algebraMap_loc_injective (I : Finset (Fin (N + 1))) :
    Function.Injective (algebraMap (MvPolynomial (Fin (N + 1)) R) (Loc R N I)) := by
  intro x y h
  apply toLaurent_injective R N
  rw [← emb_algebraMap R N I, ← emb_algebraMap R N I, h]

theorem emb_locRes {S T : Finset (Fin (N + 1))} (h : S ⊆ T) (x : Loc R N S) :
    emb R N T (locRes h x) = emb R N S x := by
  have key : (emb R N T).toRingHom.comp (locRes (R := R) h).toRingHom = (emb R N S).toRingHom := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (prodX R N S))
    ext a
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      rw [locRes_algebraMap, emb_algebraMap, emb_algebraMap]
    · simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      rw [locRes_algebraMap, emb_algebraMap, emb_algebraMap]
  exact congrArg (fun φ : Loc R N S →+* LaurentRing R N => φ x) key

theorem emb_mk_mul (I : Finset (Fin (N + 1))) (a : MvPolynomial (Fin (N + 1)) R) (j : ℕ) :
    emb R N I (Localization.mk a (⟨prodX R N I ^ j, j, rfl⟩ : Submonoid.powers (prodX R N I))) *
      AddMonoidAlgebra.single (j • expI N I) 1 = toLaurent R N a := by
  rw [← toLaurent_prodX_pow, ← emb_algebraMap R N I, ← map_mul, Localization.mk_eq_mk',
    IsLocalization.mk'_spec, emb_algebraMap]

theorem emb_mk (I : Finset (Fin (N + 1))) (a : MvPolynomial (Fin (N + 1)) R) (j : ℕ) :
    emb R N I (Localization.mk a (⟨prodX R N I ^ j, j, rfl⟩ : Submonoid.powers (prodX R N I))) =
      toLaurent R N a * AddMonoidAlgebra.single (-(j • expI N I)) 1 := by
  rw [← emb_mk_mul R N I a j, mul_assoc, AddMonoidAlgebra.single_mul_single, add_neg_cancel,
    mul_one]
  exact (mul_one _).symm

/-- The set of exponents `{e : ℤ^{N+1} | NEG(e) ⊆ I ∧ Σ e = d}`. -/
def good (I : Finset (Fin (N + 1))) (d : ℤ) : Set (Fin (N + 1) → ℤ) :=
  {e | (∀ k, e k < 0 → k ∈ I) ∧ ∑ k, e k = d}

theorem mem_good {I : Finset (Fin (N + 1))} {d : ℤ} {e : Fin (N + 1) → ℤ} :
    e ∈ good N I d ↔ (∀ k, e k < 0 → k ∈ I) ∧ ∑ k, e k = d := Iff.rfl

theorem good_mono {I J : Finset (Fin (N + 1))} (h : I ⊆ J) (d : ℤ) : good N I d ⊆ good N J d :=
  fun _ he => ⟨fun k hk => h (he.1 k hk), he.2⟩

/-- `emb I` maps `(R[T]_{T_I})_d` into `supported (good I d)`. -/
theorem emb_mem_supported (I : Finset (Fin (N + 1))) (d : ℤ) {x : Loc R N I}
    (hx : x ∈ degPiece R N I d) :
    emb R N I x ∈ AddMonoidAlgebra.supported R R (good N I d) := by
  classical
  have : (degPiece R N I d).map (emb R N I).toLinearMap ≤
      AddMonoidAlgebra.supported R R (good N I d) := by
    rw [degPiece, Submodule.map_span_le]
    rintro _ ⟨j, i, a, ha, hi, rfl⟩
    rw [AlgHom.toLinearMap_apply, emb_mk, AddMonoidAlgebra.mem_supported']
    intro e he
    rw [AddMonoidAlgebra.coeff_mul_single_apply, mul_one, neg_neg]
    by_contra hne
    obtain ⟨m, hm, hme⟩ := exists_of_coeff_toLaurent_ne_zero R N a _ hne
    have hdeg : m.degree = i := by
      rw [MvPolynomial.mem_homogeneousSubmodule] at ha
      have := ha hm
      rwa [Finsupp.degree_eq_weight_one]
    apply he
    refine ⟨fun k hk => ?_, ?_⟩
    · by_contra hkI
      have h1 := congrFun hme k
      simp only [castExp_apply, Pi.add_apply, Pi.smul_apply, expI_apply, if_neg hkI, smul_zero,
        add_zero] at h1
      rw [← h1] at hk
      exact absurd hk (not_lt.2 (Int.natCast_nonneg _))
    · have h1 : ∑ k, (e + j • expI N I) k = ∑ k, castExp N m k := by rw [hme]
      simp only [Pi.add_apply] at h1
      rw [sum_castExp, hdeg, Finset.sum_add_distrib] at h1
      have h2 : ∑ k, (j • expI N I) k = j * I.card := by
        simp only [Pi.smul_apply, nsmul_eq_mul, ← Finset.mul_sum, sum_expI]
      rw [h2] at h1
      rw [hi] at h1
      linarith
  exact this (Submodule.mem_map_of_mem hx)

/-- Conversely, `single e r` (`e ∈ good I d`) is the image of `monomial (e + j·1_I) r / T_I^j`. -/
theorem single_mem_map_degPiece (I : Finset (Fin (N + 1))) (d : ℤ) {e : Fin (N + 1) → ℤ}
    (he : e ∈ good N I d) (r : R) :
    AddMonoidAlgebra.single e r ∈ (degPiece R N I d).map (emb R N I).toLinearMap := by
  classical
  set j : ℕ := ∑ k, (e k).natAbs with hj
  have hnn : ∀ k, 0 ≤ e k + (j • expI N I) k := by
    intro k
    simp only [Pi.smul_apply, expI_apply, nsmul_eq_mul]
    split_ifs with hk
    · have : (e k).natAbs ≤ j := Finset.single_le_sum (f := fun k => (e k).natAbs)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
      have h2 : ((e k).natAbs : ℤ) ≤ (j : ℤ) := by exact_mod_cast this
      omega
    · have := he.1 k
      simp only [mul_zero, add_zero]
      by_contra h
      exact hk (this (not_le.1 h))
  set m : Fin (N + 1) →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun k => (e k + (j • expI N I) k).toNat)
    with hm
  have hcast : castExp N m = e + j • expI N I := by
    funext k
    rw [castExp_apply, hm, Finsupp.coe_equivFunOnFinite_symm, Int.toNat_of_nonneg (hnn k)]
    rfl
  have hdeg : (m.degree : ℤ) = j * I.card + d := by
    rw [← sum_castExp, hcast]
    simp only [Pi.add_apply]
    rw [Finset.sum_add_distrib, he.2]
    simp only [Pi.smul_apply, nsmul_eq_mul, ← Finset.mul_sum, sum_expI]
    ring
  refine Submodule.mem_map.2 ⟨Localization.mk (MvPolynomial.monomial m r)
    (⟨prodX R N I ^ j, j, rfl⟩ : Submonoid.powers (prodX R N I)), ?_, ?_⟩
  · apply Submodule.subset_span
    exact ⟨j, m.degree, MvPolynomial.monomial m r,
      MvPolynomial.isHomogeneous_monomial r rfl, hdeg, rfl⟩
  · rw [AlgHom.toLinearMap_apply, emb_mk, toLaurent_monomial, hcast,
      AddMonoidAlgebra.single_mul_single, mul_one, add_neg_cancel_right]

/-- **Image description**: `emb I ((R[T]_{T_I})_d) = supported (good I d)`. -/
theorem map_degPiece (I : Finset (Fin (N + 1))) (d : ℤ) :
    (degPiece R N I d).map (emb R N I).toLinearMap =
      AddMonoidAlgebra.supported R R (good N I d) := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    exact emb_mem_supported R N I d hx
  · rw [AddMonoidAlgebra.supported_eq_span_single, Submodule.span_le]
    rintro _ ⟨e, he, rfl⟩
    exact single_mem_map_degPiece R N I d he 1

theorem exists_emb_eq (I : Finset (Fin (N + 1))) (d : ℤ) {f : LaurentRing R N}
    (hf : f ∈ AddMonoidAlgebra.supported R R (good N I d)) :
    ∃ x ∈ degPiece R N I d, emb R N I x = f := by
  rw [← map_degPiece] at hf
  obtain ⟨x, hx, hxf⟩ := Submodule.mem_map.1 hf
  exact ⟨x, hx, hxf⟩

/-- Elements of `polyPiece` land in the degree-`d` piece of `S_{T_I}`. -/
theorem algebraMap_mem_degPiece (I : Finset (Fin (N + 1))) (d : ℤ)
    {a : MvPolynomial (Fin (N + 1)) R} (ha : a ∈ polyPiece R N d) :
    algebraMap _ (Loc R N I) a ∈ degPiece R N I d := by
  rw [polyPiece] at ha
  split_ifs at ha with hd
  · apply Submodule.subset_span
    refine ⟨0, d.toNat, a, ha, by simp [Int.toNat_of_nonneg hd], ?_⟩
    have h1 : (⟨prodX R N I ^ 0, 0, rfl⟩ : Submonoid.powers (prodX R N I)) = 1 :=
      Subtype.ext (pow_zero _)
    rw [h1, Localization.mk_one_eq_algebraMap]
  · rw [Submodule.mem_bot] at ha
    rw [ha, map_zero]
    exact Submodule.zero_mem _

/-- A Laurent polynomial with nonnegative support and `Σ = d` comes from `polyPiece d`. -/
theorem exists_polyPiece_toLaurent_eq (d : ℤ) {f : LaurentRing R N}
    (hf : f ∈ AddMonoidAlgebra.supported R R {e : Fin (N + 1) → ℤ | (∀ k, 0 ≤ e k) ∧ ∑ k, e k = d}) :
    ∃ a ∈ polyPiece R N d, toLaurent R N a = f := by
  classical
  have : AddMonoidAlgebra.supported R R {e : Fin (N + 1) → ℤ | (∀ k, 0 ≤ e k) ∧ ∑ k, e k = d} ≤
      (polyPiece R N d).map (toLaurent R N).toLinearMap := by
    rw [AddMonoidAlgebra.supported_eq_span_single, Submodule.span_le]
    rintro _ ⟨e, he, rfl⟩
    set m : Fin (N + 1) →₀ ℕ := Finsupp.equivFunOnFinite.symm (fun k => (e k).toNat) with hm
    have hcast : castExp N m = e := by
      funext k
      rw [castExp_apply, hm, Finsupp.coe_equivFunOnFinite_symm, Int.toNat_of_nonneg (he.1 k)]
    have hdeg : (m.degree : ℤ) = d := by rw [← sum_castExp, hcast, he.2]
    have hd : 0 ≤ d := hdeg ▸ Int.natCast_nonneg _
    refine Submodule.mem_map.2 ⟨MvPolynomial.monomial m 1, ?_, ?_⟩
    · rw [polyPiece, if_pos hd]
      exact MvPolynomial.isHomogeneous_monomial 1 (by omega)
    · rw [AlgHom.toLinearMap_apply, toLaurent_monomial, hcast]
  obtain ⟨a, ha, haf⟩ := Submodule.mem_map.1 (this hf)
  exact ⟨a, ha, haf⟩

end LaurentCech

end
