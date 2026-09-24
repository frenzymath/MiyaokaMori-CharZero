import MiyaokaMori.Prelude
import MiyaokaMori.RingTheory.OrderOfVanishing.LatticeDistance

/-! # The order of a determinant as a lattice distance (Stacks 02MI)

Let `A` be a Noetherian domain of Krull dimension `≤ 1`, `K = Frac A`, `V` a finite-dimensional
`K`-vector space, `M ⊆ V` a lattice, and `φ : V → V` a `K`-linear map with `det φ ≠ 0`. Then
`ord_A(det φ) = d(M, φM)` (Stacks 02MI); in particular, if `φM ⊆ M` then `ord_A(det φ) = length_A(M/φM)`.
In Mathlib terms: `Ring.ordFrac A (LinearMap.det φ) = WithZero.exp (latDist M (φM))`.

Proof:
1. Both sides are multiplicative/additive in `φ` (`LatticeDistance` (4); `det` is multiplicative and `ordFrac`
   is a monoid homomorphism), and the right-hand side does not depend on the lattice, so choose a basis
   `V ≅ K^n`, `M₀ = A^n`, and check on generators of `GL_n(K)` (Mathlib
   `Matrix.diagonal_transvection_induction_of_det_ne_zero`: an invertible matrix is a product of transvections,
   a diagonal matrix, and transvections).
2. Diagonal `diag(b)`, `b_i ∈ A ∖ 0`: `diag(b)·A^n = ⊕ b_i A ⊆ A^n`, with quotient `≅ ∏ A/(b_i)`
   (`Submodule.quotientPi`), of length `Σ ord_A(b_i)` (`Module.length_pi_of_fintype`, the definition of
   `Ring.ord`), while `ord_A(det) = ord_A(∏ b_i) = Σ ord_A(b_i)`.
3. General diagonal `diag(d)`, `d_i = b_i/c_i`: `diag(d)·diag(c) = diag(b)`, reduce to step 2 by additivity.
4. Transvection `t = 1 + (p/q)E_ij` (`i ≠ j`): take the lattice `M_q = diag(1,…,q,…,1)·A^n` (`q` in position
   `j`); then `t·M_q ⊆ M_q` (`t(v) = v + (p/q)v_j e_i`, `v_j ∈ qA`), likewise `t⁻¹·M_q ⊆ M_q`, so
   `t·M_q = M_q` and `e(t) = d(M_q, M_q) = 0 = ord_A(1) = ord_A(det t)`.
5. General `V`: choose a `K`-basis `b`, `e : V ≃ K^n`; `det` is invariant under conjugation
   (`LinearMap.det_conj`), and the distance is invariant under `e` (`LatticeDistance` (3)).

Reference: Stacks 02MI (algebra-lemma-order-vanishing-determinant).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false

universe u v

noncomputable section

namespace Submodule

variable (A : Type*) [CommRing A] [IsDomain A] [IsNoetherianRing A] [Ring.KrullDimLE 1 A]
variable (K : Type*) [Field K] [Algebra A K] [IsFractionRing A K]
variable (ι : Type*) [Fintype ι] [DecidableEq ι]

/-- The map `A^n → K^n`. -/
def stdEmb : (ι → A) →ₗ[A] (ι → K) := (Algebra.linearMap A K).compLeft ι

lemma stdEmb_apply (a : ι → A) (i : ι) : stdEmb A K ι a i = algebraMap A K (a i) := rfl

lemma stdEmb_injective : Function.Injective (stdEmb A K ι) := by
  intro a b h
  ext i
  exact IsFractionRing.injective A K (congrFun h i)

/-- The standard lattice `A^n ⊆ K^n`. -/
def stdLattice : Submodule A (ι → K) := (⊤ : Submodule A (ι → A)).map (stdEmb A K ι)

theorem stdLattice_isLattice : IsLattice K (stdLattice A K ι) where
  fg := (Module.Finite.fg_top (R := A) (M := ι → A)).map _
  span_eq_top := by
    rw [eq_top_iff]
    intro v _
    rw [pi_eq_sum_univ' v]
    refine Submodule.sum_mem _ fun i _ => ?_
    refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    refine ⟨Pi.single i 1, trivial, ?_⟩
    ext k
    rw [stdEmb_apply]
    by_cases h : k = i
    · subst h; simp
    · simp [Pi.single_eq_of_ne h]

variable {A K ι}

/-- The image of the standard lattice under a matrix `N`. -/
abbrev matImage (N : Matrix ι ι K) : Submodule A (ι → K) :=
  (stdLattice A K ι).map ((Matrix.toLin' N).restrictScalars A)

lemma relLength_top {X : Type*} [AddCommGroup X] [Module A X] (P : Submodule A X) :
    relLength ⊤ P = Module.length A (X ⧸ P) := by
  unfold relLength
  refine (Submodule.Quotient.equiv _ _ (Submodule.topEquiv (R := A) (M := X)) ?_).length_eq
  ext x
  simp [Submodule.submoduleOf]

/-- Diagonal multiplication `A^n → A^n`. -/
def diagMul (b : ι → A) : (ι → A) →ₗ[A] (ι → A) :=
  LinearMap.pi fun i => (b i) • LinearMap.proj i

lemma diagMul_apply (b : ι → A) (a : ι → A) (i : ι) : diagMul b a i = b i * a i := rfl

lemma range_diagMul (b : ι → A) :
    LinearMap.range (diagMul b) = Submodule.pi Set.univ fun i => (Ideal.span {b i} : Ideal A) := by
  ext v
  simp only [LinearMap.mem_range, Submodule.mem_pi, Set.mem_univ, forall_true_left,
    Ideal.mem_span_singleton']
  constructor
  · rintro ⟨w, rfl⟩ i
    exact ⟨w i, by rw [diagMul_apply, mul_comm]⟩
  · intro h
    choose w hw using h
    exact ⟨w, by ext i; rw [diagMul_apply, mul_comm]; exact hw i⟩

lemma matImage_diagonal (b : ι → A) :
    (matImage (Matrix.diagonal fun i => algebraMap A K (b i)) : Submodule A (ι → K)) =
      (LinearMap.range (diagMul b)).map (stdEmb A K ι) := by
  unfold matImage stdLattice
  rw [← Submodule.map_comp, LinearMap.range_eq_map, ← Submodule.map_comp]
  congr 1
  ext a i
  simp [stdEmb_apply, diagMul_apply, Matrix.mulVec_diagonal]

lemma matImage_diagonal_le (b : ι → A) :
    (matImage (Matrix.diagonal fun i => algebraMap A K (b i)) : Submodule A (ι → K)) ≤
      stdLattice A K ι := by
  rw [matImage_diagonal]
  exact Submodule.map_mono le_top

/-- `length(A^n / diag(b) A^n) = Σ ord(b_i)`. -/
theorem relLength_matImage_diagonal (b : ι → A) :
    relLength (stdLattice A K ι) (matImage (Matrix.diagonal fun i => algebraMap A K (b i))) =
      ∑ i, Ring.ord A (b i) := by
  rw [matImage_diagonal, stdLattice, relLength_map _ (stdEmb_injective A K ι), relLength_top,
    range_diagMul, (Submodule.quotientPi _).length_eq, Module.length_pi_of_fintype]
  rfl

lemma ordFrac_algebraMap {x : A} (hx : x ≠ 0) :
    Ring.ordFrac A (algebraMap A K x) = WithZero.exp ((Ring.ord A x).toNat : ℤ) := by
  rw [Ring.ordFrac_eq_ord A hx]
  exact Ring.ordMonoidWithZeroHom_eq_coe A (mem_nonZeroDivisors_of_ne_zero hx)
    (ENat.natCast_toNat (Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero hx))).symm

lemma exp_sum_int {α : Type*} (s : Finset α) (g : α → ℤ) :
    (WithZero.exp (∑ i ∈ s, g i) : WithZero (Multiplicative ℤ)) = ∏ i ∈ s, WithZero.exp (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x t hx ih => rw [Finset.sum_insert hx, Finset.prod_insert hx, WithZero.exp_add, ih]

lemma toLin'_bijective {N : Matrix ι ι K} (h : N.det ≠ 0) :
    Function.Bijective (Matrix.toLin' N) := by
  have hu : IsUnit N.det := isUnit_iff_ne_zero.mpr h
  refine Function.bijective_iff_has_inverse.mpr ⟨Matrix.toLin' N⁻¹, fun v => ?_, fun v => ?_⟩
  · rw [← LinearMap.comp_apply, ← Matrix.toLin'_mul, Matrix.nonsing_inv_mul _ hu,
      Matrix.toLin'_one, LinearMap.id_apply]
  · rw [← LinearMap.comp_apply, ← Matrix.toLin'_mul, Matrix.mul_nonsing_inv _ hu,
      Matrix.toLin'_one, LinearMap.id_apply]

/-- The property to be proved for all invertible matrices. -/
def DetOrdProp (N : Matrix ι ι K) : Prop :=
  Ring.ordFrac A N.det =
    WithZero.exp (latDist (stdLattice A K ι) (matImage (A := A) N))

theorem detOrdProp_mul {N N' : Matrix ι ι K} (h : N.det ≠ 0) (h' : N'.det ≠ 0)
    (hN : DetOrdProp (A := A) N) (hN' : DetOrdProp (A := A) N') :
    DetOrdProp (A := A) (N * N') := by
  have := stdLattice_isLattice A K ι
  unfold DetOrdProp at *
  have hc : (matImage (A := A) (N * N') : Submodule A (ι → K)) =
      (stdLattice A K ι).map ((Matrix.toLin' N ∘ₗ Matrix.toLin' N').restrictScalars A) := by
    unfold matImage; rw [Matrix.toLin'_mul]
  rw [Matrix.det_mul, map_mul, hN, hN', hc,
    latDist_map_comp (K := K) _ _ (toLin'_bijective h) (toLin'_bijective h'), WithZero.exp_add]

/-- Diagonal matrices with integral entries. -/
theorem detOrdProp_diagonal_int (b : ι → A) (hb : ∀ i, b i ≠ 0) :
    DetOrdProp (A := A) (Matrix.diagonal fun i => algebraMap A K (b i)) := by
  unfold DetOrdProp
  rw [latDist_of_le (matImage_diagonal_le b), relLength_matImage_diagonal, Matrix.det_diagonal,
    map_prod]
  have h1 : ∀ i, Ring.ord A (b i) = (((Ring.ord A (b i)).toNat : ℕ) : ℕ∞) := fun i =>
    (ENat.natCast_toNat (Ring.ord_ne_top (mem_nonZeroDivisors_of_ne_zero (hb i)))).symm
  rw [Finset.sum_congr rfl fun i _ => h1 i, ← Nat.cast_sum, ENat.toNat_natCast, Nat.cast_sum,
    exp_sum_int]
  exact Finset.prod_congr rfl fun i _ => ordFrac_algebraMap (hb i)

/-- General diagonal matrices. -/
theorem detOrdProp_diagonal (d : ι → K) (hd : (Matrix.diagonal d).det ≠ 0) :
    DetOrdProp (A := A) (Matrix.diagonal d) := by
  have hd' : ∀ i, d i ≠ 0 := by
    rw [Matrix.det_diagonal] at hd
    exact fun i => (Finset.prod_ne_zero_iff.mp hd) i (Finset.mem_univ i)
  have hex : ∀ i, ∃ b c : A, b ≠ 0 ∧ c ≠ 0 ∧ d i * algebraMap A K c = algebraMap A K b := by
    intro i
    obtain ⟨b, c, hc, hbc⟩ := IsFractionRing.div_surjective (A := A) (d i)
    have hc0 : algebraMap A K c ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr (nonZeroDivisors.ne_zero hc)
    refine ⟨b, c, ?_, nonZeroDivisors.ne_zero hc, ?_⟩
    · rintro rfl
      rw [map_zero, zero_div] at hbc
      exact hd' i hbc.symm
    · rw [← hbc, div_mul_cancel₀ _ hc0]
  choose b c hb hc hbc using hex
  have hmul : Matrix.diagonal d * Matrix.diagonal (fun i => algebraMap A K (c i)) =
      Matrix.diagonal fun i => algebraMap A K (b i) := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    ext i
    exact hbc i
  have hcdet : (Matrix.diagonal fun i => algebraMap A K (c i)).det ≠ 0 := by
    rw [Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.mpr fun i _ =>
      (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr (hc i)
  have hB := detOrdProp_diagonal_int (K := K) b hb
  have hC := detOrdProp_diagonal_int (K := K) c hc
  have := stdLattice_isLattice A K ι
  unfold DetOrdProp at *
  have hcomp : (matImage (A := A) (Matrix.diagonal fun i => algebraMap A K (b i)) :
      Submodule A (ι → K)) = (stdLattice A K ι).map ((Matrix.toLin' (Matrix.diagonal d) ∘ₗ
        Matrix.toLin' (Matrix.diagonal fun i => algebraMap A K (c i))).restrictScalars A) := by
    unfold matImage; rw [← hmul, Matrix.toLin'_mul]
  rw [hcomp, latDist_map_comp (K := K) _ _ (toLin'_bijective hd) (toLin'_bijective hcdet),
    WithZero.exp_add, ← hC, ← hmul, Matrix.det_mul, map_mul] at hB
  have hne : Ring.ordFrac A (Matrix.diagonal fun i => algebraMap A K (c i)).det ≠ 0 :=
    (map_ne_zero _).mpr hcdet
  exact mul_right_cancel₀ hne hB

lemma transvection_mulVec (i j : ι) (c : K) (v : ι → K) :
    (Matrix.transvection i j c).mulVec v = v + Pi.single i (c * v j) := by
  ext k
  simp only [Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply]
  congr 1
  by_cases h : k = i
  · subst h
    simp [Matrix.mulVec, dotProduct, Matrix.single_apply]
  · simp [Matrix.mulVec, dotProduct, Ne.symm h]

/-- The auxiliary lattice `M_q = diag(1,…,q,…,1) A^n` (`q` in position `j`). -/
def auxLattice (j : ι) (q : A) : Submodule A (ι → K) :=
  matImage (A := A) (Matrix.diagonal fun k => if k = j then algebraMap A K q else 1)

lemma transvection_auxLattice_le (i j : ι) (hij : i ≠ j) (p q : A)
    (hq : algebraMap A K q ≠ 0) :
    (auxLattice (K := K) j q).map ((Matrix.toLin' (Matrix.transvection i j
      (algebraMap A K p / algebraMap A K q))).restrictScalars A) ≤ auxLattice (K := K) j q := by
  rintro _ ⟨_, ⟨_, ⟨a, -, rfl⟩, rfl⟩, rfl⟩
  refine ⟨stdEmb A K ι (a + Pi.single i (p * a j)), ⟨_, trivial, rfl⟩, ?_⟩
  simp only [LinearMap.coe_restrictScalars, Matrix.toLin'_apply, transvection_mulVec]
  ext k
  simp only [Pi.add_apply, Matrix.mulVec_diagonal, stdEmb_apply, if_true, map_add]
  by_cases hk : k = i
  · subst hk
    simp only [Pi.single_eq_same, if_neg hij, one_mul, map_mul]
    field_simp
  · simp [Pi.single_eq_of_ne hk]

theorem detOrdProp_transvection (t : Matrix.TransvectionStruct ι K) :
    DetOrdProp (A := A) t.toMatrix := by
  obtain ⟨i, j, hij, c⟩ := t
  obtain ⟨p, q, hq, rfl⟩ := IsFractionRing.div_surjective (A := A) c
  have hq0 : algebraMap A K q ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective A K)).mpr (nonZeroDivisors.ne_zero hq)
  have hM₀ := stdLattice_isLattice A K ι
  set c := algebraMap A K p / algebraMap A K q with hc
  have hdet : (Matrix.transvection i j c).det = 1 := Matrix.det_transvection_of_ne i j hij c
  have hbij : Function.Bijective (Matrix.toLin' (Matrix.transvection i j c)) :=
    toLin'_bijective (by rw [hdet]; exact one_ne_zero)
  have hDq : (Matrix.diagonal fun k => if k = j then algebraMap A K q else 1).det ≠ 0 := by
    rw [Matrix.det_diagonal]
    refine Finset.prod_ne_zero_iff.mpr fun k _ => ?_
    split_ifs
    · exact hq0
    · exact one_ne_zero
  have hMq : IsLattice K (auxLattice (K := K) j q) :=
    IsLattice.map' _ (toLin'_bijective hDq).2 _
  have hle := transvection_auxLattice_le (K := K) i j hij p q hq0
  have hle' := transvection_auxLattice_le (K := K) i j hij (-p) q hq0
  have hneg : algebraMap A K (-p) / algebraMap A K q = -c := by rw [map_neg, neg_div]
  rw [hneg] at hle'
  have hcomp : Matrix.toLin' (Matrix.transvection i j c) ∘ₗ
      Matrix.toLin' (Matrix.transvection i j (-c)) = LinearMap.id := by
    rw [← Matrix.toLin'_mul, Matrix.transvection_mul_transvection_same _ _ hij, add_neg_cancel,
      Matrix.transvection_zero, Matrix.toLin'_one]
  have heq : (auxLattice (K := K) j q).map
      ((Matrix.toLin' (Matrix.transvection i j c)).restrictScalars A) = auxLattice (K := K) j q := by
    refine le_antisymm hle ?_
    calc auxLattice (K := K) j q
        = (auxLattice (K := K) j q).map ((Matrix.toLin' (Matrix.transvection i j c) ∘ₗ
            Matrix.toLin' (Matrix.transvection i j (-c))).restrictScalars A) := by
          rw [hcomp]; exact (Submodule.map_id _).symm
      _ = ((auxLattice (K := K) j q).map ((Matrix.toLin'
            (Matrix.transvection i j (-c))).restrictScalars A)).map
              ((Matrix.toLin' (Matrix.transvection i j c)).restrictScalars A) := by
          rw [← Submodule.map_comp]; rfl
      _ ≤ _ := Submodule.map_mono hle'
  unfold DetOrdProp
  show Ring.ordFrac A (Matrix.transvection i j c).det = _
  rw [hdet, map_one]
  show (1 : WithZero (Multiplicative ℤ)) = WithZero.exp (latDist (stdLattice A K ι)
    ((stdLattice A K ι).map ((Matrix.toLin' (Matrix.transvection i j c)).restrictScalars A)))
  rw [latDist_map_indep (K := K) _ hbij (stdLattice A K ι) (auxLattice (K := K) j q), heq,
    latDist_self, WithZero.exp_zero]

/-- On the standard lattice: `ord_A(det N) = d(A^n, N A^n)`. -/
theorem detOrdProp_of_det_ne_zero (N : Matrix ι ι K) (h : N.det ≠ 0) : DetOrdProp (A := A) N :=
  Matrix.diagonal_transvection_induction_of_det_ne_zero (DetOrdProp (A := A)) N h
    (fun d hd => detOrdProp_diagonal d hd) detOrdProp_transvection
    (fun _ _ hA hB PA PB => detOrdProp_mul hA hB PA PB)

variable {V : Type*} [AddCommGroup V] [Module A V] [Module K V] [IsScalarTower A K V]
  [Module.Finite K V]

/-- Stacks 02MI: `ord_A(det φ) = d(M, φM)`. -/
theorem ordFrac_det_eq_exp_latDist (M : Submodule A V) [IsLattice K M] (φ : V →ₗ[K] V)
    (hφ : LinearMap.det φ ≠ 0) :
    Ring.ordFrac A (LinearMap.det φ) =
      WithZero.exp (latDist M (M.map (φ.restrictScalars A))) := by
  classical
  let b := Module.finBasis K V
  let e : V ≃ₗ[K] (Fin (Module.finrank K V) → K) := b.equivFun
  let eL : V →ₗ[K] (Fin (Module.finrank K V) → K) := e.toLinearMap
  let φ' : (Fin (Module.finrank K V) → K) →ₗ[K] (Fin (Module.finrank K V) → K) :=
    eL ∘ₗ φ ∘ₗ e.symm.toLinearMap
  let N := LinearMap.toMatrix' φ'
  have hN : Matrix.toLin' N = φ' := Matrix.toLin'_toMatrix' φ'
  have hdet : N.det = LinearMap.det φ := by
    rw [← LinearMap.det_toLin', hN]
    exact LinearMap.det_conj φ e
  have hP := detOrdProp_of_det_ne_zero (A := A) N (by rw [hdet]; exact hφ)
  unfold DetOrdProp matImage at hP
  rw [hdet, hN] at hP
  rw [hP]
  congr 1
  have hM₀ := stdLattice_isLattice A K (Fin (Module.finrank K V))
  have hbij : Function.Bijective φ' := by
    rw [← hN]; exact toLin'_bijective (by rw [hdet]; exact hφ)
  have heM : IsLattice K (M.map (eL.restrictScalars A)) :=
    IsLattice.map' _ e.surjective M
  rw [latDist_map_indep (K := K) φ' hbij _ (M.map (eL.restrictScalars A)),
    ← latDist_map (A := A) eL e.injective M (M.map (φ.restrictScalars A))]
  congr 1
  rw [← Submodule.map_comp, ← Submodule.map_comp]
  congr 1
  ext v
  simp [φ', eL]

/-- The usual form of Stacks 02MI: for `φM ⊆ M`, `ord_A(det φ) = length_A(M/φM)`. -/
theorem ordFrac_det_eq_exp_relLength (M : Submodule A V) [IsLattice K M] (φ : V →ₗ[K] V)
    (hφ : LinearMap.det φ ≠ 0) (hle : M.map (φ.restrictScalars A) ≤ M) :
    Ring.ordFrac A (LinearMap.det φ) =
      WithZero.exp (((relLength M (M.map (φ.restrictScalars A))).toNat : ℕ) : ℤ) := by
  rw [ordFrac_det_eq_exp_latDist M φ hφ, latDist_of_le hle]

end Submodule

end
