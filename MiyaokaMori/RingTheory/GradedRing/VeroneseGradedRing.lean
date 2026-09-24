import MiyaokaMori.Prelude

/-! # The Veronese subring of a graded ring

The Veronese subring `S^{(d)} = ⊕_n S_{nd}` of a graded ring, with the grading `n ↦ S_{nd}` (notation as
around Stacks Algebra 00JN). Used for the Veronese polarization (§2 of the paper).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/- The carrier predicates and the decomposition function of `veroneseSubring` / `veroneseGrading` and the
   `GradedRing` instance are explicit; each proof obligation (closure of the subring and of the
   subgroups, the graded ring axioms, the two membership statements and the inverse laws of the
   decomposition) is a separate named theorem. -/

/-- Route: `proj_k(ab) = Σ_{i+j=k} a_i b_j` (`DirectSum.coe_mul_apply` + `DirectSum.decompose_mul`); if
`d ∤ k` then in each term `d ∤ i` or `d ∤ j`, so `a_i = 0` or `b_j = 0`. -/
theorem veroneseSubring.mul_mem_aux {σ A : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℕ) {a b : A}
    (ha : ∀ i, ¬ d ∣ i → GradedRing.proj 𝒜 i a = 0) (hb : ∀ i, ¬ d ∣ i → GradedRing.proj 𝒜 i b = 0) :
    ∀ i, ¬ d ∣ i → GradedRing.proj 𝒜 i (a * b) = 0 := by
  classical
  intro n hn
  rw [GradedRing.proj_apply, DirectSum.decompose_mul, DirectSum.coe_mul_apply]
  refine Finset.sum_eq_zero fun ij hij => ?_
  have hsum : ij.1 + ij.2 = n := (Finset.mem_filter.mp hij).2
  have h : ¬ d ∣ ij.1 ∨ ¬ d ∣ ij.2 := by
    by_contra hc
    push_neg at hc
    exact hn (hsum ▸ dvd_add hc.1 hc.2)
  rcases h with h | h
  · have h0 := ha _ h
    rw [GradedRing.proj_apply] at h0
    rw [h0, zero_mul]
  · have h0 := hb _ h
    rw [GradedRing.proj_apply] at h0
    rw [h0, mul_zero]

/-- Route: `1 ∈ 𝒜 0`, so `proj_i 1 = 0` for `i ≠ 0` (`DirectSum.decompose_of_mem_ne`); and `d ∤ i`
implies `i ≠ 0`. -/
theorem veroneseSubring.one_mem_aux {σ A : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℕ) :
    ∀ i, ¬ d ∣ i → GradedRing.proj 𝒜 i (1 : A) = 0 := by
  intro i hi
  have h0 : i ≠ 0 := fun h => hi (h ▸ dvd_zero d)
  rw [GradedRing.proj_apply]
  exact DirectSum.decompose_of_mem_ne 𝒜 (SetLike.GradedOne.one_mem) (Ne.symm h0)

/-- `S^{(d)}`: the elements whose homogeneous components are nonzero only in degrees that are multiples
of `d` (for `d = 0` this is `S_0`). -/

def veroneseSubring {σ A : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℕ) : Subring A where
  carrier := {a | ∀ i, ¬ d ∣ i → GradedRing.proj 𝒜 i a = 0}
  mul_mem' := fun ha hb => veroneseSubring.mul_mem_aux 𝒜 d ha hb   -- 𝒜(ad)·𝒜(bd) ⊆ 𝒜((a+b)d)
  one_mem' := veroneseSubring.one_mem_aux 𝒜 d   -- 1 ∈ 𝒜 0
  add_mem' := fun ha hb i hi => by rw [map_add, ha i hi, hb i hi, add_zero]
  zero_mem' := fun i _ => map_zero _
  neg_mem' := fun ha i hi => by rw [map_neg, ha i hi, neg_zero]

/-- The `n`-th piece is `S_{nd}`; for `d = 0` only the `0`-th piece is nonzero by convention (otherwise the
pieces would repeat and not form a grading). -/

def veroneseGrading {σ A : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℕ) : ℕ → AddSubgroup (veroneseSubring 𝒜 d) := fun n =>
  { carrier := {x | (x : A) ∈ 𝒜 (n * d) ∧ (d = 0 → n = 0 ∨ x = 0)}
    add_mem' := fun {x y} hx hy =>
      ⟨by simpa using add_mem hx.1 hy.1, fun h0 =>
        (hx.2 h0).elim Or.inl fun hx0 => (hy.2 h0).elim Or.inl fun hy0 =>
          Or.inr (by rw [hx0, hy0, add_zero])⟩
    zero_mem' := ⟨zero_mem _, fun _ => Or.inr rfl⟩
    neg_mem' := fun {x} hx =>
      ⟨by simpa using neg_mem hx.1, fun h0 => (hx.2 h0).imp id fun h => by rw [h, neg_zero]⟩ }

theorem veroneseGrading.one_mem {σ A : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℕ) :
    (1 : veroneseSubring 𝒜 d) ∈ veroneseGrading 𝒜 d 0 :=
  ⟨by simpa using (SetLike.GradedOne.one_mem : (1 : A) ∈ 𝒜 0), fun _ => Or.inl rfl⟩

/-- Route: the first component is `SetLike.GradedMul.mul_mem` plus `(i+j)·d = i·d + j·d`; for the second
component, if `d = 0` and `i = j = 0` take the left disjunct, otherwise one factor is `0` and so is the
product. -/
theorem veroneseGrading.mul_mem {σ A : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℕ) {i j : ℕ}
    {x y : veroneseSubring 𝒜 d} (hx : x ∈ veroneseGrading 𝒜 d i) (hy : y ∈ veroneseGrading 𝒜 d j) :
    x * y ∈ veroneseGrading 𝒜 d (i + j) := by
  refine ⟨?_, fun h0 => ?_⟩
  · have h := SetLike.GradedMul.mul_mem hx.1 hy.1
    rw [Nat.add_mul]
    simpa using h
  · rcases hx.2 h0 with hi | hx0
    · rcases hy.2 h0 with hj | hy0
      · left; omega
      · right; rw [hy0, mul_zero]
    · right; rw [hx0, zero_mul]

/-- Homogeneous components stay in `S^{(d)}` (when `d ∣ i`). Route: `proj_j(proj_i x)` is `0` for `j ≠ i`,
and for `j = i` we have `d ∣ j`. -/
theorem veroneseSubring.proj_mem {σ A : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℕ) (x : A) {i : ℕ} (hi : d ∣ i) :
    (GradedRing.proj 𝒜 i x : A) ∈ veroneseSubring 𝒜 d := by
  show ∀ j, ¬ d ∣ j → GradedRing.proj 𝒜 j (GradedRing.proj 𝒜 i x) = 0
  intro j hj
  have hne : i ≠ j := fun h => hj (h ▸ hi)
  have hm : (GradedRing.proj 𝒜 i x : A) ∈ 𝒜 i := by
    rw [GradedRing.proj_apply]; exact SetLike.coe_mem _
  rw [GradedRing.proj_apply]
  exact DirectSum.decompose_of_mem_ne 𝒜 hm hne

/-- Route: `proj_i x ∈ 𝒜 i = 𝒜 ((i/d)·d)` (`Nat.div_mul_cancel hi`); for `d = 0`, `i/d = 0` and the left
disjunct applies. -/
theorem veroneseGrading.proj_mem {σ A : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℕ) (x : A) {i : ℕ} (hi : d ∣ i) :
    (⟨GradedRing.proj 𝒜 i x, veroneseSubring.proj_mem 𝒜 d x hi⟩ : veroneseSubring 𝒜 d) ∈
      veroneseGrading 𝒜 d (i / d) := by
  refine ⟨?_, fun h0 => Or.inl (by subst h0; simp)⟩
  show (GradedRing.proj 𝒜 i x : A) ∈ 𝒜 (i / d * d)
  rw [Nat.div_mul_cancel hi, GradedRing.proj_apply]
  exact SetLike.coe_mem _

/-- A homogeneous element of degree divisible by `d` lies in `S^{(d)}`.

Reference: first paragraph of the proof of Stacks 0B5J (description of the carrier of
`S^{(d)} = ⊕_n S_{nd}`).

Proof: let `a ∈ 𝒜 i` with `d ∣ i`. We show `¬ d ∣ j ⟹ proj_j a = 0` for all `j`. From `d ∣ i` and
`¬ d ∣ j` we get `i ≠ j`, so the component of the homogeneous element `a ∈ 𝒜 i` at `j ≠ i` vanishes
(`DirectSum.decompose_of_mem_ne`). -/
theorem veroneseSubring.mem_of_mem_graded {σ A : Type*} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℕ) {i : ℕ} (hi : d ∣ i) {a : A}
    (ha : a ∈ 𝒜 i) : a ∈ veroneseSubring 𝒜 d := by
  show ∀ j, ¬ d ∣ j → GradedRing.proj 𝒜 j a = 0
  intro j hj
  have hne : i ≠ j := fun h => hj (h ▸ hi)
  rw [GradedRing.proj_apply]
  exact DirectSum.decompose_of_mem_ne 𝒜 ha hne

/-- The decomposition: the `n`-th piece of `x ∈ S^{(d)}` is the `nd`-th homogeneous component in `S`
(the components with `d ∤ i` are `0`). -/

def veroneseDecompose {σ A : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℕ) (x : veroneseSubring 𝒜 d) :
    DirectSum ℕ fun n => veroneseGrading 𝒜 d n := by
  classical
  exact ∑ i ∈ (DirectSum.decompose 𝒜 (x : A)).support,
    if h : d ∣ i then
      DirectSum.of (fun n => veroneseGrading 𝒜 d n) (i / d)
        ⟨⟨GradedRing.proj 𝒜 i (x : A), veroneseSubring.proj_mem 𝒜 d (x : A) h⟩,
          veroneseGrading.proj_mem 𝒜 d (x : A) h⟩
    else 0

/-- A homogeneous element `a ∈ 𝒜 i` of degree divisible by `d`, as an element of `S^{(d)}`, lies in the
`i/d`-th piece of the Veronese grading. Route: `i/d·d = i` (`Nat.div_mul_cancel`); for `d = 0`, `i/d = 0`
and the left disjunct applies. -/
theorem veroneseGrading.mem_of_mem_graded {σ A : Type*} [CommRing A] [SetLike σ A]
    [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℕ) {i : ℕ} (hi : d ∣ i) {a : A}
    (ha : a ∈ 𝒜 i) :
    (⟨a, veroneseSubring.mem_of_mem_graded 𝒜 d hi ha⟩ : veroneseSubring 𝒜 d) ∈
      veroneseGrading 𝒜 d (i / d) := by
  refine ⟨?_, fun h0 => Or.inl (by subst h0; simp)⟩
  show a ∈ 𝒜 (i / d * d)
  rw [Nat.div_mul_cancel hi]
  exact ha

/-- The additive homomorphism from the `i`-th homogeneous component `𝒜 i` to the `i/d`-th piece of the
Veronese grading (when `d ∣ i`). -/
def veroneseComponentHom {σ A : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℕ) (i : ℕ) (hi : d ∣ i) :
    𝒜 i →+ veroneseGrading 𝒜 d (i / d) where
  toFun a := ⟨⟨(a : A), veroneseSubring.mem_of_mem_graded 𝒜 d hi a.2⟩,
    veroneseGrading.mem_of_mem_graded 𝒜 d hi a.2⟩
  map_zero' := Subtype.ext (Subtype.ext (by simp))
  map_add' := fun a b => Subtype.ext (Subtype.ext (by simp))

/-- The additive-homomorphism version of `veroneseDecompose`: `⨁_i 𝒜 i → ⨁_n S^{(d)}_n`, sending the
`i`-th component to the `i/d`-th piece when `d ∣ i` and to `0` otherwise.
`veroneseDecompose x = veroneseDecomposeHom (decompose 𝒜 x)` (`veroneseDecompose_eq_hom`). -/
def veroneseDecomposeHom {σ A : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℕ) :
    (DirectSum ℕ fun i => 𝒜 i) →+ DirectSum ℕ fun n => veroneseGrading 𝒜 d n :=
  DirectSum.toAddMonoid fun i =>
    if hi : d ∣ i then
      (DirectSum.of (fun n => veroneseGrading 𝒜 d n) (i / d)).comp (veroneseComponentHom 𝒜 d i hi)
    else 0

theorem veroneseDecomposeHom_of {σ A : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℕ) (i : ℕ) (a : 𝒜 i) :
    veroneseDecomposeHom 𝒜 d (DirectSum.of (fun i => 𝒜 i) i a) =
      if hi : d ∣ i then
        DirectSum.of (fun n => veroneseGrading 𝒜 d n) (i / d) (veroneseComponentHom 𝒜 d i hi a)
      else 0 := by
  rw [veroneseDecomposeHom, DirectSum.toAddMonoid_of]
  split_ifs <;> rfl

/-- `veroneseDecompose` is `veroneseDecomposeHom` composed with `DirectSum.decompose 𝒜`. -/
theorem veroneseDecompose_eq_hom {σ A : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℕ) (x : veroneseSubring 𝒜 d) :
    veroneseDecompose 𝒜 d x = veroneseDecomposeHom 𝒜 d (DirectSum.decompose 𝒜 (x : A)) := by
  classical
  unfold veroneseDecompose
  conv_rhs => rw [← DirectSum.sum_support_of (DirectSum.decompose 𝒜 (x : A)), map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [veroneseDecomposeHom_of]
  split_ifs with hi
  · exact congrArg _ (Subtype.ext (Subtype.ext (GradedRing.proj_apply 𝒜 i (x : A))))
  · rfl

theorem veroneseDecompose_zero {σ A : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℕ) : veroneseDecompose 𝒜 d 0 = 0 := by
  rw [veroneseDecompose_eq_hom, Subring.coe_zero, DirectSum.decompose_zero, map_zero]

/-- The decomposition is a left inverse of `coeAddMonoidHom` (the `left_inv` field of the `GradedRing`
instance).

Reference: standard (the Veronese subring `S^{(d)} = ⊕_n S_{nd}`, cf. Stacks Algebra 00JN).

Proof: `veroneseDecompose x = veroneseDecomposeHom (decompose 𝒜 x)` (`veroneseDecompose_eq_hom`);
write `decompose 𝒜 x` as `∑ i ∈ supp, of i (decompose 𝒜 x i)` and commute the additive homomorphisms
with the sum; termwise, for `d ∣ i`, `coeAddMonoidHom_of` gives `(decompose 𝒜 x i : A)`, and for
`d ∤ i` the term is `0`, while the definition of `x ∈ S^{(d)}` says exactly `proj 𝒜 i x = 0`, so both
cases equal `(decompose 𝒜 x i : A)`; finally `DirectSum.sum_support_decompose` reassembles `x`. -/
theorem veroneseDecompose_left_inv {σ A : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℕ) :
    Function.LeftInverse (DirectSum.coeAddMonoidHom (veroneseGrading 𝒜 d)) (veroneseDecompose 𝒜 d) := by
  classical
  intro x
  apply Subtype.ext
  rw [veroneseDecompose_eq_hom]
  conv_lhs => rw [← DirectSum.sum_support_of (DirectSum.decompose 𝒜 (x : A)), map_sum, map_sum]
  rw [AddSubmonoidClass.coe_finsetSum]
  conv_rhs => rw [← DirectSum.sum_support_decompose 𝒜 (x : A)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [veroneseDecomposeHom_of]
  split_ifs with hi
  · rw [DirectSum.coeAddMonoidHom_of]
    rfl
  · rw [map_zero, Subring.coe_zero, ← GradedRing.proj_apply]
    exact (x.2 i hi).symm

/-- The decomposition is a right inverse of `coeAddMonoidHom` (the `right_inv` field of the
`GradedRing` instance).

Proof: `DirectSum.induction_on` on `z`. The zero and addition cases reduce to additive homomorphisms
via `veroneseDecompose_eq_hom`. For a generator `of n y` (`y ∈ 𝒜 (n d)`, with `d = 0 → n = 0 ∨ y = 0`):
if `y = 0` both sides are `0`; otherwise `decompose 𝒜 y = of (n d) ⟨y, _⟩` (`decompose_of_mem`),
`veroneseDecomposeHom` sends it to `of (n d / d) ⟨y, _⟩`, and `n d / d = n`: for `d > 0` by
`Nat.mul_div_cancel`, for `d = 0` by the extra condition `n = 0`. This is exactly where the extra
condition "`d = 0 → n = 0 ∨ x = 0`" in the carrier of `veroneseGrading` is used. -/
theorem veroneseDecompose_right_inv {σ A : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℕ) :
    Function.RightInverse (DirectSum.coeAddMonoidHom (veroneseGrading 𝒜 d)) (veroneseDecompose 𝒜 d) := by
  classical
  intro z
  induction z using DirectSum.induction_on with
  | zero =>
    rw [map_zero]
    exact veroneseDecompose_zero 𝒜 d
  | of n y =>
    rw [DirectSum.coeAddMonoidHom_of]
    by_cases hy : y = 0
    · subst hy
      rw [map_zero]
      exact veroneseDecompose_zero 𝒜 d
    have key : ∀ (m : ℕ) (_ : m = n) (v : veroneseGrading 𝒜 d m),
        ((v : veroneseSubring 𝒜 d) : A) = ((y : veroneseSubring 𝒜 d) : A) →
        DirectSum.of (fun n => veroneseGrading 𝒜 d n) m v =
          DirectSum.of (fun n => veroneseGrading 𝒜 d n) n y := by
      rintro m rfl v hv
      congr 1
      exact Subtype.ext (Subtype.ext hv)
    have hmem : ((y : veroneseSubring 𝒜 d) : A) ∈ 𝒜 (n * d) := y.2.1
    rw [veroneseDecompose_eq_hom, DirectSum.decompose_of_mem 𝒜 hmem, veroneseDecomposeHom_of,
      dif_pos (dvd_mul_left d n)]
    refine key _ ?_ _ rfl
    rcases Nat.eq_zero_or_pos d with hd | hd
    · subst hd
      rcases y.2.2 rfl with hn | hy0
      · subst hn; rfl
      · exact absurd (Subtype.ext hy0) hy
    · exact Nat.mul_div_cancel n hd
  | add x y hx hy =>
    rw [map_add, veroneseDecompose_eq_hom, Subring.coe_add, DirectSum.decompose_add, map_add,
      ← veroneseDecompose_eq_hom, ← veroneseDecompose_eq_hom, hx, hy]

instance {σ A : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℕ) : GradedRing (veroneseGrading 𝒜 d) where
  one_mem := veroneseGrading.one_mem 𝒜 d
  mul_mem := fun _ _ _ _ hx hy => veroneseGrading.mul_mem 𝒜 d hx hy
  decompose' := veroneseDecompose 𝒜 d
  left_inv := veroneseDecompose_left_inv 𝒜 d
  right_inv := veroneseDecompose_right_inv 𝒜 d

/-- If `f` is homogeneous of degree `m` and `d ≥ 1`, then `f^d ∈ S^{(d)}` and it is homogeneous of
degree `m` in `S^{(d)}`.

Reference: Stacks 0B5J (comparison of the Veronese subring with `D_+(f)`: `f ↦ f^d` matches the chart
`D_+(f)` with the chart `D_+(f^d)` of `S^{(d)}`).

Proof: `SetLike.pow_mem_graded` gives `f^d ∈ 𝒜 (d • m) = 𝒜 (m * d)`; `d ∣ m * d`, so
`veroneseSubring.mem_of_mem_graded` gives `f^d ∈ S^{(d)}`. The carrier condition of
`veroneseGrading 𝒜 d m` is "`(x : A) ∈ 𝒜 (m * d)`" together with "`d = 0 → m = 0 ∨ x = 0`"; the former
is the above, the latter is vacuous under `hd : 0 < d`. -/
theorem veronese_pow_mem {σ A : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (d : ℕ) (hd : 0 < d) {f : A} {m : ℕ} (hf : f ∈ 𝒜 m) :
    f ^ d ∈ veroneseSubring 𝒜 d ∧ ∃ h : f ^ d ∈ veroneseSubring 𝒜 d, (⟨f ^ d, h⟩ : veroneseSubring 𝒜 d) ∈ veroneseGrading 𝒜 d m := by
  have hpow : f ^ d ∈ 𝒜 (m * d) := by
    have h := SetLike.pow_mem_graded d hf
    rwa [smul_eq_mul, Nat.mul_comm] at h
  have hsub : f ^ d ∈ veroneseSubring 𝒜 d :=
    veroneseSubring.mem_of_mem_graded 𝒜 d (dvd_mul_left d m) hpow
  exact ⟨hsub, hsub, hpow, fun h0 => absurd h0 hd.ne'⟩

end
