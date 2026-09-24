import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.Algebra.DirectSum.Module
import Mathlib.Algebra.DirectSum.Internal

/-! # The weighted grading on the symmetric algebra of a direct sum

Pure ring theory, no geometry. Let `R` be a commutative ring, `W : ι → Type*` a family of `R`-modules
(`ι` finite with decidable equality), and `w : ι → ℕ` weights. Then `Sym_R(⨁_q W_q)` carries the
**`ℕ`-weighted grading**

```
piece R W w m = ⨆_{d : ι → ℕ, Σ_q w q * d q = m} ∏_q (range (gen q))^(d q)
```

(`gen q : W q →ₗ Sym_R(⨁ W)` is the degree-one generator of the `q`-th component), and it is a
`GradedAlgebra`.

**The decomposition data are fully constructive**: `decompose` is the universal property
`SymmetricAlgebra.lift` of `Sym` applied to the linear map `⨁_q W_q → ⨁_m piece m` (the `q`-th
component is placed in the `w q`-th piece); there is no `Classical.choice` and no `dite` branching.
This is the weighted generalization of the unweighted grading `symmetricGrading` (all generators of
weight `1`): the unweighted version puts all of `M` in the first piece, here the components of `⨁` go
to the pieces `w q`.

Further results:
* `WeightedSym.piece_le_of_gen`: a **general induction principle** — if a family of submodules
  `Q : ℕ → Submodule R (Sym …)` satisfies `1 ∈ Q 0`, `Q i * Q j ≤ Q (i+j)` and
  `range (gen q) ≤ Q (w q)`, then `piece m ≤ Q m`. Every downstream statement of the form "some map
  preserves weighted degree" or "a weighted piece lies in some submodule" follows from it in one line
  (the `left_inv` of this file is itself an instance), without redoing the threefold induction over
  `⨆`/`∏`/`^`.
* `piece_zero`: when all weights are positive, `piece 0 = 1` (i.e. `S_0 = R`, as required by
  `GradedAffineAlgebra.IsConnected`).
* `gen_mem_piece`: the generators of the `q`-th component lie in the `w q`-th piece (the weight
  convention in citable form).

Here multiplication is the ring multiplication of `SymmetricAlgebra` (the `CommRing` instance is
available), so the monoid laws need no proof, and the finite index set of monomials of weight `m` is
the fibre of `wdeg w · = m`.

Sources: §2 of the paper (the generators are `V_q^∨`; the weight convention `q+1` is fixed downstream,
this file is completely general in the weights `w`). Reuses Mathlib `SymmetricAlgebra.lift`,
`GradedAlgebra.ofAlgHom`; same idea as `MiyaokaMori.RingTheory.RuledSurfaceAlgebra.symmetricGrading` (unweighted).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe u v w'

open DirectSum

noncomputable section

namespace WeightedSym

variable (R : Type u) [CommRing R] {ι : Type v} [DecidableEq ι] [Fintype ι]
  (W : ι → Type w') [∀ q, AddCommGroup (W q)] [∀ q, Module R (W q)]

/-- The degree-one generator map `W q → Sym_R(⨁_p W_p)` of the `q`-th component. -/
def gen (q : ι) : W q →ₗ[R] SymmetricAlgebra R (⨁ p, W p) :=
  (SymmetricAlgebra.ι R (⨁ p, W p)).comp (DirectSum.lof R ι W q)

/-- The submodule spanned by the degree-one generators of the `q`-th component. -/
def genSpan (q : ι) : Submodule R (SymmetricAlgebra R (⨁ p, W p)) :=
  LinearMap.range (gen R W q)

theorem gen_mem_genSpan (q : ι) (x : W q) : gen R W q x ∈ genSpan R W q :=
  LinearMap.mem_range_self _ x

/-- The monomial submodule `∏_q (range (gen q))^{d q}` of multidegree `d`. -/
def monomial (d : ι → ℕ) : Submodule R (SymmetricAlgebra R (⨁ p, W p)) :=
  ∏ q, genSpan R W q ^ d q

variable {R W}

/-- The weighted degree `Σ_q w q * d q` of a multidegree `d`. -/
def wdeg (w d : ι → ℕ) : ℕ := ∑ q, w q * d q

theorem wdeg_zero (w : ι → ℕ) : wdeg w 0 = 0 := by simp [wdeg]

theorem wdeg_add (w d d' : ι → ℕ) : wdeg w (d + d') = wdeg w d + wdeg w d' := by
  simp [wdeg, Pi.add_apply, mul_add, Finset.sum_add_distrib]

variable (R W)

/-- **The `m`-th piece of the weighted grading**: the sum of the monomial submodules of weighted degree `m`. -/
def piece (w : ι → ℕ) (m : ℕ) : Submodule R (SymmetricAlgebra R (⨁ p, W p)) :=
  ⨆ d : {d : ι → ℕ // wdeg w d = m}, monomial R W d.1

variable {R W}

theorem monomial_le_piece {w d : ι → ℕ} {m : ℕ} (hd : wdeg w d = m) :
    monomial R W d ≤ piece R W w m :=
  le_iSup (fun d : {d : ι → ℕ // wdeg w d = m} => monomial R W d.1) ⟨d, hd⟩

theorem monomial_zero : monomial R W 0 = 1 := by simp [monomial]

theorem monomial_mul (d d' : ι → ℕ) :
    monomial R W d * monomial R W d' = monomial R W (d + d') := by
  simp only [monomial, ← Finset.prod_mul_distrib, ← pow_add, Pi.add_apply]

/-- For the multidegree with a single exponent `1` at `q`, the monomial submodule is `genSpan q`. -/
theorem monomial_single (q : ι) : monomial R W (Pi.single q 1) = genSpan R W q := by
  classical
  rw [monomial, Finset.prod_eq_single q]
  · rw [Pi.single_eq_same, pow_one]
  · intro b _ hb; rw [Pi.single_eq_of_ne hb, pow_zero]
  · intro h; exact absurd (Finset.mem_univ q) h

theorem wdeg_single (w : ι → ℕ) (q : ι) : wdeg w (Pi.single q 1) = w q := by
  classical
  rw [wdeg, Finset.sum_eq_single q]
  · rw [Pi.single_eq_same, mul_one]
  · intro b _ hb; rw [Pi.single_eq_of_ne hb, mul_zero]
  · intro h; exact absurd (Finset.mem_univ q) h

theorem genSpan_le_piece (w : ι → ℕ) (q : ι) : genSpan R W q ≤ piece R W w (w q) :=
  monomial_single (R := R) (W := W) q ▸ monomial_le_piece (wdeg_single w q)

theorem gen_mem_piece (w : ι → ℕ) (q : ι) (x : W q) : gen R W q x ∈ piece R W w (w q) :=
  genSpan_le_piece w q (gen_mem_genSpan R W q x)

theorem one_le_piece_zero (w : ι → ℕ) : (1 : Submodule R (SymmetricAlgebra R (⨁ p, W p)))
    ≤ piece R W w 0 :=
  monomial_zero (R := R) (W := W) ▸ monomial_le_piece (wdeg_zero w)

/-- Submodule multiplication is monotone in `≤` (Mathlib lacks the `Submodule` version of this). -/
theorem mul_le_mul {A B C D : Submodule R (SymmetricAlgebra R (⨁ p, W p))}
    (h₁ : A ≤ B) (h₂ : C ≤ D) : A * C ≤ B * D :=
  Submodule.mul_le.mpr fun _ ha _ hb => Submodule.mul_mem_mul (h₁ ha) (h₂ hb)

instance instGradedMonoid (w : ι → ℕ) : SetLike.GradedMonoid (piece R W w) where
  one_mem := Submodule.one_le.mp (one_le_piece_zero w)
  mul_mem := by
    intro i j x y hx hy
    have h : piece R W w i * piece R W w j ≤ piece R W w (i + j) := by
      simp only [piece]
      rw [Submodule.iSup_mul]
      refine iSup_le fun d => ?_
      rw [Submodule.mul_iSup]
      refine iSup_le fun d' => ?_
      rw [monomial_mul]
      exact monomial_le_piece (by rw [wdeg_add, d.2, d'.2])
    exact h (Submodule.mul_mem_mul hx hy)

/-! ## The general induction principle

`piece` is a three-level stack of `⨆ / ∏ / ^`, and inducting on it directly is tedious. The following
statement removes the three levels at once: whenever a target family contains `1`, is closed under
multiplication and contains the generators, `piece m` lies entirely inside it. The `left_inv` of this
file is its first user; downstream, "restriction preserves weighted degree" (`restrict_mem`), "a weighted
piece is absorbed by a subalgebra", etc. follow the same pattern. -/

section Induction

variable {Q : ℕ → Submodule R (SymmetricAlgebra R (⨁ p, W p))} {w : ι → ℕ}

theorem pow_genSpan_le (h1 : (1 : SymmetricAlgebra R (⨁ p, W p)) ∈ Q 0)
    (hmul : ∀ i j, Q i * Q j ≤ Q (i + j)) (hgen : ∀ q, genSpan R W q ≤ Q (w q))
    (q : ι) (n : ℕ) : genSpan R W q ^ n ≤ Q (w q * n) := by
  induction n with
  | zero => simpa using Submodule.one_le.mpr h1
  | succ n ih =>
    rw [pow_succ, Nat.mul_succ]
    exact le_trans (mul_le_mul ih (hgen q)) (hmul _ _)

theorem prod_genSpan_le (h1 : (1 : SymmetricAlgebra R (⨁ p, W p)) ∈ Q 0)
    (hmul : ∀ i j, Q i * Q j ≤ Q (i + j)) (hgen : ∀ q, genSpan R W q ≤ Q (w q))
    (d : ι → ℕ) (s : Finset ι) :
    (∏ q ∈ s, genSpan R W q ^ d q) ≤ Q (∑ q ∈ s, w q * d q) := by
  induction s using Finset.cons_induction with
  | empty => simpa using Submodule.one_le.mpr h1
  | cons q s hq ih =>
    rw [Finset.prod_cons, Finset.sum_cons]
    exact le_trans (mul_le_mul (pow_genSpan_le h1 hmul hgen q (d q)) ih) (hmul _ _)

/-- **Induction principle for the weighted pieces**: a family of submodules containing `1`, closed under
multiplication and containing all generators absorbs the whole `piece m`. -/
theorem piece_le_of_gen (h1 : (1 : SymmetricAlgebra R (⨁ p, W p)) ∈ Q 0)
    (hmul : ∀ i j, Q i * Q j ≤ Q (i + j)) (hgen : ∀ q, genSpan R W q ≤ Q (w q))
    (m : ℕ) : piece R W w m ≤ Q m := by
  simp only [piece]
  refine iSup_le fun d => ?_
  obtain ⟨d, rfl⟩ := d
  exact prod_genSpan_le h1 hmul hgen d Finset.univ

end Induction

/-! ## The decomposition map (constructive) -/

variable (R W)

/-- The generator map into the graded direct sum: the `q`-th component is placed entirely in the `w q`-th
piece. -/
def gradedInclusion (w : ι → ℕ) : (⨁ p, W p) →ₗ[R] ⨁ m, piece R W w m :=
  DirectSum.toModule R ι _ fun q =>
    (DirectSum.lof R ℕ (fun m => (piece R W w m : Submodule R _)) (w q)).comp
      ((gen R W q).codRestrict (piece R W w (w q)) fun x => gen_mem_piece w q x)

/-- **The decomposition map**: given directly by the universal property of `Sym`, without any choice. -/
def decompose (w : ι → ℕ) :
    SymmetricAlgebra R (⨁ p, W p) →ₐ[R] ⨁ m, piece R W w m :=
  SymmetricAlgebra.lift (gradedInclusion R W w)

variable {R W}

theorem decompose_gen (w : ι → ℕ) (q : ι) (x : W q) :
    decompose R W w (gen R W q x) =
      DirectSum.of (fun m => (piece R W w m : Submodule R _)) (w q)
        ⟨gen R W q x, gen_mem_piece w q x⟩ := by
  have h1 : decompose R W w (gen R W q x) = gradedInclusion R W w (DirectSum.lof R ι W q x) :=
    SymmetricAlgebra.lift_ι_apply _ _
  rw [h1, gradedInclusion, DirectSum.toModule_lof]
  rfl

theorem coeAlgHom_comp_decompose (w : ι → ℕ) :
    (DirectSum.coeAlgHom (piece R W w)).comp (decompose R W w) = AlgHom.id R _ := by
  apply SymmetricAlgebra.algHom_ext
  refine DirectSum.linearMap_ext R fun q => LinearMap.ext fun x => ?_
  show DirectSum.coeAlgHom (piece R W w) (decompose R W w (gen R W q x)) = gen R W q x
  rw [decompose_gen, DirectSum.coeAlgHom_of]

theorem coeAlgHom_decompose (w : ι → ℕ) (a : SymmetricAlgebra R (⨁ p, W p)) :
    DirectSum.coeAlgHom (piece R W w) (decompose R W w a) = a :=
  AlgHom.congr_fun (coeAlgHom_comp_decompose w) a

variable (R W)

/-- Elements sent by `decompose` into the image of the `m`-th piece (used to run the induction principle). -/
def preimagePiece (w : ι → ℕ) (m : ℕ) : Submodule R (SymmetricAlgebra R (⨁ p, W p)) :=
  Submodule.comap (decompose R W w).toLinearMap
    (LinearMap.range (DirectSum.lof R ℕ (fun k => (piece R W w k : Submodule R _)) m))

variable {R W}

theorem mem_preimagePiece {w : ι → ℕ} {m : ℕ} {a : SymmetricAlgebra R (⨁ p, W p)} :
    a ∈ preimagePiece R W w m ↔ decompose R W w a ∈
      LinearMap.range (DirectSum.lof R ℕ (fun k => (piece R W w k : Submodule R _)) m) :=
  Iff.rfl

theorem one_mem_preimagePiece (w : ι → ℕ) :
    (1 : SymmetricAlgebra R (⨁ p, W p)) ∈ preimagePiece R W w 0 := by
  rw [mem_preimagePiece, map_one]
  exact ⟨_, (DirectSum.one_def _).symm⟩

theorem preimagePiece_mul (w : ι → ℕ) (i j : ℕ) :
    preimagePiece R W w i * preimagePiece R W w j ≤ preimagePiece R W w (i + j) := by
  refine Submodule.mul_le.mpr fun a ha b hb => ?_
  obtain ⟨x, hx⟩ := mem_preimagePiece.mp ha
  obtain ⟨y, hy⟩ := mem_preimagePiece.mp hb
  rw [DirectSum.lof_eq_of] at hx hy
  rw [mem_preimagePiece, map_mul, ← hx, ← hy, DirectSum.of_mul_of]
  exact ⟨_, rfl⟩

theorem genSpan_le_preimagePiece (w : ι → ℕ) (q : ι) :
    genSpan R W q ≤ preimagePiece R W w (w q) := by
  rintro _ ⟨x, rfl⟩
  rw [mem_preimagePiece, decompose_gen]
  exact ⟨_, rfl⟩

/-- **The decomposition of a homogeneous element is itself** (the `left_inv` of `GradedAlgebra.ofAlgHom`). -/
theorem decompose_coe (w : ι → ℕ) (m : ℕ) (x : piece R W w m) :
    decompose R W w (x : SymmetricAlgebra R (⨁ p, W p)) =
      DirectSum.of (fun k => (piece R W w k : Submodule R _)) m x := by
  have hle : piece R W w m ≤ preimagePiece R W w m :=
    piece_le_of_gen (one_mem_preimagePiece w) (preimagePiece_mul w) (genSpan_le_preimagePiece w) m
  obtain ⟨y, hy⟩ := mem_preimagePiece.mp (hle x.2)
  rw [DirectSum.lof_eq_of] at hy
  have hcoe : (y : SymmetricAlgebra R (⨁ p, W p)) = (x : SymmetricAlgebra R (⨁ p, W p)) := by
    have h := congrArg (DirectSum.coeAlgHom (piece R W w)) hy
    rw [DirectSum.coeAlgHom_of, coeAlgHom_decompose] at h
    exact h
  exact hy.symm.trans (congrArg _ (Subtype.ext hcoe))

/-- **The graded algebra structure of the weighted symmetric algebra** (constructive decomposition data,
no choice). -/
instance instGradedAlgebra (w : ι → ℕ) : GradedAlgebra (piece R W w) :=
  GradedAlgebra.ofAlgHom _ (decompose R W w) (coeAlgHom_comp_decompose w) (decompose_coe w)

/-! ## The degree-zero piece -/

theorem algebraMap_mem_piece_zero (w : ι → ℕ) (r : R) :
    algebraMap R (SymmetricAlgebra R (⨁ p, W p)) r ∈ piece R W w 0 :=
  one_le_piece_zero w (Submodule.algebraMap_mem r)

/-- **`S_0 = R`**: when all weights are positive, the degree-zero piece is exactly the image of the
coefficient ring. -/
theorem piece_zero (w : ι → ℕ) (hw : ∀ q, w q ≠ 0) : piece R W w 0 = 1 := by
  refine le_antisymm ?_ (one_le_piece_zero w)
  simp only [piece]
  refine iSup_le fun d => ?_
  have hd : d.1 = 0 := by
    funext q
    have h := Finset.sum_eq_zero_iff.mp d.2 q (Finset.mem_univ q)
    rcases Nat.mul_eq_zero.mp h with h' | h'
    · exact absurd h' (hw q)
    · exact h'
  rw [hd, monomial_zero]

end WeightedSym

end
