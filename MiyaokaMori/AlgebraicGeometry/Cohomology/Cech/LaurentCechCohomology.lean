import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.LaurentCechComplex
import MiyaokaMori.AlgebraicGeometry.Cohomology.Cech.LaurentCechLaurentRing
import MiyaokaMori.AlgebraicGeometry.Cohomology.Cech.LaurentCechCochainEmbedding
import MiyaokaMori.AlgebraicGeometry.Cohomology.Cech.LaurentCechTopDegree

/-! # Cohomology of the Laurent–Čech complex

Purely algebraic, `R` any commutative ring, `S = R[T_0..T_N]`, `d ∈ ℤ`. The cohomology of the
Laurent–Čech complex `C^p = ∏_{i_0<⋯<i_p} (S_{T_{i_0}⋯T_{i_p}})_d` (`LaurentCech.Cochain R N d p`,
differential `LaurentCech.δ`):
(A) `S → S_{T_I}` is injective;
(B) for `N ≥ 1`, `ker δ^0 = S_d` (the image of the diagonal embedding; `0` for `d < 0`);
(C) except when `p+1 = N` and `d ≤ −N−1`, every cocycle of `C^{p+1}` is a coboundary;
(D) every cohomology group is a finite `R`-module.

Proof: the proof of Stacks 01XT, decomposing the complex by multidegree `e ∈ ℤ^{N+1}` (`Σe_i = d`).
The complex is embedded via `toL` into the constant-coefficient complex over the Laurent polynomial
ring `L = R[ℤ^{N+1}]` (`LaurentCechLaurentRing.lean`: `emb`, image description `map_degPiece`;
`LaurentCechCochainEmbedding.lean`: `toL`, `dL`, blockwise homotopy `exists_dL_eq`, basis cochain
decomposition; `LaurentCechTopDegree.lean`: top degree and `N = 0`).

Source: Stacks 01XT (= EGA III 2.1.12; Hartshorne III.5.1).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

noncomputable section

namespace LaurentCech

variable (R : Type u) [CommRing R] (N : ℕ)

/-- **(A)**: `S → S_{T_I}` is injective.
Proof: `T_I = ∏_{i∈I} T_i` is a monomial, hence not a zero divisor in `R[T]` for any commutative ring
`R` (multiplication by `monomial m 1` only shifts the support, `MvPolynomial.coeff_monomial_mul` /
`coeff_mul_monomial`), so `Submonoid.powers T_I ≤ nonZeroDivisors` and `IsLocalization.injective`
applies. For the zero ring both sides are zero; for `I = ∅`, `T_I = 1`.
Source: the first paragraph of the proof of Stacks 01XT (implicit in the monomial basis of
`S_{T_{i_0}…T_{i_p}}`). -/
theorem algebraMap_injective (S : Finset (Fin (N + 1))) :
    Function.Injective (algebraMap (MvPolynomial (Fin (N + 1)) R) (Loc R N S)) :=
  algebraMap_loc_injective R N S

/-- An element of `Fin 1 ↪o Fin n` is determined by `σ 0`. -/
theorem fin_one_emb_ext {n : ℕ} {σ σ' : Fin 1 ↪o Fin n} (h : σ 0 = σ' 0) : σ = σ' :=
  DFunLike.ext σ σ' fun i => by rw [Fin.fin_one_eq_zero i]; exact h

/-- Two distinct `0`-simplices are the two faces of some `1`-simplex. -/
theorem exists_face_eq {n : ℕ} (σ σ' : Fin 1 ↪o Fin n) (hlt : σ 0 < σ' 0) :
    ∃ τ : Fin 2 ↪o Fin n, CechAltAlg.face τ 1 = σ ∧ CechAltAlg.face τ 0 = σ' := by
  refine ⟨OrderEmbedding.ofStrictMono ![σ 0, σ' 0]
    (Fin.strictMono_iff_lt_succ.2 fun i => by fin_cases i; simpa using hlt), ?_, ?_⟩
  · exact fin_one_emb_ext rfl
  · exact fin_one_emb_ext rfl

/-- **(B)**: for `N ≥ 1`, a `0`-cochain `s = (s_i)_i`, `s_i ∈ (S_{T_i})_d`, is a cocycle iff there is
`a ∈ S_d` (`a = 0` when `d < 0`) with `s_i = a/1` for every `i`. (Uniqueness of `a` follows from (A).)
For `N = 0` the statement fails (one chart only, `C^1 = 0`, `ker δ^0 = (R[T]_T)_d = R·T^d`, nonzero
also for `d < 0`), hence the hypothesis `1 ≤ N`.
Proof: (⇐) `(δ s)_{(i<j)} = res(s_j) − res(s_i) = a/1 − a/1 = 0` (`CechAltAlg.d_apply` +
`Fin.sum_univ_two` + `locRes_algebraMap`).
(⇒) `S_{T_i}` and `S_{T_iT_j}` embed by (A) into `S_{T_0⋯T_N}`, which has the Laurent monomial
`R`-basis `T^e` (`e ∈ ℤ^{N+1}`); `S_{T_I}` is spanned by those with `e_k ≥ 0` for `k ∉ I`. The
cocycle condition says `s_i = s_j` in `S_{T_iT_j}`, so every monomial of the common element has "only
`e_i` may be negative" and "only `e_j` may be negative"; `i ≠ j` (using `N ≥ 1`) gives all `e_k ≥ 0`,
i.e. it comes from `S`, and by degree from `S_d`.
Source: the proof of Stacks 01XT (the block `NEG(e) = ∅`: augmented simplicial cochain complex,
`H^0 = R`). -/
theorem δ_zero_eq_zero_iff (hN : 1 ≤ N) (d : ℤ) (s : Cochain R N d 0) :
    δ R N d 0 s = 0 ↔ ∃ a ∈ polyPiece R N d, ∀ σ : Fin (0 + 1) ↪o Fin (N + 1),
      ((s σ : Term R N d (V N 0 σ)) : Loc R N (OrderDual.ofDual (V N 0 σ))) = algebraMap _ _ a := by
  constructor
  · intro hδ
    have hf : dL R N 0 (toL R N d 0 s) = 0 := by rw [← toL_δ, hδ, map_zero]
    have hpair : ∀ τ : Fin 2 ↪o Fin (N + 1),
        toL R N d 0 s (CechAltAlg.face τ 0) = toL R N d 0 s (CechAltAlg.face τ 1) := by
      intro τ
      have := congrFun hf τ
      rw [dL_apply, Fin.sum_univ_two] at this
      exact add_neg_eq_zero.1 (by simpa using this)
    have hconst : ∀ σ σ' : Fin 1 ↪o Fin (N + 1), toL R N d 0 s σ = toL R N d 0 s σ' := by
      intro σ σ'
      rcases lt_trichotomy (σ 0) (σ' 0) with h | h | h
      · obtain ⟨τ, h1, h2⟩ := exists_face_eq σ σ' h
        rw [← h1, ← h2]
        exact (hpair τ).symm
      · rw [fin_one_emb_ext h]
      · obtain ⟨τ, h1, h2⟩ := exists_face_eq σ' σ h
        rw [← h1, ← h2]
        exact hpair τ
    obtain ⟨σ₀⟩ : Nonempty (Fin 1 ↪o Fin (N + 1)) := ⟨Fin.castLEOrderEmb (by omega)⟩
    have hf₀ : toL R N d 0 s σ₀ ∈ AddMonoidAlgebra.supported R R
        {e : Fin (N + 1) → ℤ | (∀ k, 0 ≤ e k) ∧ ∑ k, e k = d} := by
      rw [AddMonoidAlgebra.mem_supported]
      intro e he
      have he' := Finsupp.mem_support_iff.1 he
      refine ⟨fun k => ?_, (mem_good_of_coeff_ne_zero R N (toL_mem R N d 0 s σ₀) he').2⟩
      obtain ⟨k', hk'⟩ : ∃ k' : Fin (N + 1), k' ≠ k := by
        by_cases hk : k = 0
        · exact ⟨⟨1, by omega⟩, by rw [hk]; exact Fin.ne_of_val_ne (by simp)⟩
        · exact ⟨0, Ne.symm hk⟩
      let σ' : Fin 1 ↪o Fin (N + 1) := OrderEmbedding.ofStrictMono (fun _ => k')
        (fun i j hij => absurd hij (by rw [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j]; exact lt_irrefl _))
      have hmem := mem_good_of_coeff_ne_zero R N (toL_mem R N d 0 s σ')
        (by rw [hconst σ' σ₀]; exact he')
      by_contra hneg
      have h1 := hmem.1 k (not_le.1 hneg)
      rw [mem_V] at h1
      obtain ⟨i, hi⟩ := h1
      exact hk' hi
    obtain ⟨a, ha, hfa⟩ := exists_polyPiece_toLaurent_eq R N d hf₀
    refine ⟨a, ha, fun σ => emb_injective R N _ ?_⟩
    rw [emb_algebraMap, hfa, ← toL_apply, hconst σ σ₀]
  · rintro ⟨a, ha, hs⟩
    apply toL_injective R N d 1
    rw [toL_δ, map_zero]
    funext τ
    rw [dL_apply, Fin.sum_univ_two, toL_apply, toL_apply, hs, hs, emb_algebraMap, emb_algebraMap]
    simp

/-- **(C)** (the main body of Stacks 01XT): except when `p + 1 = N ∧ d ≤ −(N+1)`, every cocycle of
`C^{p+1}` is a coboundary.
Edge cases: for `p + 1 > N`, `Fin (p+2) ↪o Fin (N+1)` is empty and `C^{p+1} = 0`; for the zero ring
everything is zero; for `N = 0` only the case `p + 1 > N` occurs.
Proof (Stacks 01XT): every `(S_{T_I})_d` has the `R`-basis
`{T^e : e ∈ ℤ^{N+1}, Σe = d, NEG(e) ⊆ I}`, `NEG(e) = {k : e_k < 0}`, and restriction sends `T^e` to
`T^e`, so the complex is the direct sum `⊕_e C^•(e)` with `C^p(e) = ∏_{σ ⊇ NEG(e)} R`.
(1) `NEG(e) ≠` everything: choose `i_fix ∉ NEG(e)` and set `(h s)_σ = ± s_{ins σ i_fix}` (`i_fix ∉ σ`),
`0` (`i_fix ∈ σ`) — this is `CechAltAlg.homotopyCochain`; `CechAltAlg.homotopy_step_mem` /
`homotopy_step_not_mem` (with `c = 1`) give `δ (h s) = s` for a cocycle `s`. One checks that
`ins σ i_fix ⊇ NEG(e)` when `σ ⊇ NEG(e)`, `i_fix ∉ NEG(e)`, and that the restriction map after
removing `i_fix` is bijective on the `e`-block (`e_{i_fix} ≥ 0`, so `T^e ∈ S_{T_{σ∖i_fix}}`).
(2) `NEG(e)` = everything: `C^p(e) ≠ 0` only for `p = N`, and then `Σe ≤ −(N+1)`, excluded by the
hypothesis.
Source: paragraphs 2–4 of the proof of Stacks 01XT. -/
theorem exists_δ_eq (d : ℤ) (p : ℕ) (hp : ¬ (p + 1 = N ∧ d ≤ -((N : ℤ) + 1)))
    (s : Cochain R N d (p + 1)) (hs : δ R N d (p + 1) s = 0) :
    ∃ t : Cochain R N d p, δ R N d p t = s := by
  obtain ⟨t', ht', hmem⟩ := exists_dL_eq R N d p hp (toL R N d (p + 1) s)
    (by rw [← toL_δ, hs, map_zero]) (toL_mem R N d (p + 1) s)
  obtain ⟨t, rfl⟩ := exists_toL_eq R N d p t' hmem
  refine ⟨t, toL_injective R N d (p + 1) ?_⟩
  rw [toL_δ, ht']

/-- **(D), degree `0`**: `H^0 = ker δ^0` is a finite `R`-module.
Proof: for `N ≥ 1`, by (B) the map `S_d → ker δ^0`, `a ↦ (a/1)_σ`, is surjective, and `S_d` is spanned
by the finitely many monomials of degree `d` (`MvPolynomial.homogeneousSubmodule`); for `d < 0`,
`polyPiece = ⊥`. For `N = 0`, `C^1 = 0` and `ker δ^0 = C^0 ≅ (R[T_0]_{T_0})_d = R·T_0^d` is generated by
one element (`a/T_0^j` with `a` homogeneous of degree `j + d` ⇒ `a = r T_0^{j+d}`).
Source: Stacks 01XT, statement (1). -/
theorem finite_ker_δ_zero (d : ℤ) : Module.Finite R (LinearMap.ker (δ R N d 0)) := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    exact finite_ker_zero_of_N_zero R d
  · have hN' : 1 ≤ N := hN
    have : Module.Finite R (polyPiece R N d) := by
      rw [Module.Finite.iff_fg, polyPiece]
      split_ifs
      · exact MvPolynomial.homogeneousSubmodule_fg _ _ _
      · exact Submodule.fg_bot
    let F : polyPiece R N d →ₗ[R] LinearMap.ker (δ R N d 0) :=
      { toFun := fun a => ⟨fun σ => ⟨algebraMap _ _ a.1, algebraMap_mem_degPiece R N _ d a.2⟩,
          LinearMap.mem_ker.2 ((δ_zero_eq_zero_iff R N hN' d _).2 ⟨a.1, a.2, fun _ => rfl⟩)⟩
        map_add' := fun a b => Subtype.ext (funext fun σ => Subtype.ext (by
          show algebraMap _ _ (a.1 + b.1) = algebraMap _ _ a.1 + algebraMap _ _ b.1
          rw [map_add]))
        map_smul' := fun r a => Subtype.ext (funext fun σ => Subtype.ext (by
          show algebraMap _ _ (r • a.1) = r • algebraMap _ _ a.1
          rw [Algebra.smul_def, map_mul, ← Algebra.smul_def, algebraMap_smul])) }
    refine Module.Finite.of_surjective F fun s => ?_
    obtain ⟨a, ha, hs⟩ := (δ_zero_eq_zero_iff R N hN' d s.1).1 (LinearMap.mem_ker.1 s.2)
    refine ⟨⟨a, ha⟩, Subtype.ext (funext fun σ => Subtype.ext ?_)⟩
    exact (hs σ).symm

/-- **(D), positive degrees**: `H^{p+1} = ker δ^{p+1} / im δ^p` is a finite `R`-module. Here
`H^{p+1}` is written as the image of `ker δ^{p+1}` in `C^{p+1} ⧸ im δ^p` (canonically isomorphic to
`ker/im`; `im ≤ ker` by `δ_comp`).
Proof: if `p + 1 ≠ N`, or `p + 1 = N` and `d > −(N+1)`, the quotient is zero by (C). If `p + 1 = N`
and `d ≤ −(N+1)`: `C^N` has the single index `σ = id`, `C^N ≅ (S_{T_0⋯T_N})_d` is spanned by the
Laurent monomials `T^e` (`Σe = d`); those with some `e_k ≥ 0` lie in the image of
`(S_{T_{all∖k}})_d`, i.e. of `± δ^{N−1}` (take the cochain nonzero only in the component "`k` removed");
the remaining `e` with all `e_k < 0`, `Σe = d`, are finitely many (`e_k ∈ [d, −1]`). Hence the quotient
is spanned by finitely many images of `T^e`. (Only spanning is needed, not linear independence.)
Source: Stacks 01XT, statements (2)(3) and the end of the proof. -/
theorem finite_homology_succ (d : ℤ) (p : ℕ) :
    Module.Finite R ((LinearMap.ker (δ R N d (p + 1))).map (LinearMap.range (δ R N d p)).mkQ) := by
  by_cases hpN : p + 1 = N
  · subst hpN
    exact finite_homology_top R d p
  · have hp : ¬ (p + 1 = N ∧ d ≤ -((N : ℤ) + 1)) := fun h => hpN h.1
    have hbot : (LinearMap.ker (δ R N d (p + 1))).map (LinearMap.range (δ R N d p)).mkQ = ⊥ := by
      rw [Submodule.eq_bot_iff]
      rintro _ ⟨s, hs, rfl⟩
      obtain ⟨t, ht⟩ := exists_δ_eq R N d p hp s (LinearMap.mem_ker.1 hs)
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact ⟨t, ht⟩
    rw [hbot]
    infer_instance

end LaurentCech

end
