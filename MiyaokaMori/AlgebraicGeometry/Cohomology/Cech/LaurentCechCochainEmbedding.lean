import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.Cech.LaurentCechLaurentRing

/-! # Embedding the Laurent–Čech complex into constant-coefficient cochains

Purely algebraic, `R` any commutative ring. The Laurent–Čech complex `C^p = ∏_σ (S_{T_σ})_d` is
embedded termwise via `emb` into the constant-coefficient complex `LC^p = ∏_σ L` (`LCochain`,
`L = R[ℤ^{N+1}]`), giving an injection `toL` compatible with the differentials: `toL ∘ δ = dL ∘ toL`
(`dL` is the instance of `CechAltAlg.d` with constant coefficients `L` and identity restriction maps);
the image is `∏_σ supported (good (V σ) d)` (`toL_mem` / `exists_toL_eq`).
Decomposition by exponents `e ∈ ℤ^{N+1}`: `proj e` extracts the coefficient at `e` and commutes with
`dL` (`dL_projC`).

Main theorem `exists_dL_eq` (the `L`-version of paragraphs 2–4 of the proof of Stacks 01XT): if
`f ∈ LC^{p+1}` is a cocycle whose components lie in `supported (good (V τ) d)`, and
`¬ (p + 1 = N ∧ d ≤ −(N+1))`, then there is `t ∈ LC^p` with components in `supported (good (V σ) d)`
and `dL t = f`.

Proof: `f = Σ_{e∈E} proj_e f` (`E` = the finite union of the supports of the components). For each
`e`, by hypothesis some `j` has `e_j ≥ 0` (otherwise `NEG(e)` = everything `⊆ range τ` forces
`p + 1 = N` and `d = Σe ≤ −(N+1)`); take `x_σ = (proj_e f)(ins σ j)`; `CechAltAlg.homotopyCochain`
gives `t_e`, and `CechAltAlg.homotopy_step_mem / homotopy_step_not_mem` (identity restriction maps,
`c = 1`) give `dL t_e = proj_e f`; `t_e σ = ± single e (coefficient)` lies in
`supported (good (V σ) d)` since `NEG(e) ⊆ range σ ∪ {j}` and `j ∉ NEG(e)`.
There are also "basis cochains" `basisCochain σ e` (with `toL` image `Pi.single σ (single e 1)`) and
the decomposition `eq_sum_basisCochain`, used for finiteness.

Source: paragraphs 2–4 of the proof of Stacks 01XT.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

noncomputable section

namespace LaurentCech

variable (R : Type u) [CommRing R] (N : ℕ)

/-- Constant-coefficient cochains `∏_σ L`. -/
abbrev LCochain (p : ℕ) : Type u := ∀ _ : Fin (p + 1) ↪o Fin (N + 1), LaurentRing R N

theorem mem_V {p : ℕ} (σ : Fin (p + 1) ↪o Fin (N + 1)) (k : Fin (N + 1)) :
    k ∈ OrderDual.ofDual (V N p σ) ↔ k ∈ Set.range σ := by
  simp [V]

/-- The termwise embedding `C^p → LC^p`. -/
def toL (d : ℤ) (p : ℕ) : Cochain R N d p →ₗ[R] LCochain R N p :=
  LinearMap.pi fun σ => ((emb R N (OrderDual.ofDual (V N p σ))).toLinearMap.comp
    (Submodule.subtype _)).comp (LinearMap.proj σ)

theorem toL_apply (d : ℤ) (p : ℕ) (s : Cochain R N d p) (σ : Fin (p + 1) ↪o Fin (N + 1)) :
    toL R N d p s σ = emb R N (OrderDual.ofDual (V N p σ)) (s σ : Loc R N _) := rfl

theorem toL_injective (d : ℤ) (p : ℕ) : Function.Injective (toL R N d p) := by
  intro s t h
  funext σ
  apply Subtype.ext
  apply emb_injective
  exact congrFun h σ

theorem toL_mem (d : ℤ) (p : ℕ) (s : Cochain R N d p) (σ : Fin (p + 1) ↪o Fin (N + 1)) :
    toL R N d p s σ ∈ AddMonoidAlgebra.supported R R (good N (OrderDual.ofDual (V N p σ)) d) :=
  emb_mem_supported R N _ d (s σ).2

theorem exists_toL_eq (d : ℤ) (p : ℕ) (g : LCochain R N p)
    (hg : ∀ σ, g σ ∈ AddMonoidAlgebra.supported R R (good N (OrderDual.ofDual (V N p σ)) d)) :
    ∃ s : Cochain R N d p, toL R N d p s = g := by
  choose x hx hxg using fun σ => exists_emb_eq R N _ d (hg σ)
  exact ⟨fun σ => ⟨x σ, hx σ⟩, funext hxg⟩

/-- The restriction maps of the constant-coefficient complex: the identity. -/
def resL {v w : (Finset (Fin (N + 1)))ᵒᵈ} (_ : w ≤ v) : LaurentRing R N →ₗ[R] LaurentRing R N :=
  LinearMap.id

theorem resL_apply {v w : (Finset (Fin (N + 1)))ᵒᵈ} (h : w ≤ v) (x : LaurentRing R N) :
    resL R N h x = x := rfl

/-- The constant-coefficient differential. -/
def dL (p : ℕ) : LCochain R N p →ₗ[R] LCochain R N (p + 1) :=
  CechAltAlg.d (V N) (fun _ => LaurentRing R N) (fun h => resL R N h) (hface N) p

theorem dL_apply (p : ℕ) (f : LCochain R N p) (τ : Fin (p + 2) ↪o Fin (N + 1)) :
    dL R N p f τ = ∑ k : Fin (p + 2), ((-1 : ℤ) ^ (k : ℕ)) • f (CechAltAlg.face τ k) := by
  rw [dL, CechAltAlg.d_apply]
  rfl

theorem toL_δ (d : ℤ) (p : ℕ) (s : Cochain R N d p) :
    toL R N d (p + 1) (δ R N d p s) = dL R N p (toL R N d p s) := by
  funext τ
  rw [toL_apply, δ, CechAltAlg.d_apply, dL_apply, Submodule.coe_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Submodule.coe_smul_of_tower, map_zsmul, toL_apply]
  congr 1
  exact emb_locRes R N (hface N p τ k) _

/-- The projection onto the coefficient at `e`: `x ↦ single e (x.coeff e)`. -/
def proj (e : Fin (N + 1) → ℤ) : LaurentRing R N →ₗ[R] LaurentRing R N :=
  (AddMonoidAlgebra.lsingle (R := R) e).comp
    ((Finsupp.lapply e).comp (AddMonoidAlgebra.coeffLinearEquiv R).toLinearMap)

theorem proj_apply (e : Fin (N + 1) → ℤ) (x : LaurentRing R N) :
    proj R N e x = AddMonoidAlgebra.single e (x.coeff e) := rfl

theorem sum_proj_eq (x : LaurentRing R N) (E : Finset (Fin (N + 1) → ℤ))
    (hE : ↑x.coeff.support ⊆ (E : Set (Fin (N + 1) → ℤ))) : ∑ e ∈ E, proj R N e x = x := by
  classical
  apply AddMonoidAlgebra.coeff_inj.1
  ext h
  rw [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  simp only [proj_apply, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  rw [Finset.sum_ite_eq']
  split_ifs with hh
  · rfl
  · by_contra hne
    exact hh (hE (Finsupp.mem_support_iff.2 (Ne.symm hne)))

/-- The `e`-block of a cochain. -/
def projC (p : ℕ) (e : Fin (N + 1) → ℤ) : LCochain R N p →ₗ[R] LCochain R N p :=
  LinearMap.pi fun σ => (proj R N e).comp (LinearMap.proj σ)

theorem projC_apply (p : ℕ) (e : Fin (N + 1) → ℤ) (f : LCochain R N p)
    (σ : Fin (p + 1) ↪o Fin (N + 1)) : projC R N p e f σ = proj R N e (f σ) := rfl

theorem dL_projC (p : ℕ) (e : Fin (N + 1) → ℤ) (f : LCochain R N p) :
    dL R N p (projC R N p e f) = projC R N (p + 1) e (dL R N p f) := by
  funext τ
  rw [projC_apply, dL_apply, dL_apply, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_zsmul, projC_apply]

theorem sum_projC_eq (p : ℕ) (f : LCochain R N p) (E : Finset (Fin (N + 1) → ℤ))
    (hE : ∀ σ, ↑(f σ).coeff.support ⊆ (E : Set (Fin (N + 1) → ℤ))) :
    ∑ e ∈ E, projC R N p e f = f := by
  funext σ
  rw [Finset.sum_apply]
  simp only [projC_apply]
  exact sum_proj_eq R N (f σ) E (hE σ)

theorem single_mem_supported {I : Finset (Fin (N + 1))} {d : ℤ} {e : Fin (N + 1) → ℤ}
    (he : e ∈ good N I d) (r : R) :
    (AddMonoidAlgebra.single e r : LaurentRing R N) ∈ AddMonoidAlgebra.supported R R (good N I d) := by
  rw [AddMonoidAlgebra.mem_supported, AddMonoidAlgebra.coeff_single]
  intro k hk
  have := Finsupp.support_single_subset hk
  rw [Finset.mem_singleton] at this
  rw [this]
  exact he

theorem mem_good_of_coeff_ne_zero {I : Finset (Fin (N + 1))} {d : ℤ} {x : LaurentRing R N}
    (hx : x ∈ AddMonoidAlgebra.supported R R (good N I d)) {e : Fin (N + 1) → ℤ}
    (he : x.coeff e ≠ 0) : e ∈ good N I d :=
  (AddMonoidAlgebra.mem_supported.1 hx) (Finsupp.mem_support_iff.2 he)

/-- Blockwise homotopy: an `e`-block cocycle with `e_j ≥ 0` is a coboundary, with a preimage whose
components lie in the same `supported` submodules. -/
theorem exists_dL_eq_block (d : ℤ) (p : ℕ) (f : LCochain R N (p + 1))
    (hf : dL R N (p + 1) f = 0)
    (hmem : ∀ τ, f τ ∈ AddMonoidAlgebra.supported R R (good N (OrderDual.ofDual (V N (p + 1) τ)) d))
    (e : Fin (N + 1) → ℤ) (j : Fin (N + 1)) (hj : 0 ≤ e j) :
    ∃ t : LCochain R N p, dL R N p t = projC R N (p + 1) e f ∧
      ∀ σ, t σ ∈ AddMonoidAlgebra.supported R R (good N (OrderDual.ofDual (V N p σ)) d) := by
  classical
  obtain ⟨s', hs'def⟩ : ∃ s', projC R N (p + 1) e f = s' := ⟨_, rfl⟩
  have hs' : dL R N (p + 1) s' = 0 := by rw [← hs'def, dL_projC, hf, map_zero]
  let x : ∀ σ : Fin (p + 1) ↪o Fin (N + 1), j ∉ Set.range σ → LaurentRing R N :=
    fun σ hj' => s' (CechAltAlg.ins σ j hj')
  have hx : ∀ σ hj', resL R N (CechAltAlg.le_ins (V N) (hface N) p σ j hj') (x σ hj') =
      (1 : R) • s' (CechAltAlg.ins σ j hj') :=
    fun _ _ => (one_smul _ _).symm
  rw [hs'def]
  refine ⟨CechAltAlg.homotopyCochain (V N) (fun _ => LaurentRing R N) p j x, ?_, ?_⟩
  · funext τ
    by_cases hjτ : j ∈ Set.range τ
    · have := CechAltAlg.homotopy_step_mem (V N) (fun _ => LaurentRing R N)
        (fun h => resL R N h) (hface N) p s' j (1 : R) x hx τ hjτ
      rw [one_smul] at this
      exact this
    · have := CechAltAlg.homotopy_step_not_mem (V N) (fun _ => LaurentRing R N)
        (fun h => resL R N h) (hface N) (fun _ _ _ => rfl) p s' hs' j (1 : R) x hx τ hjτ
      rw [one_smul, resL_apply, resL_apply] at this
      exact this
  · intro σ
    by_cases hjσ : j ∈ Set.range σ
    · rw [CechAltAlg.homotopyCochain_mem _ _ _ _ _ _ hjσ]
      exact Submodule.zero_mem _
    · rw [CechAltAlg.homotopyCochain_not_mem _ _ _ _ _ _ hjσ]
      apply zsmul_mem
      show s' (CechAltAlg.ins σ j hjσ) ∈ _
      rw [← hs'def, projC_apply, proj_apply]
      by_cases hc : (f (CechAltAlg.ins σ j hjσ)).coeff e = 0
      · rw [hc, AddMonoidAlgebra.single_zero]
        exact Submodule.zero_mem _
      · apply single_mem_supported
        have hgood := mem_good_of_coeff_ne_zero R N (hmem _) hc
        refine ⟨fun k hk => ?_, hgood.2⟩
        have h1 := hgood.1 k hk
        rw [mem_V, CechAltAlg.range_ins, Set.mem_insert_iff] at h1
        rw [mem_V]
        rcases h1 with rfl | h1
        · exact absurd hk (not_lt.2 hj)
        · exact h1

/-- If all coordinates of `e` are negative, a component containing `e` can only occur at `τ` with
`range τ` = everything, in which case `p + 1 = N` and `d ≤ −(N+1)`. -/
theorem exists_nonneg_of_mem_good (d : ℤ) (p : ℕ) (hp : ¬ (p + 1 = N ∧ d ≤ -((N : ℤ) + 1)))
    (τ : Fin (p + 2) ↪o Fin (N + 1)) {e : Fin (N + 1) → ℤ}
    (he : e ∈ good N (OrderDual.ofDual (V N (p + 1) τ)) d) : ∃ j, 0 ≤ e j := by
  by_contra hneg
  simp only [not_exists, not_le] at hneg
  apply hp
  have hall : ∀ k, k ∈ OrderDual.ofDual (V N (p + 1) τ) := fun k => he.1 k (hneg k)
  have huniv : OrderDual.ofDual (V N (p + 1) τ) = Finset.univ := Finset.eq_univ_iff_forall.2 hall
  have hcard : (OrderDual.ofDual (V N (p + 1) τ)).card = p + 2 := by
    show (Finset.univ.map τ.toEmbedding).card = p + 2
    rw [Finset.card_map, Finset.card_univ, Fintype.card_fin]
  rw [huniv, Finset.card_univ, Fintype.card_fin] at hcard
  refine ⟨by omega, ?_⟩
  rw [← he.2]
  have : ∑ k : Fin (N + 1), e k ≤ ∑ _k : Fin (N + 1), (-1 : ℤ) :=
    Finset.sum_le_sum fun k _ => by have := hneg k; omega
  simpa using this

/-- **Main theorem, `L`-version** (paragraphs 2–4 of the proof of Stacks 01XT): except when
`p + 1 = N ∧ d ≤ −(N+1)`, a cocycle of the constant-coefficient complex lying in
`∏ supported (good (V ·) d)` is the coboundary of a cochain lying in the same submodule. -/
theorem exists_dL_eq (d : ℤ) (p : ℕ) (hp : ¬ (p + 1 = N ∧ d ≤ -((N : ℤ) + 1)))
    (f : LCochain R N (p + 1)) (hf : dL R N (p + 1) f = 0)
    (hmem : ∀ τ, f τ ∈ AddMonoidAlgebra.supported R R (good N (OrderDual.ofDual (V N (p + 1) τ)) d)) :
    ∃ t : LCochain R N p, dL R N p t = f ∧
      ∀ σ, t σ ∈ AddMonoidAlgebra.supported R R (good N (OrderDual.ofDual (V N p σ)) d) := by
  classical
  have : Fintype (Fin (p + 2) ↪o Fin (N + 1)) := Fintype.ofFinite _
  set E : Finset (Fin (N + 1) → ℤ) := Finset.univ.biUnion fun τ => (f τ).coeff.support with hE
  have hEmem : ∀ τ, ↑(f τ).coeff.support ⊆ (E : Set (Fin (N + 1) → ℤ)) := by
    intro τ e he
    rw [hE, Finset.coe_biUnion]
    exact Set.mem_biUnion (Finset.mem_univ τ) he
  have hEnn : ∀ e ∈ E, ∃ j, 0 ≤ e j := by
    intro e he
    rw [hE, Finset.mem_biUnion] at he
    obtain ⟨τ, -, he⟩ := he
    exact exists_nonneg_of_mem_good N d p hp τ
      (mem_good_of_coeff_ne_zero R N (hmem τ) (Finsupp.mem_support_iff.1 he))
  let T : (Fin (N + 1) → ℤ) → LCochain R N p := fun e =>
    if h : ∃ j, 0 ≤ e j then
      Classical.choose (exists_dL_eq_block R N d p f hf hmem e (Classical.choose h)
        (Classical.choose_spec h))
    else 0
  have hT : ∀ e ∈ E, dL R N p (T e) = projC R N (p + 1) e f ∧
      ∀ σ, T e σ ∈ AddMonoidAlgebra.supported R R (good N (OrderDual.ofDual (V N p σ)) d) := by
    intro e he
    have h := hEnn e he
    simp only [T, dif_pos h]
    exact Classical.choose_spec (exists_dL_eq_block R N d p f hf hmem e (Classical.choose h)
      (Classical.choose_spec h))
  refine ⟨∑ e ∈ E, T e, ?_, ?_⟩
  · rw [map_sum, Finset.sum_congr rfl fun e he => (hT e he).1]
    exact sum_projC_eq R N (p + 1) f E hEmem
  · intro σ
    rw [Finset.sum_apply]
    exact Submodule.sum_mem _ fun e he => (hT e he).2 σ

/-! ## Basis cochains and decomposition -/

open Classical in
theorem pi_single_mem (d : ℤ) (p : ℕ) (σ : Fin (p + 1) ↪o Fin (N + 1)) {e : Fin (N + 1) → ℤ}
    (he : e ∈ good N (OrderDual.ofDual (V N p σ)) d) (τ : Fin (p + 1) ↪o Fin (N + 1)) :
    (Pi.single (M := fun _ => LaurentRing R N) σ (AddMonoidAlgebra.single e (1 : R)) τ ∈
      AddMonoidAlgebra.supported R R (good N (OrderDual.ofDual (V N p τ)) d)) := by
  classical
  by_cases h : τ = σ
  · subst h
    rw [Pi.single_eq_same]
    exact single_mem_supported R N he 1
  · rw [Pi.single_eq_of_ne h]
    exact Submodule.zero_mem _

/-- Basis cochain: its `toL` image is `Pi.single σ (single e 1)` if `e ∈ good (V σ) d`, and `0`
otherwise. -/
def basisCochain (d : ℤ) (p : ℕ) (σ : Fin (p + 1) ↪o Fin (N + 1)) (e : Fin (N + 1) → ℤ) :
    Cochain R N d p := by
  classical
  exact if h : e ∈ good N (OrderDual.ofDual (V N p σ)) d then
    Classical.choose (exists_toL_eq R N d p
      (Pi.single (M := fun _ => LaurentRing R N) σ (AddMonoidAlgebra.single e (1 : R)))
      (pi_single_mem R N d p σ h))
  else 0

open Classical in
theorem toL_basisCochain (d : ℤ) (p : ℕ) (σ : Fin (p + 1) ↪o Fin (N + 1)) {e : Fin (N + 1) → ℤ}
    (he : e ∈ good N (OrderDual.ofDual (V N p σ)) d) :
    toL R N d p (basisCochain R N d p σ e) =
      Pi.single (M := fun _ => LaurentRing R N) σ (AddMonoidAlgebra.single e (1 : R)) := by
  classical
  rw [basisCochain, dif_pos he]
  exact Classical.choose_spec (exists_toL_eq R N d p _ (pi_single_mem R N d p σ he))

theorem basisCochain_of_not_mem (d : ℤ) (p : ℕ) (σ : Fin (p + 1) ↪o Fin (N + 1))
    {e : Fin (N + 1) → ℤ} (he : e ∉ good N (OrderDual.ofDual (V N p σ)) d) :
    basisCochain R N d p σ e = 0 := by
  classical
  rw [basisCochain, dif_neg he]

/-- Decomposition: `s = Σ_σ Σ_{e∈E} (toL s σ).coeff e • basisCochain σ e`, whenever `E` contains the
supports of all components. -/
theorem eq_sum_basisCochain (d : ℤ) (p : ℕ) [Fintype (Fin (p + 1) ↪o Fin (N + 1))]
    (s : Cochain R N d p) (E : Finset (Fin (N + 1) → ℤ))
    (hE : ∀ σ, ↑(toL R N d p s σ).coeff.support ⊆ (E : Set (Fin (N + 1) → ℤ))) :
    s = ∑ σ, ∑ e ∈ E, (toL R N d p s σ).coeff e • basisCochain R N d p σ e := by
  classical
  apply toL_injective R N d p
  funext τ
  rw [map_sum, Finset.sum_apply]
  have hterm : ∀ σ : Fin (p + 1) ↪o Fin (N + 1),
      toL R N d p (∑ e ∈ E, (toL R N d p s σ).coeff e • basisCochain R N d p σ e) τ =
      if σ = τ then ∑ e ∈ E, proj R N e (toL R N d p s τ) else 0 := by
    intro σ
    rw [map_sum, Finset.sum_apply]
    split_ifs with hστ
    · subst hστ
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [map_smul, Pi.smul_apply, proj_apply]
      by_cases he : e ∈ good N (OrderDual.ofDual (V N p σ)) d
      · rw [toL_basisCochain R N d p σ he, Pi.single_eq_same, AddMonoidAlgebra.smul_single', mul_one]
      · have hc : (toL R N d p s σ).coeff e = 0 := by
          by_contra hc
          exact he (mem_good_of_coeff_ne_zero R N (toL_mem R N d p s σ) hc)
        rw [hc, zero_smul, AddMonoidAlgebra.single_zero]
    · refine Finset.sum_eq_zero fun e _ => ?_
      rw [map_smul, Pi.smul_apply]
      by_cases he : e ∈ good N (OrderDual.ofDual (V N p σ)) d
      · rw [toL_basisCochain R N d p σ he, Pi.single_eq_of_ne (Ne.symm hστ), smul_zero]
      · rw [basisCochain_of_not_mem R N d p σ he, map_zero, Pi.zero_apply, smul_zero]
  rw [Finset.sum_congr rfl fun σ _ => hterm σ, Finset.sum_ite_eq', if_pos (Finset.mem_univ τ)]
  exact (sum_proj_eq R N _ E (hE τ)).symm

/-- If a finite set of exponents `E` contains every `good (V σ) d`, then `C^p` is a finite
`R`-module. -/
theorem finite_cochain (d : ℤ) (p : ℕ) (E : Finset (Fin (N + 1) → ℤ))
    (hE : ∀ σ : Fin (p + 1) ↪o Fin (N + 1), good N (OrderDual.ofDual (V N p σ)) d ⊆ E) :
    Module.Finite R (Cochain R N d p) := by
  classical
  have : Fintype (Fin (p + 1) ↪o Fin (N + 1)) := Fintype.ofFinite _
  rw [Module.finite_def, Submodule.fg_def]
  refine ⟨Set.range fun σe : (Fin (p + 1) ↪o Fin (N + 1)) × E =>
    basisCochain R N d p σe.1 σe.2, Set.finite_range _, ?_⟩
  refine eq_top_iff.2 fun s _ => ?_
  rw [eq_sum_basisCochain R N d p s E fun σ => (AddMonoidAlgebra.mem_supported.1
    (toL_mem R N d p s σ)).trans (hE σ)]
  refine Submodule.sum_mem _ fun σ _ => Submodule.sum_mem _ fun e he => Submodule.smul_mem _ _ ?_
  exact Submodule.subset_span ⟨(σ, ⟨e, he⟩), rfl⟩

end LaurentCech

end
