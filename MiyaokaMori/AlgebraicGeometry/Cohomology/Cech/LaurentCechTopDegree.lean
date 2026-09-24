import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.Cech.LaurentCechCochainEmbedding

/-! # Top degree of the Laurent–Čech complex, and the case `N = 0`

Purely algebraic, `R` any commutative ring.
1. `Fin n ↪o Fin n` contains only the identity (`orderEmb_self_eq`); for `n < m`, `Fin m ↪o Fin n` is
   empty, so `C^{p}` is zero and `ker δ^p = ⊤`.
2. **Top degree `p + 1 = N`**: `H^N = C^N / im δ^{N−1}` is spanned by the images of the finitely many
   basis cochains `basisCochain σ e` with `e` entirely negative and `Σ e = d`, hence a finite `R`-module
   (`finite_homology_top`). Proof: by `eq_sum_basisCochain`, every element of `C^N` is a finite linear
   combination of `basisCochain σ e`; if some `e_k ≥ 0`, choose `k0` with `σ k0 = k` (`σ` is a
   bijection); then `basisCochain σ e = δ((−1)^{k0} • basisCochain (face σ k0) e)`
   (`basisCochain_mem_range`: `e ∈ good (range σ ∖ {σ k0}) d`, after `toL` only the term `l = k0`
   survives, and the sign squares to `1`), so its image is zero; the remaining `e` with all `e_k < 0`
   and `Σ e = d` satisfy `d ≤ e_k ≤ −1`, and there are finitely many.
3. **`N = 0`**: `good (range σ) d ⊆ {(d)}`, `finite_cochain` gives finiteness of `C^0`, and `C^1 = 0`
   so `ker δ^0 = C^0` (`finite_ker_zero_of_N_zero`).

Source: Stacks 01XT, statements (2)(3) and the end of the proof (only spanning is used; freeness of
`H^N` is not proved).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

noncomputable section

namespace LaurentCech

theorem orderEmb_self_eq {n : ℕ} (σ τ : Fin n ↪o Fin n) : σ = τ := by
  apply CechAltAlg.emb_ext
  rw [Set.range_eq_univ.2 (Finite.injective_iff_surjective.1 σ.injective),
    Set.range_eq_univ.2 (Finite.injective_iff_surjective.1 τ.injective)]

theorem isEmpty_orderEmb {m n : ℕ} (h : n < m) : IsEmpty (Fin m ↪o Fin n) :=
  ⟨fun τ => by
    have := Fintype.card_le_of_embedding τ.toEmbedding
    simp only [Fintype.card_fin] at this
    omega⟩

theorem face_injective {m n : ℕ} (σ : Fin (m + 1) ↪o Fin n) {l k : Fin (m + 1)}
    (h : CechAltAlg.face σ l = CechAltAlg.face σ k) : l = k := by
  have hr := congrArg (fun e : Fin m ↪o Fin n => Set.range e) h
  simp only [CechAltAlg.range_face] at hr
  by_contra hne
  have h1 : σ l ∈ Set.range σ \ {σ k} := ⟨⟨l, rfl⟩, fun h' => hne (σ.injective h')⟩
  rw [← hr] at h1
  exact h1.2 rfl

variable (R : Type u) [CommRing R] (N : ℕ)

theorem ker_δ_eq_top_of_isEmpty (d : ℤ) (p : ℕ) [IsEmpty (Fin (p + 2) ↪o Fin (N + 1))] :
    LinearMap.ker (δ R N d p) = ⊤ := by
  rw [LinearMap.ker_eq_top]
  ext s τ
  exact isEmptyElim τ

/-- In top degree, a basis cochain with some nonnegative coordinate is a coboundary. -/
theorem basisCochain_mem_range (d : ℤ) (p : ℕ) (σ : Fin (p + 2) ↪o Fin (p + 2))
    {e : Fin (p + 2) → ℤ} (he : e ∈ good (p + 1) (OrderDual.ofDual (V (p + 1) (p + 1) σ)) d)
    (k0 : Fin (p + 2)) (hk : 0 ≤ e (σ k0)) :
    basisCochain R (p + 1) d (p + 1) σ e ∈ LinearMap.range (δ R (p + 1) d p) := by
  classical
  have he' : e ∈ good (p + 1) (OrderDual.ofDual (V (p + 1) p (CechAltAlg.face σ k0))) d := by
    refine ⟨fun k hk' => ?_, he.2⟩
    rw [mem_V, CechAltAlg.range_face]
    refine ⟨(mem_V _ _ _).1 (he.1 k hk'), fun h => ?_⟩
    rw [Set.mem_singleton_iff] at h
    rw [h] at hk'
    exact absurd hk' (not_lt.2 hk)
  refine ⟨((-1 : ℤ) ^ (k0 : ℕ)) • basisCochain R (p + 1) d p (CechAltAlg.face σ k0) e, ?_⟩
  apply toL_injective
  rw [toL_δ, map_zsmul, toL_basisCochain _ _ _ _ _ he', toL_basisCochain _ _ _ _ _ he]
  funext τ
  obtain rfl := orderEmb_self_eq τ σ
  rw [dL_apply, Pi.single_eq_same, Finset.sum_eq_single k0]
  · rw [Pi.smul_apply, Pi.single_eq_same, smul_smul, CechAltAlg.sign_sq, one_smul]
  · intro l _ hl
    rw [Pi.smul_apply, Pi.single_eq_of_ne (fun h => hl (face_injective τ h)), smul_zero, smul_zero]
  · intro h
    exact absurd (Finset.mem_univ _) h

/-- The top-degree quotient `C^N / im δ^{N−1}` is a finite `R`-module. -/
theorem finite_quot_top (d : ℤ) (p : ℕ) :
    Module.Finite R (Cochain R (p + 1) d (p + 1) ⧸ LinearMap.range (δ R (p + 1) d p)) := by
  classical
  have : Fintype (Fin (p + 2) ↪o Fin (p + 2)) := Fintype.ofFinite _
  set Eneg : Set (Fin (p + 2) → ℤ) := {e | (∀ k, e k < 0) ∧ ∑ k, e k = d} with hEneg
  have hfin : Eneg.Finite := by
    refine Set.Finite.subset (Set.Finite.pi (t := fun _ : Fin (p + 2) => Set.Icc d (-1))
      fun _ => Set.finite_Icc _ _) ?_
    intro e he
    rw [Set.mem_univ_pi]
    intro k
    have h1 : ∑ l, e l = e k + ∑ l ∈ Finset.univ.erase k, e l :=
      (Finset.add_sum_erase _ _ (Finset.mem_univ k)).symm
    have h2 : ∑ l ∈ Finset.univ.erase k, e l ≤ 0 := Finset.sum_nonpos fun l _ => (he.1 l).le
    have h3 := he.1 k
    rw [he.2] at h1
    exact ⟨by omega, by omega⟩
  have := hfin.to_subtype
  rw [Module.finite_def, Submodule.fg_def]
  refine ⟨Set.range fun σe : (Fin (p + 2) ↪o Fin (p + 2)) × Eneg =>
    (LinearMap.range (δ R (p + 1) d p)).mkQ (basisCochain R (p + 1) d (p + 1) σe.1 σe.2),
    Set.finite_range _, ?_⟩
  refine eq_top_iff.2 fun q _ => ?_
  obtain ⟨s, rfl⟩ := Submodule.mkQ_surjective _ q
  set E : Finset (Fin (p + 2) → ℤ) :=
    Finset.univ.biUnion fun τ => (toL R (p + 1) d (p + 1) s τ).coeff.support with hE
  have hEmem : ∀ σ, ↑(toL R (p + 1) d (p + 1) s σ).coeff.support ⊆ (E : Set (Fin (p + 2) → ℤ)) := by
    intro σ e he
    rw [hE, Finset.coe_biUnion]
    exact Set.mem_biUnion (Finset.mem_univ σ) he
  rw [eq_sum_basisCochain R (p + 1) d (p + 1) s E hEmem, map_sum]
  refine Submodule.sum_mem _ fun σ _ => ?_
  rw [map_sum]
  refine Submodule.sum_mem _ fun e _ => ?_
  rw [map_smul]
  refine Submodule.smul_mem _ _ ?_
  by_cases hgood : e ∈ good (p + 1) (OrderDual.ofDual (V (p + 1) (p + 1) σ)) d
  · by_cases hneg : ∀ k, e k < 0
    · exact Submodule.subset_span ⟨(σ, ⟨e, hneg, hgood.2⟩), rfl⟩
    · simp only [not_forall, not_lt] at hneg
      obtain ⟨k, hk⟩ := hneg
      obtain ⟨k0, rfl⟩ := Finite.injective_iff_surjective.1 σ.injective k
      rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).2
        (basisCochain_mem_range R d p σ hgood k0 hk)]
      exact Submodule.zero_mem _
  · rw [basisCochain_of_not_mem _ _ _ _ _ hgood, map_zero]
    exact Submodule.zero_mem _

/-- **Top-degree case of finiteness**: for `p + 1 = N`, `H^{p+1}` is finite (for every `d`). -/
theorem finite_homology_top (d : ℤ) (p : ℕ) :
    Module.Finite R ((LinearMap.ker (δ R (p + 1) d (p + 1))).map
      (LinearMap.range (δ R (p + 1) d p)).mkQ) := by
  have := isEmpty_orderEmb (m := p + 3) (n := p + 2) (by omega)
  rw [ker_δ_eq_top_of_isEmpty, Submodule.map_top, Submodule.range_mkQ]
  have := finite_quot_top R d p
  exact Module.Finite.equiv Submodule.topEquiv.symm

/-- `N = 0`: `C^0 ≅ (R[T_0]_{T_0})_d = R·T_0^d` is finite. -/
theorem finite_cochain_zero (d : ℤ) : Module.Finite R (Cochain R 0 d 0) := by
  apply finite_cochain R 0 d 0 {fun _ => d}
  intro σ e he
  rw [Finset.coe_singleton, Set.mem_singleton_iff]
  funext k
  have := he.2
  rw [Fin.sum_univ_one] at this
  rw [Fin.fin_one_eq_zero k]
  exact this

/-- **The case `N = 0` of finiteness of `H^0`**. -/
theorem finite_ker_zero_of_N_zero (d : ℤ) : Module.Finite R (LinearMap.ker (δ R 0 d 0)) := by
  have := isEmpty_orderEmb (m := 2) (n := 1) (by omega)
  rw [ker_δ_eq_top_of_isEmpty]
  have := finite_cochain_zero R d
  exact Module.Finite.equiv Submodule.topEquiv.symm

end LaurentCech

end
