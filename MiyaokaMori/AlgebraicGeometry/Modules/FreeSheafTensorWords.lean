import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.MonoidalElementsGenerating

/-! # Words in the tensor powers of a free sheaf

Support for the identification of the symmetric algebra of a free sheaf with a weighted polynomial
algebra. Write `F := free σ = O_X^{⊕σ}` and `F^{⊗m} := monoidalPow F m` (right-recursive:
`F^{⊗(m+1)} = F^{⊗m} ⊗ F`).

* A *word* `w : Fin m → σ` gives an element `ιWord m w : 𝟙_ ⟶ F^{⊗m}`, by recursion:
  `ιWord (m+1) w = elTensor (ιWord m (Fin.init w)) (ιFree (w (last m)))`. The words generate
  `F^{⊗m}` (`generates_ιWord`, from `Generates.tensor`).
* The *exponent vector* `expVec w := ∑ j, single (w j) 1 : σ →₀ ℕ` has weight `m` for the weight
  vector `(1, …, 1)`; every exponent vector of weight `m` comes from a word (`exists_word`).
* The adjacent transposition `monoidalPowTransp F m k` sends a word to a word with the same
  exponent vector (`exists_ιWord_transp`; for `k = 0` it swaps the last two letters,
  `ιWord_transp_zero`), and the concatenation `monoidalPowCat F m n` sends `ιWord u ⊗ ιWord v` to
  `ιWord (Fin.append u v)` (`ιWord_cat`).
* The degree map `wordHom m : F^{⊗m} ⟶ P_m := free (weightedMonomials 1 m)` (recursively
  `(wordHom m ⊗ letterHom) ≫ mulHom m 1`) sends `ιWord w` to the basis element `expVec w`
  (`ιWord_wordHom`); hence it is invariant under the transpositions (`transp_wordHom`) and turns
  concatenation into `mulHom` (`cat_wordHom`), because `expVec (append u v) = expVec u + expVec v`.

Reference: Bourbaki, Algebra III §6 no. 6 Theorem 1 (the symmetric algebra of a free module with
basis `(x_i)` is the polynomial algebra in the `x_i`), formalised as in Mathlib's
`SymmetricAlgebra.equivMvPolynomial`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open scoped CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

open MiyaokaMori.Monoidal weightedPolynomialQCAlgebra

variable {X : AlgebraicGeometry.Scheme.{u}} {σ : Type u}

/-! ## Words -/

/-- The element of `F^{⊗m}` given by a word `w : Fin m → σ`: the tensor of the generators
`ιFree (w 0) ⊗ ⋯ ⊗ ιFree (w (m-1))`, built right-recursively like `monoidalPow`. -/
def ιWord : (m : ℕ) → (Fin m → σ) → (𝟙_ X.Modules ⟶ monoidalPow (free (X := X) σ) m)
  | 0, _ => 𝟙 _
  | m + 1, w => elTensor (ιWord m (Fin.init w)) (ιM X (w (Fin.last m)))

theorem ιWord_zero (w : Fin 0 → σ) : ιWord (X := X) 0 w = 𝟙 _ := rfl

theorem ιWord_succ (m : ℕ) (w : Fin (m + 1) → σ) :
    ιWord (X := X) (m + 1) w = elTensor (ιWord m (Fin.init w)) (ιM X (w (Fin.last m))) := rfl

theorem ιWord_snoc (m : ℕ) (u : Fin m → σ) (a : σ) :
    ιWord (X := X) (m + 1) (Fin.snoc u a) = elTensor (ιWord m u) (ιM X a) := by
  rw [ιWord_succ, Fin.init_snoc, Fin.snoc_last]

/-- The words generate `F^{⊗m}`. -/
theorem generates_ιWord : ∀ m : ℕ, Generates (fun w : Fin m → σ => ιWord (X := X) m w)
  | 0 => Generates.of_surj generates_unit fun _ => ⟨Fin.elim0, rfl⟩
  | m + 1 =>
    Generates.of_surj (Generates.tensor (generates_ιWord m) (generates_free σ)) fun p =>
      ⟨Fin.snoc p.1 p.2, (ιWord_snoc m p.1 p.2).symm⟩

/-! ## Exponent vectors -/

/-- The exponent vector of a word: `x_{w 0} ⋯ x_{w (m-1)} = ∏ x_i^{e i}`. -/
def expVec {m : ℕ} (w : Fin m → σ) : σ →₀ ℕ := ∑ j, Finsupp.single (w j) 1

theorem expVec_zero (w : Fin 0 → σ) : expVec w = 0 := by
  simp [expVec]

theorem expVec_snoc {m : ℕ} (u : Fin m → σ) (a : σ) :
    expVec (Fin.snoc u a) = expVec u + Finsupp.single a 1 := by
  unfold expVec
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

theorem expVec_append {m n : ℕ} (u : Fin m → σ) (v : Fin n → σ) :
    expVec (Fin.append u v) = expVec u + expVec v := by
  unfold expVec
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]

theorem weight_expVec {m : ℕ} (w : Fin m → σ) :
    Finsupp.weight (fun _ : σ => (1 : ℕ)) (expVec w) = m := by
  unfold expVec
  rw [map_sum]
  simp [Finsupp.weight_single]

theorem exists_of_expVec_apply_ne_zero {m : ℕ} (w : Fin m → σ) (i : σ) (h : expVec w i ≠ 0) :
    ∃ j, w j = i := by
  classical
  by_contra hc
  apply h
  unfold expVec
  rw [Finsupp.finsetSum_apply]
  exact Finset.sum_eq_zero fun j _ => by
    rw [Finsupp.single_apply, if_neg fun hj => hc ⟨j, hj⟩]

/-- Every exponent vector of weight `m` is the exponent vector of a word of length `m`. -/
theorem exists_word : ∀ (m : ℕ) (e : σ →₀ ℕ), Finsupp.weight (fun _ : σ => (1 : ℕ)) e = m →
    ∃ w : Fin m → σ, expVec w = e
  | 0, e, he => by
    rw [← Finsupp.degree_eq_weight_one, Finsupp.degree_eq_zero_iff] at he
    exact ⟨Fin.elim0, by rw [expVec_zero, he]⟩
  | m + 1, e, he => by
    rw [← Finsupp.degree_eq_weight_one] at he
    have hne : e ≠ 0 := by
      rintro rfl
      simp at he
    obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hne
    rw [Finsupp.mem_support_iff] at hi
    have hle : Finsupp.single i 1 ≤ e := Finsupp.single_le_iff.mpr (Nat.one_le_iff_ne_zero.mpr hi)
    have he' : (e - Finsupp.single i 1) + Finsupp.single i 1 = e := tsub_add_cancel_of_le hle
    have hdeg : Finsupp.weight (fun _ : σ => (1 : ℕ)) (e - Finsupp.single i 1) = m := by
      rw [← Finsupp.degree_eq_weight_one]
      have := congrArg Finsupp.degree he'
      rw [map_add, Finsupp.degree_single, he] at this
      omega
    obtain ⟨u, hu⟩ := exists_word m (e - Finsupp.single i 1) hdeg
    exact ⟨Fin.snoc u i, by rw [expVec_snoc, hu, he']⟩

/-! ## Transpositions and concatenation on words -/

/-- Unfolding of `monoidalPowTransp` in the case `(n + 1, k + 1)` (copy of the private lemma in
`SheafSymmetricAlgebra`). -/
theorem monoidalPowTransp_succ_succ' (V : X.Modules) (n k : ℕ) :
    monoidalPowTransp V (n + 1) (k + 1) = monoidalPowTransp V n k ▷ V := by
  cases n <;> rfl

/-- The transposition `transp (n+2) 0` swaps the last two letters of a word. -/
theorem ιWord_transp_zero (n : ℕ) (u : Fin n → σ) (a b : σ) :
    ιWord (X := X) (n + 2) (Fin.snoc (Fin.snoc u a) b) ≫ monoidalPowTransp (free (X := X) σ) (n + 2) 0 =
      ιWord (n + 2) (Fin.snoc (Fin.snoc u b) a) := by
  have e : monoidalPowTransp (free (X := X) σ) (n + 2) 0 =
      (α_ (monoidalPow (free (X := X) σ) n) (free (X := X) σ) (free (X := X) σ)).hom ≫
        (monoidalPow (free (X := X) σ) n ◁ (β_ (free (X := X) σ) (free (X := X) σ)).hom) ≫
        (α_ (monoidalPow (free (X := X) σ) n) (free (X := X) σ) (free (X := X) σ)).inv := rfl
  rw [ιWord_snoc, ιWord_snoc, ιWord_snoc, ιWord_snoc, e]
  erw [elTensor_comp_associator_hom_assoc, elTensor_comp_whiskerLeft_assoc, elTensor_comp_braiding,
    elTensor_comp_associator_inv]
  rfl

/-- Every adjacent transposition sends a word to a word with the same exponent vector. -/
theorem exists_ιWord_transp : ∀ (m k : ℕ) (w : Fin m → σ), ∃ w' : Fin m → σ,
    ιWord (X := X) m w ≫ monoidalPowTransp (free (X := X) σ) m k = ιWord m w' ∧ expVec w' = expVec w
  | 0, k, w => ⟨w, by
      rw [show monoidalPowTransp (free (X := X) σ) 0 k = 𝟙 _ from rfl, Category.comp_id], rfl⟩
  | 1, 0, w => ⟨w, by
      rw [show monoidalPowTransp (free (X := X) σ) 1 0 = 𝟙 _ from rfl, Category.comp_id], rfl⟩
  | n + 2, 0, w => by
    obtain ⟨u, a, b, rfl⟩ : ∃ (u : Fin n → σ) (a b : σ), w = Fin.snoc (Fin.snoc u a) b :=
      ⟨Fin.init (Fin.init w), Fin.init w (Fin.last n), w (Fin.last (n + 1)), by
        rw [Fin.snoc_init_self, Fin.snoc_init_self]⟩
    refine ⟨Fin.snoc (Fin.snoc u b) a, ιWord_transp_zero n u a b, ?_⟩
    simp only [expVec_snoc]
    exact add_right_comm _ _ _
  | n + 1, k + 1, w => by
    obtain ⟨u, a, rfl⟩ : ∃ (u : Fin n → σ) (a : σ), w = Fin.snoc u a :=
      ⟨Fin.init w, w (Fin.last n), (Fin.snoc_init_self w).symm⟩
    obtain ⟨u', hu', he⟩ := exists_ιWord_transp n k u
    refine ⟨Fin.snoc u' a, ?_, ?_⟩
    · rw [monoidalPowTransp_succ_succ', ιWord_snoc, ιWord_snoc]
      erw [elTensor_comp_whiskerRight]
      rw [hu']
    · rw [expVec_snoc, expVec_snoc, he]

/-- Concatenation on words: `ιWord u ⊗ ιWord v ↦ ιWord (append u v)`. -/
theorem ιWord_cat (m : ℕ) (u : Fin m → σ) : ∀ (n : ℕ) (v : Fin n → σ),
    elTensor (ιWord (X := X) m u) (ιWord n v) ≫ (monoidalPowCat (free (X := X) σ) m n).hom =
      ιWord (m + n) (Fin.append u v)
  | 0, v => by
    have hv : v = Fin.elim0 := funext fun i => i.elim0
    subst hv
    rw [ιWord_zero, show (monoidalPowCat (free (X := X) σ) m 0).hom = (ρ_ _).hom from rfl]
    erw [elTensor_comp_rightUnitor]
    rw [Fin.append_elim0]
    rfl
  | n + 1, v => by
    obtain ⟨v', b, rfl⟩ : ∃ (v' : Fin n → σ) (b : σ), v = Fin.snoc v' b :=
      ⟨Fin.init v, v (Fin.last n), (Fin.snoc_init_self v).symm⟩
    rw [show (monoidalPowCat (free (X := X) σ) m (n + 1)).hom =
        (α_ (monoidalPow (free (X := X) σ) m) (monoidalPow (free (X := X) σ) n) (free (X := X) σ)).inv ≫
          ((monoidalPowCat (free (X := X) σ) m n).hom ▷ free (X := X) σ) from rfl,
      ιWord_snoc, Fin.append_snoc]
    erw [elTensor_comp_associator_inv_assoc, elTensor_comp_whiskerRight, ιWord_cat m u n v']
    exact (ιWord_snoc (m + n) (Fin.append u v') b).symm

/-! ## The degree map `F^{⊗m} ⟶ P_m` -/

/-- The letter `x_i` as a monomial of weight `1`. -/
def letterMonomial (i : σ) : weightedMonomials (fun _ : σ => (1 : ℕ)) 1 :=
  ⟨Finsupp.single i 1, by simp [Finsupp.weight_single]⟩

/-- `F = free σ ⟶ P_1`, `ιFree i ↦ x_i`. -/
def letterHom : free (X := X) σ ⟶ weightedPolynomialQCAlgebra.part X (fun _ : σ => (1 : ℕ)) 1 :=
  SheafOfModules.freeMap (R := X.ringCatSheaf) letterMonomial

theorem ιM_letterHom (i : σ) : ιM X i ≫ letterHom = ιM X (letterMonomial i) :=
  SheafOfModules.ιFree_freeMap (R := X.ringCatSheaf) _ i

/-- The degree map `F^{⊗m} ⟶ P_m`: a word goes to its exponent vector. -/
def wordHom : (m : ℕ) → (monoidalPow (free (X := X) σ) m ⟶
    weightedPolynomialQCAlgebra.part X (fun _ : σ => (1 : ℕ)) m)
  | 0 => ιM X (⟨0, map_zero _⟩ : weightedMonomials (fun _ : σ => (1 : ℕ)) 0)
  | m + 1 => (wordHom m ⊗ₘ letterHom) ≫ mulHom X (fun _ : σ => (1 : ℕ)) m 1

theorem wordHom_zero : wordHom (X := X) (σ := σ) 0 = oneHom X (fun _ : σ => (1 : ℕ)) := rfl

theorem wordHom_succ (m : ℕ) :
    wordHom (X := X) (σ := σ) (m + 1) = (wordHom m ⊗ₘ letterHom) ≫ mulHom X (fun _ : σ => (1 : ℕ)) m 1 :=
  rfl

/-- The exponent vector of a word as a basis element of `P_m`. -/
def expMonomial {m : ℕ} (w : Fin m → σ) : weightedMonomials (fun _ : σ => (1 : ℕ)) m :=
  ⟨expVec w, weight_expVec w⟩

@[reassoc]
theorem ιWord_wordHom : ∀ (m : ℕ) (w : Fin m → σ),
    ιWord (X := X) m w ≫ wordHom m = ιM X (expMonomial w)
  | 0, w => by
    rw [ιWord_zero]
    exact (Category.id_comp (wordHom 0)).trans (ιM_congr X _ (expVec_zero w).symm)
  | m + 1, w => by
    obtain ⟨u, a, rfl⟩ : ∃ (u : Fin m → σ) (a : σ), w = Fin.snoc u a :=
      ⟨Fin.init w, w (Fin.last m), (Fin.snoc_init_self w).symm⟩
    rw [ιWord_snoc, wordHom_succ]
    erw [← Category.assoc, elTensor_comp_tensorHom]
    rw [ιWord_wordHom m u, ιM_letterHom, elTensor_ιM_ιM_mulHom]
    exact ιM_congr X _ (expVec_snoc u a).symm

/-- The degree map is invariant under the adjacent transpositions. -/
theorem transp_wordHom (m k : ℕ) :
    monoidalPowTransp (free (X := X) σ) m k ≫ wordHom m = wordHom m := by
  apply generates_ιWord m
  intro w
  obtain ⟨w', hw', he⟩ := exists_ιWord_transp m k w
  rw [← Category.assoc, hw', ιWord_wordHom, ιWord_wordHom]
  exact ιM_congr X _ he

/-- The degree map turns concatenation into the multiplication of the polynomial algebra. -/
theorem cat_wordHom (m n : ℕ) :
    (monoidalPowCat (free (X := X) σ) m n).hom ≫ wordHom (m + n) =
      (wordHom m ⊗ₘ wordHom n) ≫ mulHom X (fun _ : σ => (1 : ℕ)) m n := by
  apply Generates.tensor (generates_ιWord m) (generates_ιWord n)
  rintro ⟨u, v⟩
  simp only
  rw [← Category.assoc, ιWord_cat, ιWord_wordHom, ← Category.assoc, elTensor_comp_tensorHom,
    ιWord_wordHom, ιWord_wordHom, elTensor_ιM_ιM_mulHom]
  exact ιM_congr X _ (expVec_append u v)

end AlgebraicGeometry.Scheme.Modules

end
