import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.GradedQCAlgebraIsoMk
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.SymGradedAlgebraCongr
import MiyaokaMori.AlgebraicGeometry.Modules.FreeSheafTensorWords

/-! # The symmetric algebra of a free sheaf is a polynomial algebra

The symmetric algebra of the free sheaf `O_X^{⊕σ}` (`σ` finite) is the polynomial algebra
`O_X[x_i : i ∈ σ]` with its standard grading (all weights `1`):
`symGradedAlgebra (free σ) ≅ weightedPolynomialQCAlgebra X (fun _ => 1)` as graded
quasi-coherent algebras. This is the sheaf version of Mathlib's `SymmetricAlgebra.equivMvPolynomial`.

References: Bourbaki, Algebra III §6 no. 6 Theorem 1 (the symmetric algebra of a free module with
basis `(x_i)` is the polynomial algebra in the `x_i`); Stacks 01CH (Sym commutes with
restriction to opens). Used for the fibres of `P(O ⊕ L)`: `Sym(O^2) = O[T_0, T_1]`, so the fibre is
`Proj κ(y)[T_0,T_1]`. The sibling result `symGradedAlgebra_isLocallyWeightedPolynomial` is the
atlas form of the same computation for a locally free sheaf of constant rank; the present statement
is the global statement for a free sheaf and gives that one on a trivialising chart.

Supporting modules: `MonoidalElementsGenerating` (elements `𝟙_ ⟶ A` of a monoidal object, their
tensors, and generating families, closed under `⊗` by the tensor-Hom adjunction) and
`FreeSheafTensorWords` (words `ιWord w : 𝟙_ ⟶ F^{⊗m}`, exponent vectors, transpositions,
concatenation, and the degree map `wordHom m : F^{⊗m} ⟶ P_m`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open scoped CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

open MiyaokaMori.Monoidal weightedPolynomialQCAlgebra

variable {X : AlgebraicGeometry.Scheme.{u}} {σ : Type u}

/-! ## `Sym^m F ⟶ P_m` -/

/-- `α_m : Sym^m F ⟶ P_m`, the degree map `wordHom m` descended along the coequaliser
(it is invariant under the adjacent transpositions, `transp_wordHom`). -/
def symToPoly (m : ℕ) :
    symPow (free (X := X) σ) m ⟶ weightedPolynomialQCAlgebra.part X (fun _ : σ => (1 : ℕ)) m :=
  symPowDesc (free (X := X) σ) m (wordHom m) fun i => transp_wordHom m i

@[reassoc]
theorem symPowπ_symToPoly (m : ℕ) :
    symPowπ (free (X := X) σ) m ≫ symToPoly m = wordHom m :=
  symPowπ_desc _ _ _ _

/-! ## Classes of words in `Sym^m F` -/

/-- The class of a word in `Sym^m F`. -/
def wordClass {m : ℕ} (w : Fin m → σ) : 𝟙_ X.Modules ⟶ symPow (free (X := X) σ) m :=
  ιWord m w ≫ symPowπ (free (X := X) σ) m

/-- The class of `w · a` is the product of the classes of `w` and of the letter `a`
(`symPowMul` is compatible with the quotient maps and with concatenation). -/
theorem wordClass_snoc (n : ℕ) (u : Fin n → σ) (a : σ) :
    wordClass (X := X) (Fin.snoc u a) =
      elTensor (wordClass u) (wordClass (fun _ : Fin 1 => a)) ≫ symPowMul (free (X := X) σ) n 1 := by
  unfold wordClass
  rw [← elTensor_comp_tensorHom, Category.assoc, tensorHom_symPowπ_symPowMul, ← Category.assoc,
    ιWord_cat, Fin.append_right_eq_snoc]

/-- The class of `w · a` depends only on the class of `w`. -/
theorem wordClass_snoc_congr {n : ℕ} {u u' : Fin n → σ}
    (h : wordClass (X := X) u = wordClass u') (a : σ) :
    wordClass (X := X) (Fin.snoc u a) = wordClass (Fin.snoc u' a) := by
  rw [wordClass_snoc, h, ← wordClass_snoc]

/-- Swapping the last two letters does not change the class (the adjacent transposition
`transp (n+2) 0` is killed by the quotient map). -/
theorem wordClass_swap (n : ℕ) (u : Fin n → σ) (a b : σ) :
    wordClass (X := X) (Fin.snoc (Fin.snoc u a) b) = wordClass (Fin.snoc (Fin.snoc u b) a) := by
  unfold wordClass
  rw [← ιWord_transp_zero n u a b, Category.assoc,
    monoidalPowTransp_symPowπ (free (X := X) σ) (n + 2) 0 (by omega)]

/-- A letter occurring in a word can be moved to the end without changing the class or the
exponent vector (induction on the length, using `wordClass_snoc_congr` and `wordClass_swap`). -/
theorem exists_wordClass_snoc : ∀ (n : ℕ) (u : Fin (n + 1) → σ) (a : σ), (∃ j, u j = a) →
    ∃ u' : Fin n → σ, wordClass (X := X) u = wordClass (Fin.snoc u' a) ∧
      expVec (Fin.snoc u' a) = expVec u
  | 0, u, a, ⟨j, hj⟩ => by
    have hlast : u (Fin.last 0) = a := by
      rw [show Fin.last 0 = j from Fin.ext (by have := j.isLt; simp only [Fin.val_last]; omega)]
      exact hj
    have hu : u = Fin.snoc (Fin.init u) a := by rw [← hlast, Fin.snoc_init_self]
    exact ⟨Fin.init u, congrArg wordClass hu, congrArg expVec hu.symm⟩
  | n + 1, u, a, ⟨j, hj⟩ => by
    by_cases hc : u (Fin.last (n + 1)) = a
    · have hu : u = Fin.snoc (Fin.init u) a := by rw [← hc, Fin.snoc_init_self]
      exact ⟨Fin.init u, congrArg wordClass hu, congrArg expVec hu.symm⟩
    · have hj' : j ≠ Fin.last (n + 1) := fun h => hc (h ▸ hj)
      obtain ⟨j', rfl⟩ := Fin.exists_castSucc_eq.mpr hj'
      obtain ⟨v, hv, he⟩ := exists_wordClass_snoc n (Fin.init u) a ⟨j', hj⟩
      refine ⟨Fin.snoc v (u (Fin.last (n + 1))), ?_, ?_⟩
      · calc wordClass (X := X) u
            = wordClass (Fin.snoc (Fin.init u) (u (Fin.last (n + 1)))) :=
              congrArg wordClass (Fin.snoc_init_self u).symm
          _ = wordClass (Fin.snoc (Fin.snoc v a) (u (Fin.last (n + 1)))) :=
              wordClass_snoc_congr hv _
          _ = wordClass (Fin.snoc (Fin.snoc v (u (Fin.last (n + 1)))) a) := wordClass_swap _ _ _ _
      · rw [expVec_snoc, expVec_snoc, add_right_comm, ← expVec_snoc, he, ← expVec_snoc,
          Fin.snoc_init_self]

/-- **Well-definedness**: two words with the same exponent vector have the same class in
`Sym^m F` (induction on the length: move the last letter of the first word to the end of the
second, cancel it, and apply the induction hypothesis). -/
theorem wordClass_eq_of_expVec_eq : ∀ (m : ℕ) (w w' : Fin m → σ), expVec w = expVec w' →
    wordClass (X := X) w = wordClass w'
  | 0, _, _, _ => congrArg wordClass (funext fun i => i.elim0)
  | n + 1, w, w', h => by
    obtain ⟨u, a, rfl⟩ : ∃ (u : Fin n → σ) (a : σ), w = Fin.snoc u a :=
      ⟨Fin.init w, w (Fin.last n), (Fin.snoc_init_self w).symm⟩
    have hne : expVec w' a ≠ 0 := by
      rw [← h, expVec_snoc, Finsupp.add_apply, Finsupp.single_eq_same]
      omega
    obtain ⟨u'', hc, he⟩ :=
      exists_wordClass_snoc n w' a (exists_of_expVec_apply_ne_zero w' a hne)
    rw [hc]
    apply wordClass_snoc_congr
    apply wordClass_eq_of_expVec_eq n
    have : expVec u + Finsupp.single a 1 = expVec u'' + Finsupp.single a 1 := by
      rw [← expVec_snoc, ← expVec_snoc, h, he]
    exact add_right_cancel this

/-! ## `P_m ⟶ Sym^m F` -/

/-- A word with a given exponent vector of weight `m` (`exists_word`). -/
def canonWord (m : ℕ) (e : weightedMonomials (fun _ : σ => (1 : ℕ)) m) : Fin m → σ :=
  Classical.choose (exists_word m e.1 e.2)

theorem expVec_canonWord (m : ℕ) (e : weightedMonomials (fun _ : σ => (1 : ℕ)) m) :
    expVec (canonWord m e) = e.1 :=
  Classical.choose_spec (exists_word m e.1 e.2)

/-- `β_m : P_m ⟶ Sym^m F`, the basis element `e` goes to the class of a word with exponent
vector `e`. -/
def polyToSym (m : ℕ) :
    weightedPolynomialQCAlgebra.part X (fun _ : σ => (1 : ℕ)) m ⟶ symPow (free (X := X) σ) m :=
  Sigma.desc (C := SheafOfModules.{u} X.ringCatSheaf)
    (f := fun _ : weightedMonomials (fun _ : σ => (1 : ℕ)) m => SheafOfModules.unit X.ringCatSheaf)
    fun e => wordClass (canonWord m e)

theorem ιM_polyToSym (m : ℕ) (e : weightedMonomials (fun _ : σ => (1 : ℕ)) m) :
    ιM X e ≫ polyToSym m = wordClass (canonWord m e) :=
  Sigma.ι_desc (C := SheafOfModules.{u} X.ringCatSheaf)
    (f := fun _ : weightedMonomials (fun _ : σ => (1 : ℕ)) m => SheafOfModules.unit X.ringCatSheaf)
    _ e

theorem symToPoly_polyToSym (m : ℕ) :
    symToPoly (X := X) (σ := σ) m ≫ polyToSym m = 𝟙 _ := by
  rw [← cancel_epi (symPowπ (free (X := X) σ) m)]
  apply generates_ιWord m
  intro w
  rw [symPowπ_symToPoly_assoc, ιWord_wordHom_assoc, ιM_polyToSym, Category.comp_id]
  exact wordClass_eq_of_expVec_eq m _ w (expVec_canonWord m _)

theorem polyToSym_symToPoly (m : ℕ) :
    polyToSym (X := X) (σ := σ) m ≫ symToPoly m = 𝟙 _ := by
  apply free_hom_ext X
  intro e
  rw [← Category.assoc, ιM_polyToSym, Category.comp_id]
  unfold wordClass
  rw [Category.assoc, symPowπ_symToPoly, ιWord_wordHom]
  exact ιM_congr X _ (expVec_canonWord m e)

/-- `α_m` is an isomorphism `Sym^m F ≅ P_m`. -/
def symPowIsoPart (m : ℕ) :
    symPow (free (X := X) σ) m ≅ weightedPolynomialQCAlgebra.part X (fun _ : σ => (1 : ℕ)) m where
  hom := symToPoly m
  inv := polyToSym m
  hom_inv_id := symToPoly_polyToSym m
  inv_hom_id := polyToSym_symToPoly m

/-! ## Compatibility with the algebra structure -/

/-- `α` is multiplicative (check after the epimorphism `π_m ⊗ π_n`, where it is `cat_wordHom`). -/
theorem symPowMul_symToPoly (m n : ℕ) :
    symPowMul (free (X := X) σ) m n ≫ symToPoly (m + n) =
      (symToPoly m ⊗ₘ symToPoly n) ≫ mulHom X (fun _ : σ => (1 : ℕ)) m n := by
  apply symPowπ_tensorHom_cancel
  rw [← Category.assoc, tensorHom_symPowπ_symPowMul, Category.assoc, symPowπ_symToPoly,
    ← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom, symPowπ_symToPoly,
    symPowπ_symToPoly]
  exact cat_wordHom m n

/-- `α` is unital: the empty word goes to the monomial `1`. -/
theorem symPowπ_zero_symToPoly :
    symPowπ (free (X := X) σ) 0 ≫ symToPoly 0 = oneHom X (fun _ : σ => (1 : ℕ)) :=
  symPowπ_symToPoly 0

/-- `Sym(O_X^{⊕σ}) ≅ O_X[x_i : i ∈ σ]` as graded quasi-coherent algebras (quasi-coherent
branch of `symGradedAlgebra`). -/
def symGradedAlgebraOfQC_free_iso_weightedPolynomialQCAlgebra [Finite σ] :
    symGradedAlgebraOfQC (free (X := X) σ) inferInstance ≅
      AlgebraicGeometry.Scheme.weightedPolynomialQCAlgebra X (fun _ : σ => 1) (fun _ => Nat.one_pos) :=
  GradedQCAlgebra.isoMk (fun m => symPowIsoPart m) symPowMul_symToPoly symPowπ_zero_symToPoly

end AlgebraicGeometry.Scheme.Modules

/-- **Sym of a free sheaf is the polynomial algebra.**

Proof (as formalised). Write `F := free σ`, `P_m := weightedPolynomialQCAlgebra.part X 1 m =
free (weightedMonomials 1 m)`, `weightedMonomials 1 m = {e : σ →₀ ℕ // weight 1 e = m}`, with
multiplication `mulHom` (`(e, e') ↦ e + e'` on basis elements) and unit the basis element `0`.
`F` is free hence quasi-coherent, so `symGradedAlgebra F = symGradedAlgebraOfQC F _`
(`symGradedAlgebra_eq_ofQC`): degree `m` is `symPow F m`, the coequaliser of the adjacent
transpositions `monoidalPowTransp F m i` on `F^{⊗m}`, with quotient map `symPowπ F m`.
1. *Words* (`…_Words`): a word `w : Fin m → σ` gives an element `ιWord m w : 𝟙_ ⟶ F^{⊗m}`
   (tensor of the generators `ιFree (w j)`); the words generate `F^{⊗m}` in the sense that
   morphisms out of `F^{⊗m}` are determined by their values on them (`generates_ιWord`, from
   `free_hom_ext` and the tensor-Hom adjunction, `Generates.tensor`). The adjacent transposition
   sends a word to a word with the same exponent vector `expVec w = ∑ single (w j) 1`
   (`exists_ιWord_transp`; `transp (n+2) 0` swaps the last two letters), and concatenation
   `monoidalPowCat` sends `ιWord u ⊗ ιWord v` to `ιWord (append u v)` (`ιWord_cat`).
2. *Degree map*: `wordHom m : F^{⊗m} ⟶ P_m`, defined recursively by
   `(wordHom m ⊗ letterHom) ≫ mulHom m 1`, sends `ιWord w` to the basis element `expVec w`
   (`ιWord_wordHom`). Hence it is invariant under the transpositions (`transp_wordHom`) and it
   descends to `α_m := symToPoly m : Sym^m F ⟶ P_m`; and `cat ≫ wordHom = (wordHom ⊗ wordHom) ≫
   mulHom` (`cat_wordHom`) because `expVec (append u v) = expVec u + expVec v`.
3. *Inverse*: every exponent vector of weight `m` is `expVec` of a word (`exists_word`, by
   induction on `m`, removing one letter); `β_m := polyToSym m : P_m ⟶ Sym^m F` sends the basis
   element `e` to the class of such a word. Well-definedness (`wordClass_eq_of_expVec_eq`): two
   words with the same exponent vector have the same class in `Sym^m F`, by induction on `m` —
   the last letter `a` of the first word occurs in the second, it can be moved to the end without
   changing the class (`exists_wordClass_snoc`: repeatedly swap the last two letters,
   `wordClass_swap`, using that the class of `w · a` depends only on the class of `w`,
   `wordClass_snoc_congr`, which is the multiplicativity of `symPowπ`), then cancel `a`.
   No permutation group is needed.
4. `α_m ≫ β_m = 𝟙` (cancel the epi `symPowπ`, check on words, use step 3) and
   `β_m ≫ α_m = 𝟙` (check on basis elements): `symPowIsoPart`.
5. Multiplicativity of `α` (`symPowMul_symToPoly`: cancel the epi `π_m ⊗ π_n`,
   `tensorHom_symPowπ_symPowMul`, then `cat_wordHom`) and unit (`symPowπ_zero_symToPoly`);
   package with `GradedQCAlgebra.isoMk`.
This is exactly the proof of `SymmetricAlgebra.equivMvPolynomial` (Mathlib) carried out on the
free sheaf. Edge cases: `σ` empty — `Sym(0)` is `O_X` in degree `0` and `0` in positive degrees,
and `weightedMonomials 1 m` is a point for `m = 0` and empty for `m > 0`: consistent (the proof
above handles it uniformly). `X` empty: trivial. -/
theorem AlgebraicGeometry.Scheme.Modules.symGradedAlgebra_free_iso_weightedPolynomialQCAlgebra
    (X : AlgebraicGeometry.Scheme.{u}) (σ : Type u) [Fintype σ] :
    Nonempty (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
        (SheafOfModules.free (R := X.ringCatSheaf) σ) ≅
      AlgebraicGeometry.Scheme.weightedPolynomialQCAlgebra X (fun _ : σ => 1) (fun _ => Nat.one_pos)) :=
  ⟨eqToIso (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra_eq_ofQC
      (AlgebraicGeometry.Scheme.Modules.free (X := X) σ) inferInstance) ≪≫
    AlgebraicGeometry.Scheme.Modules.symGradedAlgebraOfQC_free_iso_weightedPolynomialQCAlgebra⟩

end
