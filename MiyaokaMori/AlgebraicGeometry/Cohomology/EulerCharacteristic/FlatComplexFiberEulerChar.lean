import MiyaokaMori.Prelude
import MiyaokaMori.Algebra.CochainComplexToTopComplex
import MiyaokaMori.AlgebraicGeometry.Cohomology.EulerCharacteristic.TopComplexFiberEulerChar

/-! # Euler characteristic of the fibres of a flat complex

Let `A` be a Noetherian ring and `K^•` a cochain complex of `A`-modules with flat terms, nonzero only in
degrees `[0, n)`, and finite `A`-modules `H^i(K^•)`. Then for every prime `p`, `H^i(K^• ⊗_A κ(p))` is a
finite-dimensional `κ(p)`-vector space, and `p ↦ Σ_{0 ≤ i < n} (−1)^i dim_{κ(p)} H^i(K^• ⊗_A κ(p))` is
locally constant on `Spec A`.

Proof sketch:
1. Rewrite `K` as an elementary complex `T` numbered from the top (`T.X j = K^{n−1−j}`); flatness and
   boundedness are inherited, and finiteness of homology, finite dimensionality and dimensions after base
   change agree with the categorical homology (`i = n−1−j`).
2. `TopComplexFiberEulerChar.lean`: the homology of `T ⊗ κ(p)` is finite-dimensional and
   `p ↦ Σ_{j ≤ n} (−1)^j h_j(T ⊗ κ(p))` is locally constant. Mathematically: induction on the length;
   `H_0` finite ⇒ choose a finite free `F` with `(d_0, φ) : X_1 ⊕ F → X_0` surjective, the kernel `Z` is flat,
   and the new complex `Z ← X_2 ← …` is one term shorter; flatness of `X_0` makes
   `Z ⊗ B → (X_1 ⊕ F) ⊗ B` universally injective, and a four-term exact sequence gives
   `χ(T ⊗ κ) = r − χ(T' ⊗ κ)`; for length `1`, `X_0` finite flat ⇒ projective, and `rankAtStalk` is locally
   constant.
3. Outside `[−1, n−1]`, `K^i = 0`, still a zero object after base change, so the homology is zero, hence
   finite-dimensional.
4. Back to cohomological numbering: the term `j = n` (`H^{−1}`) vanishes, and `Finset.sum_range_reflect`
   gives `Σ_{i<n} (−1)^i h^i = (−1)^{n+1} Σ_{j ≤ n} (−1)^j h_j`.

Source: Hartshorne III.12.2–12.3; Mumford, *Abelian Varieties*, §5, Lemmas 1–2; Stacks 07VK, 0BDJ (the
algebraic core of 0B9T).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits

noncomputable section

theorem CochainComplex.fiberEulerChar_isLocallyConstant {A : CommRingCat.{u}} [IsNoetherianRing A]
    (K : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℕ)
    (hflat : ∀ i, Module.Flat A (K.X i))
    (hbdd : ∀ i : ℤ, (i < 0 ∨ (n : ℤ) ≤ i) → IsZero (K.X i))
    (hfin : ∀ i, Module.Finite A (K.homology i)) :
    (∀ (p : PrimeSpectrum A) (i : ℤ), Module.Finite p.asIdeal.ResidueField
      ((((ModuleCat.extendScalars (CommRingCat.ofHom
        (algebraMap A p.asIdeal.ResidueField)).hom).mapHomologicalComplex _).obj K).homology i)) ∧
    IsLocallyConstant (fun p : PrimeSpectrum A =>
      ∑ i ∈ Finset.range n, (-1 : ℤ) ^ i *
        (Module.finrank p.asIdeal.ResidueField
          ((((ModuleCat.extendScalars (CommRingCat.ofHom
            (algebraMap A p.asIdeal.ResidueField)).hom).mapHomologicalComplex _).obj K).homology
              (i : ℤ)) : ℤ)) := by
  have hn : IsZero (K.X n) := hbdd n (Or.inr le_rfl)
  obtain ⟨h1, h2⟩ := TopCx.fiberEulerChar_isLocallyConstant n (TopCx.ofCochainComplex K n)
    (TopCx.ofCochainComplex_flat K n hflat) (TopCx.ofCochainComplex_subsingleton K n hbdd)
    (fun j => (TopCx.ofCochainComplex_fin0 K n hn j).mpr (hfin _))
  -- homology vanishes at zero objects
  have hzero : ∀ (p : PrimeSpectrum A) (i : ℤ), (i < 0 ∨ (n : ℤ) ≤ i) →
      Subsingleton ((((ModuleCat.extendScalars (CommRingCat.ofHom
        (algebraMap A p.asIdeal.ResidueField)).hom).mapHomologicalComplex _).obj K).homology i) := by
    intro p i hi
    have hz : IsZero ((((ModuleCat.extendScalars (CommRingCat.ofHom
        (algebraMap A p.asIdeal.ResidueField)).hom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K).X i) :=
      (ModuleCat.extendScalars _).map_isZero (hbdd i hi)
    exact ModuleCat.isZero_iff_subsingleton.mp
      ((HomologicalComplex.exactAt_iff_isZero_homology _ _).mp
        (HomologicalComplex.ExactAt.of_isZero hz))
  refine ⟨fun p i => ?_, ?_⟩
  · by_cases hi : i < -1 ∨ (n : ℤ) ≤ i
    · have := hzero p i (hi.imp (fun h => by omega) id)
      infer_instance
    · obtain ⟨j, rfl⟩ : ∃ j : ℕ, i = (n : ℤ) - 1 - (j : ℤ) :=
        ⟨((n : ℤ) - 1 - i).toNat, by omega⟩
      exact ((TopCx.ofCochainComplex_hfin_hdim K n hn p j).1).mp (h1 p j)
  · have hlc := h2.comp (fun z : ℤ => (-1 : ℤ) ^ (n + 1) * z)
    refine cast (congrArg IsLocallyConstant (funext fun p => ?_)) hlc
    simp only [Function.comp_apply]
    -- write `c i := dim H^i`
    set c : ℤ → ℤ := fun i => (Module.finrank p.asIdeal.ResidueField
      ((((ModuleCat.extendScalars (CommRingCat.ofHom
        (algebraMap A p.asIdeal.ResidueField)).hom).mapHomologicalComplex _).obj K).homology i) : ℤ)
      with hc
    have hdim : ∀ j : ℕ, ((TopCx.ofCochainComplex K n).hdim p.asIdeal.ResidueField j : ℤ)
        = c ((n : ℤ) - 1 - (j : ℤ)) := fun j => by
      rw [(TopCx.ofCochainComplex_hfin_hdim K n hn p j).2]
    have hneg : c ((n : ℤ) - 1 - (n : ℤ)) = 0 := by
      have := hzero p ((n : ℤ) - 1 - (n : ℤ)) (Or.inl (by omega))
      simp only [hc]
      exact_mod_cast Module.finrank_zero_of_subsingleton
    rw [Finset.sum_range_succ, hdim n, hneg, mul_zero, add_zero]
    rw [← Finset.sum_range_reflect, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hin : i < n := Finset.mem_range.mp hi
    rw [hdim]
    have e1 : ((n : ℤ) - 1 - ((n - 1 - i : ℕ) : ℤ)) = (i : ℤ) := by omega
    have e2 : n + 1 + (n - 1 - i) = 2 * (n - i) + i := by omega
    rw [e1, ← mul_assoc, ← pow_add, e2, pow_add, pow_mul]
    simp only [even_two, Even.neg_pow, one_pow, one_mul]
    rfl

end
