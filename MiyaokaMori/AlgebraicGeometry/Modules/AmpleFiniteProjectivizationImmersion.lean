import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Morphisms.AffineOpenFiniteTypeGenerators
import MiyaokaMori.AlgebraicGeometry.Modules.Ample.AmpleFiniteAffineCover
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.AmpleUniformSectionExtension
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectivizationChartImmersion
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.Stacks01q1

/-! # An ample line bundle gives an immersion into projective space

Statement: for an ample line bundle `L` on a quasi-compact scheme of finite type over a field `k`,
some positive tensor power of `L` has finitely many global sections with no common zero such
that the associated `projectivizationMorphism` is an immersion into a finite-dimensional
projective space.

Proof (following the proof of Stacks 01VU), assembled from five named lemmas:
1. Ampleness gives a cover by affine non-vanishing loci; quasi-compactness gives a finite subcover,
   and the sections are raised to a common positive power (`IsAmple.exists_finite_affine_cover`).
2. Each affine piece is of finite type over `k`, so its coordinate ring is finitely generated;
   choose finitely many algebra generators on each piece
   (`exists_surjective_eval₂Hom_of_isAffineOpen`).
3. By Stacks 01PW, these local generators, multiplied by a sufficiently high power of the covering
   sections, extend to global sections; finiteness allows a common exponent
   (`Scheme.Modules.exists_uniform_tensorPow_extension`; `X` is quasi-separated by
   `IsAmple.quasiSeparatedSpace`).
4. The covering sections and the extended sections form a finite family with no common zero
   (index set `Option (ι ⊕ Σ i, Fin (m i))`, where the extra `none` slot carries the section `0`,
   so that the index set has the form `Fin (N + 1)`); hence `projectivizationMorphism` gives a
   `k`-morphism to `ProjectiveSpace N k`.
5. On each covering piece `V_ℓ`, the coordinate ratios of the target standard affine chart pull
   back to the generators of step 2, so the chart ring map `k[x] → Γ(V_ℓ, O)` is surjective
   (`projectivizationChartEval_surjective_of_generators`); `Spec` of a surjection is a closed
   immersion, so the chart morphism `g_ℓ : V_ℓ → D_+(x_ℓ)` is a closed immersion
   (`isClosedImmersion_projectivizationChartMap`); `φ⁻¹(D_+(x_ℓ)) = V_ℓ`
   (`projectivizationMorphism_preimage_basicOpen`) and `φ` lands in `⋃_ℓ D_+(x_ℓ)` over the
   covering indices, so `IsZariskiLocalAtTarget.of_range_subset_iSup` shows that `φ` is an
   immersion (`isImmersion_projectivizationMorphism_of_charts`).

References: Stacks 01VU, 01VR (with the section-extension proof of 01PW).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem AlgebraicGeometry.IsAmple.exists_projectivizationMorphism_isImmersion
    (k : Type u) [Field k]
    (X : AlgebraicGeometry.Scheme.{u})
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.LocallyOfFiniteType
      (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))]
    [CompactSpace X] (L : X.Modules) [L.IsLineBundle]
    (hL : AlgebraicGeometry.IsAmple L) :
    ∃ (n N : ℕ) (hn : 0 < n)
      (P : Fin (N + 1) →
        Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L n, ⊤))
      (hP : ∀ x : X, ∃ ℓ, ¬ IsZeroAt (P ℓ) x),
      AlgebraicGeometry.IsImmersion
        (projectivizationMorphism (k := k)
          (AlgebraicGeometry.Scheme.Modules.tensorPow L n) P hP) := by
  have hqs : QuasiSeparatedSpace X := AlgebraicGeometry.IsAmple.quasiSeparatedSpace L hL
  -- Step 1: finite affine cover by sections of one power `L^{⊗n}`
  obtain ⟨n, hn, ι, hι, s, hcov, haff⟩ :=
    AlgebraicGeometry.IsAmple.exists_finite_affine_cover L hL
  -- Step 2: finitely many algebra generators on each chart
  have hgen := fun i => AlgebraicGeometry.exists_surjective_eval₂Hom_of_isAffineOpen k X
    ((AlgebraicGeometry.Scheme.Modules.tensorPow L n).nonvanishingLocus (s i)) (haff i)
  choose m t hsurj using hgen
  -- Step 3: extend the generators (times a common power of the covering sections)
  obtain ⟨n', hn', S, T, hS, hT⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_uniform_tensorPow_extension L hn s m t
  -- Step 4: the tuple, indexed by `Fin (N + 1)` via `Option (ι ⊕ Σ i, Fin (m i))`
  let J := ι ⊕ Σ i : ι, Fin (m i)
  let e : Fin (Fintype.card J + 1) ≃ Option J :=
    (finSuccEquiv (Fintype.card J)).trans (Equiv.optionCongr (Fintype.equivFin J).symm)
  let Q : J → Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L n', ⊤) :=
    Sum.elim S (fun p => T p.1 p.2)
  let P : Fin (Fintype.card J + 1) → Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L n', ⊤) :=
    fun a => (e a).elim 0 Q
  have hPS : ∀ i, P (e.symm (some (Sum.inl i))) = S i := by
    intro i
    simp [P, Q]
  have hPT : ∀ i (b : Fin (m i)), P (e.symm (some (Sum.inr ⟨i, b⟩))) = T i b := by
    intro i b
    simp [P, Q]
  have hmemS : ∀ (x : X) (i : ι),
      x ∈ (AlgebraicGeometry.Scheme.Modules.tensorPow L n).nonvanishingLocus (s i) →
        ¬ IsZeroAt (P (e.symm (some (Sum.inl i)))) x := by
    intro x i hx
    rw [hPS]
    have hx' : x ∈ (AlgebraicGeometry.Scheme.Modules.tensorPow L n').nonvanishingLocus (S i) := by
      rw [hS]; exact hx
    exact hx'
  have hP : ∀ x : X, ∃ a, ¬ IsZeroAt (P a) x := by
    intro x
    obtain ⟨i, hx⟩ := hcov x
    exact ⟨_, hmemS x i hx⟩
  refine ⟨n', Fintype.card J, hn', P, hP, ?_⟩
  -- Step 5: immersion via the covering charts
  apply isImmersion_projectivizationMorphism_of_charts (AlgebraicGeometry.Scheme.Modules.tensorPow L n')
    P hP {a | ∃ i, e a = some (Sum.inl i)}
  · intro x
    obtain ⟨i, hx⟩ := hcov x
    exact ⟨e.symm (some (Sum.inl i)), ⟨i, by simp⟩, hmemS x i hx⟩
  · rintro a ⟨i, ha⟩
    have hPa : P a = S i := by simp [P, Q, ha]
    have hchart : projectivizationChart P a =
        (AlgebraicGeometry.Scheme.Modules.tensorPow L n).nonvanishingLocus (s i) := by
      show (AlgebraicGeometry.Scheme.Modules.tensorPow L n').nonvanishingLocus (P a) = _
      rw [hPa, hS]
    apply isClosedImmersion_projectivizationChartMap P a
    · rw [hchart]; exact haff i
    · apply projectivizationChartEval_surjective_of_generators P a hchart (t i) (hsurj i)
      intro b
      refine ⟨e.symm (some (Sum.inr ⟨i, b⟩)), ?_⟩
      rw [hPT, hPa]
      exact hT i b

end
