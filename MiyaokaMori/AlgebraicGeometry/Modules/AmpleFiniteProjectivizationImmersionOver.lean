import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Morphisms.AffineOpenFiniteTypeGeneratorsOver
import MiyaokaMori.AlgebraicGeometry.Modules.Ample.AmpleFiniteAffineCover
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.AmpleUniformSectionExtension
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectivizationOverRing
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.Stacks01q1

/-! # An ample line bundle gives an immersion into projective space over a ring

Stacks 01VU over a commutative ring `R`: `f : X → Spec R` locally of finite type, `X` quasi-compact, `L`
ample on `X` ⇒ there are `n > 0` and finitely many sections `P_0, …, P_N ∈ Γ(X, L^{⊗n})` without common
zero such that `projectivizationMorphismOver f (L^{⊗n}) P hP : X ⟶ P^N_R` is an immersion.

Proof (Stacks 01VU; the five steps of the field version
`IsAmple.exists_projectivizationMorphism_isImmersion`, with `k` replaced by `R`):
1. finite affine cover `X = ⋃ X_{s_i}`, `s_i ∈ Γ(X, L^{⊗n})` (`IsAmple.exists_finite_affine_cover`, base-free);
2. finitely many `R`-algebra generators `t_{i,b}` of each `Γ(X_{s_i}, O)`
   (`exists_surjective_eval₂Hom_of_isAffineOpen_over`, `X → Spec R` locally of finite type);
3. extend `t_{i,b} · s_i^e` to global sections `T_{i,b} ∈ Γ(X, L^{⊗n'})` for a common `n'`
   (`Scheme.Modules.exists_uniform_tensorPow_extension`, base-free; `X` quasi-separated by
   `IsAmple.quasiSeparatedSpace`);
4. the tuple `P = (S_i) ∪ (T_{i,b}) ∪ {0}` indexed by `Fin (N + 1)` has no common zero;
5. on each covering chart `X_{s_i}` the chart evaluation `R[T] → Γ(X_{s_i}, O)` is surjective
   (`projectivizationChartEvalOver_surjective_of_generators`), so the chart map is a closed immersion
   (`isClosedImmersion_projectivizationChartMapOver`), and `φ` is an immersion
   (`isImmersion_projectivizationMorphismOver_of_charts`).

References: Stacks 01VU, 01VR (via 01PW).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem AlgebraicGeometry.IsAmple.exists_projectivizationMorphismOver_isImmersion
    {R : Type u} [CommRing R] {X : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of R)) [AlgebraicGeometry.LocallyOfFiniteType f]
    [CompactSpace X] (L : X.Modules) [L.IsLineBundle]
    (hL : AlgebraicGeometry.IsAmple L) :
    ∃ (n N : ℕ) (_ : 0 < n)
      (P : Fin (N + 1) →
        Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L n, ⊤))
      (hP : ∀ x : X, ∃ ℓ, ¬ IsZeroAt (P ℓ) x),
      AlgebraicGeometry.IsImmersion
        (projectivizationMorphismOver f
          (AlgebraicGeometry.Scheme.Modules.tensorPow L n) P hP) := by
  have hqs : QuasiSeparatedSpace X := AlgebraicGeometry.IsAmple.quasiSeparatedSpace L hL
  -- Step 1: finite affine cover by sections of one power `L^{⊗n}`
  obtain ⟨n, hn, ι, hι, s, hcov, haff⟩ :=
    AlgebraicGeometry.IsAmple.exists_finite_affine_cover L hL
  -- Step 2: finitely many algebra generators on each chart
  have hgen := fun i => AlgebraicGeometry.exists_surjective_eval₂Hom_of_isAffineOpen_over f
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
  apply isImmersion_projectivizationMorphismOver_of_charts f
    (AlgebraicGeometry.Scheme.Modules.tensorPow L n') P hP {a | ∃ i, e a = some (Sum.inl i)}
  · intro x
    obtain ⟨i, hx⟩ := hcov x
    exact ⟨e.symm (some (Sum.inl i)), ⟨i, by simp⟩, hmemS x i hx⟩
  · rintro a ⟨i, ha⟩
    have hPa : P a = S i := by simp [P, Q, ha]
    have hchart : projectivizationChart P a =
        (AlgebraicGeometry.Scheme.Modules.tensorPow L n).nonvanishingLocus (s i) := by
      show (AlgebraicGeometry.Scheme.Modules.tensorPow L n').nonvanishingLocus (P a) = _
      rw [hPa, hS]
    apply isClosedImmersion_projectivizationChartMapOver f P a
    · rw [hchart]; exact haff i
    · apply projectivizationChartEvalOver_surjective_of_generators f P a hchart (t i) (hsurj i)
      intro b
      refine ⟨e.symm (some (Sum.inr ⟨i, b⟩)), ?_⟩
      rw [hPT, hPa]
      exact hT i b

end
