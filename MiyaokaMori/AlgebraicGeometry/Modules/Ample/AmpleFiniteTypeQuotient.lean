import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.ModulesEpiOfOpenCover
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.Stacks01q1
import MiyaokaMori.AlgebraicGeometry.Modules.Ample.AmpleFiniteAffineCover
import MiyaokaMori.AlgebraicGeometry.Modules.Ample.AmpleFiniteTypeQuotientOnNonvanishingLocus

/-! # Finite type quasi-coherent sheaves are quotients of sums of `L^{⊗-n}` (Stacks 01Q3)

Stacks 01Q3 (1)⇒(8): if `L` is ample, every quasi-coherent sheaf `G` of finite type is a quotient
of a finite direct sum of copies of `L^{⊗−n}` for some `n > 0`.

Reference: Stacks 01Q3 (`properties-proposition-characterize-ample`), (1)⇒(5)⇒(7)⇒(8).

Route. Ampleness gives, for every point, a homogeneous section
`s_x ∈ Γ(X, L^{⊗m_x})` (`m_x > 0`) with `X_{s_x}` affine; by quasi-compactness finitely many of these
affine opens `X_{s_i}` (`i < t`) cover `X` (`IsAmple.exists_finite_nonvanishingLocus_cover`, a renumbering of
`IsAmple.exists_finite_affine_cover`). On each `X_{s_i}` the local lemma
`Scheme.Modules.exists_epi_pullback_nonvanishingLocus_biproduct_zpow_neg`
(Stacks 01Q3 (1)⇒(5)⇒(7) on one affine `X_s`) gives `n₀ i` such that for every `n ≥ n₀ i`
divisible by `m i` finitely many morphisms
`L^{⊗-n} ⟶ G` are jointly surjective on `X_{s_i}`. Take
`n := (∏ i, m i) · (∑ i, n₀ i + 1)`: it is positive, divisible by every `m i` and `≥ n₀ i`. Concatenate
the finitely many families (`finSigmaFinEquiv`) into one family `ψ : Fin (∑ i, r i) → (L^{⊗-n} ⟶ G)`;
then `p := biproduct.desc ψ` restricted to `X_{s_i}` is an epimorphism because the sub-biproduct
inclusion followed by `p` is `biproduct.desc (φ i)` (`epi_of_epi`), and `p` is an epimorphism by
`Scheme.Modules.epi_of_openCover` applied to the open cover `X = ⋃ X_{s_i}`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- An ample invertible sheaf on `X` gives finitely many homogeneous sections
`s i ∈ Γ(X, L^{⊗ m i})` (`m i > 0`, `i < t`) whose nonvanishing loci are affine and cover `X`.

Special case (all `m i` equal) of `IsAmple.exists_finite_affine_cover` (Stacks 01Q3 / 01PS), which
gives one exponent `n > 0` and a `Fintype`-indexed family; renumber it by `Fintype.equivFin`. Kept in
the per-section-exponent form that `exists_epi_biproduct_zpow_neg` below consumes. -/
theorem AlgebraicGeometry.IsAmple.exists_finite_nonvanishingLocus_cover
    {X : AlgebraicGeometry.Scheme.{u}} (L : X.Modules) [L.IsLineBundle]
    (hL : AlgebraicGeometry.IsAmple L) :
    ∃ (t : ℕ) (m : Fin t → ℕ) (s : ∀ i, Γ(AlgebraicGeometry.Scheme.Modules.tensorPow L (m i), ⊤)),
      (∀ i, 0 < m i) ∧
      (∀ i, AlgebraicGeometry.IsAffineOpen
        ((AlgebraicGeometry.Scheme.Modules.tensorPow L (m i)).nonvanishingLocus (s i))) ∧
      ⨆ i, (AlgebraicGeometry.Scheme.Modules.tensorPow L (m i)).nonvanishingLocus (s i) = ⊤ := by
  classical
  obtain ⟨n, hn, ι, hι, s, hcov, haff⟩ := hL.exists_finite_affine_cover
  haveI : Fintype ι := hι
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  refine ⟨Fintype.card ι, fun _ => n, fun i => s (e.symm i), fun _ => hn, fun i => haff _, ?_⟩
  refine eq_top_iff.mpr fun y _ => TopologicalSpace.Opens.mem_iSup.mpr ?_
  obtain ⟨i, hi⟩ := hcov y
  exact ⟨e i, by simpa only [Equiv.symm_apply_apply] using hi⟩

/- Stacks 01Q3 (1)⇒(8): for `G` quasi-coherent of finite type there are `n > 0`, `r` and an epimorphism
   `⊕_{j<r} L^{⊗−n} ↠ G` (the negative power is the `ℤ`-power `L ^ (−n)` on `X.Modules`). -/

theorem AlgebraicGeometry.IsAmple.exists_epi_biproduct_zpow_neg {X : AlgebraicGeometry.Scheme.{u}}
    (L : X.Modules) [L.IsLineBundle] (hL : AlgebraicGeometry.IsAmple L)
    (G : X.Modules) [G.IsQuasicoherent] [G.IsFiniteType] :
    ∃ (n : ℕ) (_ : 0 < n) (r : ℕ)
      (p : CategoryTheory.Limits.biproduct (fun _ : Fin r => L ^ (-(n : ℤ))) ⟶ G),
      CategoryTheory.Epi p := by
  classical
  have hc : CompactSpace X := hL.1
  have hqs : QuasiSeparatedSpace X := AlgebraicGeometry.IsAmple.quasiSeparatedSpace L hL
  obtain ⟨t, m, s, hm, haff, hcov⟩ := hL.exists_finite_nonvanishingLocus_cover
  let U : Fin t → X.Opens := fun i =>
    (AlgebraicGeometry.Scheme.Modules.tensorPow L (m i)).nonvanishingLocus (s i)
  choose n₀ hn₀ using fun i =>
    AlgebraicGeometry.Scheme.Modules.exists_epi_pullback_nonvanishingLocus_biproduct_zpow_neg
      L (hm i) (s i) (haff i) G
  -- the common exponent
  set P : ℕ := ∏ i, m i with hP
  set n : ℕ := P * (∑ i, n₀ i + 1) with hn
  have hPpos : 0 < P := Finset.prod_pos (fun i _ => hm i)
  have hnpos : 0 < n := Nat.mul_pos hPpos (Nat.succ_pos _)
  have hle : ∀ i, n₀ i ≤ n := fun i => by
    calc n₀ i ≤ ∑ j, n₀ j := Finset.single_le_sum (fun j _ => Nat.zero_le (n₀ j)) (Finset.mem_univ i)
      _ ≤ ∑ j, n₀ j + 1 := Nat.le_succ _
      _ = 1 * (∑ j, n₀ j + 1) := (one_mul _).symm
      _ ≤ P * (∑ j, n₀ j + 1) := Nat.mul_le_mul_right _ hPpos
  have hdvd : ∀ i, m i ∣ n := fun i =>
    (Finset.dvd_prod_of_mem m (Finset.mem_univ i)).mul_right _
  choose r φ hφ using fun i => hn₀ i n (hle i) (hdvd i)
  -- concatenate the families
  let e : ((i : Fin t) × Fin (r i)) ≃ Fin (∑ i, r i) := finSigmaFinEquiv
  let ψ : Fin (∑ i, r i) → (L ^ (-(n : ℤ)) ⟶ G) := fun j => φ (e.symm j).1 (e.symm j).2
  refine ⟨n, hnpos, ∑ i, r i, CategoryTheory.Limits.biproduct.desc ψ, ?_⟩
  let 𝒰 : X.OpenCover := X.openCoverOfIsOpenCover U (TopologicalSpace.IsOpenCover.mk hcov)
  refine AlgebraicGeometry.Scheme.Modules.epi_of_openCover _ 𝒰 fun i => ?_
  let incl : (⨁ fun _ : Fin (r i) => L ^ (-(n : ℤ))) ⟶ (⨁ fun _ : Fin (∑ i, r i) => L ^ (-(n : ℤ))) :=
    CategoryTheory.Limits.biproduct.desc fun j =>
      CategoryTheory.Limits.biproduct.ι (fun _ : Fin (∑ i, r i) => L ^ (-(n : ℤ))) (e ⟨i, j⟩)
  have hcomp : incl ≫ CategoryTheory.Limits.biproduct.desc ψ =
      CategoryTheory.Limits.biproduct.desc (φ i) := by
    refine CategoryTheory.Limits.biproduct.hom_ext' _ _ fun j => ?_
    have he : e.symm (e ⟨i, j⟩) = ⟨i, j⟩ := e.symm_apply_apply _
    simp only [incl, ψ, CategoryTheory.Limits.biproduct.ι_desc_assoc,
      CategoryTheory.Limits.biproduct.ι_desc]
    rw [he]
  have h1 : CategoryTheory.Epi ((AlgebraicGeometry.Scheme.Modules.pullback (𝒰.f i)).map
      (incl ≫ CategoryTheory.Limits.biproduct.desc ψ)) := by
    rw [hcomp]
    exact hφ i
  rw [Functor.map_comp] at h1
  exact CategoryTheory.epi_of_epi ((AlgebraicGeometry.Scheme.Modules.pullback (𝒰.f i)).map incl)
    ((AlgebraicGeometry.Scheme.Modules.pullback (𝒰.f i)).map (CategoryTheory.Limits.biproduct.desc ψ))

end
