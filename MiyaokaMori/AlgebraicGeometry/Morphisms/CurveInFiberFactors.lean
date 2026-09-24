import MiyaokaMori.Prelude

/-! # A curve in a fiber lies in the scheme-theoretic fiber

If a reduced scheme maps by a closed immersion `ι` into `Y` and `π ∘ ι` has image contained in a
closed point `{c}`, then `ι` factors through the scheme-theoretic fiber `π⁻¹(c)` by a closed
immersion `j`: `ι = j ≫ π.fiberι c` (Lemma 2.5 of the paper: a curve
contained in a fiber of `π_k` lies in the scheme-theoretic fiber).

Route: lift `ι` directly through the closed immersion `π.fiberι c : π.fiber c → Y` (a base change
of the closed immersion `Spec κ(c) → S`, `isClosed_singleton_iff_isClosedImmersion`), whose image is
`π⁻¹{c}` (`Scheme.Hom.range_fiberι`). The lift exists because `Γ` is reduced and `ι` is quasi-compact
(closed immersions are affine): the kernel of `ι` is a radical ideal sheaf, hence equals the
vanishing ideal of its support `closure (range ι) ⊆ range (π.fiberι c)`, so
`(π.fiberι c).ker ≤ ι.ker` and `IsClosedImmersion.lift` applies (Stacks 01R8 / Hartshorne II
Ex. 3.11(d)). Finally `j` is a closed immersion by `IsClosedImmersion.of_comp_isClosedImmersion`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- A quasi-compact morphism `g` from a reduced scheme whose image lies in the image of a closed
immersion `ι` factors through `ι` (Stacks 01R8, Hartshorne II Ex. 3.11(d)). Proof: `g.ker` is
radical (sections of `S` are reduced rings), so `g.ker = vanishingIdeal (closure (range g))`;
`ι.ker ≤ vanishingIdeal (range ι)` and `closure (range g) ⊆ range ι` give `ι.ker ≤ g.ker`, and
`IsClosedImmersion.lift` does the rest. (Same argument as
`exists_lift_isClosedImmersion_of_range_subset` in `FiberPolynomialExtensionDegree`, restated here
to keep this module's imports at `Prelude`.) -/
theorem AlgebraicGeometry.IsClosedImmersion.exists_lift_of_range_subset_of_isReduced
    {S Z T : AlgebraicGeometry.Scheme.{u}} (g : S ⟶ T) (ι : Z ⟶ T)
    [AlgebraicGeometry.IsClosedImmersion ι] [AlgebraicGeometry.IsReduced S]
    [AlgebraicGeometry.QuasiCompact g] (h : Set.range g.base ⊆ Set.range ι.base) :
    ∃ Φ : S ⟶ Z, Φ ≫ ι = g := by
  have hrad : g.ker.radical = g.ker := by
    ext U : 2
    rw [AlgebraicGeometry.Scheme.IdealSheafData.radical_ideal, AlgebraicGeometry.Scheme.Hom.ker_apply]
    apply Ideal.radical_eq_iff.mpr
    intro x hx
    rw [Ideal.mem_radical_iff] at hx
    obtain ⟨n, hn⟩ := hx
    rw [RingHom.mem_ker, map_pow] at hn
    exact RingHom.mem_ker.mpr (IsNilpotent.eq_zero ⟨n, hn⟩)
  have hsupp : g.ker.support ≤ ι.ker.support := by
    change (g.ker.support : Set T) ⊆ ι.ker.support
    rw [AlgebraicGeometry.Scheme.Hom.support_ker]
    refine (closure_mono h).trans ?_
    rw [ι.isClosedEmbedding.isClosed_range.closure_eq]
    exact ι.range_subset_ker_support
  have hle : ι.ker ≤ g.ker := by
    calc ι.ker ≤ ι.ker.radical := AlgebraicGeometry.Scheme.IdealSheafData.le_radical _
      _ = AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal ι.ker.support :=
          AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal_support.symm
      _ ≤ AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal g.ker.support :=
          AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal_antimono hsupp
      _ = g.ker.radical := AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal_support
      _ = g.ker := hrad
  exact ⟨AlgebraicGeometry.IsClosedImmersion.lift ι g hle,
    AlgebraicGeometry.IsClosedImmersion.lift_fac ι g hle⟩

theorem AlgebraicGeometry.exists_closedImmersion_to_fiber_of_range_subset
    {Γ Y S : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsReduced Γ]
    (ι : Γ ⟶ Y) [AlgebraicGeometry.IsClosedImmersion ι] (π : Y ⟶ S)
    (c : S) (hc : IsClosed ({c} : Set S))
    (hrange : Set.range (ι ≫ π).base ⊆ {c}) :
    ∃ j : Γ ⟶ π.fiber c, AlgebraicGeometry.IsClosedImmersion j ∧ j ≫ π.fiberι c = ι := by
  -- `π.fiberι c = pullback.fst π s_c` is the base change of the closed immersion
  -- `s_c = S.fromSpecResidueField c` (`c` closed); the same fact is
  -- `Scheme.Hom.isClosedImmersion_fiberι_of_isClosed` in `ResolvedSurfaceGeneralFiberDegree`,
  -- inlined here to keep this module at `Prelude` level and avoid a duplicate global name.
  have hsc : AlgebraicGeometry.IsClosedImmersion (S.fromSpecResidueField c) :=
    AlgebraicGeometry.isClosed_singleton_iff_isClosedImmersion.mp hc
  have hfib : AlgebraicGeometry.IsClosedImmersion (π.fiberι c) :=
    AlgebraicGeometry.IsClosedImmersion.isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback π (S.fromSpecResidueField c)).flip hsc
  have hrange' : Set.range ι.base ⊆ Set.range (π.fiberι c).base := by
    have hr : Set.range (π.fiberι c).base = π.base ⁻¹' {c} := π.range_fiberι c
    rw [hr]
    rintro _ ⟨x, rfl⟩
    have hx : (ι ≫ π).base x ∈ ({c} : Set S) := hrange ⟨x, rfl⟩
    simpa [AlgebraicGeometry.Scheme.Hom.comp_apply] using hx
  obtain ⟨j, hj⟩ :=
    AlgebraicGeometry.IsClosedImmersion.exists_lift_of_range_subset_of_isReduced ι (π.fiberι c)
      hrange'
  refine ⟨j, ?_, hj⟩
  have : AlgebraicGeometry.IsClosedImmersion (j ≫ π.fiberι c) := hj ▸ inferInstance
  exact AlgebraicGeometry.IsClosedImmersion.of_comp_isClosedImmersion j (π.fiberι c)

end
