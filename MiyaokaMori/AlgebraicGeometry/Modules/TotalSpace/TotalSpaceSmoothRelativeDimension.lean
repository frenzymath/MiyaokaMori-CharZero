import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.LocalTrivializationPullback
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.RankAtStalkLocalIso
import MiyaokaMori.AlgebraicGeometry.Varieties.Smooth.EtaleChartAffineSpaceSmooth
import MiyaokaMori.AlgebraicGeometry.Modules.FiniteTypeRestrictFreeIndexFinite
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotalSpaceSectionsRingEquivMvPolynomial
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotalSpaceVectorBundle

/-! # The total space of a vector bundle is smooth over the base

The total space of a rank-`r` vector bundle is smooth of relative dimension `r` over the base (`Tot(L)^× → base` has
relative dimension 1; in the paper, `Tot(L) → C̃` is smooth of relative dimension 1).

* Route (Stacks 01M2 area / Hartshorne II Ex. 5.18, "Tot(V) is locally `A^r_U`"): `SmoothOfRelativeDimension r`
  is Zariski-local on the target (`HasRingHomProperty` ⇒ `IsZariskiLocalAtTarget`), so it suffices to
  check it over the nonempty affine opens `U` on which `V` is trivial (they cover `X`:
  `exists_pullback_iso_free_of_isLocallyFree` + `exists_isAffineOpen_mem_and_subset` + `pullback_iso_free_of_le`).
  Over such `U`, `Tot(V) = Spec_X A` with `A = Sym(V^∨)` restricts to `Spec A(U) → U`
  (`AffineAlgebra.chart_isPullback`; the two pullback squares of the cospan `(U.ι, p)` are identified by
  `IsPullback.isoIsPullback`), i.e. to `Spec.map (unit) ≫ (U ≅ Spec Γ(U)).inv`. By `RespectsIso`,
  `HasRingHomProperty.Spec_iff` and `RingHom.locally_of` this is the ring statement
  `IsStandardSmoothOfRelativeDimension r (Γ(X, U) → A(U))`.
* Ring statement (`totalSpace_sectionsUnit_isStandardSmoothOfRelativeDimension`): `A(U) ≅ Γ(U)[x_I]`
  over `Γ(U)` (`totalSpace_exists_sectionsRing_ringEquiv_mvPolynomial`), `|I| = rankAtStalk V x = r` at a point `x ∈ U`
  (`rankAtStalk_of_restrict_iso_free`, `finite_index_of_restrict_iso_free`), and the polynomial algebra in `r`
  variables is standard smooth of relative dimension `r`
  (`Algebra.IsStandardSmoothOfRelativeDimension.mvPolynomial`, `EtaleChartAffineSpaceSmooth`).
* No scheme-level isomorphism `Tot(V)|_U ≅ 𝔸^r_U` is needed: the `A^r_U`-chart is taken directly as
  `Spec Γ(U)[x_1, …, x_r]`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- **Ring side**: on a nonempty affine open `U` trivialising `V` (with `x ∈ U`), the structure map
`Γ(X, U) → Γ(U, Sym(V^∨))` is standard smooth of relative dimension `r = rankAtStalk V x`.
Proof: `totalSpace_exists_sectionsRing_ringEquiv_mvPolynomial` gives `φ : A(U) ≃+* Γ(U)[x_I]` with
`φ ∘ sectionsUnit = C`, so `sectionsUnit = φ⁻¹ ∘ algebraMap`; `I` is finite of cardinality
`rankAtStalk V x = r` (`finite_index_of_restrict_iso_free`, `rankAtStalk_of_restrict_iso_free`); the polynomial
algebra is standard smooth of relative dimension `Nat.card I` (`Algebra.IsStandardSmoothOfRelativeDimension.mvPolynomial`);
transport along `φ⁻¹` by `RingHom.isStandardSmoothOfRelativeDimension_respectsIso`. -/
theorem AlgebraicGeometry.Scheme.totalSpace_sectionsUnit_isStandardSmoothOfRelativeDimension
    {X : AlgebraicGeometry.Scheme.{u}} (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType] (r : ℕ)
    (hr : ∀ x : X, AlgebraicGeometry.Scheme.Modules.rankAtStalk V x = r)
    (U : X.affineOpens) (I : Type u)
    (e : (AlgebraicGeometry.Scheme.Modules.pullback U.1.ι).obj V ≅
      SheafOfModules.free (R := U.1.toScheme.ringCatSheaf) I)
    (x : X) (hx : x ∈ U.1) :
    RingHom.IsStandardSmoothOfRelativeDimension r
      ((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
        (AlgebraicGeometry.Scheme.Modules.dual V)).total.sectionsUnit U.1) := by
  obtain ⟨φ, hφ⟩ :=
    AlgebraicGeometry.Scheme.totalSpace_exists_sectionsRing_ringEquiv_mvPolynomial V U I e
  have hfin : Finite I :=
    AlgebraicGeometry.Scheme.Modules.finite_index_of_restrict_iso_free V U.1 I e x hx
  let _ := Fintype.ofFinite I
  have hcard : Nat.card I = r := by
    rw [Nat.card_eq_fintype_card,
      ← AlgebraicGeometry.Scheme.Modules.rankAtStalk_of_restrict_iso_free V U.1 I e x hx, hr x]
  have hpoly : RingHom.IsStandardSmoothOfRelativeDimension r
      (algebraMap Γ(X, U.1) (MvPolynomial I Γ(X, U.1))) := by
    rw [RingHom.isStandardSmoothOfRelativeDimension_algebraMap, ← hcard]
    exact Algebra.IsStandardSmoothOfRelativeDimension.mvPolynomial Γ(X, U.1) I
  have heq : (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
        (AlgebraicGeometry.Scheme.Modules.dual V)).total.sectionsUnit U.1 =
      (φ.symm.toRingHom).comp (algebraMap Γ(X, U.1) (MvPolynomial I Γ(X, U.1))) := by
    ext s
    rw [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.algebraMap_eq,
      ← hφ s, RingEquiv.symm_apply_apply]
  rw [heq]
  exact RingHom.isStandardSmoothOfRelativeDimension_respectsIso.left _ φ.symm hpoly

set_option backward.isDefEq.respectTransparency false in
/-- **The total space of a rank-`r` vector bundle is smooth of relative dimension `r` over the base.**
Locality on the target + the chart `Spec A(U) → U` of the relative Spec +
`totalSpace_sectionsUnit_isStandardSmoothOfRelativeDimension`. -/
theorem AlgebraicGeometry.Scheme.totalSpace_smoothOfRelativeDimension
    {X : AlgebraicGeometry.Scheme.{u}} (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType] (r : ℕ)
    (hr : ∀ x : X, AlgebraicGeometry.Scheme.Modules.rankAtStalk V x = r) :
    AlgebraicGeometry.SmoothOfRelativeDimension r (AlgebraicGeometry.Scheme.totalSpace V).hom := by
  classical
  let A : X.QCAlgebra := (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
    (AlgebraicGeometry.Scheme.Modules.dual V)).total
  let p : (AlgebraicGeometry.Scheme.totalSpace V).left ⟶ X := (AlgebraicGeometry.Scheme.totalSpace V).hom
  -- index type: the nonempty affine opens on which `V` is trivial
  let ι : Type u := { U : X.affineOpens // (U.1 : Set X).Nonempty ∧ ∃ I : Type u,
    Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback U.1.ι).obj V ≅
      SheafOfModules.free (R := U.1.toScheme.ringCatSheaf) I) }
  have hcov : ⨆ U : ι, U.1.1 = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [TopologicalSpace.Opens.mem_iSup]
    obtain ⟨W, I, hxW, ⟨e⟩⟩ :=
      AlgebraicGeometry.Scheme.Modules.exists_pullback_iso_free_of_isLocallyFree V x
    obtain ⟨U, hUaff, hxU, hUW⟩ :=
      AlgebraicGeometry.exists_isAffineOpen_mem_and_subset (x := x) (U := W) hxW
    exact ⟨⟨⟨U, hUaff⟩, ⟨x, hxU⟩, I,
      AlgebraicGeometry.Scheme.Modules.pullback_iso_free_of_le V hUW I e⟩, hxU⟩
  -- locality on the target
  rw [AlgebraicGeometry.IsZariskiLocalAtTarget.iff_of_iSup_eq_top
    (P := @AlgebraicGeometry.SmoothOfRelativeDimension.{u} r) (fun U : ι => U.1.1) hcov]
  intro U
  obtain ⟨⟨x, hx⟩, I, ⟨e⟩⟩ := U.2
  let W : X.AffineZariskiSite := ⟨U.1.1, U.1.2⟩
  -- `p ∣_ U` and the chart `Spec A(U) → U` are two pullbacks of the cospan `(U.ι, p)`
  have h1 : IsPullback (p ∣_ U.1.1) (p ⁻¹ᵁ U.1.1).ι U.1.1.ι p :=
    AlgebraicGeometry.isPullback_morphismRestrict p U.1.1
  have h2 : IsPullback (A.toAffineAlgebra.chartToOpen W) (A.toAffineAlgebra.chart W) U.1.1.ι p :=
    A.toAffineAlgebra.chart_isPullback W
  rw [← MorphismProperty.cancel_left_of_respectsIso
    (P := @AlgebraicGeometry.SmoothOfRelativeDimension.{u} r) (h2.isoIsPullback _ _ h1).hom,
    h2.isoIsPullback_hom_fst _ _ h1]
  -- the chart is `Spec.map (unit) ≫ (U ≅ Spec Γ(U)).inv`
  show AlgebraicGeometry.SmoothOfRelativeDimension r
    (AlgebraicGeometry.Spec.map (A.toAffineAlgebra.unit.app (op W)) ≫ W.2.isoSpec.inv)
  rw [MorphismProperty.cancel_right_of_respectsIso
    (P := @AlgebraicGeometry.SmoothOfRelativeDimension.{u} r),
    AlgebraicGeometry.HasRingHomProperty.Spec_iff
      (P := @AlgebraicGeometry.SmoothOfRelativeDimension.{u} r)]
  refine RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ ?_
  exact AlgebraicGeometry.Scheme.totalSpace_sectionsUnit_isStandardSmoothOfRelativeDimension
    V r hr U.1 I e x hx

end
