import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.IdealSheafComapIdealEqMap
import MiyaokaMori.AlgebraicGeometry.Blowup.Stacks0804
import MiyaokaMori.AlgebraicGeometry.Blowup.Stacks0agsChartAlgebra
import MiyaokaMori.AlgebraicGeometry.Blowup.Stacks0agtLeavesSectionsSurjectiveProjCharts

/-! # `Γ(X, O_X) ↠ Γ(X, O_X/I·O_X)` on `Bl_𝔪 Spec A`

Stacks 0AGS(3) ("`H¹(X, ℱ) = 0` for globally generated `ℱ`", applied to `ℱ = I·O_X`) in the form
Stacks 0AGT actually uses: the restriction map from `Γ(X, O_X)` to the compatible families
`(s_U ∈ Γ(X, U)/(I·O_X)(U))_U` (`IdealSheafData.quotFamilies`, i.e. `Γ(X, O_X/I·O_X)`) is
surjective. Together with 0AGS(4) `Γ(X, O_X) = A` (`blowup_regularLocalRing_dimTwo_sections`) this
gives `A/I ↠ Γ(X, O_X/I·O_X)`, the first inequality of the proof of 0AGT.

Route (replacing the Serre-vanishing argument of Stacks 0AGS): a two-chart Čech computation, no
sheaf cohomology. The identification of `U_x ⊓ U_y` and of the three sections rings with their
restriction maps is done on `Proj (⊕ₙ 𝔪ⁿ)` itself through the open immersion
`blowupChartι : Proj (⊕ₙ 𝔪ⁿ) ⟶ X` of Stacks 0804 (onto `X`, since the base is affine), Mathlib's
`awayToSection` / `awayMap_awayToSection` and `appIso_inv_naturality`; the general two-chart Čech
criterion for a scheme covered by `Proj 𝒜` with `D₊(f) ∪ D₊(g) = Proj 𝒜` is
`toQuotFamilies_surjective_of_proj_two_charts` (`Stacks0agtLeavesSectionsSurjectiveProjCharts.lean`).
The chart is `(Rees 𝔪)_{(xX)} = A[yX/xX]` directly (`exists_eval₂_isLocalizationElem_eq`), and the
structure-morphism compatibility of the charts is not needed, because
`I·O_X(V) = (I·Γ(X, O_X))·Γ(V)` (`comap_ideal_eq_map_appLE` with `U = ⊤`) only involves restriction
maps of `X`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace HomogeneousLocalization
open scoped AlgebraicGeometry
open scoped AlgebraicGeometry.Scheme.IdealSheafData.QuotFamilies0agt

noncomputable section

/-- **Laurent splitting.** In a field `K`, for `u : K`, the `A`-subalgebra `A[u, u⁻¹]` is, as an
`A`-module, the sum `A[u] + A[u⁻¹]`: every element is a Laurent polynomial `Σ aₖ uᵏ` (`k ∈ ℤ`), and
the terms with `k ≥ 0` (resp. `k < 0`) lie in `A[u]` (resp. `A[u⁻¹]`).
Applied to `u = y/x` in `Frac(A)`: `A[x/y, y/x] = A[y/x] + A[x/y]`. (Not used by the proof below,
which works with the ring-level form `exists_eq_add_of_localization_of_eval₂_surjective`.) -/
theorem Subalgebra.toSubmodule_adjoin_pair_inv {A K : Type*} [CommRing A] [Field K] [Algebra A K]
    (u : K) :
    Subalgebra.toSubmodule (Algebra.adjoin A {u, u⁻¹}) =
      Subalgebra.toSubmodule (Algebra.adjoin A {u}) ⊔
        Subalgebra.toSubmodule (Algebra.adjoin A {u⁻¹}) := by
  apply le_antisymm
  · rw [Algebra.adjoin_eq_span, Submodule.span_le]
    intro z hz
    rw [SetLike.mem_coe] at hz
    have hpow : ∀ k : ℤ, u ^ k ∈ Subalgebra.toSubmodule (Algebra.adjoin A {u}) ⊔
        Subalgebra.toSubmodule (Algebra.adjoin A {u⁻¹}) := by
      intro k
      obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg k
      · rw [zpow_natCast]
        exact Submodule.mem_sup_left ((Subalgebra.mem_toSubmodule _).2
          (Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_singleton u)) n))
      · rw [zpow_neg, zpow_natCast, ← inv_pow]
        exact Submodule.mem_sup_right ((Subalgebra.mem_toSubmodule _).2
          (Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_singleton u⁻¹)) n))
    rcases eq_or_ne u 0 with hu | hu
    · -- `{u, u⁻¹} = {u}`: the closure consists of the natural powers of `u`
      have : z ∈ Submonoid.closure ({u} : Set K) := by
        rwa [hu, inv_zero, Set.pair_eq_singleton, ← hu] at hz
      obtain ⟨n, rfl⟩ := Submonoid.mem_closure_singleton.1 this
      have := hpow n
      rwa [zpow_natCast] at this
    · -- the closure lies in the submonoid of integer powers of `u`
      let S : Submonoid K :=
        { carrier := Set.range fun k : ℤ => u ^ k
          one_mem' := ⟨0, zpow_zero u⟩
          mul_mem' := by
            rintro _ _ ⟨k, rfl⟩ ⟨l, rfl⟩
            exact ⟨k + l, zpow_add₀ hu k l⟩ }
      have hle : Submonoid.closure ({u, u⁻¹} : Set K) ≤ S := by
        rw [Submonoid.closure_le]
        rintro x (rfl | rfl)
        · exact ⟨1, zpow_one _⟩
        · exact ⟨-1, zpow_neg_one _⟩
      obtain ⟨k, rfl⟩ := hle hz
      exact hpow k
  · have h1 : Algebra.adjoin A ({u} : Set K) ≤ Algebra.adjoin A ({u, u⁻¹} : Set K) :=
      Algebra.adjoin_mono (Set.singleton_subset_iff.2 (Set.mem_insert u {u⁻¹}))
    have h2 : Algebra.adjoin A ({u⁻¹} : Set K) ≤ Algebra.adjoin A ({u, u⁻¹} : Set K) :=
      Algebra.adjoin_mono (Set.singleton_subset_iff.2 (Set.mem_insert_of_mem u (Set.mem_singleton u⁻¹)))
    exact sup_le (fun z hz => h1 hz) (fun z hz => h2 hz)

/-- **Stacks 0AGS(3) in Čech-`H⁰` form.** `A` a two-dimensional regular local ring,
`X = Bl_𝔪 Spec A`, `I ⊆ A` any ideal, `IX = I·O_X`. Every compatible family of sections of
`O_X/IX` over the affine opens of `X` (`IX.quotFamilies`) is the restriction of a global section
of `O_X`.

Source: Stacks 0AGS (3), (4); 0AGT proof, second paragraph ("Since `I·O_X` is globally generated,
`H¹(X, I·O_X) = 0`, hence `A/I → Γ(X, O_X/I·O_X)` is surjective"). The route below avoids
cohomology and Serre vanishing.

Proof (as formalized):
0. **Charts.** Write `R = Γ(Spec A, O)` (`≅ A`, regular local of dimension `2`) and `𝔪 = (x, y)`
   (`IsRegularLocalRing.exists_span_pair_prime_not_dvd`). Since the base `Spec A` is affine, the chart
   morphism `ι = blowupChartι : P := Proj (⊕ₙ 𝔪ⁿ) ⟶ X` of Stacks 0804 is an
   open immersion with image `b⁻¹(Spec A) = X`. In `P`, `D₊(xX) ∪ D₊(yX) = P`
   (`reesGrading_basicOpen_sup_basicOpen_eq_top`) and `D₊(xX) ∩ D₊(yX) = D₊(xX·yX)`
   (`Proj.basicOpen_mul`), all affine, with sections rings `(Rees 𝔪)_{(xX)}`, `(Rees 𝔪)_{(yX)}`,
   `(Rees 𝔪)_{(xyX²)}` (Mathlib `awayToSection`) and restriction maps `awayMap`
   (Mathlib `awayMap_awayToSection`); these are transported to `X` along `ι.appIso`
   (`Proj.awaySectionsHom`, `Proj.presheaf_map_awaySectionsHom`).
1. **Sections of `IX`.** For every affine `V ⊆ X`, `IX(V) = (I·Γ(X, O_X))·Γ(V)`
   (`comap_ideal_eq_map_appLE` with `U = ⊤ ⊆ Spec A`).
2. **Laurent splitting.** `(Rees 𝔪)_{(xX)} = R[t]`, `t = yX/xX` (`exists_eval₂_isLocalizationElem_eq`,
   from the presentation `R[T] ↠ R[𝔪/x]`), `(Rees 𝔪)_{(xyX²)} = (Rees 𝔪)_{(xX)}[1/t]` and `t·t' = 1`
   with `t' = xX/yX ∈ (Rees 𝔪)_{(yX)}`, so
   `Γ(U_xy) = res Γ(U_x) + res Γ(U_y)` (`exists_eq_add_of_localization_of_eval₂_surjective`) and hence
   `IX(U_xy) = res IX(U_x) + res IX(U_y)` (`exists_mem_map_add_of_forall_exists_eq_add`).
3. **Gluing and locality.** The two-chart Čech criterion
   `toQuotFamilies_surjective_of_two_affineOpens`:
   lift the family on `U_x`, `U_y`, correct by step 2 so the lifts agree on `U_xy`, glue by the sheaf
   axiom, and check equality with the family on every affine open by locality of membership in an
   ideal sheaf (`mem_ideal_of_forall_exists_basicOpen`).
Steps 0–3 are assembled in `toQuotFamilies_surjective_of_proj_two_charts`. -/
theorem AlgebraicGeometry.blowup_regularLocalRing_dimTwo_toQuotFamilies_surjective
    (A : Type u) [CommRing A] [IsRegularLocalRing A] (hdim : ringKrullDim A = 2) (I : Ideal A) :
    let e := (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
    let J : (AlgebraicGeometry.Spec (CommRingCat.of A)).IdealSheafData :=
      AlgebraicGeometry.Scheme.IdealSheafData.ofIdealTop ((IsLocalRing.maximalIdeal A).map e)
    let X := (AlgebraicGeometry.Scheme.blowup J).left
    let IX : X.IdealSheafData :=
      (AlgebraicGeometry.Scheme.IdealSheafData.ofIdealTop (I.map e)).comap
        (AlgebraicGeometry.Scheme.blowup J).hom
    Function.Surjective IX.toQuotFamilies := by
  intro e J X IX
  -- Step 0: transport regularity and dimension of `A` to `R := Γ(Spec A, ⊤)` along `ΓSpecIso`
  let ε : A ≃+* Γ(AlgebraicGeometry.Spec (CommRingCat.of A), ⊤) :=
    (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of A)).symm.commRingCatIsoToRingEquiv
  have : IsRegularLocalRing Γ(AlgebraicGeometry.Spec (CommRingCat.of A), ⊤) :=
    IsRegularLocalRing.of_ringEquiv ε
  have hdim' : ringKrullDim Γ(AlgebraicGeometry.Spec (CommRingCat.of A), ⊤) = 2 := by
    rw [← ringKrullDim_eq_of_ringEquiv ε, hdim]
  have hmax : (IsLocalRing.maximalIdeal A).map
      (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom =
        IsLocalRing.maximalIdeal Γ(AlgebraicGeometry.Spec (CommRingCat.of A), ⊤) :=
    IsLocalRing.map_ringEquiv_maximalIdeal ε
  let U : (AlgebraicGeometry.Spec (CommRingCat.of A)).affineOpens :=
    ⟨⊤, AlgebraicGeometry.isAffineOpen_top _⟩
  have hJ : J.ideal U = IsLocalRing.maximalIdeal Γ(AlgebraicGeometry.Spec (CommRingCat.of A), ⊤) := by
    show (AlgebraicGeometry.Scheme.IdealSheafData.ofIdealTop _).ideal ⟨⊤, _⟩ = _
    simpa using hmax
  -- `𝔪 = (x, y)`
  obtain ⟨x, y, hspan, -, -⟩ := IsRegularLocalRing.exists_span_pair_prime_not_dvd
    Γ(AlgebraicGeometry.Spec (CommRingCat.of A), ⊤) hdim'
  have hspan' : J.ideal U = Ideal.span {x, y} := hJ.trans hspan.symm
  have hxJ : x ∈ J.ideal U := hspan' ▸ Ideal.subset_span (by simp)
  have hyJ : y ∈ J.ideal U := hspan' ▸ Ideal.subset_span (by simp)
  -- the chart morphism `Proj (⊕ₙ 𝔪ⁿ) ⟶ X` of Stacks 0804, onto `X`
  obtain ⟨ε', hε', -⟩ := J.exists_reesAlgebra_sectionsRing_equiv U
  have hι : (AlgebraicGeometry.Scheme.blowupChartι J U ε' hε').opensRange = ⊤ := by
    rw [AlgebraicGeometry.Scheme.blowupChartι_opensRange]; rfl
  -- Step 1: `IX(V) = (I·Γ(X, O_X))·Γ(V)`
  have hK : ∀ V : X.affineOpens, IX.ideal V =
      ((I.map e).map (AlgebraicGeometry.Scheme.blowup J).hom.appTop.hom).map
        (X.presheaf.map (homOfLE le_top).op).hom := by
    intro V
    show ((AlgebraicGeometry.Scheme.IdealSheafData.ofIdealTop (I.map e)).comap
      (AlgebraicGeometry.Scheme.blowup J).hom).ideal V = _
    rw [AlgebraicGeometry.Scheme.IdealSheafData.comap_ideal_eq_map_appLE _ _ U V le_top, Ideal.map_map]
    congr 1
    show (AlgebraicGeometry.Scheme.IdealSheafData.ofIdealTop (I.map e)).ideal ⟨⊤, _⟩ = _
    simp
  -- Step 2 (chart algebra): `(Rees 𝔪)_{(xX)} = 𝔪₀[t]`, `t = yX/xX`
  have hgen : ∀ b : Away (J.ideal U).reesGrading ((J.ideal U).reesX x hxJ),
      ∃ p : Polynomial ((J.ideal U).reesGrading 0),
        p.eval₂ (fromZeroRingHom (J.ideal U).reesGrading (Submonoid.powers ((J.ideal U).reesX x hxJ)))
          (Away.isLocalizationElem ((J.ideal U).reesX_mem x hxJ) ((J.ideal U).reesX_mem y hyJ)) = b := by
    intro b
    obtain ⟨p, hp⟩ := (J.ideal U).exists_eval₂_isLocalizationElem_eq x y hxJ hyJ hspan'
      ((fromZeroRingHom (J.ideal U).reesGrading (Submonoid.powers ((J.ideal U).reesX x hxJ))).comp
        (algebraMap _ ((J.ideal U).reesGrading 0))) (fun r => rfl) b
    exact ⟨p.map (algebraMap _ _), by rw [Polynomial.eval₂_map]; exact hp⟩
  -- Steps 0–3 assembled
  exact AlgebraicGeometry.Scheme.IdealSheafData.toQuotFamilies_surjective_of_proj_two_charts
    (J.ideal U).reesGrading IX _ hK (AlgebraicGeometry.Scheme.blowupChartι J U ε' hε') hι
    ((J.ideal U).reesX_mem x hxJ) ((J.ideal U).reesX_mem y hyJ) one_pos one_pos
    ((J.ideal U).reesGrading_basicOpen_sup_basicOpen_eq_top x y hxJ hyJ hspan') hgen

end
