import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.Cech.CechComplexAlternating
import MiyaokaMori.AlgebraicGeometry.Cohomology.Cech.CechComplexAlternatingDefs
import MiyaokaMori.AlgebraicGeometry.Cohomology.Cech.CechAlternatingLocalizationAcyclic

/-! # Elementwise vanishing criterion for the alternating Čech complex

Let `X` be a scheme, `U : Fin n → X.Opens`, `M` an `O_X`-module and `q ≥ 0`. Suppose that for every
alternating `(q+1)`-cochain `s = (s_σ)`, `s_σ ∈ Γ(M, U_{σ_0} ∩ ⋯ ∩ U_{σ_{q+1}})` (`σ` strictly
increasing), with `Σ_k (-1)^k s_{τ minus k}|_{U_τ} = 0` for all `τ`, there is a `q`-cochain `t` with
`Σ_k (-1)^k t_{τ minus k}|_{U_τ} = s_τ` for all `τ`. Then the alternating Čech complex
`cechComplexAlt U M` has zero homology in degree `q+1` (`Subsingleton`). In other words, vanishing
of the homology of `cechComplexAlt` can be checked elementwise on families of sections.

Proof sketch:
1. `HomologicalComplex.exactAt_iff'` (`i = q, j = q+1, k = q+2`) + `exactAt_iff_isZero_homology` +
   `ModuleCat.subsingleton_of_isZero` reduce the claim to exactness of the short complex
   `C^q → C^{q+1} → C^{q+2}`; `ShortComplex.moduleCat_exact_iff` makes exactness elementwise.
2. `CochainComplex.of_d` identifies the differential with `cechDiffAlt`; the family-of-sections API
   (`cechToFamily`, `cechToFamily_diff`, `cechToFamily_bijective`, in `CechComplexAlternatingDefs.lean`)
   exchanges elements of `∏ᶜ` with families and gives `(d x)_τ = Σ_k (-1)^k res(x_{τ minus k})`.
3. Apply the hypothesis to `s = (π_σ x)_σ` and take the element corresponding to `t`.
4. Also: the converse `exists_family_of_homology_subsingleton` (vanishing homology ⇒ cocycle
   families are coboundary families); a morphism of modules commutes with restriction (`app_map`) and
   with the differential on families (`cechFamilyD_map`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}} {n : ℕ} (U : Fin n → X.Opens) (M : X.Modules)

theorem cechComplexAlt_d (q : ℕ) :
    (cechComplexAlt U M).d ((q : ℕ) : ℤ) (((q + 1 : ℕ) : ℤ)) = cechDiffAlt U M q :=
  CochainComplex.of_d (cechTermAltZ U M) (cechDiffAltZ U M) ((q : ℕ) : ℤ)

/-- Vanishing of the homology of `cechComplexAlt` in degree `q+1` can be checked elementwise. -/
theorem cechComplexAlt_homology_subsingleton_of_family (q : ℕ)
    (H : ∀ s : CechFamily U M (q + 1), cechFamilyD U M (q + 1) s = 0 →
      ∃ t : CechFamily U M q, cechFamilyD U M q t = s) :
    Subsingleton (((cechComplexAlt U M).homology (((q + 1 : ℕ) : ℤ))) : Type u) := by
  apply ModuleCat.subsingleton_of_isZero
  rw [← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff' _ ((q : ℕ) : ℤ) (((q + 1 : ℕ) : ℤ)) (((q + 2 : ℕ) : ℤ))
      (by simp) (by simp; ring),
    ShortComplex.moduleCat_exact_iff]
  intro x₂ hx₂
  obtain ⟨y₂, hy₂⟩ : ∃ y : ↑(cechTermAlt U M (q + 1)), y = x₂ := ⟨x₂, rfl⟩
  have hy₂0 : (cechDiffAlt U M (q + 1)).hom y₂ = 0 := by
    refine (congrArg (fun φ => φ.hom y₂) (cechComplexAlt_d U M (q + 1))).symm.trans ?_
    rw [hy₂]
    exact hx₂
  have e := cechToFamily_diff U M (q + 1) y₂
  obtain ⟨t, ht⟩ := H (cechToFamily U M (q + 1) y₂) (by
    rw [← e, hy₂0]
    funext τ
    exact map_zero _)
  obtain ⟨x₁, rfl⟩ := (cechToFamily_bijective U M q).2 t
  have hfin : (cechDiffAlt U M q).hom x₁ = y₂ := by
    apply (cechToFamily_bijective U M (q + 1)).1
    rw [cechToFamily_diff, ht]
  exact ⟨x₁, ((congrArg (fun φ => φ.hom x₁) (cechComplexAlt_d U M q)).trans hfin).trans hy₂⟩

/-- Converse: vanishing homology ⇒ every cocycle family is a coboundary family. -/
theorem exists_family_of_homology_subsingleton (q : ℕ)
    (h : Subsingleton (((cechComplexAlt U M).homology (((q + 1 : ℕ) : ℤ))) : Type u))
    (s : CechFamily U M (q + 1)) (hs : cechFamilyD U M (q + 1) s = 0) :
    ∃ t : CechFamily U M q, cechFamilyD U M q t = s := by
  have hz : IsZero ((cechComplexAlt U M).homology (((q + 1 : ℕ) : ℤ))) :=
    ModuleCat.isZero_of_subsingleton _
  rw [← HomologicalComplex.exactAt_iff_isZero_homology,
    HomologicalComplex.exactAt_iff' _ ((q : ℕ) : ℤ) (((q + 1 : ℕ) : ℤ)) (((q + 2 : ℕ) : ℤ))
      (by simp) (by simp; ring),
    ShortComplex.moduleCat_exact_iff] at hz
  obtain ⟨y₂, rfl⟩ := (cechToFamily_bijective U M (q + 1)).2 s
  have hy₂0 : (cechDiffAlt U M (q + 1)).hom y₂ = 0 := by
    apply (cechToFamily_bijective U M (q + 2)).1
    rw [cechToFamily_diff, hs]
    funext τ
    exact (map_zero _).symm
  obtain ⟨x₁, hx₁⟩ := hz y₂
    ((congrArg (fun φ => φ.hom y₂) (cechComplexAlt_d U M (q + 1))).trans hy₂0)
  have hx₁' : (cechDiffAlt U M q).hom x₁ = y₂ :=
    (congrArg (fun φ => φ.hom x₁) (cechComplexAlt_d U M q)).symm.trans hx₁
  obtain ⟨z₁, hz₁⟩ : ∃ z : ↑(cechTermAlt U M q), z = x₁ := ⟨x₁, rfl⟩
  have hz₁' : (cechDiffAlt U M q).hom z₁ = y₂ := by
    rw [hz₁]
    exact hx₁'
  exact ⟨cechToFamily U M q z₁, by rw [← cechToFamily_diff, hz₁']⟩

variable {M} in
/-- A morphism of modules commutes with restriction maps (elementwise). -/
theorem app_map {N : X.Modules} (φ : M ⟶ N) {W W' : X.Opens} (h : W' ≤ W) (x : Γ(M, W)) :
    φ.app W' (M.presheaf.map (homOfLE h).op x) = N.presheaf.map (homOfLE h).op (φ.app W x) :=
  ConcreteCategory.congr_hom (φ.mapPresheaf.naturality (homOfLE h).op) x

variable {M} in
/-- A morphism of modules commutes with the differential on families of sections. -/
theorem cechFamilyD_map {N : X.Modules} (φ : M ⟶ N) (q : ℕ) (t : CechFamily U M q) :
    (fun τ => φ.app _ (cechFamilyD U M q t τ)) =
      cechFamilyD U N q (fun σ => φ.app _ (t σ)) := by
  funext τ
  show φ.app _ (∑ k : Fin (q + 2), _) = ∑ k : Fin (q + 2), _
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_zsmul, app_map]

end AlgebraicGeometry.Scheme.Modules

end
