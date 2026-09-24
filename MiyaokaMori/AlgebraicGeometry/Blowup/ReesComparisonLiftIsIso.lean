import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Blowup.ReesComparisonMemPow
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.IsIsoOfAffineOpensCoverBijective
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.IdealSheafComapIdealEqMap

/-! # The Rees comparison map is an isomorphism for flat base change

For `g : X₁ ⟶ X₂` **flat**, the factorized comparison map `θₙ : g^*(Iⁿ) ⟶ I₁ⁿ`
(`IdealSheafData.reesComparisonLift`, `I₁ = I.comap g`) is an isomorphism of `O_{X₁}`-modules.

Source: Stacks 0805 (first paragraph of the proof: "`g^*(⊕ Iⁿ) = ⊕ I₁ⁿ` because `g` is flat");
used for the point blowups in the proof of Corollary 4.3 of the paper (§4).
This is the main step of `reesAlgebra_comap_iso_pullback_of_flat`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X₁ X₂ : AlgebraicGeometry.Scheme.{u}} (g : X₁ ⟶ X₂) (I : X₂.IdealSheafData)

/-- **`θₙ` is an isomorphism for `g` flat.**

Source: Stacks 0805 (first paragraph). Flatness is necessary:
`g : Spec k[x]/(x) → Spec k[x]`, `I = (x)`: `g^*I ≅ I/I² ≅ k ≠ 0` while `I.comap g = 0`.

## Proof

Use `Modules.isIso_of_affineOpens_cover_bijective`:
a morphism of quasi-coherent modules that is bijective on the sections over each member of a family
of affine opens covering `X₁` is an isomorphism.

1. **Quasi-coherence.** `I₁ⁿ` is quasi-coherent (`IdealSheafData.pow_isQuasicoherent`), and
   `g^*(Iⁿ)` is quasi-coherent as the pullback of the quasi-coherent `Iⁿ`
   (`Modules.isQuasicoherent_pullback`).
2. **The family.** Index type `{p : X₂.affineOpens × X₁.affineOpens // p.2.1 ≤ g ⁻¹ᵁ p.1.1}`, open
   `V := p.2`. It covers `X₁`: for `x ∈ X₁` choose an affine `U ∋ g x` (`X₂.isBasis_affineOpens`),
   then an affine `V ∋ x` inside the open `g⁻¹U` (`X₁.isBasis_affineOpens`,
   `Opens.IsBasis.exists_subset_of_mem_open`).
3. **Bijectivity on such a `V`** (`U` affine, `V ≤ g⁻¹U`, `φ := g.appLE U V`).
   `θₙ.app V` is `ψₙ.app V` with codomain restricted to `(I₁.powSubmodule n)(V)`
   (`reesComparisonLift_app_val`, `LinearMap.codRestrict`), so
   * injective ⟸ `ψₙ.app V` injective: `reesComparison_app_injective` (this is where `Flat g` is used);
   * surjective ⟸ `(I₁.powSubmodule n)(V) ⊆ range (ψₙ.app V)`. By `range_reesComparison_app` the
     range is `((I.powSubmodule n)(U)).map φ`; `(I.powSubmodule n)(U) = (I.ideal U)ⁿ` for affine `U`
     (`mem_powSubmodule_iff_of_isAffineOpen`; `⊆` is the definition with `V := U`, `⊇` is
     `Ideal.map_pow` + Mathlib `IdealSheafData.map_ideal`), so the range is
     `((I.ideal U)ⁿ).map φ = ((I.ideal U).map φ)ⁿ` (`Ideal.map_pow`) `= (I₁.ideal V)ⁿ`
     (`IdealSheafData.comap_ideal_eq_map_appLE`) `= (I₁.powSubmodule n)(V)` (the same lemma for `I₁`).

## Edge cases
`n = 0`: `θ₀` is `ε' : g^*O ≅ O` restricted to `I₁⁰ = O`, an iso. `I = ⊥`, `n ≥ 1`: both sides `0`.
`X₁ = ∅`: the empty family; both modules are `0`. -/
theorem reesComparisonLift_isIso [AlgebraicGeometry.Flat g] (n : ℕ) :
    IsIso (I.reesComparisonLift g n) := by
  haveI : ((AlgebraicGeometry.Scheme.Modules.pullback g).obj (I.pow n)).IsQuasicoherent := by
    haveI := I.pow_isQuasicoherent n
    infer_instance
  haveI : ((I.comap g).pow n).IsQuasicoherent := (I.comap g).pow_isQuasicoherent n
  refine AlgebraicGeometry.Scheme.Modules.isIso_of_affineOpens_cover_bijective
    (I.reesComparisonLift g n)
    (ι := {p : X₂.affineOpens × X₁.affineOpens // p.2.1 ≤ g ⁻¹ᵁ p.1.1}) (fun p => p.1.2.1)
    (fun p => p.1.2.2) ?_ ?_
  · intro x
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := X₂.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (g.base x)) isOpen_univ
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ := X₁.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ ((g ⁻¹ᵁ U : X₁.Opens) : Set X₁) from hxU) (g ⁻¹ᵁ U).isOpen
    exact ⟨⟨(⟨U, hU⟩, ⟨V, hV⟩), hVU⟩, hxV⟩
  · rintro ⟨⟨U, V⟩, h⟩
    constructor
    · intro x y hxy
      exact reesComparison_app_injective g I n U V h (congrArg Subtype.val hxy)
    · intro y
      have hy : y.1 ∈ ((I.comap g).ideal V) ^ n :=
        (mem_powSubmodule_iff_of_isAffineOpen (I.comap g) n V y.1).mp y.2
      rw [comap_ideal_eq_map_appLE I g U V h, ← Ideal.map_pow] at hy
      have hN : (I.ideal U) ^ n = (I.powSubmodule n).obj (op U.1) :=
        Submodule.ext fun s => (mem_powSubmodule_iff_of_isAffineOpen I n U s).symm
      rw [hN] at hy
      have hy' : y.1 ∈ Set.range ((I.reesComparison g n).app V.1) := by
        rw [range_reesComparison_app g I n U V h]
        exact hy
      obtain ⟨x, hx⟩ := hy'
      exact ⟨x, Subtype.ext hx⟩

end AlgebraicGeometry.Scheme.IdealSheafData

end
