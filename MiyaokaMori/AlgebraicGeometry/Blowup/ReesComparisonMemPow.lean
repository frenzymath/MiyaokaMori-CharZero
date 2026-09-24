import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Blowup.ReesComparisonAffineLocal
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.IdealSheafComapIdealEqMap

/-! # The Rees comparison map lands in the powers of the inverse image ideal

The comparison map `ψₙ : g^*(Iⁿ) ⟶ O_{X₁}` (`IdealSheafData.reesComparison`) takes values in the
subsheaf `I₁ⁿ ⊆ O_{X₁}`, `I₁ := I.comap g = g⁻¹I·O_{X₁}`; hence it factors through
`θₙ := reesComparisonLift : g^*(Iⁿ) ⟶ I₁ⁿ` with `θₙ ≫ I₁.powι n = ψₙ`. No flatness is needed here.

Source: Stacks 0805 (first paragraph of the proof); used for the point blowups in the proof of
Corollary 4.3 of the paper (§4). This is a step of
`reesAlgebra_comap_iso_pullback_of_flat`.
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

/-- **`ψₙ` lands in `I₁ⁿ`.** For every open `W ⊆ X₁` and `x ∈ Γ(W, g^*Iⁿ)`, the section
`ψₙ(x) ∈ Γ(X₁, W)` lies in `Γ(W, I₁ⁿ) = (I₁.powSubmodule n)(W)`, i.e. for every affine `V ≤ W`,
`ψₙ(x)|_V ∈ (I₁.ideal V)ⁿ`, where `I₁ = I.comap g`.

Source: Stacks 0805 (the image of `g^*(Iⁿ) → O_{X'}` is `(g⁻¹I·O_{X'})ⁿ`).

## Proof

Fix an affine open `V ≤ W` and write `s := ψₙ(x)|_V ∈ Γ(X₁, V)`. We must show `s ∈ (I₁.ideal V)ⁿ`.

1. **Membership is local on the affine `V`.** By Mathlib, `Γ(X₁, D(f))` is the localization of
   `Γ(X₁, V)` at `f` (`IsAffineOpen.isLocalization_basicOpen`) and
   `(I₁ ^ n).ideal (D(f)) = ((I₁ ^ n).ideal V)·Γ(X₁, D(f))` (`IdealSheafData.map_ideal_basicOpen`,
   `ideal_pow` is `rfl`); membership in a submodule can be tested after localizing at a family
   generating the unit ideal (`Submodule.mem_of_isLocalized_span`), and finitely many basic opens
   `D(f_j)` covering `V` have `span {f_j} = ⊤` (`IsAffineOpen.self_le_iSup_basicOpen_iff`). So it
   suffices: every point `p ∈ V` has a basic open `D(f) ∋ p` of `V` with
   `s|_{D(f)} ∈ (I₁.ideal D(f))ⁿ` (`IdealSheafData.mem_ideal_of_forall_exists_basicOpen` applied to
   `I₁ ^ n`).
2. **Shrink into a `g⁻¹U`.** Given `p ∈ V`, pick an affine open `U ⊆ X₂` with `g p ∈ U`
   (`X₂.isBasis_affineOpens`); then `p ∈ V ⊓ g⁻¹U`, an open subset of `V`, so there is a basic open
   `D(f)` of `V` with `p ∈ D(f) ≤ V ⊓ g⁻¹U` (`IsAffineOpen.exists_basicOpen_le`). `D(f)` is affine
   (`X₁.affineBasicOpen f`) and `D(f) ≤ g⁻¹U`.
3. **Affine computation.** `s|_{D(f)} = ψₙ.app (D(f)) (x|_{D(f)})` (naturality of `ψₙ` with respect
   to restriction, `Hom.mapPresheaf.naturality`). By `range_reesComparison_app` this lies in
   `((I.powSubmodule n).obj (op U)).map φ`, `φ := g.appLE U (D(f))`.
4. **Identify the ideal.** `(I.powSubmodule n).obj (op U) = (I.ideal U)ⁿ` for affine `U` (the
   inclusion `⊆` is the definition with `V := U`; `⊇` is `Ideal.map_pow` + Mathlib
   `IdealSheafData.map_ideal` for affine `V' ≤ U`; `mem_powSubmodule_iff_of_isAffineOpen`).
   Hence the image is `((I.ideal U)ⁿ).map φ = ((I.ideal U).map φ)ⁿ` (`Ideal.map_pow`)
   `= (I₁.ideal (D(f)))ⁿ` by `IdealSheafData.comap_ideal_eq_map_appLE`.

## Edge cases
`n = 0`: both sides are `O`, trivial. `I = ⊥`, `n ≥ 1`: `Iⁿ = 0`, `x = 0`, `ψₙ(x) = 0 ∈ I₁ⁿ`.
`W = ∅`: `Γ(∅, -) = 0`. `X₁ = ∅`: vacuous. -/
theorem reesComparison_mem_powSubmodule (n : ℕ) (W : X₁.Opensᵒᵖ)
    (x : ((AlgebraicGeometry.Scheme.Modules.pullback g).obj (I.pow n)).val.obj W) :
    ((I.reesComparison g n).val.app W).hom x ∈ ((I.comap g).powSubmodule n).obj W := by
  intro V hV
  change X₁.presheaf.map (homOfLE hV).op ((I.reesComparison g n).app W.unop x) ∈
    ((I.comap g) ^ n).ideal V
  refine ((I.comap g) ^ n).mem_ideal_of_forall_exists_basicOpen V _ ?_
  rintro ⟨p, hp⟩
  obtain ⟨_, ⟨U, hU, rfl⟩, hgp, -⟩ := X₂.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (g.base p)) isOpen_univ
  obtain ⟨f, hfle, hpf⟩ := V.2.exists_basicOpen_le (V := V.1 ⊓ g ⁻¹ᵁ U) ⟨p, ⟨hp, hgp⟩⟩ hp
  refine ⟨f, hpf, ?_⟩
  have hD : (X₁.affineBasicOpen f).1 ≤ g ⁻¹ᵁ U := hfle.trans inf_le_right
  have hle : (X₁.affineBasicOpen f).1 ≤ W.unop := (X₁.basicOpen_le f).trans hV
  have hres := ConcreteCategory.congr_hom
    ((I.reesComparison g n).mapPresheaf.naturality (homOfLE hle).op) x
  simp only [ConcreteCategory.comp_apply] at hres
  rw [AlgebraicGeometry.Scheme.presheaf_map_homOfLE_map_homOfLE]
  erw [← hres]
  have hmem : (I.reesComparison g n).app (X₁.affineBasicOpen f).1
      (((AlgebraicGeometry.Scheme.Modules.pullback g).obj (I.pow n)).presheaf.map (homOfLE hle).op x) ∈
      Set.range ((I.reesComparison g n).app (X₁.affineBasicOpen f).1) := ⟨_, rfl⟩
  rw [range_reesComparison_app g I n ⟨U, hU⟩ (X₁.affineBasicOpen f) hD] at hmem
  have hN : (I.ideal ⟨U, hU⟩) ^ n = (I.powSubmodule n).obj (op U) :=
    Submodule.ext fun s => (mem_powSubmodule_iff_of_isAffineOpen I n ⟨U, hU⟩ s).symm
  change _ ∈ ((I.comap g).ideal (X₁.affineBasicOpen f)) ^ n
  rw [comap_ideal_eq_map_appLE I g ⟨U, hU⟩ (X₁.affineBasicOpen f) hD, ← Ideal.map_pow, hN]
  exact hmem

/-- `θₙ : g^*(Iⁿ) ⟶ I₁ⁿ`, the factorization of `ψₙ` through the subsheaf `I₁ⁿ ⊆ O_{X₁}`. -/
def reesComparisonLift (n : ℕ) :
    (AlgebraicGeometry.Scheme.Modules.pullback g).obj (I.pow n) ⟶ (I.comap g).pow n :=
  (I.comap g).liftPow n (I.reesComparison g n) (I.reesComparison_mem_powSubmodule g n)

/-- The factorization `θₙ ≫ (I₁.powι n) = ψₙ`. -/
theorem reesComparisonLift_powι (n : ℕ) :
    I.reesComparisonLift g n ≫ (I.comap g).powι n = I.reesComparison g n := rfl

/-- On sections, `θₙ` is `ψₙ` with restricted codomain. -/
theorem reesComparisonLift_app_val (n : ℕ) (V : X₁.Opens)
    (x : Γ((AlgebraicGeometry.Scheme.Modules.pullback g).obj (I.pow n), V)) :
    ((I.reesComparisonLift g n).app V x).1 = (I.reesComparison g n).app V x := rfl

end AlgebraicGeometry.Scheme.IdealSheafData

end
