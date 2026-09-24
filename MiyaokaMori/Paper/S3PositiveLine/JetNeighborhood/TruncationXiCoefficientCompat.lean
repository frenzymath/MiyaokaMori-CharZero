import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.JetWeightComponentEqCoefficient
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.JetProjectivize
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.TruncatedJetPositivePiecesVanishSubring

/-! # Compatibility of the truncation `Γ(Tot(L), p⁻¹V) → 𝒜(V)` with the `ξ`-coefficient maps
(helper of `BasedJet.weightComponent_germ_mem_of_forall_pieceSection`; proof of Lemma 3.1 of the paper)

`trunc := structureIso⁻¹ ≫ truncation : p_*O_{Tot(L)} ⟶ ⊕_{q ≤ κ} L^{-q}` is the section-level form of the closed
immersion `C̃_(κ)(L) ↪ Tot(L)`. This module proves: (1) `trunc ≫ π_m = symCoeffHom_m ≫ pieceIso_m⁻¹` for `m ≤ κ`;
(2) `trunc` is additive and multiplicative on sections; (3) hence, for `y ∈ U' ≤ V`, "all positive
`ξ`-coefficients of `g` vanish at `y`" is equivalent to `PositivePiecesVanishAt` of `trunc(g)|_{U'}`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace truncatedJetAlgebra

variable {k : Type u} [Field k] {Ct : SmoothProjectiveCurve k} (L : LineBundle Ct.toVariety) (κ : ℕ)

/-- `τ ≫ π_m = totalProj m ≫ symPartToMonoidalPow m ≫ pieceIso_m⁻¹` for `m ≤ κ` (`Sigma.hom_ext` + `ι_truncation`,
`totalIncl_totalProj(_of_ne)`, `biproduct.ι_π_self/ne`). -/
theorem truncation_comp_π {m : ℕ} (hm : m ≤ κ) :
    truncatedJetAlgebra.truncation L κ ≫
        CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
          ⟨m, Nat.lt_succ_of_le hm⟩ =
      ((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
          (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).totalProj m ≫
        AlgebraicGeometry.Scheme.Modules.symPartToMonoidalPow (AlgebraicGeometry.Scheme.Modules.dual L.toModules) m ≫
        (truncatedJetAlgebra.pieceIso L m).inv :
        (∐ (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
          (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).part) ⟶ truncatedJetAlgebra.piece L m) := by
  apply CategoryTheory.Limits.Sigma.hom_ext
  intro n
  have h1 := truncatedJetAlgebra.ι_truncation L κ n
  have h2 : (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
        (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).totalIncl n ≫
        (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
          (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).totalProj m =
      if h : n = m then CategoryTheory.eqToHom (congrArg (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
        (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).part h) else 0 :=
    CategoryTheory.Limits.Sigma.ι_desc _ _
  show CategoryTheory.Limits.Sigma.ι (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
        (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).part n ≫ truncatedJetAlgebra.truncation L κ ≫
        CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
          ⟨m, Nat.lt_succ_of_le hm⟩ =
      (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
        (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).totalIncl n ≫
      (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
        (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).totalProj m ≫
      AlgebraicGeometry.Scheme.Modules.symPartToMonoidalPow (AlgebraicGeometry.Scheme.Modules.dual L.toModules) m ≫
      (truncatedJetAlgebra.pieceIso L m).inv
  rw [← CategoryTheory.Category.assoc (CategoryTheory.Limits.Sigma.ι _ n) (truncatedJetAlgebra.truncation L κ), h1,
    ← CategoryTheory.Category.assoc ((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
        (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).totalIncl n), h2]
  by_cases hnm : n = m
  · subst hnm
    rw [dif_pos rfl, dif_pos hm, CategoryTheory.eqToHom_refl, CategoryTheory.Category.id_comp,
      CategoryTheory.Category.assoc, CategoryTheory.Category.assoc, CategoryTheory.Limits.biproduct.ι_π_self,
      CategoryTheory.Category.comp_id]
  · rw [dif_neg hnm, CategoryTheory.Limits.zero_comp]
    split_ifs with hn
    · rw [CategoryTheory.Category.assoc, CategoryTheory.Category.assoc,
        CategoryTheory.Limits.biproduct.ι_π_ne _ (fun h => hnm (congrArg Fin.val h)),
        CategoryTheory.Limits.comp_zero, CategoryTheory.Limits.comp_zero]
    · exact CategoryTheory.Limits.zero_comp

/-- `trunc := structureIso⁻¹ ≫ τ : p_*O_{Tot(L)} ⟶ ⊕_{q ≤ κ} L^{-q}` (section-level closed immersion
`C̃_(κ)(L) ↪ Tot(L)`). -/
noncomputable def truncHom :
    (AlgebraicGeometry.Scheme.Modules.pushforward (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        (SheafOfModules.unit (AlgebraicGeometry.Scheme.totalSpace L.toModules).left.ringCatSheaf) ⟶
      (truncatedJetAlgebra L κ).carrier :=
  (AlgebraicGeometry.Scheme.relativeSpec.structureIso
      (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
        (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).total).inv ≫
    truncatedJetAlgebra.truncation L κ

/-- `trunc ≫ π_m = symCoeffHom_m ≫ pieceIso_m⁻¹` for `m ≤ κ`. -/
theorem truncHom_comp_π {ρ : FiniteCover k Ct} (L : LineBundle ρ.source.toVariety) {m : ℕ} (hm : m ≤ κ) :
    truncHom L κ ≫
        CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
          ⟨m, Nat.lt_succ_of_le hm⟩ =
      BasedJet.symCoeffHom L m ≫ (truncatedJetAlgebra.pieceIso L m).inv :=
  (CategoryTheory.Category.assoc _ _ _).trans
    ((congrArg (fun g => (AlgebraicGeometry.Scheme.relativeSpec.structureIso
      (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
        (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).total).inv ≫ g) (truncation_comp_π L κ hm)).trans
      ((congrArg (fun g => (AlgebraicGeometry.Scheme.relativeSpec.structureIso
        (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
          (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).total).inv ≫ g)
        (CategoryTheory.Category.assoc _ _ _).symm).trans (CategoryTheory.Category.assoc _ _ _).symm))

section Sections

variable (V : Ct.toScheme.Opens)

/-- `trunc` is additive on sections. -/
theorem truncHom_app_add
    (g g' : Γ((AlgebraicGeometry.Scheme.totalSpace L.toModules).left,
      (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ V)) :
    (truncHom L κ).app V (g + g') = (truncHom L κ).app V g + (truncHom L κ).app V g' :=
  ((truncHom L κ).app V).hom.map_add g g'

/-- `trunc` is multiplicative on sections (`structureIso_inv_app_mul`, `totalMul_comp_truncation`,
`tensorHom_tensorSections`, `sectionsMul_eq_mul_tensorSections`). -/
theorem truncHom_app_mul
    (g g' : Γ((AlgebraicGeometry.Scheme.totalSpace L.toModules).left,
      (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ V)) :
    (show (truncatedJetAlgebra L κ).sectionsRing V from (truncHom L κ).app V (g * g')) =
      (show (truncatedJetAlgebra L κ).sectionsRing V from (truncHom L κ).app V g) *
        (show (truncatedJetAlgebra L κ).sectionsRing V from (truncHom L κ).app V g') := by
  have h1 := AlgebraicGeometry.Scheme.relativeSpec.structureIso_inv_app_mul
    (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).total
    V g g'
  have h2 := congrArg (fun φ => φ.app V (AlgebraicGeometry.Scheme.Modules.tensorSections _ _ V
      ((AlgebraicGeometry.Scheme.relativeSpec.structureIso
        (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
          (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).total).inv.app V g)
      ((AlgebraicGeometry.Scheme.relativeSpec.structureIso
        (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
          (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).total).inv.app V g')))
    (truncatedJetAlgebra.totalMul_comp_truncation L κ)
  have h3 := AlgebraicGeometry.Scheme.Modules.tensorHom_tensorSections
    (truncatedJetAlgebra.truncation L κ) (truncatedJetAlgebra.truncation L κ) V
    ((AlgebraicGeometry.Scheme.relativeSpec.structureIso
        (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
          (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).total).inv.app V g)
    ((AlgebraicGeometry.Scheme.relativeSpec.structureIso
        (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
          (AlgebraicGeometry.Scheme.Modules.dual L.toModules)).total).inv.app V g')
  refine (congrArg (fun z => (truncatedJetAlgebra.truncation L κ).app V z) h1).trans ?_
  refine h2.trans ?_
  refine (congrArg (fun z => (truncatedJetAlgebra.mulHom L κ).app V z) h3).trans ?_
  exact (AlgebraicGeometry.Scheme.QCAlgebra.sectionsMul_eq_mul_tensorSections (truncatedJetAlgebra L κ) V _ _).symm

end Sections

section Criterion

variable {ρ : FiniteCover k Ct} (L : LineBundle ρ.source.toVariety) (κ : ℕ)

/-- `π_m (trunc(g)|_{U'}) = (pieceIso_m⁻¹ (symCoeffHom_m g))|_{U'}` for `m ≤ κ` (naturality of `π_m` + `truncHom_comp_π`). -/
theorem π_sectionsRestrict_truncHom_app {V U' : ρ.source.toScheme.Opens} (h : U' ≤ V)
    (g : Γ((AlgebraicGeometry.Scheme.totalSpace L.toModules).left,
      (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ V)) {m : ℕ} (hm : m ≤ κ) :
    (CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
        ⟨m, Nat.lt_succ_of_le hm⟩).app U'
      ((truncatedJetAlgebra L κ).sectionsRestrict h
        (show (truncatedJetAlgebra L κ).sectionsRing V from (truncHom L κ).app V g)) =
    (truncatedJetAlgebra.piece L m).presheaf.map (CategoryTheory.homOfLE h).op
      ((truncatedJetAlgebra.pieceIso L m).inv.app V ((BasedJet.symCoeffHom L m).app V g)) := by
  have hn := PresheafOfModules.naturality_apply
    (CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
      ⟨m, Nat.lt_succ_of_le hm⟩).val (CategoryTheory.homOfLE h).op ((truncHom L κ).app V g)
  have hc := congrArg (fun φ => φ.app V g) (truncHom_comp_π κ L hm)
  exact hn.trans (congrArg _ hc)

/-- **Transfer of the vanishing criterion to the truncated ring.** For `y ∈ U' ≤ V` and
`g ∈ Γ(Tot(L), p⁻¹V)`: all positive pieces of `trunc(g)|_{U'}` vanish at `y` iff for every `1 ≤ m ≤ κ` the germ at
`y` of the `m`-th `ξ`-coefficient `symCoeffHom_m g` lies in `𝔪_y • ⊤` (`π_sectionsRestrict_truncHom_app`,
`germ_res_mem_maximalIdeal_smul_iff`, `germ_hom_app_mem_maximalIdeal_smul_iff_of_iso` for `pieceIso_m`). -/
theorem positivePiecesVanishAt_sectionsRestrict_truncHom_iff {V U' : ρ.source.toScheme.Opens} (h : U' ≤ V)
    {y : ρ.source.toScheme} (hy : y ∈ U')
    (g : Γ((AlgebraicGeometry.Scheme.totalSpace L.toModules).left,
      (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom ⁻¹ᵁ V)) :
    truncatedJetAlgebra.PositivePiecesVanishAt L κ hy
        ((truncatedJetAlgebra L κ).sectionsRestrict h
          (show (truncatedJetAlgebra L κ).sectionsRing V from (truncHom L κ).app V g)) ↔
      ∀ (m : ℕ), 1 ≤ m → ∀ hm : m ≤ κ,
        (AlgebraicGeometry.Scheme.Modules.monoidalPow (AlgebraicGeometry.Scheme.Modules.dual L.toModules) m).presheaf.germ
            V y (h hy) ((BasedJet.symCoeffHom L m).app V g) ∈
          (IsLocalRing.maximalIdeal (ρ.source.toScheme.presheaf.stalk y)) •
            (⊤ : Submodule (ρ.source.toScheme.presheaf.stalk y)
              ((AlgebraicGeometry.Scheme.Modules.monoidalPow
                (AlgebraicGeometry.Scheme.Modules.dual L.toModules) m).presheaf.stalk y)) := by
  have key : ∀ (m : ℕ) (hm : m ≤ κ),
      ((truncatedJetAlgebra.piece L m).presheaf.germ U' y hy
        ((CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
          ⟨m, Nat.lt_succ_of_le hm⟩).app U'
        ((truncatedJetAlgebra L κ).sectionsRestrict h
          (show (truncatedJetAlgebra L κ).sectionsRing V from (truncHom L κ).app V g))) ∈
        (IsLocalRing.maximalIdeal (ρ.source.toScheme.presheaf.stalk y)) •
          (⊤ : Submodule (ρ.source.toScheme.presheaf.stalk y) ((truncatedJetAlgebra.piece L m).presheaf.stalk y))) ↔
      (AlgebraicGeometry.Scheme.Modules.monoidalPow (AlgebraicGeometry.Scheme.Modules.dual L.toModules) m).presheaf.germ
          V y (h hy) ((BasedJet.symCoeffHom L m).app V g) ∈
        (IsLocalRing.maximalIdeal (ρ.source.toScheme.presheaf.stalk y)) •
          (⊤ : Submodule (ρ.source.toScheme.presheaf.stalk y)
            ((AlgebraicGeometry.Scheme.Modules.monoidalPow
              (AlgebraicGeometry.Scheme.Modules.dual L.toModules) m).presheaf.stalk y)) := by
    intro m hm
    rw [π_sectionsRestrict_truncHom_app L κ h g hm,
      AlgebraicGeometry.Scheme.Modules.germ_res_mem_maximalIdeal_smul_iff (truncatedJetAlgebra.piece L m) h hy]
    exact AlgebraicGeometry.Scheme.Modules.germ_hom_app_mem_maximalIdeal_smul_iff_of_iso
      (truncatedJetAlgebra.pieceIso L m).symm V (h hy) _
  constructor
  · intro H m h1 hm
    exact (key m hm).mp (H ⟨m, Nat.lt_succ_of_le hm⟩ h1)
  · intro H q hq
    obtain ⟨m, hm'⟩ := q
    exact (key m (Nat.lt_succ_iff.mp hm')).mpr (H m hq (Nat.lt_succ_iff.mp hm'))

end Criterion

end truncatedJetAlgebra

end
