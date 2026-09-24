import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.JetNeighborhoodZeroSectionSurjective
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.NegativeDegreeNoSections
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.DegreeOfTensorPower
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.ModuleSheafFrameIso

/-! # Global functions on the jet neighbourhood are pulled back from the curve when `deg L > 0`

When `deg L > 0`, every global function on the jet neighbourhood `C̃_(κ)(L)` is pulled back from the curve:
`a = p^*(σ₀^* a)` (its components in `H^0(C̃, L^{-q})`, `q ≥ 1`, vanish because these line bundles have negative
degree).

Source: Lemma 4.1 of the paper (`deg L^{-q} = −q d_L < 0`, so `c_q = 0`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- **Global functions on the thickening are constant along the fibres when `deg L > 0`.** For
`a ∈ Γ(C̃_(κ)(L), O)`, `a = p^*(σ₀^* a)`, where `p = jetNeighborhood.proj` and `σ₀ = jetNeighborhood.zeroSection`.

**Proof** (as formalized). `C̃_(κ)(L) = Spec_C̃ 𝒜` with `𝒜 = truncatedJetAlgebra L κ = ⊕_{q ≤ κ} piece_q`.
1. The structure map `S = relativeSpec.structureHom 𝒜 : 𝒜 → p_*O` is an isomorphism of sheaves
   (`relativeSpec.structureIso`), so `a = S(a')` for a unique global section `a'` of `𝒜`
   (`Modules.Iso.app_bijective` at `⊤`).
2. `σ₀^*(S c) = augmentation(c) = π₀ c` (`relativeSpec.ofAlgebraMap_appLE_structureHom` at `V = ⊤`; the zero
   section is `relativeSpecHomEquiv.symm` of the augmentation `biproduct.π 0`, `JetZeroSection`).
3. For `q ≥ 1`, `Γ(C̃, piece_q) = 0`: `piece_q ≅ (L.zpow (-q)).toModules` (`piece_iso_negativePower`,
   `zpow_neg_natCast_toModules`), `(L.zpow (-q)).degree = -q · deg L < 0` (`LineBundle.degree_zpow`), and a line
   bundle of negative degree on `C̃` has `H^0 = 0` (`no_global_sections_of_degree_neg`), transported to global
   sections by `sheafCohomologyZeroEquiv` and along the isomorphism by `Iso.app_bijective`.
4. Hence `a' − ι₀(π₀ a')` has all components zero (`ι₀ ≫ π₀ = 𝟙`, `ι₀ ≫ π_q = 0`), so it is `0`
   (`truncatedJetAlgebra.eq_zero_of_weightGE`), i.e. `a' = ι₀(π₀ a')`.
5. `S(ι₀ r) = p^*(r)` because `S` is an `O`-algebra map and `ι₀ = 𝒜.one`
   (`QCAlgebra.algebraMapSections_comp_sectionsUnit`, `jetNeighborhood.structureHom_isAlgebraMap`).
Altogether `a = S(a') = S(ι₀ π₀ a') = p^*(π₀ a') = p^*(σ₀^* a)`. The `κ = 0` case needs no special treatment. -/
theorem jetNeighborhood.appTop_eq_proj_zeroSection_of_degree_pos {k : Type u} [Field k]
    {Ct : SmoothProjectiveCurve k} (L : LineBundle Ct.toVariety) (hL : 0 < L.degree) (κ : ℕ)
    (a : Γ((jetNeighborhood L κ).left, ⊤)) :
    a = (jetNeighborhood.proj L κ).appTop ((jetNeighborhood.zeroSection L κ).appTop a) := by
  have hle : (⊤ : Ct.toScheme.Opens) ≤
      jetNeighborhood.zeroSection L κ ⁻¹ᵁ (jetNeighborhood.proj L κ ⁻¹ᵁ ⊤) :=
    jetNeighborhood.le_zeroSection_preimage_proj_preimage L κ ⊤
  -- Step 1: `a = S a'` for a global section `a'` of the truncated jet algebra
  obtain ⟨a', ha'⟩ : ∃ a' : Γ(truncatedJetAlgebra.obj L κ, ⊤),
      (AlgebraicGeometry.Scheme.relativeSpec.structureHom (truncatedJetAlgebra L κ)).app ⊤ a' = a :=
    (AlgebraicGeometry.Scheme.Modules.Iso.app_bijective
      (AlgebraicGeometry.Scheme.relativeSpec.structureIso (truncatedJetAlgebra L κ)) ⊤).2 a
  -- Step 2: `σ₀^♯ a = π₀ a'`
  have hσ : ((jetNeighborhood.zeroSection L κ).appLE (jetNeighborhood.proj L κ ⁻¹ᵁ ⊤) ⊤ hle).hom a =
      (CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
        ⟨0, Nat.succ_pos κ⟩).app ⊤ a' := by
    have hD := AlgebraicGeometry.Scheme.relativeSpec.ofAlgebraMap_appLE_structureHom
      (truncatedJetAlgebra L κ) (CategoryTheory.Over.mk (CategoryTheory.CategoryStruct.id Ct.toScheme))
      (jetNeighborhood.augmentation L κ) (jetNeighborhood.augmentation_isAlgebraMap L κ) ⊤ a' hle
    have h1 : ((jetNeighborhood.zeroSection L κ).appLE (jetNeighborhood.proj L κ ⁻¹ᵁ ⊤) ⊤ hle).hom a =
        ((jetNeighborhood.zeroSection L κ).appLE (jetNeighborhood.proj L κ ⁻¹ᵁ ⊤) ⊤ hle).hom
          ((AlgebraicGeometry.Scheme.relativeSpec.structureHom (truncatedJetAlgebra L κ)).app ⊤ a') :=
      congrArg _ ha'.symm
    exact h1.trans hD
  -- Step 3: the components of weight `q ≥ 1` vanish (negative degree)
  have hpos : ∀ q : Fin (κ + 1), q ≠ ⟨0, Nat.succ_pos κ⟩ →
      (CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q) q).app ⊤ a'
        = 0 := by
    intro q hq
    have hq0 : 0 < (q : ℕ) := Nat.pos_of_ne_zero (fun h => hq (Fin.ext h))
    have hdeg : (L.zpow (-((q : ℕ) : ℤ))).degree < 0 := by
      rw [LineBundle.degree_zpow]
      exact mul_neg_of_neg_of_pos (by omega) hL
    have h0 : Subsingleton
        (AlgebraicGeometry.sheafCohomology Ct.toScheme (L.zpow (-((q : ℕ) : ℤ))).toModules 0) :=
      no_global_sections_of_degree_neg Ct _ hdeg
    have h1 : Subsingleton Γ((L.zpow (-((q : ℕ) : ℤ))).toModules, ⊤) :=
      (AlgebraicGeometry.sheafCohomologyZeroEquiv
        (L.zpow (-((q : ℕ) : ℤ))).toModules).symm.toEquiv.subsingleton
    let e : truncatedJetAlgebra.piece L q ≅ (L.zpow (-((q : ℕ) : ℤ))).toModules :=
      (truncatedJetAlgebra.piece_iso_negativePower L q).some ≪≫
        CategoryTheory.eqToIso (LineBundle.zpow_neg_natCast_toModules L q).symm
    have hsub : Subsingleton Γ(truncatedJetAlgebra.piece L q, ⊤) :=
      (Equiv.ofBijective _ (AlgebraicGeometry.Scheme.Modules.Iso.app_bijective e ⊤)).subsingleton
    exact Subsingleton.elim _ _
  -- Step 4: `a' = ι₀ (π₀ a')`
  have hdecomp : a' =
      (CategoryTheory.Limits.biproduct.ι (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
        ⟨0, Nat.succ_pos κ⟩).app ⊤
        ((CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
          ⟨0, Nat.succ_pos κ⟩).app ⊤ a') := by
    rw [← sub_eq_zero]
    apply truncatedJetAlgebra.eq_zero_of_weightGE L κ ⊤
    intro q _
    rw [map_sub]
    by_cases hq : q = ⟨0, Nat.succ_pos κ⟩
    · subst hq
      have h2 := congrArg (fun φ : truncatedJetAlgebra.piece L ((⟨0, Nat.succ_pos κ⟩ : Fin (κ + 1)) : ℕ) ⟶
          truncatedJetAlgebra.piece L ((⟨0, Nat.succ_pos κ⟩ : Fin (κ + 1)) : ℕ) =>
          φ.app ⊤ ((CategoryTheory.Limits.biproduct.π
            (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q) ⟨0, Nat.succ_pos κ⟩).app ⊤ a'))
        (CategoryTheory.Limits.biproduct.ι_π_self
          (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q) ⟨0, Nat.succ_pos κ⟩)
      rw [AlgebraicGeometry.Scheme.Modules.Hom.comp_app_apply'] at h2
      rw [h2]
      exact sub_self _
    · have h2 := AlgebraicGeometry.Scheme.Modules.biproduct_ι_π_ne_app_apply
        (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q) (Ne.symm hq) ⊤
        ((CategoryTheory.Limits.biproduct.π
          (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q) ⟨0, Nat.succ_pos κ⟩).app ⊤ a')
      rw [AlgebraicGeometry.Scheme.Modules.Hom.comp_app_apply'] at h2
      rw [h2, hpos q hq, sub_zero]
  -- Step 5: `S (ι₀ r) = p^♯ r`
  have hp : ∀ r : Γ(Ct.toScheme, ⊤),
      ((jetNeighborhood.proj L κ).app ⊤).hom r =
        (AlgebraicGeometry.Scheme.relativeSpec.structureHom (truncatedJetAlgebra L κ)).app ⊤
          ((CategoryTheory.Limits.biproduct.ι (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
            ⟨0, Nat.succ_pos κ⟩).app ⊤ r) := fun r =>
    (AlgebraicGeometry.Scheme.QCAlgebra.algebraMapSections_comp_sectionsUnit
      (truncatedJetAlgebra L κ) (jetNeighborhood.proj L κ)
      (AlgebraicGeometry.Scheme.relativeSpec.structureHom (truncatedJetAlgebra L κ))
      (jetNeighborhood.structureHom_isAlgebraMap L κ) ⊤ r).symm
  -- `σ₀.appLE (p⁻¹⊤) ⊤ = σ₀.appTop` (the opens `⊤`, `p⁻¹⊤`, `σ₀⁻¹p⁻¹⊤` are definitionally equal)
  have hσtop : ((jetNeighborhood.zeroSection L κ).appLE (jetNeighborhood.proj L κ ⁻¹ᵁ ⊤) ⊤ hle).hom a =
      ((jetNeighborhood.zeroSection L κ).appTop).hom a :=
    congrArg (fun φ : Γ((jetNeighborhood L κ).left, jetNeighborhood.proj L κ ⁻¹ᵁ ⊤) ⟶
        Γ(Ct.toScheme, jetNeighborhood.zeroSection L κ ⁻¹ᵁ (jetNeighborhood.proj L κ ⁻¹ᵁ ⊤)) => φ.hom a)
      (AlgebraicGeometry.Scheme.Hom.appLE_eq_app (jetNeighborhood.zeroSection L κ)
        (U := jetNeighborhood.proj L κ ⁻¹ᵁ ⊤))
  -- Assemble
  refine ha'.symm.trans (Eq.trans (congrArg _ hdecomp) ?_)
  refine (hp _).symm.trans ?_
  exact (congrArg _ hσ.symm).trans (congrArg _ hσtop)

end
