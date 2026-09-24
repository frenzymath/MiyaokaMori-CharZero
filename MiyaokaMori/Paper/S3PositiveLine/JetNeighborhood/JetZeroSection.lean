import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.RelativeSpecAffine
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.RelativeSpecUniversalProperty
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.JetNeighborhood
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.TruncatedJetAlgebra

/-! # The zero section of the jet neighbourhood

The zero section `ι : C̃ → C̃_(κ)(L)`, a closed immersion given by the augmentation `⊕_{q≤κ} L^{-q} → O_C̃`
(keeping only `q = 0`), with `p_L ∘ ι = id` (§3 of the paper).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The augmentation `ε = π_0 : ⊕_q M^{⊗q} ⟶ M^{⊗0} = 𝟙_ = O_C̃`, followed by the identity isomorphism of `(𝟙)_*`;
the universal property of the relative Spec (with `T = (C̃, 𝟙)`) turns it into the zero section. -/
noncomputable def jetNeighborhood.augmentation {k : Type u} [Field k]
    {Ct : SmoothProjectiveCurve k} (L : LineBundle Ct.toVariety) (κ : ℕ) :
    (truncatedJetAlgebra L κ).carrier ⟶
      (AlgebraicGeometry.Scheme.Modules.pushforward
          (CategoryTheory.Over.mk (CategoryTheory.CategoryStruct.id Ct.toScheme)).hom).obj
        (SheafOfModules.unit Ct.toScheme.ringCatSheaf) :=
  CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
      ⟨0, Nat.succ_pos κ⟩ ≫
    (AlgebraicGeometry.Scheme.Modules.pushforwardId Ct.toScheme).inv.app
      (SheafOfModules.unit Ct.toScheme.ringCatSheaf)

/-- The augmentation `ε = π₀ ≫ (𝟙_*)⁻¹` is a map of `O_C̃`-algebras (`IsAlgebraMapToPushforward`: two conditions on
each open `U`). Proof of `jetNeighborhood.augmentation_isAlgebraMap` below:
* at the level of morphisms, `hmul : mulHom ≫ π₀ = (π₀ ⊗ π₀) ≫ ρ_`: `mulHom = Σ_{a,b} (π_a ⊗ π_b) ≫ m_{a,b} ≫ ι_{a+b}`
  (`0` for weight `> κ`); after `π₀`, `ι_{a+b} ≫ π₀ = 0` (`biproduct.ι_π_ne`, `a + b ≠ 0`), so only the term
  `a = b = 0` survives (two applications of `Finset.sum_eq_single`), and `ι_0 ≫ π_0 = 𝟙` (`biproduct.ι_π`),
  `pieceMul L 0 0 = ρ_` (by definition);
* multiplication: evaluate on a section `a ⊗ b`; `tensorHom_tensorSections` gives `(π₀ ⊗ π₀)(a ⊗ b) = π₀a ⊗ π₀b`,
  `rightUnitor_app_tensorSections` gives `ρ_(π₀a ⊗ π₀b) = π₀b • π₀a`, and on `O_C̃(U)` the action `•` is
  multiplication, then commute;
* unit: `one = ι₀` and `ι₀ ≫ π₀ = 𝟙` (`biproduct.ι_π_self`), so `π₀(ι₀ 1) = 1`;
* `(pushforwardId C̃).inv` is the identity on sections (Mathlib `pushforwardId_inv_app_app : … = 𝟙 _ := rfl`) and
  disappears by definitional unfolding.
Source: §3 of the paper (the augmentation gives the zero section). -/
/- the projection `π₀` onto the `0`-th piece (`= 𝟙_ = O_C̃`); a local notation, which unfolds to the first factor of
   `augmentation` -/
local notation3 "π₀[" L ", " κ "]" =>
  CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
    ⟨0, Nat.succ_pos κ⟩

theorem jetNeighborhood.augmentation_isAlgebraMap {k : Type u} [Field k]
    {Ct : SmoothProjectiveCurve k} (L : LineBundle Ct.toVariety) (κ : ℕ) :
    (truncatedJetAlgebra L κ).IsAlgebraMapToPushforward
      (CategoryTheory.Over.mk (CategoryTheory.CategoryStruct.id Ct.toScheme)).hom
      (jetNeighborhood.augmentation L κ) := by
  open scoped CategoryTheory.MonoidalCategory in
  -- the terms other than `(0,0)` vanish after `π₀` (`ι_{a+b} ≫ π₀ = 0` since `a + b ≠ 0`)
  have hterm : ∀ a b : Fin (κ + 1), ¬ (a = ⟨0, Nat.succ_pos κ⟩ ∧ b = ⟨0, Nat.succ_pos κ⟩) →
      (if h : a.val + b.val ≤ κ then
        CategoryTheory.MonoidalCategory.tensorHom
            (CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q) a)
            (CategoryTheory.Limits.biproduct.π (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q) b) ≫
          truncatedJetAlgebra.pieceMul L a b ≫
          CategoryTheory.Limits.biproduct.ι (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
            ⟨a.val + b.val, Nat.lt_succ_of_le h⟩
      else 0) ≫ π₀[L, κ] = 0 := by
    intro a b hab
    split_ifs with h
    · have hne : (⟨a.val + b.val, Nat.lt_succ_of_le h⟩ : Fin (κ + 1)) ≠ ⟨0, Nat.succ_pos κ⟩ := by
        intro heq
        apply hab
        have h0 : a.val + b.val = 0 := congrArg Fin.val heq
        exact ⟨Fin.ext (Nat.eq_zero_of_add_eq_zero_right h0),
          Fin.ext (Nat.eq_zero_of_add_eq_zero_left h0)⟩
      rw [CategoryTheory.Category.assoc, CategoryTheory.Category.assoc,
        CategoryTheory.Limits.biproduct.ι_π_ne _ hne, CategoryTheory.Limits.comp_zero,
        CategoryTheory.Limits.comp_zero]
    · exact CategoryTheory.Limits.zero_comp
  -- at the level of morphisms: `mulHom ≫ π₀ = (π₀ ⊗ π₀) ≫ ρ_` (only the term `a = b = 0` survives, and
  -- `pieceMul 0 0 = ρ_`)
  have hmul : truncatedJetAlgebra.mulHom L κ ≫ π₀[L, κ] =
      CategoryTheory.MonoidalCategory.tensorHom π₀[L, κ] π₀[L, κ] ≫ (ρ_ (𝟙_ Ct.toScheme.Modules)).hom := by
    unfold truncatedJetAlgebra.mulHom
    rw [CategoryTheory.Preadditive.sum_comp,
      Finset.sum_eq_single (⟨0, Nat.succ_pos κ⟩ : Fin (κ + 1))]
    · rw [CategoryTheory.Preadditive.sum_comp,
        Finset.sum_eq_single (⟨0, Nat.succ_pos κ⟩ : Fin (κ + 1))]
      · rw [dif_pos (show ((⟨0, Nat.succ_pos κ⟩ : Fin (κ + 1)) : ℕ) +
            ((⟨0, Nat.succ_pos κ⟩ : Fin (κ + 1)) : ℕ) ≤ κ from Nat.zero_le κ),
          CategoryTheory.Category.assoc, CategoryTheory.Category.assoc,
          CategoryTheory.Limits.biproduct.ι_π,
          dif_pos (show (⟨((⟨0, Nat.succ_pos κ⟩ : Fin (κ + 1)) : ℕ) +
            ((⟨0, Nat.succ_pos κ⟩ : Fin (κ + 1)) : ℕ), Nat.lt_succ_of_le (Nat.zero_le κ)⟩ : Fin (κ + 1)) =
            ⟨0, Nat.succ_pos κ⟩ from rfl)]
        -- `eqToHom` between definitionally equal objects is `𝟙`; `pieceMul 0 0 = ρ_` by definition
        exact congrArg (fun g => CategoryTheory.CategoryStruct.comp
            (CategoryTheory.MonoidalCategory.tensorHom π₀[L, κ] π₀[L, κ]) g)
          (CategoryTheory.Category.comp_id (truncatedJetAlgebra.pieceMul L
            ((⟨0, Nat.succ_pos κ⟩ : Fin (κ + 1)) : ℕ) ((⟨0, Nat.succ_pos κ⟩ : Fin (κ + 1)) : ℕ)))
      · intro b _ hb
        exact hterm _ b (fun h => hb h.2)
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro a _ ha
      rw [CategoryTheory.Preadditive.sum_comp]
      exact Finset.sum_eq_zero (fun b _ => hterm a b (fun h => ha h.1))
    · intro h; exact absurd (Finset.mem_univ _) h
  constructor
  · intro U a b
    -- on sections: `π₀(a·b) = ρ_((π₀ ⊗ π₀)(a ⊗ b)) = π₀(b) • π₀(a) = π₀(a) π₀(b)`
    have h1 : π₀[L, κ].app U ((truncatedJetAlgebra.mulHom L κ).app U
          (AlgebraicGeometry.Scheme.Modules.tensorSections
            (truncatedJetAlgebra.obj L κ) (truncatedJetAlgebra.obj L κ) U a b)) =
        (ρ_ (𝟙_ Ct.toScheme.Modules)).hom.app U
          ((CategoryTheory.MonoidalCategory.tensorHom π₀[L, κ] π₀[L, κ]).app U
            (AlgebraicGeometry.Scheme.Modules.tensorSections
              (truncatedJetAlgebra.obj L κ) (truncatedJetAlgebra.obj L κ) U a b)) :=
      congrArg (fun f => f.app U (AlgebraicGeometry.Scheme.Modules.tensorSections
        (truncatedJetAlgebra.obj L κ) (truncatedJetAlgebra.obj L κ) U a b)) hmul
    have h2 := AlgebraicGeometry.Scheme.Modules.tensorHom_tensorSections π₀[L, κ] π₀[L, κ] U a b
    have h3 := AlgebraicGeometry.Scheme.Modules.rightUnitor_app_tensorSections
      (𝟙_ Ct.toScheme.Modules) U (π₀[L, κ].app U a) (π₀[L, κ].app U b)
    have hfin := mul_comm (id (π₀[L, κ].app U b) : Γ(Ct.toScheme, U))
      (id (π₀[L, κ].app U a) : Γ(Ct.toScheme, U))
    exact h1.trans ((congrArg ((ρ_ (𝟙_ Ct.toScheme.Modules)).hom.app U) h2).trans (h3.trans hfin))
  · intro U
    -- unit: `1 = ι₀(1)` and `ι₀ ≫ π₀ = 𝟙`
    have h' := congrArg (fun f => f.app U (1 : Γ(Ct.toScheme, U)))
      (CategoryTheory.Limits.biproduct.ι_π_self (fun q : Fin (κ + 1) => truncatedJetAlgebra.piece L q)
        ⟨0, Nat.succ_pos κ⟩)
    exact h'

/-- The zero section `ι : C̃ → C̃_(κ)(L)`, the morphism over `C̃` corresponding to the augmentation under the
universal property of the relative Spec. -/
noncomputable def jetNeighborhood.zeroSection {k : Type u} [Field k]
    {Ct : SmoothProjectiveCurve k} (L : LineBundle Ct.toVariety) (κ : ℕ) :
    Ct.toScheme ⟶ (jetNeighborhood L κ).left :=
  ((AlgebraicGeometry.Scheme.relativeSpecHomEquiv (truncatedJetAlgebra L κ)
      (CategoryTheory.Over.mk (CategoryTheory.CategoryStruct.id Ct.toScheme))).symm
    ⟨jetNeighborhood.augmentation L κ, jetNeighborhood.augmentation_isAlgebraMap L κ⟩).left

/-- `p_L ∘ ι = id`. -/
theorem jetNeighborhood.zeroSection_proj {k : Type u} [Field k]
    {Ct : SmoothProjectiveCurve k} (L : LineBundle Ct.toVariety) (κ : ℕ) :
    jetNeighborhood.zeroSection L κ ≫ jetNeighborhood.proj L κ = CategoryTheory.CategoryStruct.id _ :=
  CategoryTheory.Over.w _

/-- The zero section is a closed immersion. The zero section is a section of `p_L` (`zeroSection_proj : ι ≫ p_L = 𝟙`),
and `p_L = Spec_C̃(A) → C̃` is an affine morphism (`relativeSpec_isAffineHom`), hence separated (Mathlib
`IsSeparated.of_isAffineHom`); a section of a separated morphism is a closed immersion: `ι ≫ p_L = 𝟙` is a
closed immersion (an isomorphism), so Mathlib's `IsClosedImmersion.of_comp` (`f ≫ g` a closed immersion and `g`
separated imply `f` a closed immersion; Stacks, chapter on schemes) gives that `ι` is a closed immersion. -/
instance jetNeighborhood.zeroSection_isClosedImmersion {k : Type u} [Field k]
    {Ct : SmoothProjectiveCurve k} (L : LineBundle Ct.toVariety) (κ : ℕ) :
    AlgebraicGeometry.IsClosedImmersion (jetNeighborhood.zeroSection L κ) := by
  have : AlgebraicGeometry.IsSeparated (jetNeighborhood.proj L κ) :=
    AlgebraicGeometry.IsSeparated.of_isAffineHom
      (h := AlgebraicGeometry.Scheme.relativeSpec_isAffineHom (truncatedJetAlgebra L κ)) _
  have : AlgebraicGeometry.IsClosedImmersion
      (jetNeighborhood.zeroSection L κ ≫ jetNeighborhood.proj L κ) := by
    rw [jetNeighborhood.zeroSection_proj]; infer_instance
  exact AlgebraicGeometry.IsClosedImmersion.of_comp _ (jetNeighborhood.proj L κ)

end
