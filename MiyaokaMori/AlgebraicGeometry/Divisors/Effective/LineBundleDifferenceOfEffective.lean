import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.ModulesBiproductLocallyFree
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.LocallyFreeQuasicoherent
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesMonoidalZero
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.TensorRightInvertibleEquivalence
import MiyaokaMori.AlgebraicGeometry.Modules.Ample.AmpleFiniteTypeQuotient
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProjectiveOverField
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierCanonicalSection
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierOfSection
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.ModulesUnitHomTopSection
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.IsLineBundleZpow
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.NonzeroSectionRegular
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModuleDualFunctor

/-! # Every line bundle on an integral projective scheme is a difference of effective divisors

On an integral projective scheme every line bundle is a difference of two effective Cartier divisors:
`L ≅ O(A) ⊗ O(B)^∨`. Sources: Stacks 0FVC, 01X0; Lazarsfeld, proof of Theorem 1.2.23 ("write
`L ≡ A − B` with `A`, `B` very ample effective").

Route formalized (using an ample rather than a very ample bundle): let `H` be an ample line bundle on `X` (`isProjectiveOver_iff_isProper_and_isAmple`).
Stacks 01Q3 (1)⇒(8) (`IsAmple.exists_epi_biproduct_zpow_neg`) applied once to the finite type
quasi-coherent module `L ⊕ O_X` gives `n > 0` and an epimorphism `⨁_{j<r} H^{-n} ↠ L ⊕ O_X`; composing
with the two projections gives epimorphisms onto `L` and onto `O_X` **with the same `n`**. Since `X` is
nonempty, `L` and `O_X` are not zero objects, so some component `φ_A : H^{-n} ⟶ L`, `φ_B : H^{-n} ⟶ O_X`
is nonzero. With `M := H^{-n}` and `M^∨` its dual, `φ ≠ 0` gives a nonzero global section of `N ⊗ M^∨`
(`N ∈ {L, O_X}`): the morphism `O_X ≅ M ⊗ M^∨ → N ⊗ M^∨` is nonzero because `− ⊗ M^∨` is faithful
(an equivalence, `isEquivalence_tensorRight_of_isLineBundle`) and preserves `0`
(`zeroMorphism_whiskerRight`). On the integral scheme `X` a nonzero section is regular
(`isRegular_germ_of_ne_zero`), so Stacks 01X0 (`exists_effectiveCartierDivisor_of_regular_section`) gives
effective Cartier divisors `A`, `B` with `O(A) ≅ L ⊗ M^∨`, `O(B) ≅ O_X ⊗ M^∨ ≅ M^∨`; finally
`O(A) ⊗ O(B)^∨ ≅ (L ⊗ M^∨) ⊗ (M^∨)^∨ ≅ L ⊗ (M^∨ ⊗ (M^∨)^∨) ≅ L` (Stacks 01CT, `tensor_dual_iso`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry CategoryTheory.MonoidalCategory

noncomputable section

/-- A line bundle on a nonempty scheme is not a zero object: a local frame `f` over a nonempty open `W`
(`exists_local_frame`) satisfies `1 • f = f` and `0 • f = 0` with `r ↦ r • f` injective, so `f = 0`
(forced by `𝟙 N = 0`) would give `1 = 0` in the nontrivial ring `Γ(X, W)`. -/
theorem AlgebraicGeometry.Scheme.Modules.not_isZero_of_isLineBundle {X : AlgebraicGeometry.Scheme.{u}}
    [Nonempty X] (N : X.Modules) [N.IsLineBundle] : ¬ CategoryTheory.Limits.IsZero N := by
  intro hz
  obtain ⟨W, hxW, f, hf⟩ :=
    MiyaokaMori.EffectiveCartierCanonicalSection.exists_local_frame N (Classical.arbitrary X)
  have hinj := (hf W le_rfl).1
  have hid : (𝟙 N : N ⟶ N) = 0 := hz.eq_of_src _ _
  have hg : (N.presheaf.map (homOfLE (le_refl W)).op f : Γ(N, W)) = 0 := by
    have h1 : ((𝟙 N : N ⟶ N).val.app (Opposite.op W)).hom
        (N.presheaf.map (homOfLE (le_refl W)).op f : Γ(N, W)) =
        (N.presheaf.map (homOfLE (le_refl W)).op f : Γ(N, W)) := rfl
    have h2 : ((0 : N ⟶ N).val.app (Opposite.op W)).hom
        (N.presheaf.map (homOfLE (le_refl W)).op f : Γ(N, W)) = 0 := rfl
    rw [← h1, hid]
    exact h2
  have h10 : (1 : Γ(X, W)) = 0 := by
    apply hinj
    show (1 : Γ(X, W)) • (N.presheaf.map (homOfLE (le_refl W)).op f : Γ(N, W)) =
      (0 : Γ(X, W)) • (N.presheaf.map (homOfLE (le_refl W)).op f : Γ(N, W))
    rw [hg, smul_zero, smul_zero]
  have : Nonempty W := ⟨⟨_, hxW⟩⟩
  exact one_ne_zero h10

/-- An epimorphism from a finite biproduct onto a non-zero object has a nonzero component. -/
theorem CategoryTheory.Limits.exists_biproduct_ι_comp_ne_zero {C : Type u} [Category.{v} C]
    [HasZeroMorphisms C] {J : Type w} (f : J → C) [HasBiproduct f] {N : C}
    (q : ⨁ f ⟶ N) [Epi q] (hN : ¬ IsZero N) :
    ∃ j, biproduct.ι f j ≫ q ≠ 0 := by
  by_contra h
  have hq : q = 0 := biproduct.hom_ext' _ _ (fun j => by
    rw [comp_zero]
    by_contra hj
    exact h ⟨j, hj⟩)
  have : Epi (0 : ⨁ f ⟶ N) := by rw [← hq]; infer_instance
  exact hN (IsZero.of_epi_zero (⨁ f) N)

/-- A nonzero morphism `φ : M ⟶ N` from a line bundle `M` gives a nonzero global section of `N ⊗ M^∨`:
the composite `O_X ≅ M ⊗ M^∨ ⟶ N ⊗ M^∨` (`φ ▷ M^∨`) is nonzero because `− ⊗ M^∨` is faithful
(`isEquivalence_tensorRight_of_isLineBundle`) and sends `0` to `0` (`zeroMorphism_whiskerRight`), and
`Hom(O_X, −) ≃ Γ(X, −)` (`unitHomEquivTop`) sends `0` to `0`. -/
theorem AlgebraicGeometry.Scheme.Modules.exists_ne_zero_section_tensorObj_dual_of_hom_ne_zero
    {X : AlgebraicGeometry.Scheme.{u}} (M N : X.Modules) [M.IsLineBundle] (φ : M ⟶ N) (hφ : φ ≠ 0) :
    ∃ σ : Γ((CategoryTheory.MonoidalCategoryStruct.tensorObj (C := X.Modules) N
        (AlgebraicGeometry.Scheme.Modules.dual M)), ⊤), σ ≠ 0 := by
  obtain ⟨u⟩ := AlgebraicGeometry.Scheme.Modules.nonempty_tensorObj_dual_iso_tensorUnit M
  -- `ψ' : 𝟙_ ⟶ N ⊗ M^∨`, and `ψ` is the same morphism with source `O_X`
  let ψ' : 𝟙_ X.Modules ⟶
      CategoryTheory.MonoidalCategoryStruct.tensorObj (C := X.Modules) N
        (AlgebraicGeometry.Scheme.Modules.dual M) :=
    u.inv ≫ (φ ▷ AlgebraicGeometry.Scheme.Modules.dual M)
  let ψ : SheafOfModules.unit X.ringCatSheaf ⟶
      CategoryTheory.MonoidalCategoryStruct.tensorObj (C := X.Modules) N
        (AlgebraicGeometry.Scheme.Modules.dual M) :=
    eqToHom (AlgebraicGeometry.Scheme.Modules.unit_eq_tensorUnit X) ≫ ψ'
  refine ⟨AlgebraicGeometry.Scheme.Modules.topSectionOfHom _ ψ, fun h0 => hφ ?_⟩
  have hψ : ψ = 0 := by
    apply (AlgebraicGeometry.Scheme.Modules.unitHomEquivTop
      (CategoryTheory.MonoidalCategoryStruct.tensorObj (C := X.Modules) N
        (AlgebraicGeometry.Scheme.Modules.dual M))).injective
    show AlgebraicGeometry.Scheme.Modules.topSectionOfHom _ ψ =
      AlgebraicGeometry.Scheme.Modules.topSectionOfHom _ 0
    rw [h0]; rfl
  have hψ' : ψ' = 0 := by
    have h1 : eqToHom (AlgebraicGeometry.Scheme.Modules.unit_eq_tensorUnit X) ≫ ψ' =
        eqToHom (AlgebraicGeometry.Scheme.Modules.unit_eq_tensorUnit X) ≫ 0 := by
      rw [comp_zero]; exact hψ
    exact (cancel_epi _).1 h1
  have hw : φ ▷ AlgebraicGeometry.Scheme.Modules.dual M = 0 := by
    have h1 : u.inv ≫ (φ ▷ AlgebraicGeometry.Scheme.Modules.dual M) = u.inv ≫ 0 := by
      rw [comp_zero]; exact hψ'
    exact (cancel_epi _).1 h1
  have := AlgebraicGeometry.Scheme.Modules.isEquivalence_tensorRight_of_isLineBundle
    (AlgebraicGeometry.Scheme.Modules.dual M)
  apply (MonoidalCategory.tensorRight (AlgebraicGeometry.Scheme.Modules.dual M)).map_injective
  show φ ▷ AlgebraicGeometry.Scheme.Modules.dual M = (0 : M ⟶ N) ▷ AlgebraicGeometry.Scheme.Modules.dual M
  rw [hw, AlgebraicGeometry.Scheme.Modules.zeroMorphism_whiskerRight]

/-- On an integral projective scheme every line bundle is a difference of two effective Cartier
divisors: `L ≅ O(A) ⊗ O(B)^∨` (Stacks 0FVC, 01X0; Lazarsfeld, Theorem 1.2.23).
Proof route: see the module docstring (Stacks 01Q3 (1)⇒(8) applied once to `L ⊕ O_X`, nonzero components,
sections of `N ⊗ (H^{-n})^∨`, Stacks 01X0, Stacks 01CT). -/
theorem AlgebraicGeometry.exists_effectiveCartierDivisor_sub {k : Type u} [Field k]
    (X : AlgebraicGeometry.Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.IsIntegral X] (hX : IsProjectiveOver k X) (L : X.Modules) [L.IsLineBundle] :
    ∃ A B : AlgebraicGeometry.EffectiveCartierDivisor X,
      Nonempty (L ≅ AlgebraicGeometry.Scheme.Modules.tensor A.lineBundle
        (AlgebraicGeometry.Scheme.Modules.dual B.lineBundle)) := by
  obtain ⟨-, H, hHL, hH⟩ := (isProjectiveOver_iff_isProper_and_isAmple k X).1 hX
  have : H.IsLineBundle := hHL
  let O : X.Modules := SheafOfModules.unit X.ringCatSheaf
  have hO : O.IsLineBundle := SheafOfModules.IsLineBundle.unit X
  -- the finite type quasi-coherent module `L ⊕ O_X`
  let F : Bool → X.Modules := fun b => bif b then L else O
  have hLF : ∀ b, (F b).IsLocallyFree := fun b => by
    cases b
    · show O.IsLocallyFree; infer_instance
    · show L.IsLocallyFree; infer_instance
  have hFT : ∀ b, (F b).IsFiniteType := fun b => by
    cases b
    · show O.IsFiniteType; infer_instance
    · show L.IsFiniteType; infer_instance
  have : (⨁ F).IsQuasicoherent := AlgebraicGeometry.Scheme.Modules.isQuasicoherent_of_isLocallyFree _
  obtain ⟨n, -, r, p, hp⟩ := AlgebraicGeometry.IsAmple.exists_epi_biproduct_zpow_neg H hH (⨁ F)
  have := hp
  -- `M := H^{-n}`, `Mᵛ := dual M`
  let M : X.Modules := H ^ (-(n : ℤ))
  have : M.IsLineBundle := SheafOfModules.IsLineBundle.zpow H _
  let Mv : X.Modules := AlgebraicGeometry.Scheme.Modules.dual M
  have : Mv.IsLineBundle := SheafOfModules.IsLineBundle.dual M
  -- nonzero components `H^{-n} ⟶ L` and `H^{-n} ⟶ O_X`
  have hL0 : ¬ IsZero (F true) := AlgebraicGeometry.Scheme.Modules.not_isZero_of_isLineBundle L
  have hO0 : ¬ IsZero (F false) :=
    AlgebraicGeometry.Scheme.Modules.not_isZero_of_isLineBundle O
  obtain ⟨jA, hjA⟩ := CategoryTheory.Limits.exists_biproduct_ι_comp_ne_zero _
    (p ≫ biproduct.π F true) hL0
  obtain ⟨jB, hjB⟩ := CategoryTheory.Limits.exists_biproduct_ι_comp_ne_zero _
    (p ≫ biproduct.π F false) hO0
  -- nonzero sections of `L ⊗ Mᵛ` and `O_X ⊗ Mᵛ`
  obtain ⟨σA, hσA⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_ne_zero_section_tensorObj_dual_of_hom_ne_zero M L _ hjA
  obtain ⟨σB, hσB⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_ne_zero_section_tensorObj_dual_of_hom_ne_zero M O _ hjB
  have : (L ⊗ Mv).IsLineBundle :=
    SheafOfModules.IsLineBundle.of_iso (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj L Mv)
  have : (O ⊗ Mv).IsLineBundle :=
    SheafOfModules.IsLineBundle.of_iso (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj O Mv)
  -- Stacks 01X0
  obtain ⟨A, -, ⟨eA⟩⟩ := AlgebraicGeometry.exists_effectiveCartierDivisor_of_regular_section (L ⊗ Mv) σA
    (isRegular_germ_of_ne_zero (L ⊗ Mv) σA hσA)
  obtain ⟨B, -, ⟨eB⟩⟩ := AlgebraicGeometry.exists_effectiveCartierDivisor_of_regular_section (O ⊗ Mv) σB
    (isRegular_germ_of_ne_zero (O ⊗ Mv) σB hσB)
  -- `L ≅ (L ⊗ Mᵛ) ⊗ (Mᵛ)^∨ ≅ O(A) ⊗ O(B)^∨`
  obtain ⟨d⟩ := AlgebraicGeometry.Scheme.Modules.nonempty_tensorObj_dual_iso_tensorUnit Mv
  refine ⟨A, B, ⟨?_⟩⟩
  let uB : (O ⊗ Mv) ≅ Mv :=
    MonoidalCategory.whiskerRightIso
      (eqToIso (AlgebraicGeometry.Scheme.Modules.unit_eq_tensorUnit X)) Mv ≪≫ λ_ Mv
  let dB : AlgebraicGeometry.Scheme.Modules.dual B.lineBundle ≅
      AlgebraicGeometry.Scheme.Modules.dual Mv :=
    (AlgebraicGeometry.Scheme.Modules.moduleSheafDualIso (eB ≪≫ uB)).symm
  exact (ρ_ L).symm ≪≫ MonoidalCategory.whiskerLeftIso L d.symm ≪≫
    (α_ L Mv (AlgebraicGeometry.Scheme.Modules.dual Mv)).symm ≪≫
    MonoidalCategory.tensorIso eA.symm dB.symm ≪≫
    (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj A.lineBundle
      (AlgebraicGeometry.Scheme.Modules.dual B.lineBundle)).symm

open AlgebraicGeometry in

/-- The version with sections: `exists_effectiveCartierDivisor_sub` only gives the divisors `A`, `B`,
while Stacks 02SQ (`firstChernClass_cap_fundamentalClass_of_regular_section`) and the restriction
sequence (`shortExact_of_regular_section`) take a line bundle with a nonzero regular section. Here the
sections `s`, `t` of `O(A)`, `O(B)` are given as well: nonzero, regular, and with zero schemes exactly
`A`, `B` (so `(idealSheafOfSection O(A) s).cycle d` can be rewritten as `A.idealSheaf.cycle d`).
`s`, `t` are the canonical sections `1_A`, `1_B`. -/
theorem AlgebraicGeometry.exists_effectiveCartierDivisor_sub_with_sections {k : Type u} [Field k]
    (X : AlgebraicGeometry.Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.IsIntegral X] (hX : IsProjectiveOver k X) (L : X.Modules) [L.IsLineBundle] :
    ∃ (A B : AlgebraicGeometry.EffectiveCartierDivisor X)
      (s : Γ(A.lineBundle, ⊤)) (t : Γ(B.lineBundle, ⊤)),
      s ≠ 0 ∧ t ≠ 0 ∧
      (∀ U : X.Opens, Function.Injective (fun r : Γ(X, U) =>
        r • ((A.lineBundle.presheaf.map (CategoryTheory.homOfLE (le_top : U ≤ ⊤)).op).hom s :
          Γ(A.lineBundle, U)))) ∧
      (∀ U : X.Opens, Function.Injective (fun r : Γ(X, U) =>
        r • ((B.lineBundle.presheaf.map (CategoryTheory.homOfLE (le_top : U ≤ ⊤)).op).hom t :
          Γ(B.lineBundle, U)))) ∧
      AlgebraicGeometry.Scheme.idealSheafOfSection A.lineBundle s = A.idealSheaf ∧
      AlgebraicGeometry.Scheme.idealSheafOfSection B.lineBundle t = B.idealSheaf ∧
      Nonempty (L ≅ AlgebraicGeometry.Scheme.Modules.tensor A.lineBundle
        (AlgebraicGeometry.Scheme.Modules.dual B.lineBundle)) := by
  obtain ⟨A, B, hL⟩ := AlgebraicGeometry.exists_effectiveCartierDivisor_sub X hX L
  exact ⟨A, B, A.canonicalSection, B.canonicalSection, A.canonicalSection_ne_zero,
    B.canonicalSection_ne_zero, A.canonicalSection_regular, B.canonicalSection_regular,
    A.idealSheafOfSection_canonicalSection, B.idealSheafOfSection_canonicalSection, hL⟩

end
