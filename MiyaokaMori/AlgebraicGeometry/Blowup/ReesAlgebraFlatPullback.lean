import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedQcAlgebraPullback
import MiyaokaMori.AlgebraicGeometry.Blowup.ReesAlgebraSheaf
import MiyaokaMori.AlgebraicGeometry.Blowup.ReesComparisonLiftIsIso

/-! # Flat base change of the Rees algebra

The core step of Stacks 0805: for `g : X₁ → X₂` flat, the pullback `g^*𝓡(I)` of the Rees algebra is
isomorphic, as a graded quasi-coherent `O_{X₁}`-algebra, to the Rees algebra `𝓡(I₁)` of the inverse
image ideal `I₁ = g⁻¹I·O_{X₁}`.

Source: Stacks 0805 (Divisors, Lemma "blowing up commutes with flat base change"); used for the point
blowups in the proof of Corollary 4.3 of the paper (§4).

## Structure

The isomorphism is assembled here from the per-degree comparison maps:

| piece | module |
|---|---|
| `ψₙ := g^*(I.powι n) ≫ ε'` and its affine-local computation (image = `Γ(U,Iⁿ)·Γ(X₁,V)`, injective for `g` flat) | `ReesComparisonAffineLocal` |
| `ψₙ` lands in `I₁ⁿ`, giving `θₙ : g^*(Iⁿ) ⟶ I₁ⁿ` with `θₙ ≫ powι = ψₙ` | `ReesComparisonMemPow` |
| `θₙ` is an isomorphism for `g` flat | `ReesComparisonLiftIsIso` |
| compatibility of `θ` with multiplication and unit; `GradedQCAlgebra` hom and iso | this module |

The compatibilities are checked after post-composing with the monomorphism `I₁.powι (m+n)`
(`hom_ext_powι`): both sides become `(ψₘ ⊗ ψₙ) ≫ (λ_ 𝟙_).hom`, because `ε'` is a morphism of
monoids `g^*O_{X₂} → O_{X₁}` (`pullback_μ_unit_leftUnitor`, a consequence of the left unitality of
the strong monoidal functor `g^*`, `Functor.Monoidal.μ_unit_leftUnitor_η`). The unit iso
`monoidalUnitIso X : 𝟙_ X.Modules ≅ SheafOfModules.unit` of `ReesAlgebraSheaf` is literally the
identity (`monoidalUnitIso_hom_eq_id`).

Technical note: `𝟙_ X.Modules` and `SheafOfModules.unit X.ringCatSheaf` are definitionally but not
syntactically equal; rewriting across that seam makes `rw` fail on the motive, so those steps use
`Eq.trans`/`congrArg` with `exact` (`pullback_map_powOne_powι_counit`) or `erw`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry CategoryTheory.MonoidalCategory

noncomputable section

/-- For a strong monoidal functor, `μ_{𝟙,𝟙} ≫ F(λ_𝟙) ≫ η = (η ⊗ η) ≫ λ_𝟙`: the counit
`η : F(𝟙) → 𝟙` is a morphism of monoids. From `LaxMonoidal.left_unitality` at `𝟙_ C` and the
naturality of the left unitor. -/
theorem CategoryTheory.Functor.Monoidal.μ_unit_leftUnitor_η {C D : Type*} [Category C] [Category D]
    [MonoidalCategory C] [MonoidalCategory D] (F : C ⥤ D) [F.Monoidal] :
    Functor.LaxMonoidal.μ F (𝟙_ C) (𝟙_ C) ≫ F.map (λ_ (𝟙_ C)).hom ≫ Functor.OplaxMonoidal.η F =
      (Functor.OplaxMonoidal.η F ⊗ₘ Functor.OplaxMonoidal.η F) ≫ (λ_ (𝟙_ D)).hom := by
  have h1 := Functor.LaxMonoidal.left_unitality F (𝟙_ C)
  have h2 : Functor.LaxMonoidal.μ F (𝟙_ C) (𝟙_ C) ≫ F.map (λ_ (𝟙_ C)).hom =
      (Functor.OplaxMonoidal.η F ▷ F.obj (𝟙_ C)) ≫ (λ_ (F.obj (𝟙_ C))).hom := by
    rw [h1, ← Category.assoc, ← MonoidalCategory.comp_whiskerRight, Functor.Monoidal.η_ε,
      MonoidalCategory.id_whiskerRight, Category.id_comp]
  rw [reassoc_of% h2, ← MonoidalCategory.leftUnitor_naturality, MonoidalCategory.tensorHom_def,
    Category.assoc]

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X₁ X₂ : AlgebraicGeometry.Scheme.{u}} (g : X₁ ⟶ X₂) (I : X₂.IdealSheafData)

/-- The unit iso of `ReesAlgebraSheaf` is the identity (`𝟙_ X.Modules` is `SheafOfModules.unit` by
definition, and `eqToHom` of a definitional equality reduces to `𝟙`). -/
theorem monoidalUnitIso_hom_eq_id (X : AlgebraicGeometry.Scheme.{u}) :
    (monoidalUnitIso X).hom = 𝟙 (SheafOfModules.unit X.ringCatSheaf) := by
  with_unfolding_all rfl

/-- The inverse of the unit iso of `ReesAlgebraSheaf` is the identity. -/
theorem monoidalUnitIso_inv_eq_id (X : AlgebraicGeometry.Scheme.{u}) :
    (monoidalUnitIso X).inv = 𝟙 (SheafOfModules.unit X.ringCatSheaf) := by
  with_unfolding_all rfl

/-- `powMulToUnit m n = (powι m ⊗ powι n) ≫ (λ_ 𝟙_).hom`: the multiplication of `O_X` on
`Iᵐ ⊗ Iⁿ` is the left unitor of the unit object. -/
theorem powMulToUnit_eq {X : AlgebraicGeometry.Scheme.{u}} (J : X.IdealSheafData) (m n : ℕ) :
    J.powMulToUnit m n = (J.powι m ⊗ₘ J.powι n) ≫ (λ_ (𝟙_ X.Modules)).hom := by
  unfold powMulToUnit
  rw [monoidalUnitIso_hom_eq_id, monoidalUnitIso_inv_eq_id, MonoidalCategory.tensorHom_id,
    MonoidalCategory.id_whiskerRight, Category.id_comp]
  rfl

/-- The degree-`0` piece is `O_X`: `powOne ≫ powι 0 = 𝟙` (`powOne_powι` of `ReesAlgebraSheaf` plus
`monoidalUnitIso_hom_eq_id`). -/
theorem powOne_powι_eq_id {X : AlgebraicGeometry.Scheme.{u}} (J : X.IdealSheafData) :
    J.powOne ≫ J.powι 0 = 𝟙 (SheafOfModules.unit X.ringCatSheaf) := by
  rw [powOne_powι, monoidalUnitIso_hom_eq_id]

/-- The oplax unit `η` of `g^*` is `(pullbackUnitIso g).hom` (from `η ≫ ε = 𝟙` and
`pullback_ε_eq : ε = (pullbackUnitIso g).inv`). -/
theorem pullback_η' :
    Functor.OplaxMonoidal.η (AlgebraicGeometry.Scheme.Modules.pullback g) =
      (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso g).hom := by
  have h := Functor.Monoidal.η_ε (AlgebraicGeometry.Scheme.Modules.pullback g)
  rw [AlgebraicGeometry.Scheme.Modules.pullback_ε_eq] at h
  exact (Iso.comp_inv_eq_id _).mp h

/-- `ε' : g^*O_{X₂} → O_{X₁}` is a morphism of monoids:
`μ ≫ g^*(mul_O) ≫ ε' = (ε' ⊗ ε') ≫ mul_O`, where `mul_O = (λ_ 𝟙_).hom`. -/
theorem pullback_μ_unit_leftUnitor :
    Functor.LaxMonoidal.μ (AlgebraicGeometry.Scheme.Modules.pullback g)
        (SheafOfModules.unit X₂.ringCatSheaf) (SheafOfModules.unit X₂.ringCatSheaf) ≫
      (AlgebraicGeometry.Scheme.Modules.pullback g).map (λ_ (𝟙_ X₂.Modules)).hom ≫
      (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso g).hom =
    ((AlgebraicGeometry.Scheme.Modules.pullbackUnitIso g).hom ⊗ₘ
        (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso g).hom) ≫ (λ_ (𝟙_ X₁.Modules)).hom := by
  rw [← pullback_η']
  exact CategoryTheory.Functor.Monoidal.μ_unit_leftUnitor_η _

/-- `μ ≫ g^*(powMulToUnit m n) ≫ ε' = (ψₘ ⊗ ψₙ) ≫ (λ_ 𝟙_).hom`. -/
theorem pullback_μ_powMulToUnit (m n : ℕ) :
    Functor.LaxMonoidal.μ (AlgebraicGeometry.Scheme.Modules.pullback g) (I.pow m) (I.pow n) ≫
        (AlgebraicGeometry.Scheme.Modules.pullback g).map (I.powMulToUnit m n) ≫
        (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso g).hom =
      (I.reesComparison g m ⊗ₘ I.reesComparison g n) ≫ (λ_ (𝟙_ X₁.Modules)).hom := by
  rw [powMulToUnit_eq, Functor.map_comp_assoc, ← Functor.LaxMonoidal.μ_natural_assoc,
    pullback_μ_unit_leftUnitor, ← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom]
  rfl

/-- `θ` is compatible with multiplication: `(g^*𝓡(I)).mul ≫ θ_{m+n} = (θₘ ⊗ θₙ) ≫ 𝓡(I₁).mul`.
Checked after post-composing with the mono `I₁.powι (m+n)`; both sides become
`(ψₘ ⊗ ψₙ) ≫ (λ_ 𝟙_).hom`. -/
theorem reesComparisonLift_map_mul (m n : ℕ) :
    (I.reesAlgebra.pullback g).mul m n ≫ I.reesComparisonLift g (m + n) =
      (I.reesComparisonLift g m ⊗ₘ I.reesComparisonLift g n) ≫ (I.comap g).reesAlgebra.mul m n := by
  apply hom_ext_powι
  dsimp only [AlgebraicGeometry.Scheme.GradedQCAlgebra.pullback, reesAlgebra]
  simp only [Category.assoc]
  rw [reesComparisonLift_powι, powMul_powι, reesComparison, ← Functor.map_comp_assoc, powMul_powι,
    pullback_μ_powMulToUnit, powMulToUnit_eq, ← Category.assoc,
    MonoidalCategory.tensorHom_comp_tensorHom, reesComparisonLift_powι, reesComparisonLift_powι]

/-- `g^*(powOne ≫ powι 0) ≫ ε' = ε'` (the degree-`0` piece is `O`, `powOne ≫ powι 0 = 𝟙`).
Proved with `Eq.trans`/`congrArg` rather than `rw`: `𝟙_ X.Modules` and `SheafOfModules.unit` are only
definitionally equal, and `rw` rejects the motive once implicit arguments mix the two. -/
theorem pullback_map_powOne_powι_counit :
    (AlgebraicGeometry.Scheme.Modules.pullback g).map (I.powOne ≫ I.powι 0) ≫
        (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso g).hom =
      (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso g).hom := by
  have e : I.powOne ≫ I.powι 0 = 𝟙 (𝟙_ X₂.Modules) := powOne_powι_eq_id I
  refine Eq.trans (congrArg (fun f => (AlgebraicGeometry.Scheme.Modules.pullback g).map f ≫
    (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso g).hom) e) ?_
  exact (congrArg (· ≫ (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso g).hom)
    ((AlgebraicGeometry.Scheme.Modules.pullback g).map_id (𝟙_ X₂.Modules))).trans
    (Category.id_comp _)

/-- `θ` is compatible with the unit: `(g^*𝓡(I)).one ≫ θ₀ = 𝓡(I₁).one`. After post-composing with
`I₁.powι 0` both sides are `𝟙`, since `ε ≫ ε' = 𝟙` (`pullback_ε_eq`). -/
theorem reesComparisonLift_map_one :
    (I.reesAlgebra.pullback g).one ≫ I.reesComparisonLift g 0 = (I.comap g).reesAlgebra.one := by
  apply hom_ext_powι
  dsimp only [AlgebraicGeometry.Scheme.GradedQCAlgebra.pullback, reesAlgebra]
  simp only [Category.assoc]
  rw [reesComparisonLift_powι, powOne_powι_eq_id, reesComparison, ← Functor.map_comp_assoc,
    pullback_map_powOne_powι_counit, AlgebraicGeometry.Scheme.Modules.pullback_ε_eq, Iso.inv_hom_id]
  rfl

/-- The graded-algebra morphism `g^*𝓡(I) ⟶ 𝓡(I.comap g)` with components `θₙ`. -/
def reesComparisonHom : I.reesAlgebra.pullback g ⟶ (I.comap g).reesAlgebra :=
  ⟨fun n => I.reesComparisonLift g n, I.reesComparisonLift_map_mul g, I.reesComparisonLift_map_one g⟩

end AlgebraicGeometry.Scheme.IdealSheafData

namespace AlgebraicGeometry.Scheme.GradedQCAlgebra

private theorem hom_ext' {X : AlgebraicGeometry.Scheme.{u}}
    {S T : X.GradedQCAlgebra} (φ ψ : S ⟶ T)
    (h : ∀ m, φ.app m = ψ.app m) : φ = ψ := by
  cases φ with
  | mk φ hmul hone =>
    cases ψ with
    | mk ψ hmul' hone' =>
      simp only at h
      cases funext h
      rfl

/-- A morphism of graded quasi-coherent algebras whose components are isomorphisms is an
isomorphism (the componentwise inverse is compatible with `mul` and `one`). -/
theorem isIso_of_app {X : AlgebraicGeometry.Scheme.{u}} {S T : X.GradedQCAlgebra} (φ : S ⟶ T)
    (h : ∀ m, IsIso (φ.app m)) : IsIso φ := by
  refine ⟨⟨⟨fun m => inv (φ.app m), fun m n => ?_, ?_⟩, ?_, ?_⟩⟩
  · rw [IsIso.comp_inv_eq, Category.assoc, φ.map_mul, ← Category.assoc,
      MonoidalCategory.tensorHom_comp_tensorHom, IsIso.inv_hom_id, IsIso.inv_hom_id,
      MonoidalCategory.tensorHom_id, MonoidalCategory.id_whiskerRight, Category.id_comp]
  · rw [IsIso.comp_inv_eq, φ.map_one]
  · exact hom_ext' _ _ fun m => IsIso.hom_inv_id (φ.app m)
  · exact hom_ext' _ _ fun m => IsIso.inv_hom_id (φ.app m)

end AlgebraicGeometry.Scheme.GradedQCAlgebra

/-- **Flat base change of the Rees algebra** (the algebraic heart of Stacks 0805).
For `g : X₁ ⟶ X₂` flat and `I` a (quasi-coherent) ideal sheaf on `X₂`, the Rees algebra of the
inverse-image ideal `I.comap g` is isomorphic, as a graded quasi-coherent `O_{X₁}`-algebra, to the
pullback `g^*` of the Rees algebra of `I`.

Source: Stacks 0805 (first paragraph of the proof: "the Rees algebra of `g⁻¹I·O_{X'}` is
`g^*(⊕ Iⁿ)` because `g` is flat").

Proof (see the module docstring): the componentwise comparison
`θₙ = reesComparisonLift : g^*(Iⁿ) ⟶ I₁ⁿ` is an isomorphism for `g`
flat (`reesComparisonLift_isIso`) and is compatible with
multiplication and unit (`reesComparisonLift_map_mul`, `reesComparisonLift_map_one`), so
`reesComparisonHom : g^*𝓡(I) ⟶ 𝓡(I₁)` is an isomorphism of graded algebras
(`GradedQCAlgebra.isIso_of_app`); take its inverse.

Edge cases: `n = 0`: `θ₀ = ε' : g^*O ≅ O`. `I = ⊥`: `⊥.comap g = ⊥`, both sides are `O ⊕ 0 ⊕ ⋯`.
`X₁ = ∅`: both sides are the zero algebra. Flatness is necessary:
`g : Spec k[x]/(x) → Spec k[x]`, `I = (x)`: `g^*I ≅ k ≠ 0` while `I.comap g = 0`. -/
theorem AlgebraicGeometry.Scheme.IdealSheafData.reesAlgebra_comap_iso_pullback_of_flat
    {X₁ X₂ : AlgebraicGeometry.Scheme.{u}} (g : X₁ ⟶ X₂) [AlgebraicGeometry.Flat g]
    (I : X₂.IdealSheafData) :
    Nonempty ((I.comap g).reesAlgebra ≅ I.reesAlgebra.pullback g) := by
  have : IsIso (I.reesComparisonHom g) :=
    AlgebraicGeometry.Scheme.GradedQCAlgebra.isIso_of_app _ (I.reesComparisonLift_isIso g)
  exact ⟨(asIso (I.reesComparisonHom g)).symm⟩

end
