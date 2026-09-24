import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProjectiveMorphism
import MiyaokaMori.AlgebraicGeometry.Blowup.Stacks01og
import MiyaokaMori.AlgebraicGeometry.Blowup.BlowupIsoAwayFromCenterAffineLeaf
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.FiniteTypeOfFiniteAffineSections
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.ModulesExactIffLocallyLift
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.SheafSymmetricAlgebra

/-! # Stacks 02NS: the blowup of a Noetherian scheme is a projective morphism

On a Noetherian scheme `X`, the blowup `b : Bl_I X → X` along a quasi-coherent ideal sheaf `I` is a
projective morphism.

Source: Stacks 02NS ("the morphism `b` is projective"); Stacks 01OG (the blowup is the relative Proj
of the Rees algebra); Hartshorne II.7.16 (c).

Proof: in the definition of `IsProjectiveMorphism` take `S := I.reesAlgebra`, `i := 𝟙`. The two
non-trivial obligations are

* `I.reesAlgebra.GeneratedInDegreeOne` (`reesAlgebra_generatedInDegreeOne`, valid on every scheme):
  `mulPowOne 1` is an isomorphism by the unit axiom `one_mul`, and for `ℓ ≥ 1`
  `mulPowOne (ℓ+1) = iso ≫ (mulPowOne ℓ ▷ I¹) ≫ mul ℓ 1`, where `mul ℓ 1 : Iˡ ⊗ I → Iˡ⁺¹` is an
  epimorphism (`epi_powMul_one`): on an affine open `V` every element of `I(V)^{ℓ+1} = I(V)^ℓ · I(V)`
  is a sum of products `a·b`, and `a·b` is the image of the pure tensor `a ⊗ b` because the Rees
  multiplication on sections is the ring multiplication (`coe_reesAlgebra_sectionsGMul`);
  membership of `a` in `Γ(V, Iˡ)` follows from Mathlib's `IdealSheafData.map_ideal`.
* `(I.pow 1).IsFiniteType` (`pow_one_isFiniteType`, needs only `IsLocallyNoetherian X`):
  `Γ(U, I¹)` is a submodule of the Noetherian ring `Γ(X, U)` for affine `U`, hence finitely
  generated, and `Modules.isFiniteType_of_finite_affine_sections` (Stacks 01PB) concludes.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry CategoryTheory.MonoidalCategory

noncomputable section

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : AlgebraicGeometry.Scheme.{u}} (I : X.IdealSheafData)

/-- An element of `I(V)^m` (`V` affine) is a section of `Γ(V, Iᵐ)`: for every affine `W ≤ V`,
`I(W) = I(V)·O(W)` (Mathlib `IdealSheafData.map_ideal`), so `s|_W ∈ (I(V)^m)·O(W) = I(W)^m`. -/
theorem mem_powSubmodule_of_mem_pow (V : X.affineOpens) (m : ℕ) (s : Γ(X, V))
    (hs : s ∈ I.ideal V ^ m) : s ∈ (I.powSubmodule m).obj (op (V : X.Opens)) := by
  intro W hW
  rw [← I.map_ideal (U := W) (V := V) hW, ← Ideal.map_pow]
  exact Ideal.mem_map_of_mem _ hs

/-- The Rees multiplication `powMul m n` on a pure tensor `a ⊗ b` has underlying section `a·b`
(this is `coe_reesAlgebra_sectionsGMul`). -/
theorem coe_powMul_app_tensorSections (U : X.Opens) (m n : ℕ)
    (a : Γ(I.pow m, U)) (b : Γ(I.pow n, U)) :
    (((I.powMul m n).app U
        (AlgebraicGeometry.Scheme.Modules.tensorSections (I.pow m) (I.pow n) U a b)).1 : Γ(X, U)) =
      (show Γ(X, U) from a.1) * (show Γ(X, U) from b.1) :=
  I.coe_reesAlgebra_sectionsGMul U m n a b

/-- A section of `Γ(V, Iᵐ)` over an affine open `V` lies in `I(V)^m` (take `W := V` in the
definition of `powSubmodule`). -/
theorem mem_ideal_pow_of_mem_powSubmodule (V : X.affineOpens) (m : ℕ) (s : Γ(X, V))
    (hs : s ∈ (I.powSubmodule m).obj (op (V : X.Opens))) : s ∈ I.ideal V ^ m := by
  simpa using hs V le_rfl

/-- Every element of `I(V)^m · I(V)` is the underlying section of `powMul m 1` applied to some
section of `Iᵐ ⊗ I¹` over the affine open `V` (induction on the product, `Submodule.mul_induction_on`,
pure tensors by `coe_powMul_app_tensorSections`). -/
theorem exists_powMul_app_eq_of_mem_mul (V : X.affineOpens) (m : ℕ) (z : Γ(X, V))
    (hz : z ∈ I.ideal V ^ m * I.ideal V) :
    ∃ y : Γ(I.pow m ⊗ I.pow 1, (V : X.Opens)),
      (((I.powMul m 1).app (V : X.Opens) y).1 : Γ(X, V)) = z := by
  refine Submodule.mul_induction_on hz ?_ ?_
  · intro a ha b hb
    refine ⟨AlgebraicGeometry.Scheme.Modules.tensorSections (I.pow m) (I.pow 1) V
      ⟨a, I.mem_powSubmodule_of_mem_pow V m a ha⟩
      ⟨b, I.mem_powSubmodule_of_mem_pow V 1 b (by rwa [pow_one])⟩, ?_⟩
    exact I.coe_powMul_app_tensorSections V m 1 _ _
  · rintro x y ⟨x', hx'⟩ ⟨y', hy'⟩
    refine ⟨x' + y', ?_⟩
    rw [map_add]
    exact congrArg₂ (· + ·) hx' hy'

/-- `Iᵐ ⊗ I → Iᵐ⁺¹` is an epimorphism of `O_X`-modules: sections are locally (on affine opens)
in the image, by `exists_powMul_app_eq_of_mem_mul` and `I(V)^{m+1} = I(V)^m · I(V)`. -/
theorem epi_powMul_one (m : ℕ) : Epi (I.powMul m 1) := by
  rw [AlgebraicGeometry.Scheme.Modules.epi_iff_locally_surjective_sections]
  intro U s p hp
  obtain ⟨V, hV, hpV, hVU⟩ := exists_isAffineOpen_mem_and_subset (U := U) (x := p) hp
  have hVU' : V ≤ U := hVU
  refine ⟨V, hVU', hpV, ?_⟩
  have ht : (((I.pow (m + 1)).presheaf.map (homOfLE hVU').op s).1 : Γ(X, V)) ∈
      I.ideal ⟨V, hV⟩ ^ (m + 1) :=
    I.mem_ideal_pow_of_mem_powSubmodule ⟨V, hV⟩ (m + 1) _
      ((I.pow (m + 1)).presheaf.map (homOfLE hVU').op s).2
  rw [pow_succ] at ht
  obtain ⟨y, hy⟩ := I.exists_powMul_app_eq_of_mem_mul ⟨V, hV⟩ m _ ht
  exact ⟨y, Subtype.ext hy⟩

/-- The Rees algebra `⊕ Iⁿ` is generated in degree one. -/
theorem reesAlgebra_generatedInDegreeOne : I.reesAlgebra.GeneratedInDegreeOne := by
  have key : ∀ ℓ : ℕ, Epi (I.reesAlgebra.mulPowOne (ℓ + 1)) := by
    intro ℓ
    induction ℓ with
    | zero =>
      -- `mulPowOne 1 = iso ≫ (one ▷ I¹) ≫ mul 0 1`, and `(one ▷ I¹) ≫ mul 0 1 = λ_ ≫ eqToHom`
      -- is an isomorphism by the unit axiom.
      have h1 : Epi ((I.reesAlgebra.one ▷ I.reesAlgebra.part 1) ≫ I.reesAlgebra.mul 0 1) := by
        rw [I.reesAlgebra.one_mul 1]; infer_instance
      exact @epi_comp _ _ _ _ _ _ (@IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_hom _)) _ h1
    | succ ℓ ih =>
      have h2 : Epi (I.reesAlgebra.mulPowOne (ℓ + 1) ▷ I.reesAlgebra.part 1) :=
        AlgebraicGeometry.Scheme.Modules.epi_whiskerRight_of_epi _ _
      have h3 : Epi (I.reesAlgebra.mul (ℓ + 1) 1) := I.epi_powMul_one (ℓ + 1)
      exact @epi_comp _ _ _ _ _ _ (@IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_hom _)) _
        (@epi_comp _ _ _ _ _ _ h2 _ h3)
  intro ℓ hℓ
  obtain ⟨k, rfl⟩ : ∃ k, ℓ = k + 1 := ⟨ℓ - 1, by omega⟩
  exact key k

/-- The inclusion `Γ(U, Iᵐ) → Γ(X, U)`, `s ↦ s.1`, as a `Γ(X, U)`-linear map (both structure
maps are definitional: `powSubmodule` is a sub-presheaf of modules of `O_X`). -/
def powSectionsIncl (U : X.Opens) (m : ℕ) : Γ(I.pow m, U) →ₗ[Γ(X, U)] Γ(X, U) where
  toFun s := s.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The inclusion `powSectionsIncl` is injective. -/
theorem powSectionsIncl_injective (U : X.Opens) (m : ℕ) :
    Function.Injective (I.powSectionsIncl U m) := fun _ _ h => Subtype.ext h

/-- On an affine open `U` of a locally Noetherian scheme, `Γ(U, Iᵐ)` is a finitely generated
`Γ(X, U)`-module: it embeds into the Noetherian ring `Γ(X, U)` (`Module.Finite.of_injective`). -/
theorem finite_pow_sections [AlgebraicGeometry.IsLocallyNoetherian X] {U : X.Opens}
    (hU : AlgebraicGeometry.IsAffineOpen U) (m : ℕ) : Module.Finite Γ(X, U) Γ(I.pow m, U) := by
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  exact Module.Finite.of_injective (I.powSectionsIncl U m) (I.powSectionsIncl_injective U m)

/-- On a locally Noetherian scheme `I¹ = I` is of finite type: on an affine open `U`,
`Γ(U, I¹) ⊆ Γ(X, U)` is a submodule of a Noetherian ring, hence finitely generated
(`finite_pow_sections`), and Stacks 01PB (`isFiniteType_of_finite_affine_sections`) applies. -/
theorem pow_one_isFiniteType [AlgebraicGeometry.IsLocallyNoetherian X] :
    (I.pow 1).IsFiniteType := by
  have := I.pow_isQuasicoherent 1
  refine AlgebraicGeometry.Scheme.Modules.isFiniteType_of_finite_affine_sections (I.pow 1)
    fun x => ?_
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) trivial
  exact ⟨U, hU, hxU, I.finite_pow_sections hU 1⟩

end AlgebraicGeometry.Scheme.IdealSheafData

/-- **Stacks 02NS.** On a Noetherian scheme the blowup along a quasi-coherent ideal sheaf is a
projective morphism.

Proof: by definition (Stacks 01OG) `Scheme.blowup I = Scheme.relativeProj I.reesAlgebra`, so in the
definition of `IsProjectiveMorphism`
(`∃ S i, S.GeneratedInDegreeOne ∧ (S.part 1).IsFiniteType ∧ IsClosedImmersion i ∧
i ≫ (relativeProj S).hom = f`) take `S := I.reesAlgebra` and `i := 𝟙`. Three things are needed:

1. `I.reesAlgebra.GeneratedInDegreeOne`: `part n = I.pow n`, and `Iⁿ⁺¹ = Iⁿ · I`, so the
   multiplication `part 1 ⊗ part n ⟶ part (n+1)` is surjective on every affine open (on `U` this is
   `Ideal.pow_succ`: `I(U)ⁿ⁺¹ = I(U)ⁿ · I(U)`, both sides being spans of products of
   `Γ(X, U)`-modules); this is `reesAlgebra_generatedInDegreeOne`, valid on every scheme.
2. `(I.reesAlgebra.part 1).IsFiniteType`: `part 1 = I.pow 1 = I`; `X` Noetherian implies `Γ(X, U)`
   Noetherian for every affine open `U`, so the ideal `I(U)` is finitely generated
   (`IsNoetherian.finite`), i.e. `I` is of finite type; this is `pow_one_isFiniteType`.
3. `IsClosedImmersion (𝟙 _)` (an isomorphism is a closed immersion, a Mathlib instance) and
   `𝟙 ≫ (relativeProj I.reesAlgebra).hom = (blowup I).hom` (after `Category.id_comp` both sides
   agree by definition). -/
theorem AlgebraicGeometry.Scheme.blowup_isProjectiveMorphism {X : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsNoetherian X] (I : X.IdealSheafData) :
    AlgebraicGeometry.IsProjectiveMorphism (AlgebraicGeometry.Scheme.blowup I).hom := by
  show AlgebraicGeometry.IsProjectiveMorphism
    (AlgebraicGeometry.Scheme.relativeProj I.reesAlgebra).hom
  exact ⟨⟨I.reesAlgebra, 𝟙 _, I.reesAlgebra_generatedInDegreeOne, I.pow_one_isFiniteType,
    inferInstance, Category.id_comp _⟩⟩

end
