import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.RelativeSpecUniversalProperty
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.RelativeSpecStructureIso

/-! # The morphism to a relative Spec induced by an algebra map, on sections

Computation rule on sections for the universal property of the relative Spec (Stacks 01LQ): for the
`X`-morphism `h = relativeSpec.ofAlgebraMap A T φ hφ : T → Spec_X A` corresponding to an algebra map
`φ : A → g_*O_T`, and a section `c ∈ A(V)` (viewed as a function on `π⁻¹V ⊆ Spec_X A` through the
structure map `structureHom`), we have `h^♯(structureHom c) = φ(c)`. A variable-level lemma.

Reference: Stacks 01LQ (the construction of `Hom_X(T, Spec_X A) ≃ Hom_{O_X-alg}(A, g_*O_T)`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- For `h = ofAlgebraMap φ` and `c ∈ A(V)`: `h^♯(structureHom(c)) = φ(c)` in `Γ(T, g⁻¹V)`.

Proof: the `right_inv` of `relativeSpecHomEquiv` on sections is
`relativeSpec.pullbackSections_ofAlgebraMap`: `pullbackSections A T h V = algebraMapSections φ V`, whose
value on `c` is by definition `φ(c)`. By definition of `pullbackSections` the left side is
`structureRingMap.app V ≫ h.left.app (π⁻¹V) ≫ restriction(eqToHom)`, whose last two factors combine to
`h.left.appLE (π⁻¹V) (g⁻¹V)` (`Scheme.Hom.appLE`; `Scheme.Hom.appLE_congr` handles the different proofs of
the inclusion). And `structureHom A = toAlgebraMap A (Spec_X A) (𝟙)`, whose sections are
`pullbackSections A _ (𝟙) V = structureRingMap.app V ≫ (𝟙).left.app ≫ restriction(eqToHom) =
structureRingMap.app V` (the `app` of the identity is the identity, the restriction along `eqToHom rfl` is
the identity). Substituting gives the claim. Edge case: for `V = ⊥` both sides lie in the zero ring. -/
theorem AlgebraicGeometry.Scheme.relativeSpec.ofAlgebraMap_appLE_structureHom {X : AlgebraicGeometry.Scheme.{u}}
    (A : X.QCAlgebra) (T : CategoryTheory.Over X)
    (φ : A.carrier ⟶ (AlgebraicGeometry.Scheme.Modules.pushforward T.hom).obj
      (SheafOfModules.unit T.left.ringCatSheaf))
    (hφ : A.IsAlgebraMapToPushforward T.hom φ) (V : X.Opens) (c : A.carrier.val.obj (Opposite.op V))
    (hle : T.hom ⁻¹ᵁ V ≤ (AlgebraicGeometry.Scheme.relativeSpec.ofAlgebraMap A T φ hφ).left ⁻¹ᵁ
      ((AlgebraicGeometry.Scheme.relativeSpec A).hom ⁻¹ᵁ V)) :
    ((AlgebraicGeometry.Scheme.relativeSpec.ofAlgebraMap A T φ hφ).left.appLE
        ((AlgebraicGeometry.Scheme.relativeSpec A).hom ⁻¹ᵁ V) (T.hom ⁻¹ᵁ V) hle).hom
      (show Γ((AlgebraicGeometry.Scheme.relativeSpec A).left, (AlgebraicGeometry.Scheme.relativeSpec A).hom ⁻¹ᵁ V) from
        (AlgebraicGeometry.Scheme.relativeSpec.structureHom A).app V c) =
    (show Γ(T.left, T.hom ⁻¹ᵁ V) from φ.app V c) := by
  -- `structureHom(c) = structureRingMap(c)` (`structureHom_app_apply`), so the left side is by definition
  -- `pullbackSections A T h V c`; then apply `pullbackSections_ofAlgebraMap`.
  rw [AlgebraicGeometry.Scheme.relativeSpec.structureHom_app_apply]
  exact congrArg (fun ψ : CommRingCat.of (A.sectionsRing V) ⟶ CommRingCat.of Γ(T.left, T.hom ⁻¹ᵁ V) => ψ.hom c)
    (AlgebraicGeometry.Scheme.relativeSpec.pullbackSections_ofAlgebraMap A T φ hφ V)

end
