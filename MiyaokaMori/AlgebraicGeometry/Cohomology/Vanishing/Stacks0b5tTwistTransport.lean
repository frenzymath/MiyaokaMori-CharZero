import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.Vanishing.Stacks0b5tProjectiveSpaceAux

/-! # Twist transport for Serre vanishing

Bookkeeping of tensor powers for Serre vanishing (Stacks 0B5T): given `i : X ⟶ P^N_k` and an
isomorphism `e : i^* O(1) ≅ L^{⊗d}`, for every `F`, `q`, `m` there is an isomorphism

  `F ⊗ L^{⊗(q + d m)} ≅ (F ⊗ L^{⊗q}) ⊗ i^* O(m)`.

Proof: `L^{⊗(q + dm)} ≅ L^{⊗q} ⊗ L^{⊗(dm)}` (`tensorPowAddIso`), `L^{⊗(dm)} ≅ (L^{⊗d})^{⊗m}`
(`tensorPowMulIso`), `(L^{⊗d})^{⊗m} ≅ (i^*O(1))^{⊗m}` (`tensorPowMapIso e.symm`),
`(i^*O(1))^{⊗m} ≅ i^*(O(1)^{⊗m})` (`pullbackTensorPowIso`), `O(1)^{⊗m} ≅ O(m)`
(`projectiveSpaceTwist_tensorPow_one`), and finally associativity of `⊗` (`tensorAssocIso`).
All isomorphisms are canonical; nothing here is specific to closed immersions.

Source: Stacks 0B5T (proof of (4)): "it suffices to treat `F ⊗ L^{⊗q}`, `0 ≤ q < d`, twisted by `O(m)`".
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry CategoryTheory.MonoidalCategory

noncomputable section

/-- `L^{⊗(q + d m)} ≅ L^{⊗q} ⊗ i^* O(m)` given `i^* O(1) ≅ L^{⊗d}`. -/
theorem AlgebraicGeometry.Scheme.Modules.tensorPow_add_mul_iso_tensor_pullback_twist {k : Type u} [Field k]
    {X : AlgebraicGeometry.Scheme.{u}} {N : ℕ} (i : X ⟶ ProjectiveSpace N k) (L : X.Modules) {d : ℕ}
    (e : (AlgebraicGeometry.Scheme.Modules.pullback i).obj (projectiveSpaceTwist k N 1) ≅
      AlgebraicGeometry.Scheme.Modules.tensorPow L d) (q m : ℕ) :
    Nonempty (AlgebraicGeometry.Scheme.Modules.tensorPow L (q + d * m) ≅
      AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.Modules.tensorPow L q)
        ((AlgebraicGeometry.Scheme.Modules.pullback i).obj (projectiveSpaceTwist k N m))) := by
  obtain ⟨t⟩ := projectiveSpaceTwist_tensorPow_one (k := k) N m
  refine ⟨AlgebraicGeometry.Scheme.Modules.tensorPowAddIso L q (d * m) ≪≫
    CategoryTheory.MonoidalCategory.whiskerLeftIso (AlgebraicGeometry.Scheme.Modules.tensorPow L q)
      ((AlgebraicGeometry.Scheme.Modules.tensorPowMulIso L d m).symm ≪≫
        AlgebraicGeometry.Scheme.Modules.tensorPowMapIso e.symm m ≪≫
        (AlgebraicGeometry.Scheme.Modules.pullbackTensorPowIso i (projectiveSpaceTwist k N 1) m).symm ≪≫
        (AlgebraicGeometry.Scheme.Modules.pullback i).mapIso t) ≪≫
    (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _).symm⟩

/-- `F ⊗ L^{⊗(q + d m)} ≅ (F ⊗ L^{⊗q}) ⊗ i^* O(m)` given `i^* O(1) ≅ L^{⊗d}`. -/
theorem AlgebraicGeometry.Scheme.Modules.tensor_tensorPow_add_mul_iso_tensor_pullback_twist {k : Type u}
    [Field k] {X : AlgebraicGeometry.Scheme.{u}} {N : ℕ} (i : X ⟶ ProjectiveSpace N k) (L : X.Modules)
    {d : ℕ} (e : (AlgebraicGeometry.Scheme.Modules.pullback i).obj (projectiveSpaceTwist k N 1) ≅
      AlgebraicGeometry.Scheme.Modules.tensorPow L d) (F : X.Modules) (q m : ℕ) :
    Nonempty (AlgebraicGeometry.Scheme.Modules.tensor F (AlgebraicGeometry.Scheme.Modules.tensorPow L (q + d * m)) ≅
      AlgebraicGeometry.Scheme.Modules.tensor
        (AlgebraicGeometry.Scheme.Modules.tensor F (AlgebraicGeometry.Scheme.Modules.tensorPow L q))
        ((AlgebraicGeometry.Scheme.Modules.pullback i).obj (projectiveSpaceTwist k N m))) := by
  obtain ⟨s⟩ := AlgebraicGeometry.Scheme.Modules.tensorPow_add_mul_iso_tensor_pullback_twist i L e q m
  exact ⟨AlgebraicGeometry.Scheme.Modules.tensorCongrRightIso F s ≪≫
    (AlgebraicGeometry.Scheme.Modules.tensorAssocIso F _ _).symm⟩

end
