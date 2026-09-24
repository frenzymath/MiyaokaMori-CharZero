import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjBaseChangeGlue
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.RelativeProjBaseChangeTwist

/-! # Base change of the relative Proj: the comparison morphism

Statement: for a morphism `g : S' ⟶ S` and a graded quasi-coherent algebra `𝒜` on `S`, there is a
canonical comparison morphism `r : Proj_{S'}(g^*𝒜) ⟶ S' ×_S Proj_S(𝒜)`; together with the two
projections it forms a pullback square, and the pullback along `r` of the twisting sheaf of the
relative Proj is isomorphic to the twisting sheaf of `g^*𝒜`.

Proof:
1. On an affine open cover of `S'`, the quasi-coherent sections formula identifies `(g^*𝒜)(V)` with
   `Γ(V) ⊗_{Γ(U)} 𝒜(U)`; the base change theorem for Proj (Stacks 01N2) gives `r` and the pullback
   square on each piece.
2. These local morphisms are compatible on overlaps by functoriality of restriction of sections; they
   are glued with `Scheme.Cover.glueMorphisms`, and `Scheme.isPullback_of_openCover` gives the global
   pullback property.
3. The twisting-sheaf isomorphisms of 01N2 are compatible on overlaps with the gluing uniqueness of
   `relativeProj.twist`, and glue to the twisting-sheaf isomorphism over `r`.

Source: Stacks 01O3, 01N2, 01I9; the base change of `P(O ⊕ L)` in Corollary 4.3
of the paper.

The proof is assembled from the following pieces:
* `GradedQCAlgebra.baseChangeHom g 𝒜 : Proj_{S'}(g^*𝒜) ⟶ Proj_S(𝒜)` and `baseChangeHom_hom`
  (over `g`), `isPullback_baseChangeHom` (`RelativeProjBaseChangeGlue.lean`); the map is glued over
  the locally directed cover of small charts (`RelativeProjBaseChangeCover.lean`) from the local
  comparison maps `Proj.map` of the unit `𝒜(U) → (g^*𝒜)(V)` (`RelativeProjBaseChangeUnit.lean`,
  `RelativeProjBaseChangeLocal.lean`);
* `baseChangeHom_twist` (θ).
`r` is `pullback.lift π' baseChangeHom _`, so `r ≫ pullback.snd = baseChangeHom` and the two
assertions are exactly `isPullback_baseChangeHom` and `baseChangeHom_twist`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem AlgebraicGeometry.Scheme.relativeProj_baseChange_comparison
    {S S' : AlgebraicGeometry.Scheme.{u}} (g : S' ⟶ S) (𝒜 : S.GradedQCAlgebra) :
    ∃ r : (AlgebraicGeometry.Scheme.relativeProj (𝒜.pullback g)).left ⟶
        CategoryTheory.Limits.pullback g (AlgebraicGeometry.Scheme.relativeProj 𝒜).hom,
      CategoryTheory.IsPullback
          (AlgebraicGeometry.Scheme.relativeProj (𝒜.pullback g)).hom
          (r ≫ CategoryTheory.Limits.pullback.snd g
            (AlgebraicGeometry.Scheme.relativeProj 𝒜).hom)
          g (AlgebraicGeometry.Scheme.relativeProj 𝒜).hom ∧
      ∀ d : ℤ, Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback
          (r ≫ CategoryTheory.Limits.pullback.snd g
            (AlgebraicGeometry.Scheme.relativeProj 𝒜).hom)).obj
        (AlgebraicGeometry.Scheme.relativeProj.twist 𝒜 d) ≅
        AlgebraicGeometry.Scheme.relativeProj.twist (𝒜.pullback g) d) := by
  refine ⟨CategoryTheory.Limits.pullback.lift
    (AlgebraicGeometry.Scheme.relativeProj (𝒜.pullback g)).hom
    (AlgebraicGeometry.Scheme.GradedQCAlgebra.baseChangeHom g 𝒜)
    (AlgebraicGeometry.Scheme.GradedQCAlgebra.baseChangeHom_hom g 𝒜).symm, ?_, ?_⟩
  · rw [CategoryTheory.Limits.pullback.lift_snd]
    exact AlgebraicGeometry.Scheme.GradedQCAlgebra.isPullback_baseChangeHom g 𝒜
  · intro d
    rw [CategoryTheory.Limits.pullback.lift_snd]
    exact AlgebraicGeometry.Scheme.GradedQCAlgebra.baseChangeHom_twist g 𝒜 d

end
