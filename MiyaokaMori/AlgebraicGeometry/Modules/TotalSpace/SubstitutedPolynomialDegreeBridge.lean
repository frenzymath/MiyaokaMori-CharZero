import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.SubstitutedPolynomialDegreeBridge_Canonical
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.SubstitutedPolynomialDegreeBridge_IsoInvariance

/-! # ξ-degree of a substituted homogeneous polynomial

Statement: on the total space `Tot(L)`, substituting a tuple of sections of ξ-degree at most `r₀` into a
homogeneous polynomial of degree `d` and transporting the result along any given isomorphism
`tensorPow (p^*M) d ≅ p^*(M^d)` yields a section of ξ-degree at most `d*r₀`.

Proof:
1. Write the homogeneous polynomial as a finite sum of monomials of total degree `d`.
2. Bound the ξ-degree of each monomial by `xiDegree_mul_le` and the iterated tensor powers.
3. Take the maximum over the finite sum and transport to `M.zpow d` along the section isomorphism of `θ`.

Assembled from:
* steps 1–3 for the **canonical** isomorphism `θ₀ = tensorPowPullbackZpowIso L M d`:
  `xiDegree_evalHomogeneousAtSections_canonical_le` (whose closure contains `xiDegree_pullback_map_le` and
  `xiDegree_pullbackUnitIso_inv_one_le_zero`);
* the passage from `θ₀` to an **arbitrary** `θ`: `θ = θ₀ ≫ (θ₀⁻¹ ≫ θ)` and `θ₀⁻¹ ≫ θ` is an automorphism of
  `p^*(M^d)`, which does not raise ξ-degree (`xiDegree_pullbackIso_hom_app_le`: units of the graded domain
  `Γ(Tot(L), O)` have degree 0).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem xiDegree_evalHomogeneousAtSections_le {k : Type u} [Field k]
    {C : SmoothProjectiveCurve k} {N r₀ dj : ℕ}
    (L M : LineBundle C.toVariety)
    (P : Fin (N + 1) →
      (((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
        M.toModules).val.obj (Opposite.op ⊤) : Type u))
    (hP : ∀ ℓ, xiDegree L M (P ℓ) ≤ (r₀ : WithBot ℕ))
    (F : MvPolynomial (Fin (N + 1)) k) (hF : F.IsHomogeneous dj)
    (θ : AlgebraicGeometry.Scheme.Modules.tensorPow
        ((AlgebraicGeometry.Scheme.Modules.pullback
          (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj M.toModules) dj ≅
      (AlgebraicGeometry.Scheme.Modules.pullback
          (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj (M.zpow dj).toModules) :
    xiDegree L (M.zpow dj)
        (θ.hom.app ⊤ (evalHomogeneousAtSections _ F hF P)) ≤ ((dj * r₀ : ℕ) : WithBot ℕ) := by
  have hθ : θ.hom = (tensorPowPullbackZpowIso L M dj).hom ≫
      ((tensorPowPullbackZpowIso L M dj).symm ≪≫ θ).hom := by
    simp
  rw [hθ]
  change xiDegree L (M.zpow dj)
    ((((tensorPowPullbackZpowIso L M dj).symm ≪≫ θ).hom.app ⊤)
      ((tensorPowPullbackZpowIso L M dj).hom.app ⊤ (evalHomogeneousAtSections _ F hF P))) ≤ _
  exact le_trans (xiDegree_pullbackIso_hom_app_le L (M.zpow dj) (M.zpow dj) _ _)
    (xiDegree_evalHomogeneousAtSections_canonical_le L M P hP F hF)

end
