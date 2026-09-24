import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Morphisms.ConstantMorphism

/-! # A constant morphism factors through the point

A morphism from a reduced scheme to `X` whose underlying image is a single point `x` factors through
`Spec κ(x) → X`; in particular, if `x` is a closed point over an algebraically closed field `k`, it
factors through the `k`-point `x` of `Spec k` (it equals the constant morphism `V → Spec k → X`).
Used implicitly in Theorem 4.2 of the paper: on a general ruling fiber, "constant"
forces equality with the seed value.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem factors_through_residueField_of_isConstant {V X : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsReduced V] (g : V ⟶ X) (x : X) (hx : ∀ v : V, g.base v = x) :
    ∃ h : V ⟶ AlgebraicGeometry.Spec (X.residueField x),
      h ≫ X.fromSpecResidueField x = g := by
  let f : AlgebraicGeometry.Spec (X.residueField x) ⟶ X := X.fromSpecResidueField x
  letI : AlgebraicGeometry.Surjective (Limits.pullback.fst g f) := by
    rw [AlgebraicGeometry.surjective_iff, ← Set.range_eq_univ,
      AlgebraicGeometry.Scheme.Pullback.range_fst]
    ext v
    simp only [Set.mem_preimage, Set.mem_range, Set.mem_univ]
    constructor
    · intro _
      trivial
    · intro _
      exact ⟨IsLocalRing.closedPoint _, by
        calc
          f (IsLocalRing.closedPoint (X.residueField x)) = x := by
            simpa [f] using AlgebraicGeometry.Scheme.fromSpecResidueField_apply x
              (IsLocalRing.closedPoint (X.residueField x))
          _ = g v := (hx v).symm⟩
  letI : AlgebraicGeometry.IsClosedImmersion (Limits.pullback.fst g f) := by
    apply AlgebraicGeometry.IsClosedImmersion.of_isPreimmersion
    have hrange : Set.range (Limits.pullback.fst g f) = Set.univ := by
      rw [Set.range_eq_univ]
      exact (AlgebraicGeometry.surjective_iff _).mp inferInstance
    rw [hrange]
    exact isClosed_univ
  letI : IsIso (Limits.pullback.fst g f) :=
    AlgebraicGeometry.isIso_of_isClosedImmersion_of_surjective _
  let h : V ⟶ AlgebraicGeometry.Spec (X.residueField x) :=
    inv (Limits.pullback.fst g f) ≫ Limits.pullback.snd g f
  refine ⟨h, ?_⟩
  dsimp [h]
  rw [Category.assoc, ← Limits.pullback.condition, IsIso.inv_hom_id_assoc]

end
