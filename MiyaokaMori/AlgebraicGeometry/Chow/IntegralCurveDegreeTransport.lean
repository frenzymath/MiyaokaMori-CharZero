import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.IntegralCurveDegree

/-! # Transport of the degree of an integral curve along a factorization

An integral curve inclusion factored through an intermediate scheme computes the
same line-bundle degree after pulling the bundle back to that intermediate scheme.
Both sides are `topSelfIntersection` on the same carrier: the proof transports the
value across the canonical pullback isomorphism (`topSelfIntersection_congr`) and
identifies the two k-structures using the factorization equation
(`topSelfIntersection_congr_over`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem IntegralCurve.degree_factor {K : Type u} [Field K]
    {Y Z : AlgebraicGeometry.Scheme.{u}}
    [Y.Over (AlgebraicGeometry.Spec (CommRingCat.of K))]
    (Γ : IntegralCurve K Y) (q : Z ⟶ Y)
    (j : Γ.carrier ⟶ Z) [AlgebraicGeometry.IsClosedImmersion j]
    (hjq : j ≫ q = Γ.ι)
    (hproperj : AlgebraicGeometry.IsProper
      (j ≫ q ≫ (Y ↘ AlgebraicGeometry.Spec (CommRingCat.of K))))
    (L : Y.Modules) [L.IsLineBundle] :
    letI : Z.Over (AlgebraicGeometry.Spec (CommRingCat.of K)) :=
      ⟨q ≫ (Y ↘ AlgebraicGeometry.Spec (CommRingCat.of K))⟩
    letI : AlgebraicGeometry.IsProper
        (j ≫ (Z ↘ AlgebraicGeometry.Spec (CommRingCat.of K))) := hproperj
    let Γz : IntegralCurve K Z :=
      { carrier := Γ.carrier
        ι := j
        dim_eq_one := Γ.dim_eq_one }
    Γ.degree L = Γz.degree ((AlgebraicGeometry.Scheme.Modules.pullback q).obj L) := by
  letI : Z.Over (AlgebraicGeometry.Spec (CommRingCat.of K)) :=
    ⟨q ≫ (Y ↘ AlgebraicGeometry.Spec (CommRingCat.of K))⟩
  letI : AlgebraicGeometry.IsProper
      (j ≫ (Z ↘ AlgebraicGeometry.Spec (CommRingCat.of K))) := hproperj
  let Γz : IntegralCurve K Z :=
    { carrier := Γ.carrier
      ι := j
      dim_eq_one := Γ.dim_eq_one }
  let e : (AlgebraicGeometry.Scheme.Modules.pullback j).obj
      ((AlgebraicGeometry.Scheme.Modules.pullback q).obj L) ≅
      (AlgebraicGeometry.Scheme.Modules.pullback Γ.ι).obj L :=
    (AlgebraicGeometry.Scheme.Modules.pullbackComp j q).app L ≪≫
      (AlgebraicGeometry.Scheme.Modules.pullbackCongr hjq).app L
  have hbase : j ≫ (Z ↘ AlgebraicGeometry.Spec (CommRingCat.of K)) =
      Γ.ι ≫ (Y ↘ AlgebraicGeometry.Spec (CommRingCat.of K)) := by
    change j ≫ q ≫ (Y ↘ AlgebraicGeometry.Spec (CommRingCat.of K)) = _
    simpa only [Category.assoc] using congrArg
      (fun e : Γ.carrier ⟶ Y => e ≫ (Y ↘ AlgebraicGeometry.Spec (CommRingCat.of K))) hjq
  -- both sides are `topSelfIntersection` on the same carrier; the k-structures agree (`hbase`) and the
  -- pulled-back modules are isomorphic (`e`)
  show AlgebraicGeometry.topSelfIntersection Γ.carrier Γ.isProperOver
      ((AlgebraicGeometry.Scheme.Modules.pullback Γ.ι).obj L) =
    @AlgebraicGeometry.topSelfIntersection K _ Γ.carrier (IntegralCurve.over Γz) Γz.isProperOver
      ((AlgebraicGeometry.Scheme.Modules.pullback j).obj
        ((AlgebraicGeometry.Scheme.Modules.pullback q).obj L)) _
  rw [AlgebraicGeometry.topSelfIntersection_congr Γ.carrier Γ.isProperOver _ _ e.symm]
  exact AlgebraicGeometry.topSelfIntersection_congr_over (IntegralCurve.over Γ) (IntegralCurve.over Γz)
    hbase.symm Γ.isProperOver Γz.isProperOver _

end
