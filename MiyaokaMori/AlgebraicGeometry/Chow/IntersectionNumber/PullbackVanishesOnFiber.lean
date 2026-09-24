import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.PullbackTrivialOnFiber
import MiyaokaMori.AlgebraicGeometry.Morphisms.CurveInFiberFactors
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.IntegralCurveDegreeTensor
import MiyaokaMori.AlgebraicGeometry.Chow.IntegralCurveDegreeTransport

/-! # A line bundle pulled back from the base has degree zero on a curve in a fiber

If an integral, proper, one-dimensional closed subscheme `Γ ↪ Y` is contained in the fiber of `π`
over a closed point `c`, then a line bundle pulled back from the base `C` has degree zero on `Γ`
(proof of Lemma 2.5 of the paper). -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The degree on `Γ` of a line bundle pulled back from the base vanishes when `Γ` lies in a fiber:
the pullback to `Γ` factors through a point, hence is trivial. -/
theorem degree_pullback_eq_zero_of_in_fiber {K : Type u} [Field K]
    {Y C : AlgebraicGeometry.Scheme.{u}} [Y.Over (AlgebraicGeometry.Spec (CommRingCat.of K))]
    (π : Y ⟶ C) (M : C.Modules) [M.IsLineBundle] (Γ : IntegralCurve K Y)
    (c : C) (hc : IsClosed ({c} : Set C)) (hin : Set.range (Γ.ι ≫ π).base ⊆ {c}) :
    Γ.degree ((AlgebraicGeometry.Scheme.Modules.pullback π).obj M) = 0 := by
  -- Step 1: Γ is reduced (it is integral), so ι factors through the scheme-theoretic fiber.
  obtain ⟨j, hj, hjq⟩ := AlgebraicGeometry.exists_closedImmersion_to_fiber_of_range_subset
    Γ.ι π c hc hin
  have hproperj : AlgebraicGeometry.IsProper
      (j ≫ π.fiberι c ≫ (Y ↘ AlgebraicGeometry.Spec (CommRingCat.of K))) := by
    rw [← Category.assoc, hjq]
    exact Γ.isProper
  let _ : (π.fiber c).Over (AlgebraicGeometry.Spec (CommRingCat.of K)) :=
    ⟨π.fiberι c ≫ (Y ↘ AlgebraicGeometry.Spec (CommRingCat.of K))⟩
  let _ : AlgebraicGeometry.IsProper
      (j ≫ ((π.fiber c) ↘ AlgebraicGeometry.Spec (CommRingCat.of K))) := hproperj
  let Γz : IntegralCurve K (π.fiber c) :=
    { carrier := Γ.carrier
      ι := j
      dim_eq_one := Γ.dim_eq_one }
  -- Step 2: transport the degree along the factorization ι = j ≫ π.fiberι c.
  have hfac : Γ.degree ((AlgebraicGeometry.Scheme.Modules.pullback π).obj M) =
      Γz.degree ((AlgebraicGeometry.Scheme.Modules.pullback (π.fiberι c)).obj
        ((AlgebraicGeometry.Scheme.Modules.pullback π).obj M)) :=
    IntegralCurve.degree_factor Γ (π.fiberι c) j hjq hproperj
      ((AlgebraicGeometry.Scheme.Modules.pullback π).obj M)
  -- Step 3: on the fiber, the pulled-back line bundle is trivial, and the trivial bundle has degree 0.
  obtain ⟨e⟩ := AlgebraicGeometry.pullback_fiberι_pullback_iso_unit π M c
  have hunit : Γz.degree ((AlgebraicGeometry.Scheme.Modules.pullback (π.fiberι c)).obj
        ((AlgebraicGeometry.Scheme.Modules.pullback π).obj M)) =
      Γz.degree (SheafOfModules.unit (π.fiber c).ringCatSheaf) :=
    IntegralCurve.degree_congr Γz
      ((AlgebraicGeometry.Scheme.Modules.pullback Γz.ι).mapIso e)
  exact hfac.trans (hunit.trans (IntegralCurve.degree_unit Γz))

end
