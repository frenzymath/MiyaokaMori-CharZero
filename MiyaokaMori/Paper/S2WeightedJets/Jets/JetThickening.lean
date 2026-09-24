import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedQcAlgebraPullback
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetBaseScheme
import MiyaokaMori.AlgebraicGeometry.Morphisms.SchemeOverBase

/-! # The jet thickening

`W ↦ W × Spec k[t]/(t^{k+1})` (fiber product over `Spec k`), and the projection `W × Spec k[t]/(t^{k+1}) ⟶ W`
(§2 of the paper: a based jet over `W` is a morphism out of `W × Spec k[t]/(t^{k+1})`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

noncomputable def jetThickening {k : Type u} [Field k] (r : ℕ) (W : AlgebraicGeometry.Scheme.{u})
    [W.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] : AlgebraicGeometry.Scheme.{u} :=
  CategoryTheory.Limits.pullback (W ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
    (jetBase k r ↘ AlgebraicGeometry.Spec (CommRingCat.of k))

noncomputable def jetThickeningProj {k : Type u} [Field k] (r : ℕ) (W : AlgebraicGeometry.Scheme.{u})
    [W.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] : jetThickening (k := k) r W ⟶ W :=
  CategoryTheory.Limits.pullback.fst _ _

noncomputable def jetThickeningMap {k : Type u} [Field k] (r : ℕ) {W W' : AlgebraicGeometry.Scheme.{u}}
    [W.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [W'.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (g : W ⟶ W')
    [g.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))] :
    jetThickening (k := k) r W ⟶ jetThickening (k := k) r W' :=
  CategoryTheory.Limits.pullback.map _ _ _ _ g (CategoryTheory.CategoryStruct.id _)
    (CategoryTheory.CategoryStruct.id _) (by simp) (by simp)

end
