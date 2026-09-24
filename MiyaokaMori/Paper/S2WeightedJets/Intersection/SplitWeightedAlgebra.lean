import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.ModulesBiproductLocallyFree
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.ClosedSubvariety
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.VarietyLineBundle
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundle
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.GradedQuasicoherentAlgebra
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.IdealSheafToModules
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.ModulesPow
import MiyaokaMori.AlgebraicGeometry.Modules.SubbundleFiltration
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.WeightedSymAlgebra

/-! # The split weighted algebra

The split weighted algebra `S^sp`: the weighted symmetric algebra of one copy of `⊕_i Q_i` in each of the weights
`1, …, k` (the coordinate algebra of `Y^sp`; Lemma 2.3 and Proposition 2.4 of the
paper).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

noncomputable def splitWeightedAlgebraOf {k : Type u} [Field k]
    {C : SmoothProjectiveCurve k} {r : ℕ} {E : AlgebraicGeometry.VectorBundle C.toVariety}
    (F : SubbundleFiltration E r) (jetOrder : ℕ) : C.toScheme.GradedQCAlgebra :=
  -- local freeness and finite type of the line quotients `Q_i` are taken directly from the `VectorBundle` fields
  -- (`C.toVariety` is a structure literal whose carrier reduces to `C.carrier`, so the instances
  -- `VectorBundle.locallyFree` etc. are not found by instance search and are given explicitly);
  -- the two instances for `⊕_i Q_i` come from the biproduct lemmas
  haveI : ∀ i : Fin r, (F.lineQuotient i).toModules.IsLocallyFree := fun i => (F.lineQuotient i).locallyFree
  haveI : ∀ i : Fin r, (F.lineQuotient i).toModules.IsFiniteType := fun i => (F.lineQuotient i).isFiniteType
  AlgebraicGeometry.Scheme.weightedSymAlgebra
    (fun _ : Fin jetOrder =>
      CategoryTheory.Limits.biproduct (fun i : Fin r => (F.lineQuotient i).toModules))

end
