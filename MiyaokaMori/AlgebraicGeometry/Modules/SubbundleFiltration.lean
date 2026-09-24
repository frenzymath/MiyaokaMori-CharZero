import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.ClosedSubvariety
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.VarietyLineBundle
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundle
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.IdealSheafToModules
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundleRank

/-! # Subbundle filtrations of a vector bundle

A subbundle filtration `0 = E_0 ⊂ E_1 ⊂ ⋯ ⊂ E_r = E` of a vector bundle, the rank increasing by one at
each step, with successive quotients `Q_i` line bundles.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

structure SubbundleFiltration {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (E : AlgebraicGeometry.VectorBundle C.toVariety) (r : ℕ) where
  sub : Fin (r + 1) → AlgebraicGeometry.VectorBundle C.toVariety
  incl : ∀ i : Fin r, (sub i.castSucc).toModules ⟶ (sub i.succ).toModules
  mono : ∀ i, CategoryTheory.Mono (incl i)
  rank_eq : ∀ i : Fin (r + 1), (sub i).rank = (i : ℕ)
  lastIso : (sub (Fin.last r)).toModules ≅ E.toModules
  lineQuotient : Fin r → LineBundle C.toVariety
  quotient_iso : ∀ i, Nonempty (CategoryTheory.Limits.cokernel (incl i) ≅
    (lineQuotient i).toModules)

end
