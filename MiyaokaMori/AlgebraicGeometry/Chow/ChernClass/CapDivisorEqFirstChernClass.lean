import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.FirstChernCapCycle
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierDivisor
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.CycleGroup
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.DivisorCycleCap
import MiyaokaMori.AlgebraicGeometry.Divisors.LineBundle.DivisorLineBundle
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Chow.RationalEquivalence.ChowGroup
import MiyaokaMori.AlgebraicGeometry.Chow.RationalEquivalence.ChowGroupX
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme
import MiyaokaMori.AlgebraicGeometry.Chow.FirstChernClass
import MiyaokaMori.AlgebraicGeometry.Modules.IdealSheaf.IdealSheafToModules
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Chow.RationalEquivalence.RationalEquivalence
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.FirstChernCapFundamental
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietyQcqs
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.FirstChernClassNoIf
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietyLocallyNoetherian

/-! # The cap with a Cartier divisor is the cap with the first Chern class

The cap of a Cartier divisor with cycles (`capDivisor D`, Fulton §2.3) equals the cap with the first Chern
class of its line bundle `O(D)` (`firstChernClass`, Fulton §2.5): `D ∩ [Z] = c₁(O(D)) ∩ [Z]`. Intersection
numbers use `capDivisor` and the commutativity of caps uses `firstChernClass`; this identity connects the
two (proof of Proposition 2.4 of the paper). -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- **`D ∩ α = c₁(O(D)) ∩ α`** (Fulton §2.5 / Stacks 02SJ: the two sides are two encodings of the same
construction). Since `capDivisor D i` is *defined* as `(firstChernClass O(D) (i+1)).comp ChowGroup.mk`, this
is `rfl`. -/
theorem capDivisor_eq_firstChernClass {k : Type u} [Field k] {X : Variety k}
    (D : CartierDivisor X) (i : ℕ) (Z : CycleGroup X (i + 1)) :
    capDivisor D i Z
      = AlgebraicGeometry.firstChernClass D.lineBundle.toModules (i + 1)
          (AlgebraicGeometry.ChowGroup.mk Z) :=
  rfl

end
