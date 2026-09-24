import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.LineBundle.DivisorLineBundleHom
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierDivisor
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.DivisorCycleCap
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.CapDivisorEqFirstChernClass
import MiyaokaMori.AlgebraicGeometry.Chow.CapTrivialBundleZero
import MiyaokaMori.AlgebraicGeometry.Chow.RationalEquivalence.ChowGroupX
import MiyaokaMori.AlgebraicGeometry.Chow.FirstChernClass
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensor
import MiyaokaMori.AlgebraicGeometry.Divisors.Weil.PrincipalDivisor
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.FirstChernClassTensor

/-! # Additivity of the cap with the first Chern class (Stacks 02SP)

Stacks 02SP (from 02SL): `c_1(L)∩α + c_1(N)∩α = c_1(L⊗N)∩α`; in the Cartier divisor form
`(D+E)∩ = D∩ + E∩` and `(−D)∩ = −(D∩)` (Fulton, Intersection Theory, Prop. 2.3(b)). -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/- The line bundle version `c_1(L ⊗ N) = c_1(L) + c_1(N)` is `AlgebraicGeometry.firstChernClass_tensor`
(with the hypothesis "locally of finite type over a field"); this file only keeps the version for
Cartier divisors on a variety, obtained by rewriting with `capDivisor_eq_firstChernClass`. -/

/-- The cap with Cartier divisors is additive: `(D + E) ∩ − = D ∩ − + E ∩ −`. -/
theorem capDivisor_add {k : Type*} [Field k] {X : Variety k} (D E : CartierDivisor X) (i : ℕ) :
    capDivisor (D + E) i = capDivisor D i + capDivisor E i := by
  ext Z
  simp only [AddMonoidHom.add_apply]
  rw [capDivisor_eq_firstChernClass, capDivisor_eq_firstChernClass,
    capDivisor_eq_firstChernClass]
  obtain ⟨e⟩ := CartierDivisor.lineBundle_add D E
  rw [AlgebraicGeometry.firstChernClass_congr _ _ e]
  rw [AlgebraicGeometry.firstChernClass_tensor (k := k)]
  simp only [AddMonoidHom.add_apply]

/-- The cap with the negative of a Cartier divisor is the negative of the cap. -/
theorem capDivisor_neg {k : Type*} [Field k] {X : Variety k} (D : CartierDivisor X) (i : ℕ) :
    capDivisor (-D) i = -capDivisor D i := by
  have hzero : capDivisor (0 : CartierDivisor X) i = 0 := by
    ext Z
    simp only [AddMonoidHom.zero_apply]
    rw [capDivisor_eq_firstChernClass]
    obtain ⟨e⟩ := CartierDivisor.lineBundle_zero (X := X)
    rw [AlgebraicGeometry.firstChernClass_congr _ _ e,
      AlgebraicGeometry.firstChernClass_one]
    simp
  have hsum : capDivisor (-D) i + capDivisor D i = 0 := by
    rw [← capDivisor_add (-D) D i, neg_add_cancel, hzero]
  exact eq_neg_of_add_eq_zero_left hsum

end
