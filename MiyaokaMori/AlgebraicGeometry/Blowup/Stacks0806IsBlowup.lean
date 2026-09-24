import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Blowup.SurfaceBlowup
import MiyaokaMori.AlgebraicGeometry.Blowup.Stacks0806

/-! # The blowup of Stacks 01OG satisfies the predicate `IsBlowup`

The blowup `(Scheme.blowup I).hom` constructed as the relative Proj of the Rees algebra (Stacks 01OG)
satisfies the universal-property predicate `MiyaokaMori.Statement.IsBlowup I`. This is the bridge from
Stacks 0806 (`blowup_universalProperty`) to that predicate: since
`EffectiveCartierDivisor Y = Y.EffCartier`, whose second field is `IsInvertibleIdeal`, the condition
"`∃ D` effective Cartier divisor with `D.idealSheaf = J`" is literally `IsInvertibleIdeal J`.

Used in the proof of Corollary 4.3 of the paper (§4).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The blowup of Stacks 01OG satisfies the universal-property predicate `IsBlowup`
(a direct translation of Stacks 0806). -/
theorem AlgebraicGeometry.Scheme.blowup_isBlowup {X : AlgebraicGeometry.Scheme.{u}}
    (I : X.IdealSheafData) :
    MiyaokaMori.Statement.IsBlowup I (AlgebraicGeometry.Scheme.blowup I).hom := by
  obtain ⟨⟨D, hD⟩, huniv⟩ := AlgebraicGeometry.Scheme.blowup_universalProperty I
  refine ⟨?_, fun T f hf => huniv f ⟨⟨I.comap f, hf⟩, rfl⟩⟩
  rw [← hD]
  exact D.isInvertible

end
