import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierDivisorPrincipal
import MiyaokaMori.AlgebraicGeometry.Divisors.LineBundle.LineBundleIsoLinearEquivalent
import MiyaokaMori.AlgebraicGeometry.Divisors.LineBundle.CanonicalBundle
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierDivisor
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.ClosedSubvariety
import MiyaokaMori.AlgebraicGeometry.Divisors.LineBundle.DivisorLineBundle
import MiyaokaMori.AlgebraicGeometry.Divisors.LineBundle.LineBundleIsDivisorial
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleIsoOfModulesIso
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.SmoothProjectiveVariety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.EffectiveCartierDivisorScheme

/-! # The canonical bundle and the canonical divisor class

Translation between the line bundle `ω_X` and the divisor class `K_X`: there is a Cartier divisor `D`
with `O_X(D) ≅ ω_X`, and such a `D` is unique up to linear equivalence of Cartier divisors
(`D − D′` is a principal Cartier divisor `div(f)`).

Sources: Hartshorne II.6.13(c), 6.14, 6.15; Hartshorne IV.1 and V, Example 1.4.4 ("any divisor in the
linear equivalence class corresponding to `ω_X` is called a canonical divisor `K`"). Used to define
`K_X` in the degree identity `d = −K_X · f_*[C]` of the paper.

Uniqueness is stated for linear equivalence of Cartier divisors, as in Hartshorne's definition of the
canonical divisor (II §6), so the statement uses only II.6.13(c)/6.14 (any scheme) and 6.15 (`X`
integral), which give `CaCl X ≅ Pic X` without regularity or the UFD property; the Cartier–Weil
isomorphism is not needed. Since `cartierWeilEquiv` sends principal Cartier divisors to principal Weil
divisors, this is not weaker than uniqueness up to linear equivalence of Weil divisors, and on a smooth
variety it is equivalent to it.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- There is a Cartier divisor `D` with `O_X(D) ≅ ω_X`, unique up to a principal Cartier divisor. -/
theorem exists_cartierDivisor_lineBundle_iso_canonicalBundle {k : Type*} [Field k]
    (X : SmoothProjectiveVariety k) :
    ∃ D : CartierDivisor X.toVariety,
      Nonempty (D.lineBundle ≅ canonicalBundle X) ∧
      ∀ D' : CartierDivisor X.toVariety, Nonempty (D'.lineBundle ≅ canonicalBundle X) →
        ∃ f : X.toScheme.functionFieldˣ, D - D' = CartierDivisor.principal f := by
  obtain ⟨D, hD⟩ :=
    LineBundle.exists_cartierDivisor_variety X.toVariety (canonicalBundle X)
  refine ⟨D, hD, ?_⟩
  rintro D' ⟨e'⟩
  obtain ⟨e⟩ := hD
  exact CartierDivisor.exists_principal_of_lineBundle_iso
    (modulesIsoOfLineBundleIso (e ≪≫ e'.symm))

end
