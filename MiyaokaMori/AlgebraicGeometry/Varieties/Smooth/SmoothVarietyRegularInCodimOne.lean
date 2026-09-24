import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.Weil.DivisorClassGroup
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.SmoothProjectiveVariety
import MiyaokaMori.AlgebraicGeometry.Varieties.Smooth.Stacks056s

/-! # Smooth varieties are regular in codimension one

A smooth variety satisfies the regularity in codimension one of Hartshorne's condition (*) (II §6):
the local rings at points of codimension one are regular, i.e. DVRs. A variety is separated as a
scheme (`X → Spec k` is separated and `Spec k` is affine). Used for the divisor class group `Cl(X)`
of a smooth projective variety.

Sources: Hartshorne II §6 (*); Stacks 00TT.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/- Regularity in codimension one for smooth varieties: the localization of a smooth `k`-algebra at a
   prime is a regular local ring (Stacks 00TT), and the stalks of a variety are such localizations
   on an affine chart. -/

instance SmoothProjectiveVariety.isRegularInCodimOne {k : Type u} [Field k]
    (X : SmoothProjectiveVariety k) : X.toScheme.IsRegularInCodimOne := by
  have hreg : AlgebraicGeometry.Scheme.IsRegular X.toScheme :=
    AlgebraicGeometry.isRegular_of_smoothOver X.toScheme X.smooth
  exact ⟨fun x _ ↦ hreg.isRegularLocalRing_stalk x⟩

/- A variety is separated as a scheme: `X → Spec k` is separated (`Variety.separated`), `Spec k` is
   affine hence separated, and the composite `X → Spec k → ⊤` is separated. -/

instance Variety.isSeparatedScheme {k : Type u} [Field k] (X : Variety k) : X.toScheme.IsSeparated :=
  ⟨by
    rw [← CategoryTheory.Limits.terminal.comp_from (X.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k))]
    infer_instance⟩

end
