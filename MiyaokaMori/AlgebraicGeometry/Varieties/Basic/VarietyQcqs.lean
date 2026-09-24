import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Morphisms.MorphismFiniteType
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety

/-! # Varieties are quasi-compact and quasi-separated

The underlying space of a variety over `k` is quasi-compact and quasi-separated (the two
instances Chevalley's theorem `Scheme.Hom.isConstructible_image` requires of the target).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

instance Variety.compactSpace {k : Type u} [Field k] (X : Variety k) : CompactSpace X.toScheme :=
  AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace
    (X.carrier ↘ AlgebraicGeometry.Spec (CommRingCat.of k))

instance Variety.quasiSeparatedSpace {k : Type u} [Field k] (X : Variety k) :
    QuasiSeparatedSpace X.toScheme :=
  AlgebraicGeometry.quasiSeparatedSpace_of_quasiSeparated
    (X.carrier ↘ AlgebraicGeometry.Spec (CommRingCat.of k))

end
