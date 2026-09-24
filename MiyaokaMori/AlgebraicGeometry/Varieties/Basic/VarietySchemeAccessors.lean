import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Smooth.SmoothOverFieldDimLeOneNormal
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.ClosedSubvariety
import MiyaokaMori.AlgebraicGeometry.Morphisms.IsProjectiveOverIsProper
import MiyaokaMori.AlgebraicGeometry.Morphisms.MorphismFiniteType
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProjectiveImpliesProper
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Smooth.SpecNormalOfIntegrallyClosed
import MiyaokaMori.AlgebraicGeometry.Varieties.Surfaces.SmoothProjectiveSurface
import MiyaokaMori.AlgebraicGeometry.Varieties.Smooth.Stacks033m

/-! # Accessors for the underlying scheme and variety

Notation used throughout: `C.toScheme`, `S.toScheme` (the underlying scheme of a smooth projective
curve or surface) and `C.toVariety`, `S.toVariety` (a smooth projective curve or surface regarded
as a variety), defined as abbreviations of the corresponding structure fields. That a smooth
projective curve is a variety needs three facts, recorded as `SmoothProjectiveCurve.isIntegral`,
`isSeparated` and `isOfFiniteType`: smooth and connected implies integral, and projective implies
separated and of finite type.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/- Smooth projective curves: the underlying scheme and the associated variety
   (integral: smooth and connected; separated and of finite type: projective). -/

abbrev SmoothProjectiveCurve.toScheme {k : Type u} [Field k] (C : SmoothProjectiveCurve k) :
    AlgebraicGeometry.Scheme.{u} :=
  C.carrier

/-- Projective implies that the structure morphism is proper (`IsProjectiveOver.isProper`: the
closed immersion `i : C ↪ P^N_k` and `P^N_k ↘ Spec k` are proper, and their composite is
`C ↘ Spec k`). Separatedness and finite type follow from this. -/
theorem SmoothProjectiveCurve.isProper {k : Type u} [Field k] (C : SmoothProjectiveCurve k) :
    AlgebraicGeometry.IsProper (C.carrier ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) :=
  IsProjectiveOver.isProper C.projective

/-- Smooth, connected, projective and one-dimensional implies integral. The one-dimensional case
does not need the general "smooth implies regular" (Stacks 00TT/056S) and "a regular local ring is
a domain" (Stacks 00NP): every standard smooth chart has relative dimension `≤ 1` because
`dim ≤ 1`, the chart rings are étale over a PID, so every stalk is a domain and in fact a PID
(`SmoothOverFieldDimLeOneNormal`); Stacks 033M (Noetherian, normal and connected implies integral)
finishes the proof. -/
instance SmoothProjectiveCurve.isIntegral {k : Type u} [Field k] (C : SmoothProjectiveCurve k) :
    AlgebraicGeometry.IsIntegral C.carrier := by
  have hsm : AlgebraicGeometry.Smooth (C.carrier ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    C.smooth
  have := C.isProper
  have : CompactSpace C.carrier :=
    AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace
      (C.carrier ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
  have : AlgebraicGeometry.IsLocallyNoetherian C.carrier :=
    AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian
      (C.carrier ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
  have : AlgebraicGeometry.IsNoetherian C.carrier := {}
  have := C.connected
  exact AlgebraicGeometry.Smooth.isIntegral_of_field_of_dim_le_one
    (C.carrier ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) (le_of_eq C.dim_one)

theorem SmoothProjectiveCurve.isSeparated {k : Type u} [Field k] (C : SmoothProjectiveCurve k) :
    AlgebraicGeometry.IsSeparated (C.carrier ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := by
  have := C.isProper
  infer_instance

instance SmoothProjectiveCurve.isOfFiniteType {k : Type u} [Field k] (C : SmoothProjectiveCurve k) :
    AlgebraicGeometry.IsOfFiniteType (C.carrier ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := by
  have := C.isProper
  exact {}

noncomputable abbrev SmoothProjectiveCurve.toVariety {k : Type u} [Field k]
    (C : SmoothProjectiveCurve k) : Variety k where
  carrier := C.carrier
  integral := SmoothProjectiveCurve.isIntegral C
  separated := SmoothProjectiveCurve.isSeparated C
  finiteType := SmoothProjectiveCurve.isOfFiniteType C

/- Accessors for smooth projective surfaces (whose field `toSmoothProjectiveVariety` is a
   structure field, not an `extends`). -/

abbrev SmoothProjectiveSurface.toVariety {k : Type u} [Field k] (S : SmoothProjectiveSurface k) :
    Variety k :=
  S.toSmoothProjectiveVariety.toVariety

abbrev SmoothProjectiveSurface.toScheme {k : Type u} [Field k] (S : SmoothProjectiveSurface k) :
    AlgebraicGeometry.Scheme.{u} :=
  S.toVariety.toScheme

end
