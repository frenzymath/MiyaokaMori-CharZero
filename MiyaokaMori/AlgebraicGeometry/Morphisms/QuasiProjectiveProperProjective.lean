import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Morphisms.QuasiProjectiveMorphism
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProjectiveMorphism
import MiyaokaMori.AlgebraicGeometry.Morphisms.Stacks01wc
import MiyaokaMori.AlgebraicGeometry.Morphisms.Stacks07rm

/-! # Quasi-projective and proper implies projective

Over a quasi-compact quasi-separated base, a quasi-projective proper morphism is projective
(the "⇐" direction of Stacks Project, Tag 0BCL (1)).

Proof (Stacks 0BCL (1), "⇐"): by Stacks 07RM the quasi-projective `f`
factors as `j ≫ f'` with `j` an open immersion and `f'` projective. Since `f'` is projective it
is proper (Stacks 01WC), hence separated; `f = j ≫ f'` is proper, so `j` is proper by
Mathlib's `IsProper.of_comp` (Stacks 01W6 (2)). A proper morphism is universally closed, so the
range of `j` is closed; an open immersion is a preimmersion, and a preimmersion with closed range
is a closed immersion (`IsClosedImmersion.of_isPreimmersion`). Finally `f'` projective gives a
closed immersion `i' : X' ⟶ Proj S` over `S`; the composite `j ≫ i'` is a closed immersion
(`IsClosedImmersion.comp`) over `S`, so `f` is projective.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem AlgebraicGeometry.IsProjectiveMorphism.of_isQuasiProjective_isProper {X S : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ S) [AlgebraicGeometry.IsQuasiProjectiveMorphism f] [AlgebraicGeometry.IsProper f]
    [CompactSpace S] [QuasiSeparatedSpace S] :
    AlgebraicGeometry.IsProjectiveMorphism f := by
  obtain ⟨X', j, f', hj, hf', hjf⟩ :=
    AlgebraicGeometry.IsQuasiProjectiveMorphism.exists_isOpenImmersion_isProjectiveMorphism f
  have : AlgebraicGeometry.IsProper f' := AlgebraicGeometry.IsProjectiveMorphism.isProper f'
  have : AlgebraicGeometry.IsProper (j ≫ f') := hjf ▸ ‹AlgebraicGeometry.IsProper f›
  have : AlgebraicGeometry.IsProper j := AlgebraicGeometry.IsProper.of_comp j f'
  have : AlgebraicGeometry.IsClosedImmersion j :=
    AlgebraicGeometry.IsClosedImmersion.of_isPreimmersion j
      (by simpa [← Set.image_univ] using j.isClosedMap _ isClosed_univ)
  obtain ⟨A, i', hgen, hft, hi', hi'f⟩ := hf'.exists_closed_immersion
  exact ⟨A, j ≫ i', hgen, hft, inferInstance, by rw [Category.assoc, hi'f, hjf]⟩

end
