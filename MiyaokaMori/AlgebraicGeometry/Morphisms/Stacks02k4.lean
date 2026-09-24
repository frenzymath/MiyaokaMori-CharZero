import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Morphisms.Stacks02k4Local

/-! # The first fundamental exact sequence for a smooth morphism

Stacks Project, Tag 02K4: for `f : X ⟶ Y` smooth over `S`, the sequence
`0 → f^*Ω_{Y/S} → Ω_{X/S} → Ω_{X/Y} → 0` is short exact (this is the relative tangent sequence of
§2.1 of the paper, (2.2)).

## Route

The maps are the canonical ones: `α = Omega.baseChangeMap f g` (the pullback map of differentials)
and `β = Omega.compMap f g` (from the universal property of `Ω_{X/S}`),
with `α ≫ β = 0` (`Stacks02k4Maps.lean`). Short exactness is checked on sections:

* `Mono α` ⟺ the complex `0 → f^*Ω_{Y/S} → Ω_{X/S}` is exact, and exactness of a complex of
  `O_X`-modules is local on sections (`Scheme.Modules.exact_iff_locally_lift_sections`); likewise
  `Epi β` is local (`epi_iff_locally_surjective_sections`).
* Every point has a neighbourhood basis of affine opens `U ⊆ f⁻¹V`, `V ⊆ g⁻¹W` with `V ⊆ Y`, `W ⊆ S`
  affine (`Omega.exists_small_affine`), and on such `U` the three statements are the affine
  first fundamental sequence of Kähler differentials `C ⊗_B Ω_{B/A} → Ω_{C/A} → Ω_{C/B} → 0`
  (Stacks 00RS; left end injective for `B → C` smooth, Stacks 00TA / 04B2):
  `Stacks02k4Affine.lean`; the globalization (`Mono α`, exactness, `Epi β`) is
  `Stacks02k4Local.lean`.

The existential statement `Omega_exact_triangle` (Stacks 01UX) is not used here: it does not pin
down `α`, so injectivity could not be added afterwards; instead 01UX follows from the same lemmas
without any smoothness hypothesis.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section



theorem AlgebraicGeometry.Omega_shortExact_of_smooth {X Y S : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ S) [AlgebraicGeometry.Smooth f] :
    ∃ (α : (AlgebraicGeometry.Scheme.Modules.pullback f).obj (AlgebraicGeometry.Omega g) ⟶
        AlgebraicGeometry.Omega (f ≫ g))
      (β : AlgebraicGeometry.Omega (f ≫ g) ⟶ AlgebraicGeometry.Omega f) (hz : α ≫ β = 0),
      (CategoryTheory.ShortComplex.mk α β hz).ShortExact :=
  ⟨AlgebraicGeometry.Omega.baseChangeMap f g, AlgebraicGeometry.Omega.compMap f g,
    AlgebraicGeometry.Omega.baseChangeMap_comp_compMap f g,
    CategoryTheory.ShortComplex.ShortExact.mk' (AlgebraicGeometry.Omega.baseChangeMap_compMap_exact f g)
      (AlgebraicGeometry.Omega.baseChangeMap_mono f g) (AlgebraicGeometry.Omega.compMap_epi f g)⟩

end
