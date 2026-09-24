import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModulesDualMap
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModulesDualCurry

/-! # Functoriality of the dual of a morphism

Contravariant functoriality of the dual: `dualMap (𝟙 V) = 𝟙 (dual V)` and
`dualMap (g ≫ h) = dualMap h ≫ dualMap g`.

Proof: `dualMap g = dualCurry (W^∨) V ((W^∨ ◁ g) ≫ dualEv W)` (`dualMap_eq`, by `rfl`: the body of
`dualMap` is this term, and the bodies of `dualCurry`/`dualEv` are its two constants, with types
spelled with `dual`; see the header of `ModulesDualEv`). Afterwards everything is computed in the
`dual` world:
* identity: `W^∨ ◁ 𝟙 = 𝟙`, and `dualCurry ((𝟙 ▷ V) ≫ dualEv V) = 𝟙` (`dualCurry_whiskerRight_ev`);
* composition: `dualMap h ≫ dualMap g = dualCurry ((dualMap h ▷ V) ≫ (W^∨ ◁ g) ≫ dualEv W)`
  (naturality in the first variable); `whisker_exchange` turns `(dualMap h ▷ V) ≫ (W^∨ ◁ g)` into
  `(Z^∨ ◁ g) ≫ (dualMap h ▷ W)`, and `(dualMap h ▷ W) ≫ dualEv W = uncurry (dualMap h) = Z^∨ ◁ h ≫ dualEv Z`
  finishes.

Downstream, use only `dualMap_eq` / `dualMap_id` / `dualMap_comp`; do not `unfold dualMap` (that exposes
the `internalHom` spelling, and every `rw` then triggers a defeq check of about 6.5 s).
`Category.id_comp` / `Category.assoc` / `whisker_exchange` need **explicit morphism arguments** on these
goals: the object `SheafOfModules.unit X.ringCatSheaf` has type `SheafOfModules X.ringCatSheaf`, and
`rw` assigns the metavariable `?Z : X.Modules` comparing types only at instances transparency, where
the plain def `X.Modules` does not match; `erw` matches but unfolds `dualEv` into the body of
`internalHomEval` (timeout).

Reference: Stacks 01CM (naturality of the tensor–Hom adjunction).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
open scoped CategoryTheory.MonoidalCategory

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

/-- `dualMap g` is the currying of `(W^∨ ◁ g) ≫ dualEv W` (spelled with `dual`; the same term after
unfolding). -/
theorem dualMap_eq {X : AlgebraicGeometry.Scheme.{u}} {V W : X.Modules} (g : V ⟶ W) :
    dualMap g = dualCurry (dual W) V ((dual W ◁ g) ≫ dualEv W) :=
  rfl

/-- The dual preserves identities: `(𝟙 V)^∨ = 𝟙 (V^∨)`. -/
theorem dualMap_id {X : AlgebraicGeometry.Scheme.{u}} (V : X.Modules) :
    dualMap (𝟙 V) = 𝟙 (dual V) := by
  rw [dualMap_eq, MonoidalCategory.whiskerLeft_id, Category.id_comp (f := dualEv V),
    ← Category.id_comp (dualEv V), ← MonoidalCategory.id_whiskerRight, dualCurry_whiskerRight_ev]

/-- The dual reverses composition: `(g ≫ h)^∨ = h^∨ ≫ g^∨`. -/
theorem dualMap_comp {X : AlgebraicGeometry.Scheme.{u}} {V W Z : X.Modules} (g : V ⟶ W) (h : W ⟶ Z) :
    dualMap (g ≫ h) = dualMap h ≫ dualMap g := by
  rw [dualMap_eq, dualMap_eq, dualMap_eq, dualCurry_naturality_left,
    ← Category.assoc (f := dualCurry (dual Z) W ((dual Z ◁ h) ≫ dualEv Z) ▷ V) (g := dual W ◁ g)
      (h := dualEv W),
    ← MonoidalCategory.whisker_exchange (f := dualCurry (dual Z) W ((dual Z ◁ h) ≫ dualEv Z)) (g := g),
    Category.assoc (f := dual Z ◁ g) (g := dualCurry (dual Z) W ((dual Z ◁ h) ≫ dualEv Z) ▷ W)
      (h := dualEv W),
    ← dualCurry_symm_apply (dual Z) W (dualCurry (dual Z) W ((dual Z ◁ h) ≫ dualEv Z)),
    Equiv.symm_apply_apply,
    ← Category.assoc (f := dual Z ◁ g) (g := dual Z ◁ h) (h := dualEv Z),
    ← MonoidalCategory.whiskerLeft_comp]

end AlgebraicGeometry.Scheme.Modules

end
