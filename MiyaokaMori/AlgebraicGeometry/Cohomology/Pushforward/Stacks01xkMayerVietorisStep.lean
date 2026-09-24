import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.Stacks01xkHPrimeExt

/-! # The Mayer–Vietoris step of Stacks 01XJ

**The Mayer–Vietoris step of Stacks 01XJ (proof paragraph 2), for the localization property.**

Let `M` be a module on a scheme `X`, `Y ⊆ X` an open and `S ⊆ Γ(X, ⊤)` a submonoid (in the
application `S = powers (a g)` and `Y = f⁻¹D(g)`). For an open `V` write `P V` for: "for every
`q`, the restriction `H'^q(V, M) → H'^q(V ⊓ Y, M)` (Mathlib `Sheaf.H'` in `Ext` form, `Ext`-linear
via `precompLinear`) is a localization of `Γ(X, ⊤)`-modules at `S`" — formulated for every open
`W'` equal to `V ⊓ Y` to avoid transporting along lattice identities. Then `P V`, `P W`,
`P (V ⊓ W)` imply `P (V ⊔ W)`.

**Proof.** Apply the generic induction step `isLocalizedModule_precompLinear_of_mv`
(Mayer–Vietoris long exact sequences for the squares `(V, W)` and
`(V ⊓ Y, W ⊓ Y)`, the ladder of restriction maps between them, the five lemma for localizations) to
the squares `mvSquare V W` and `mvSquare (V ⊓ Y) (W ⊓ Y)` (short exact by `mvShortExact`) and the
restriction maps `tᵢ = ℤ[hom]`; the squares commute because `Opens X` is a thin category. The
hypotheses `P V`, `P W` give the vertical maps at `X₂, X₃`; `P (V ⊓ W)` gives the one at
`X₁ = (V ⊓ Y) ⊓ (W ⊓ Y) = (V ⊓ W) ⊓ Y`; the conclusion at `X₄ = (V ⊓ Y) ⊔ (W ⊓ Y) = (V ⊔ W) ⊓ Y`
is transported along this identity (`isLocalizedModule_precompLinear_congr`).

Source: Stacks 01XJ proof paragraph 2, 01EC. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

open CategoryTheory.Abelian CategoryTheory.Abelian.Ext

variable {X : AlgebraicGeometry.Scheme.{u}} (M : X.Modules)

attribute [local instance] smulEndAction ExtAction.module

/-- The localization property of the restriction maps `H'^q(V) → H'^q(W')` for all `W' = V ⊓ Y`. -/
def LocProp (S : Submonoid Γ(X, ⊤)) (Y V : X.Opens) : Prop :=
  ∀ (W' : X.Opens) (hle : W' ≤ V), W' = V ⊓ Y → ∀ q : ℕ,
    IsLocalizedModule S
      (precompLinear Γ(X, ⊤) M.toAddCommGrpSheaf ((freeSheafFunctor X).map (homOfLE hle)) q)

/-- **Mayer–Vietoris step**: `P V`, `P W`, `P (V ⊓ W)` imply `P (V ⊔ W)`. -/
theorem locProp_sup (S : Submonoid Γ(X, ⊤)) (Y V W : X.Opens) (hV : LocProp M S Y V)
    (hW : LocProp M S Y W) (hVW : LocProp M S Y (V ⊓ W)) : LocProp M S Y (V ⊔ W) := by
  intro W' hle hW' q
  have e : W' = (V ⊓ Y) ⊔ (W ⊓ Y) := hW'.trans (inf_sup_right _ _ _)
  refine isLocalizedModule_precompLinear_congr M S e.symm (sup_le_sup inf_le_left inf_le_left) hle q ?_
  refine isLocalizedModule_precompLinear_of_mv' Γ(X, ⊤) M.toAddCommGrpSheaf S
    ((freeSheafFunctor X).map (homOfLE (inf_le_left : V ⊓ W ≤ V)))
    ((freeSheafFunctor X).map (homOfLE (inf_le_right : V ⊓ W ≤ W)))
    ((freeSheafFunctor X).map (homOfLE (le_sup_left : V ≤ V ⊔ W)))
    ((freeSheafFunctor X).map (homOfLE (le_sup_right : W ≤ V ⊔ W))) (mvSquare V W).fac
    ((freeSheafFunctor X).map (homOfLE (inf_le_left : (V ⊓ Y) ⊓ (W ⊓ Y) ≤ V ⊓ Y)))
    ((freeSheafFunctor X).map (homOfLE (inf_le_right : (V ⊓ Y) ⊓ (W ⊓ Y) ≤ W ⊓ Y)))
    ((freeSheafFunctor X).map (homOfLE (le_sup_left : V ⊓ Y ≤ (V ⊓ Y) ⊔ (W ⊓ Y))))
    ((freeSheafFunctor X).map (homOfLE (le_sup_right : W ⊓ Y ≤ (V ⊓ Y) ⊔ (W ⊓ Y))))
    (mvSquare (V ⊓ Y) (W ⊓ Y)).fac (mvShortExact V W) (mvShortExact (V ⊓ Y) (W ⊓ Y))
    ((freeSheafFunctor X).map (homOfLE (inf_le_inf inf_le_left inf_le_left)))
    ((freeSheafFunctor X).map (homOfLE inf_le_left))
    ((freeSheafFunctor X).map (homOfLE inf_le_left))
    ((freeSheafFunctor X).map (homOfLE (sup_le_sup inf_le_left inf_le_left)))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ q
  all_goals try
    (rw [← (freeSheafFunctor X).map_comp, ← (freeSheafFunctor X).map_comp]
     exact congrArg _ (Subsingleton.elim _ _))
  · intro n
    exact hVW _ _ (show (V ⊓ Y) ⊓ (W ⊓ Y) = V ⊓ W ⊓ Y by rw [inf_inf_inf_comm, inf_idem]) n
  · intro n
    exact hV _ _ rfl n
  · intro n
    exact hW _ _ rfl n

end AlgebraicGeometry.Scheme.Modules

end
