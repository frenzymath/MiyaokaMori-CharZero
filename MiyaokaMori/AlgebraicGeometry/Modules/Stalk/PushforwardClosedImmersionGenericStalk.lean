import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ProjectionFormulaClosedImmersion

/-! # Generic stalk of a pushforward along a closed immersion

Stalk of a pushforward along a closed immersion `i : Z → X` from an **integral** scheme `Z`, at the image
`ξ := i η` of the generic point `η`: if `M_η` is a one-dimensional `O_{Z,η}`-vector space
(`Module.length = 1`; `O_{Z,η} = κ(η)` is a field), then `(i_* M)_ξ` is killed by `m_ξ` and has length `1`
over `O_{X,ξ}`. This is the stalk bookkeeping of Stacks 01YI condition (2) / 0BEN, used in the
dévissage over a Noetherian scheme (with `Z = closure {ξ}` and `M = π_* L^{⊗n}`); the case `M = O_Z` is
`maximalIdeal_le_annihilator_and_length_pushforward_unit_stalk`.

Source: Stacks 00AE (stalks of a pushforward along a closed embedding), 01YI (2) and 0BEN (proof);
Mathlib `Module.length_eq_of_surjective`, `Module.length_eq_one_iff`.

The `O_{X,iz}`-linear comparison `(i_* M)_{iz} ≃ M_z` (Stacks 00AE, the `O_{X,iz}`-action on `M_z`
being `Module.compHom` along the stalk map `i^♯_z`) is `pushforwardStalkLinearEquiv i G z` /
`pushforwardStalkModule` / `pushforwardStalkModule_isScalarTower` (see `ProjectionFormulaClosedImmersion`).
The stalk map is local and surjective into a field, so it kills `m_x`; the length is transported
by `LinearEquiv.length_eq` and `Module.length_eq_of_surjective`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

section StalkOfPushforward

variable {Z X : AlgebraicGeometry.Scheme.{u}} (i : Z ⟶ X) [AlgebraicGeometry.IsClosedImmersion i]
  (M : Z.Modules) (z : Z)

/-- **General form.** `i : Z → X` a closed immersion, `z ∈ Z` with `O_{Z,z}` a field, `M : Z.Modules`
with `length_{O_{Z,z}} M_z = 1`. Then at `x := i z`, `m_x` kills `(i_* M)_x` and
`length_{O_{X,x}} (i_* M)_x = 1`.

Proof: through `pushforwardStalkLinearEquiv` (Stacks 00AE), `(i_* M)_x ≃ M_z` `O_{X,x}`-linearly, the action on `M_z`
being through `i^♯_z`. This map is local (Mathlib instance) and surjective (`Scheme.Hom.stalkMap_surjective`),
so it sends `m_x` into the maximal ideal `0` of the field `O_{Z,z}`: annihilation. For the length,
`Module.length_eq_of_surjective` (scalars extended along the surjection `i^♯_z`) and `LinearEquiv.length_eq`. -/
theorem maximalIdeal_le_annihilator_and_length_pushforward_stalk
    (hF : IsField (Z.presheaf.stalk z))
    (hM : Module.length (Z.presheaf.stalk z) (M.stalk z) = 1) {x : X} (hx : i.base z = x) :
    IsLocalRing.maximalIdeal (X.presheaf.stalk x) ≤
        Module.annihilator (X.presheaf.stalk x)
          (((AlgebraicGeometry.Scheme.Modules.pushforward i).obj M).stalk x) ∧
      Module.length (X.presheaf.stalk x)
        (((AlgebraicGeometry.Scheme.Modules.pushforward i).obj M).stalk x) = 1 := by
  subst hx
  let _ := pushforwardStalkModule i M z
  let _ : Algebra (X.presheaf.stalk (i.base z)) (Z.presheaf.stalk z) := (i.stalkMap z).hom.toAlgebra
  have := pushforwardStalkModule_isScalarTower i M z
  let e := pushforwardStalkLinearEquiv i M z
  -- the stalk map is local and lands in a field, so it kills the maximal ideal
  have hφ : ∀ r ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (i.base z)), i.stalkMap z r = 0 := by
    intro r hr
    have hnu : ¬ IsUnit (i.stalkMap z r) := fun h =>
      (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal r).mp hr))
        (isUnit_of_map_unit (i.stalkMap z).hom r h)
    by_contra hne
    obtain ⟨b, hb⟩ := hF.mul_inv_cancel hne
    exact hnu (isUnit_iff_exists_inv.mpr ⟨b, hb⟩)
  have hann : ∀ r ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (i.base z)),
      ∀ m : ((AlgebraicGeometry.Scheme.Modules.pushforward i).obj M).presheaf.stalk (i.base z),
        r • m = 0 := by
    intro r hr m
    apply e.injective
    erw [e.map_smul, e.map_zero]
    change i.stalkMap z r • e m = 0
    rw [hφ r hr, zero_smul]
  have hsurj : Function.Surjective (algebraMap (X.presheaf.stalk (i.base z)) (Z.presheaf.stalk z)) :=
    i.stalkMap_surjective z
  have hlen : Module.length (X.presheaf.stalk (i.base z))
      (((AlgebraicGeometry.Scheme.Modules.pushforward i).obj M).presheaf.stalk (i.base z)) = 1 := by
    rw [e.length_eq, Module.length_eq_of_surjective (S := X.presheaf.stalk (i.base z))
      (R := Z.presheaf.stalk z) (M := M.presheaf.stalk z) hsurj]
    exact hM
  exact ⟨fun r hr => Module.mem_annihilator.mpr (fun m => hann r hr m), hlen⟩

end StalkOfPushforward

/-- `Z` integral with generic point `η`,
`i : Z → X` a closed immersion, `M : Z.Modules` with `length_{O_{Z,η}} M_η = 1`. Then, at `ξ := i η`,
`m_ξ ≤ Ann_{O_{X,ξ}} ((i_* M)_ξ)` and `length_{O_{X,ξ}} ((i_* M)_ξ) = 1`.

Instance of `maximalIdeal_le_annihilator_and_length_pushforward_stalk` at the generic point `η` of the
integral scheme `Z`: `O_{Z,η}` is Mathlib's `Z.functionField` (an `abbrev` for `Z.presheaf.stalk (genericPoint Z)`),
a field since `Z` is integral (Stacks 00AE for the stalk of the pushforward, 01YI (2) / 0BEN for the use). -/
theorem pushforward_stalk_genericPoint_of_isClosedImmersion
    {Z X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsIntegral Z] (i : Z ⟶ X)
    [AlgebraicGeometry.IsClosedImmersion i] (M : Z.Modules)
    (hM : Module.length (Z.presheaf.stalk (genericPoint Z)) (M.stalk (genericPoint Z)) = 1) :
    IsLocalRing.maximalIdeal (X.presheaf.stalk (i.base (genericPoint Z))) ≤
        Module.annihilator (X.presheaf.stalk (i.base (genericPoint Z)))
          (((AlgebraicGeometry.Scheme.Modules.pushforward i).obj M).stalk (i.base (genericPoint Z))) ∧
      Module.length (X.presheaf.stalk (i.base (genericPoint Z)))
        (((AlgebraicGeometry.Scheme.Modules.pushforward i).obj M).stalk (i.base (genericPoint Z))) = 1 :=
  maximalIdeal_le_annihilator_and_length_pushforward_stalk i M (genericPoint Z)
    (Field.toIsField Z.functionField) hM rfl

end AlgebraicGeometry.Scheme.Modules

end
