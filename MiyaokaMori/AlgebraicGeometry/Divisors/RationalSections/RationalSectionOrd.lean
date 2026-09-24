import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModuleSheafStalk
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModuleSheafStalkStmt
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Divisors.Weil.PrincipalDivisor
import MiyaokaMori.RingTheory.SubmoduleLatticeIndex
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModuleGenericFiber

/-! # The order of vanishing of a rational section

`ord_{z,L}(s)`: the order of vanishing at a point `z` of a rational section `s ∈ L_η` of a module sheaf `L`
on an integral locally Noetherian scheme `W`. The module hierarchy is `RationalSectionOrd` →
`RationalSectionOrdCoordinate` → `RationalSectionDivisor`.

**Choice-free definition.** The order does not depend on a choice of generator `t_z` of `L_z` and of the
coefficient `g` with `g • t_η = s` (`rationalSectionOrd_eq_ord_of_generator`), so it is *defined* without
any witness: with `N := j(L_z) ⊆ L_η` the image of the stalk under the specialization
map `j = moduleStalkToGenericFiber` (an `O_{W,z}`-lattice in the `K(W)`-line `L_η`; `L_η` is an `O_{W,z}`-module by
restriction of scalars, `genericFiberModule`) and `S := O_{W,z} • s`,

  `ord_{z,L}(s) := [N : S] = length(N/(N ⊓ S)) − length(S/(N ⊓ S))`   (`Submodule.latticeIndex`).

This is Stacks 02MD's `ord_A(a/b) = ℓ(A/aA) − ℓ(A/bA)` transported to the lattice `N` (which is `A•t` for any
generator `t`), i.e. exactly Stacks 02SE's `ord_{Z,L}(s) := ord_Z(g)` for `s = g t`; see
`RationalSectionOrdCoordinate` (`rationalSectionOrd_eq_ord_genericCoordinate`) for the proof that it equals
`W.ord (c s) z` for every rank-1 trivialization coordinate `c`, and `LatticeOrd.ordFrac_eq_latticeIndex`
for the algebra. Junk values (same as Mathlib's `Scheme.ord`): `0` when
`coheight z ≠ 1` (`rationalSectionOrd_eq_zero_of_coheight_ne_one`) and `0` when `s = 0` (`rationalSectionOrd_zero`);
all evaluation lemmas either carry these hypotheses or handle the junk cases separately.

Sources: Stacks 02SE, 02MD; Fulton, Chapter 2 (`D ∩ [V]`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {W : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsIntegral W]

/-- The `O_{W,z}`-module structure on the generic fiber `L_η = L.presheaf.stalk η` (the carrier of `L.stalk η`,
spelled on the presheaf side so that it matches `moduleStalkToGenericFiber` and `genericCoordinate`) by restriction of
scalars along `O_{W,z} → K(W)`. **Not an instance** (for `z = η` it would compete with the stalk's own module
structure); use it with `letI`. -/
abbrev genericFiberModule (L : W.Modules) (z : W) :
    Module (W.presheaf.stalk z) (L.presheaf.stalk (genericPoint W)) :=
  Module.compHom (L.presheaf.stalk (genericPoint W)) (algebraMap (W.presheaf.stalk z) W.functionField)

/-- `genericFiberModule` is the restriction of scalars: `r • v = algebraMap r • v`. -/
theorem genericFiberModule_isScalarTower (L : W.Modules) (z : W) :
    letI := genericFiberModule L z
    IsScalarTower (W.presheaf.stalk z) W.functionField (L.presheaf.stalk (genericPoint W)) :=
  letI := genericFiberModule L z
  ⟨fun r k v => by
    show (r • k) • v = algebraMap (W.presheaf.stalk z) W.functionField r • (k • v)
    rw [Algebra.smul_def, mul_smul]⟩

/-- The stalk lattice `j(L_z) ⊆ L_η`: the `O_{W,z}`-submodule of the generic fiber spanned by the image of the
specialization map `j = moduleStalkToGenericFiber W L z` (for a line bundle it is `O_{W,z} • j(t)` for any
generator `t` of `L_z`). -/
def stalkLattice (L : W.Modules) (z : W) :
    @Submodule (W.presheaf.stalk z) (L.presheaf.stalk (genericPoint W)) _ _ (genericFiberModule L z) :=
  letI := genericFiberModule L z
  Submodule.span (W.presheaf.stalk z) (Set.range (AlgebraicGeometry.Scheme.Modules.moduleStalkToGenericFiber W L z))

open Classical in
/-- `ord_{z,L}(s)`: the order of vanishing of the rational section `s ∈ L_η` at `z`, defined without choices as the
lattice index `[j(L_z) : O_{W,z} • s] = length(N/(N ⊓ S)) − length(S/(N ⊓ S))` (`Submodule.latticeIndex`,
`stalkLattice`). Junk value `0` when `coheight z ≠ 1` or `s = 0` (as for Mathlib's `Scheme.ord`).
Evaluation: `rationalSectionOrd_eq_ord_genericCoordinate` (`= W.ord (c s) z` for a trivialization coordinate `c`),
`rationalSectionOrd_eq_ord_of_generator` (`= W.ord g z` for `s = g • j t`, `t` any generator of `L_z`).
(`[IsLocallyNoetherian W]` is not needed by the definition itself; it is kept so that the signature is unchanged.) -/
noncomputable def rationalSectionOrd [AlgebraicGeometry.IsLocallyNoetherian W] (L : W.Modules)
    (s : L.stalk (genericPoint W)) (z : W) : ℤ :=
  if Order.coheight z = 1 then
    if s = 0 then 0
    else
      letI := genericFiberModule L z
      Submodule.latticeIndex (stalkLattice L z)
        (Submodule.span (W.presheaf.stalk z) {(s : L.presheaf.stalk (genericPoint W))})
  else 0

/-- At points of coheight `≠ 1` the order is zero (junk value, as for `Scheme.ord`). -/
theorem rationalSectionOrd_eq_zero_of_coheight_ne_one [AlgebraicGeometry.IsLocallyNoetherian W]
    (L : W.Modules) (s : L.stalk (genericPoint W)) {z : W} (hz : Order.coheight z ≠ 1) :
    L.rationalSectionOrd s z = 0 := by
  unfold rationalSectionOrd
  rw [if_neg hz]

/-- For `s = 0` the order is zero (junk value). -/
theorem rationalSectionOrd_zero [AlgebraicGeometry.IsLocallyNoetherian W] (L : W.Modules) (z : W) :
    L.rationalSectionOrd 0 z = 0 := by
  unfold rationalSectionOrd
  simp only [if_true]
  split_ifs <;> rfl

/-- The defining formula in the non-junk case `coheight z = 1`, `s ≠ 0`. -/
theorem rationalSectionOrd_of_coheight_eq_one [AlgebraicGeometry.IsLocallyNoetherian W]
    (L : W.Modules) (s : L.stalk (genericPoint W)) {z : W} (hz : Order.coheight z = 1) (hs : s ≠ 0) :
    L.rationalSectionOrd s z =
      letI := genericFiberModule L z
      Submodule.latticeIndex (stalkLattice L z)
        (Submodule.span (W.presheaf.stalk z) {(s : L.presheaf.stalk (genericPoint W))}) := by
  unfold rationalSectionOrd
  rw [if_pos hz, if_neg hs]

end AlgebraicGeometry.Scheme.Modules

end
