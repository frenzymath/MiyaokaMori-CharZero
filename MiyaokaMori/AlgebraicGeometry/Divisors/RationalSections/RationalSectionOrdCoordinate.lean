import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.OrderOfVanishing.OrdFiniteOnNoetherianOpen
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Divisors.Weil.PrincipalDivisor
import MiyaokaMori.AlgebraicGeometry.Divisors.RationalSections.RationalSectionOrd
import MiyaokaMori.AlgebraicGeometry.Divisors.RationalSections.LineGenericCoordinateOrder

/-! # The order of a rational section equals the order of its trivialization coordinate

Let `W` be integral and locally Noetherian, `M` a module sheaf on `W`, `U ∋ z` an open,
`e_U : M|_U ≅ O_U^{⊕1}` a rank-one trivialization and `s` a nonzero element of the generic stalk of `M`.
Then `ord_{z,M}(s)` (`rationalSectionOrd`, defined as a lattice index) equals the order at `z` of the
generic coordinate of `s` in `e_U` (`AlgebraicGeometry.Divisors.LineGenericCoordinates.genericCoordinate`, an element of
`K(W)`). Consequences (in `RationalSectionDivisor`): (a) if `M ≅ O_W` globally, `div_M(s)` is the principal
cycle `div(c(s))`; (b) for every `f ∈ K(W)^×` there is a nonzero rational section `t` of `O_W` with
`div_{O_W}(t) = div(f)`.

Proof: `e_U` gives an `O_{W,z}`-linear isomorphism `e_z : M_z ≃ O_{W,z}` (`lineStalkEquivOfTrivialization`)
and a `K`-linear isomorphism `c : M_η ≃ K` with `c(j m) =` the image of `e_z(m)` in `K` (`j : M_z → M_η` the
specialization map; `lineStalkEquivOfTrivialization_toGenericFiber`). `t₀ := e_z⁻¹(1)` generates `M_z`, so
`j(M_z) = O_{W,z} • j(t₀)` and `c(j t₀) = 1`, hence `s = c(s) • j(t₀)`; `ord_eq_latticeIndex` (`Scheme.ord` as
a lattice index, from `LatticeOrd.ordFrac_eq_latticeIndex`) gives `[O • j t₀ : O • (c(s) • j t₀)] = ord_z(c(s))`.
For (a), `M ≅ O_W` restricted to `U = ⊤` gives a global trivialization with the same `c` at all points
(`principalCycle_apply`); for (b), take any nonzero `t₀`, so `div(t₀) = div(g₀)` by (a), and put
`t = (f/g₀) • t₀` (`rationalSectionDivisor_smul`, `principalCycle_mul`).
Sources: Stacks 02SE (definition of `div_L(s)`), 02SH (well-definedness, local computation).

Also: `trivializationOfIsoUnit` / `exists_trivialization` (rank-one trivializations of a line bundle), the
version `rationalSectionOrd_eq_ord_genericCoordinate'` without the hypothesis `s ≠ 0`, and the local
finiteness `exists_nhds_finite_support_rationalSectionOrd`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

open AlgebraicGeometry.Divisors AlgebraicGeometry.Divisors.LineGenericCoordinates

section Trivialization

/-- From `M|_U ≅ O_U`, the rank-one trivialization on `U` in the form required by `genericCoordinate`. -/
def trivializationOfIsoUnit {W : AlgebraicGeometry.Scheme.{u}} (M : W.Modules) (U : W.Opens)
    (e : AlgebraicGeometry.Scheme.Modules.restrict M U.ι ≅
      SheafOfModules.unit U.toScheme.ringCatSheaf) :
    AlgebraicGeometry.Scheme.Modules.restrict M U.ι ≅
      SheafOfModules.free (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin 1)) :=
  e ≪≫ (moduleFreeOneIsoUnit U.toScheme).symm

/-- A line bundle has a rank-one trivialization near every point. -/
theorem exists_trivialization {W : AlgebraicGeometry.Scheme.{u}} (M : W.Modules) [M.IsLineBundle]
    (z : W) :
    ∃ (U : W.Opens) (_ : z ∈ U), Nonempty (AlgebraicGeometry.Scheme.Modules.restrict M U.ι ≅
      SheafOfModules.free (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin 1))) := by
  obtain ⟨U, hz, ⟨e⟩⟩ := SheafOfModules.IsLineBundle.locally_trivial (M := M) z
  exact ⟨U, hz, ⟨trivializationOfIsoUnit M U e⟩⟩

/-- A global trivialization (to `O_W`) induces a rank-one trivialization on `U = ⊤`. -/
def topTrivializationOfIsoUnit {W : AlgebraicGeometry.Scheme.{u}} (M : W.Modules)
    (e : M ≅ SheafOfModules.unit W.ringCatSheaf) :
    M.restrict (⊤ : W.Opens).ι ≅
      SheafOfModules.free (R := (⊤ : W.Opens).toScheme.ringCatSheaf) (ULift.{u} (Fin 1)) :=
  (AlgebraicGeometry.Scheme.Modules.restrictFunctor (⊤ : W.Opens).ι).mapIso e ≪≫
    AlgebraicGeometry.Scheme.Modules.restrictUnitIso (⊤ : W.Opens).ι ≪≫
      (moduleFreeOneIsoUnit (⊤ : W.Opens).toScheme).symm

/-- The generic stalk of a line bundle is nonzero (the preimage of `1` under a trivialization coordinate). -/
theorem exists_ne_zero_of_trivialization {W : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsIntegral W] (M : W.Modules) [M.IsLineBundle] :
    ∃ s : M.stalk (genericPoint W), s ≠ 0 := by
  obtain ⟨U, hz, ⟨eU⟩⟩ := exists_trivialization M (genericPoint W)
  have hne : Nonempty U := ⟨⟨genericPoint W, hz⟩⟩
  refine ⟨(genericCoordinate W M U hne eU).symm 1, fun h => ?_⟩
  have h2 : (genericCoordinate W M U hne eU) ((genericCoordinate W M U hne eU).symm 1) = 0 :=
    (genericCoordinate W M U hne eU).map_eq_zero_iff.mpr h
  rw [LinearEquiv.apply_symm_apply] at h2
  exact one_ne_zero h2

end Trivialization

variable {W : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsIntegral W]
  [AlgebraicGeometry.IsLocallyNoetherian W]

/-- The image in the function field of a unit of the local ring has order `0`. -/
theorem ord_algebraMap_of_isUnit (z : W) {a : W.presheaf.stalk z} (ha : IsUnit a) :
    W.ord (algebraMap (W.presheaf.stalk z) W.functionField a) z = 0 := by
  by_cases hx : Order.coheight z = 1
  · have : Ring.KrullDimLE 1 (W.presheaf.stalk z) :=
      AlgebraicGeometry.krullDimLE_of_coheight_le hx.le
    have hne : algebraMap (W.presheaf.stalk z) W.functionField a ≠ 0 := by
      intro h
      have := (IsUnit.map (algebraMap (W.presheaf.stalk z) W.functionField) ha).ne_zero
      exact this h
    apply (AlgebraicGeometry.Scheme.ord_eq_iff hx hne).2
    change Ring.ordFrac (W.presheaf.stalk z) _ = 1
    exact Ring.ordFrac_of_isUnit ha
  · exact AlgebraicGeometry.Scheme.ord_eq_zero_of_coheight_neq_one hx _

/-- `Scheme.ord` as a lattice index in the generic fiber of a module sheaf: for `coheight z = 1`, `t ≠ 0` in `L_η`
and `g ≠ 0` in `K(W)`, `W.ord g z = [O_{W,z} • t : O_{W,z} • (g • t)]` (`Submodule.latticeIndex`, `L_η` an
`O_{W,z}`-module by `genericFiberModule`). This is `LatticeOrd.ordFrac_eq_latticeIndex` read through
`Scheme.ord_eq_iff` (`Scheme.ordHom z hz = Ring.ordFrac (O_{W,z})`). -/
theorem ord_eq_latticeIndex (L : W.Modules) {z : W} (hz : Order.coheight z = 1)
    {t : L.presheaf.stalk (genericPoint W)} (ht : t ≠ 0) {g : W.functionField} (hg : g ≠ 0) :
    letI := genericFiberModule L z
    W.ord g z = Submodule.latticeIndex (Submodule.span (W.presheaf.stalk z) {t})
      (Submodule.span (W.presheaf.stalk z) {g • t}) := by
  let _ := genericFiberModule L z
  have : IsScalarTower (W.presheaf.stalk z) W.functionField (L.presheaf.stalk (genericPoint W)) :=
    genericFiberModule_isScalarTower L z
  have : Ring.KrullDimLE 1 (W.presheaf.stalk z) :=
    AlgebraicGeometry.krullDimLE_of_coheight_le hz.le
  apply (AlgebraicGeometry.Scheme.ord_eq_iff hz hg).2
  change Ring.ordFrac (W.presheaf.stalk z) g = _
  exact LatticeOrd.ordFrac_eq_latticeIndex ht hg

/-- The core statement: the lattice-index `ord_{z,M}(s)` equals the order of the trivialization coordinate.
Proof: `t₀ := e_z⁻¹(1)` generates `M_z`, so the stalk lattice is `O_{W,z} • j(t₀)`; `c(j t₀) = 1`, hence
`s = c(s) • j(t₀)`, and `ord_eq_latticeIndex` gives `[O • j t₀ : O • (c s • j t₀)] = W.ord (c s) z`.
The junk case `coheight z ≠ 1` gives `0 = 0`. -/
theorem rationalSectionOrd_eq_ord_genericCoordinate (M : W.Modules) (U : W.Opens) (z : W)
    (hz : z ∈ U)
    (eU : M.restrict U.ι ≅
      SheafOfModules.free (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin 1)))
    (s : M.stalk (genericPoint W)) (hs : s ≠ 0) :
    M.rationalSectionOrd s z = W.ord (genericCoordinate W M U ⟨⟨z, hz⟩⟩ eU s) z := by
  by_cases hz1 : Order.coheight z = 1
  swap
  · rw [rationalSectionOrd_eq_zero_of_coheight_ne_one M s hz1,
      AlgebraicGeometry.Scheme.ord_eq_zero_of_coheight_neq_one hz1]
  let _ := genericFiberModule M z
  let ez := lineStalkEquivOfTrivialization W M U ⟨z, hz⟩ eU
  let c := genericCoordinate W M U ⟨⟨z, hz⟩⟩ eU
  let j := moduleStalkToGenericFiber W M z
  have hj : ∀ m, c (j m) = algebraMap (W.presheaf.stalk z) W.functionField (ez m) :=
    fun m => lineStalkEquivOfTrivialization_toGenericFiber W M U eU ⟨z, hz⟩ _ m
  set t₀ : M.presheaf.stalk z := ez.symm 1 with ht₀
  set jt : M.presheaf.stalk (genericPoint W) := j t₀ with hjt₀
  have hct : c jt = 1 := by
    rw [hjt₀, hj, ht₀, LinearEquiv.apply_symm_apply, map_one]
  have hjt : jt ≠ 0 := by
    intro h
    rw [h, map_zero] at hct
    exact zero_ne_one hct
  have hcs : c s ≠ 0 := fun h => hs (c.map_eq_zero_iff.mp h)
  have hs' : (s : M.presheaf.stalk (genericPoint W)) = c s • jt := by
    apply c.injective
    rw [c.map_smul, hct, smul_eq_mul, mul_one]
  have hN : stalkLattice M z = Submodule.span (W.presheaf.stalk z) {jt} := by
    apply le_antisymm
    · unfold stalkLattice
      rw [Submodule.span_le]
      rintro _ ⟨m, rfl⟩
      have hm : m = ez m • t₀ := by
        apply ez.injective
        rw [ez.map_smul, ht₀, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one]
      rw [hm, LinearMap.map_smulₛₗ]
      exact Submodule.smul_mem _ (ez m) (Submodule.mem_span_singleton_self _)
    · unfold stalkLattice
      exact Submodule.span_mono (Set.singleton_subset_iff.2 (Set.mem_range_self t₀))
  have hord := ord_eq_latticeIndex M hz1 hjt hcs
  rw [rationalSectionOrd_of_coheight_eq_one M s hz1 hs, hN]
  refine Eq.trans ?_ hord.symm
  rw [← hs']
  rfl

/-- The version without `s ≠ 0`: for `s = 0` both sides are `0` (`rationalSectionOrd_zero`, `Scheme.ord_zero`). -/
theorem rationalSectionOrd_eq_ord_genericCoordinate' (M : W.Modules) (U : W.Opens) (z : W)
    (hz : z ∈ U)
    (eU : M.restrict U.ι ≅
      SheafOfModules.free (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin 1)))
    (s : M.stalk (genericPoint W)) :
    M.rationalSectionOrd s z = W.ord (genericCoordinate W M U ⟨⟨z, hz⟩⟩ eU s) z := by
  by_cases hs : s = 0
  · subst hs
    rw [rationalSectionOrd_zero]
    exact ((congrArg (fun f => W.ord f z) (map_zero (genericCoordinate W M U ⟨⟨z, hz⟩⟩ eU))).trans
      (congrFun AlgebraicGeometry.Scheme.ord_zero z)).symm
  · exact rationalSectionOrd_eq_ord_genericCoordinate M U z hz eU s hs

/-- The support of `rationalSectionOrd` is locally finite (no quasi-compactness of `W` needed): take an affine
open neighbourhood `V` of `z` inside a trivializing open; on `V`, `ord_{·,M}(s)` is the order of the rational
function `c(s)`, which is nonzero at finitely many points (`finite_ord_ne_zero_inter_opens`). -/
theorem exists_nhds_finite_support_rationalSectionOrd (M : W.Modules) [M.IsLineBundle]
    (s : M.stalk (genericPoint W)) (z : W) :
    ∃ t ∈ nhds z, Set.Finite (t ∩ Function.support (M.rationalSectionOrd s)) := by
  classical
  obtain ⟨U, hzU, ⟨eU⟩⟩ := exists_trivialization M z
  obtain ⟨V, hzV, hVU, hfin⟩ := AlgebraicGeometry.Scheme.exists_isOpen_finite_ord_ne_zero
    (genericCoordinate W M U ⟨⟨z, hzU⟩⟩ eU s) z U hzU
  refine ⟨(V : Set W), V.isOpen.mem_nhds hzV, hfin.subset ?_⟩
  rintro x ⟨hxV, hxsupp⟩
  refine ⟨hxV, ?_⟩
  have hx := rationalSectionOrd_eq_ord_genericCoordinate' M U x (hVU hxV) eU s
  have hne : M.rationalSectionOrd s x ≠ 0 := hxsupp
  rw [hx] at hne
  exact hne

end AlgebraicGeometry.Scheme.Modules

end
