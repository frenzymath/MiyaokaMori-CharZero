import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.RationalSections.RationalSectionOrdGenerator
import MiyaokaMori.AlgebraicGeometry.Divisors.RationalSections.RationalSectionOrdRestrict
import MiyaokaMori.AlgebraicGeometry.Divisors.RationalSections.RationalSectionDivisor
import MiyaokaMori.AlgebraicGeometry.Chow.RationalEquivalence.RationalEquivalenceX
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.PointClosureKrullDim
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.Stacks02suPointClosure
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.FirstChernCapFundamentalCycle
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.TameSymbolOnPointClosure

/-! # generating locus of a rational section; stalk bookkeeping for the key formula (Stacks 0AYC)

Stacks 0AYC indexes the key-formula family by a locally finite set of codimension-1 points `Z_i` **outside
of which `s` and `t` are generators** (chow.tex, section "The key formula", first paragraph), not by the
support of `div_L(s) ∪ div_N(t)`. The two index sets differ at non-normal codimension-1 points `w` (where
`Ring.ord` is a length, and `ord_w(f) = 0` does not force `f ∈ O_{X,w}^*`), and the difference matters:
see the docstring of `exists_keyFormula_principalFamily_of_normalizationFinite` in `CycleIdentitySplit.lean`
for a counterexample to the support-indexed statement. This file provides the Stacks index set:

* `Scheme.Modules.RationalSectionGeneratesAt L s w`: the rational section `s ∈ L_η` is the image of a generator of `L_w`
  ("`s` generates `L` at `w`"; equivalently `s = f • j(σ_w)` with `f ∈ O_{X,w}^*` for a generator `σ_w`).
* stalk lemmas for line bundles: a generator specializes to a generator, two generators differ by a unit,
  the generic image of a generator is nonzero, `RationalSectionGeneratesAt ⇒ ord = 0`, and the coordinate change
  `f = a_w · f_w` (Stacks 0AYC, third paragraph: `s_i = a_i s`).
* `IsRatEquivGen.mem_cycleSubgroup`: generators of `ratEquivZero X p` are `p`-cycles (dimension formula 0A21).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

/-- A generator of a module `M` free of rank one (given by `e : M ≃ R`) is an element with unit coordinate. -/
theorem span_singleton_eq_top_iff_isUnit {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    (e : M ≃ₗ[R] R) (t : M) : Submodule.span R {t} = ⊤ ↔ IsUnit (e t) := by
  constructor
  · intro ht
    have hmem : e.symm 1 ∈ Submodule.span R {t} := by rw [ht]; trivial
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmem
    have h1 : a * e t = 1 := by
      have h2 := (e.map_smul a t).symm.trans (congrArg e ha)
      rwa [LinearEquiv.apply_symm_apply, smul_eq_mul] at h2
    exact IsUnit.of_mul_eq_one a (by rw [mul_comm]; exact h1)
  · rintro ⟨u, hu⟩
    rw [eq_top_iff]
    rintro m -
    refine Submodule.mem_span_singleton.mpr ⟨e m * ((u⁻¹ : Rˣ) : R), ?_⟩
    apply e.injective
    rw [e.map_smul, smul_eq_mul, ← hu, mul_assoc, Units.inv_mul, mul_one]

variable {X : Scheme.{u}}

/-- A generator of `L_z` specializes to a generator of `L_w` for every generalization `w ⤳ z`
(compute in one rank-one trivialization around `z`; `w` lies in it because opens are stable under
generalization, and the coordinate of the specialization is the specialization of the coordinate,
`lineStalkEquivOfTrivialization_specializes`; ring maps preserve units). -/
theorem span_moduleStalkSpecializes_eq_top (L : X.Modules) [L.IsLineBundle] {w z : X} (h : w ⤳ z)
    (σ : L.presheaf.stalk z) (hσ : Submodule.span (X.presheaf.stalk z) {σ} = ⊤) :
    Submodule.span (X.presheaf.stalk w) {AlgebraicGeometry.Scheme.Modules.moduleStalkSpecializes X L h σ} = ⊤ := by
  obtain ⟨U, hz, ⟨eU⟩⟩ := exists_trivialization L z
  have hw : w ∈ U := h.mem_open U.isOpen hz
  rw [span_singleton_eq_top_iff_isUnit (AlgebraicGeometry.Divisors.LineGenericCoordinates.lineStalkEquivOfTrivialization X L U ⟨w, hw⟩ eU),
    AlgebraicGeometry.Divisors.LineGenericCoordinates.lineStalkEquivOfTrivialization_specializes X L U eU ⟨w, hw⟩ ⟨z, hz⟩ h σ]
  exact ((span_singleton_eq_top_iff_isUnit
    (AlgebraicGeometry.Divisors.LineGenericCoordinates.lineStalkEquivOfTrivialization X L U ⟨z, hz⟩ eU) σ).mp hσ).map
      (X.presheaf.stalkSpecializes h).hom

/-- Two generators of the stalk of a line bundle differ by a unit of the local ring. -/
theorem exists_units_smul_eq_of_span_eq_top (L : X.Modules) [L.IsLineBundle] (w : X)
    (σ σ' : L.presheaf.stalk w) (hσ : Submodule.span (X.presheaf.stalk w) {σ} = ⊤)
    (hσ' : Submodule.span (X.presheaf.stalk w) {σ'} = ⊤) :
    ∃ u : (X.presheaf.stalk w)ˣ, σ' = (u : X.presheaf.stalk w) • σ := by
  obtain ⟨U, hw, ⟨eU⟩⟩ := exists_trivialization L w
  set e := AlgebraicGeometry.Divisors.LineGenericCoordinates.lineStalkEquivOfTrivialization X L U ⟨w, hw⟩ eU
  obtain ⟨u, hu⟩ := (span_singleton_eq_top_iff_isUnit e σ).mp hσ
  obtain ⟨u', hu'⟩ := (span_singleton_eq_top_iff_isUnit e σ').mp hσ'
  refine ⟨u' * u⁻¹, ?_⟩
  apply e.injective
  rw [e.map_smul, smul_eq_mul, ← hu, ← hu', Units.val_mul, mul_assoc, Units.inv_mul, mul_one]

variable [IsIntegral X]

/-- The generic image of a generator of `L_w` is nonzero (it spans the nonzero `K(X)`-line `L_η`). -/
theorem moduleStalkToGenericFiber_ne_zero_of_span_eq_top (L : X.Modules) [L.IsLineBundle] (w : X)
    (σ : L.presheaf.stalk w) (hσ : Submodule.span (X.presheaf.stalk w) {σ} = ⊤) :
    AlgebraicGeometry.Scheme.Modules.moduleStalkToGenericFiber X L w σ ≠ 0 := by
  intro h0
  obtain ⟨v, hv⟩ := exists_stalk_genericPoint_ne_zero L
  obtain ⟨g, hg⟩ := exists_smul_toGenericFiber_eq L w σ hσ v
  apply hv
  rw [← hg, h0, smul_zero]
  rfl

/-- **`s` generates `L` at `w`** (Stacks 0AYC: the points `w` of codimension 1 where this fails for `s` or
`t` form the index set `{Z_i}` of the key formula): the rational section `s ∈ L_η` is the generic image of
a generator of the stalk `L_w`. Equivalently, for any generator `σ_w` of `L_w` and `s = f • j(σ_w)`, the
coordinate `f` is a unit of `O_{X,w}` (`exists_units_mul_eq_of_generators`). -/
def RationalSectionGeneratesAt (L : X.Modules) (s : L.stalk (genericPoint X)) (w : X) : Prop :=
  ∃ σ : L.presheaf.stalk w, Submodule.span (X.presheaf.stalk w) {σ} = ⊤ ∧
    AlgebraicGeometry.Scheme.Modules.moduleStalkToGenericFiber X L w σ = s

variable [IsLocallyNoetherian X]

/-- `X.ord 1 z = 0`. -/
theorem ord_one_apply (z : X) : X.ord (1 : X.functionField) z = 0 := by
  have := Scheme.ord_mul (X := X) (x := z) (f := (1 : X.functionField)) (g := 1) one_ne_zero one_ne_zero
  rw [mul_one] at this
  linarith

/-- If `s` generates `L` at `w`, then `ord_w(s) = 0` (`rationalSectionOrd_eq_ord_of_generator` with
coordinate `1`). Hence `Supp div_L(s) ⊆ {w | ¬ RationalSectionGeneratesAt L s w}`. -/
theorem RationalSectionGeneratesAt.rationalSectionOrd_eq_zero (L : X.Modules) [L.IsLineBundle]
    {s : L.stalk (genericPoint X)} {w : X} (h : L.RationalSectionGeneratesAt s w) :
    L.rationalSectionOrd s w = 0 := by
  obtain ⟨σ, hσ, hσs⟩ := h
  have hs : s ≠ 0 := hσs ▸ moduleStalkToGenericFiber_ne_zero_of_span_eq_top L w σ hσ
  rw [rationalSectionOrd_eq_ord_of_generator L w σ hσ 1 s hs (by rw [one_smul]; exact hσs)]
  exact ord_one_apply w

omit [IsLocallyNoetherian X] in
/-- **Coordinate change from `z` to a generalization `w ⤳ z`** (Stacks 0AYC, third paragraph:
`s_i = a_i s` with `a_i ∈ A_{q_i}^*`). If `σ` generates `L_z` with `s = f • j(σ)`, and `σ_w` generates `L_w`
with `s = f_w • j(σ_w)`, then `σ_w = a • σ|_w` for a unit `a ∈ O_{X,w}^*` and `f = a · f_w` in `K(X)`
(`j(σ|_w) = j(σ)`, and `j(σ) ≠ 0` spans the line `L_η`). -/
theorem exists_units_mul_eq_of_generators (L : X.Modules) [L.IsLineBundle] {w z : X} (hwz : w ⤳ z)
    (σ : L.presheaf.stalk z) (hσ : Submodule.span (X.presheaf.stalk z) {σ} = ⊤)
    (σw : L.presheaf.stalk w) (hσw : Submodule.span (X.presheaf.stalk w) {σw} = ⊤)
    {s : L.stalk (genericPoint X)} (f fw : X.functionField)
    (hf : f • AlgebraicGeometry.Scheme.Modules.moduleStalkToGenericFiber X L z σ = s)
    (hfw : fw • AlgebraicGeometry.Scheme.Modules.moduleStalkToGenericFiber X L w σw = s) :
    ∃ a : (X.presheaf.stalk w)ˣ,
      σw = (a : X.presheaf.stalk w) • AlgebraicGeometry.Scheme.Modules.moduleStalkSpecializes X L hwz σ ∧
      f = algebraMap (X.presheaf.stalk w) X.functionField a * fw := by
  obtain ⟨a, ha⟩ := exists_units_smul_eq_of_span_eq_top L w
    (AlgebraicGeometry.Scheme.Modules.moduleStalkSpecializes X L hwz σ) σw (span_moduleStalkSpecializes_eq_top L hwz σ hσ) hσw
  refine ⟨a, ha, ?_⟩
  have hj : AlgebraicGeometry.Scheme.Modules.moduleStalkToGenericFiber X L w σw =
      algebraMap (X.presheaf.stalk w) X.functionField a •
        AlgebraicGeometry.Scheme.Modules.moduleStalkToGenericFiber X L z σ := by
    rw [ha, (AlgebraicGeometry.Scheme.Modules.moduleStalkToGenericFiber X L w).map_smulₛₗ]
    congr 1
    exact MiyaokaMori.RationalSectionOrdRestrict.moduleStalkSpecializes_comp L _ hwz σ
  have h1 : (f - algebraMap (X.presheaf.stalk w) X.functionField a * fw) •
      AlgebraicGeometry.Scheme.Modules.moduleStalkToGenericFiber X L z σ = 0 := by
    rw [sub_smul, mul_comm, mul_smul, ← hj, hfw, hf]
    exact sub_self s
  rcases smul_eq_zero.mp h1 with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h (moduleStalkToGenericFiber_ne_zero_of_span_eq_top L z σ hσ)

/-- If `s` and `t` both generate at `w ⤳ z`, the tame symbol of their `z`-coordinates at `w` is trivial
(the coordinates are units of `O_{X,w}`, Stacks 0EAN), so `(ι_w)_* div(∂_w(f, g)) = 0`. -/
theorem keyFormulaTameCycle_eq_zero_of_generatesAt (L N : X.Modules) [L.IsLineBundle] [N.IsLineBundle]
    {s : L.stalk (genericPoint X)} {t : N.stalk (genericPoint X)} {w z : X} (hwz : w ⤳ z)
    (hw : Order.coheight w = 1)
    (hfin : Module.Finite (X.presheaf.stalk w) (integralClosure (X.presheaf.stalk w) X.functionField))
    (σ : L.presheaf.stalk z) (hσ : Submodule.span (X.presheaf.stalk z) {σ} = ⊤)
    (τ : N.presheaf.stalk z) (hτ : Submodule.span (X.presheaf.stalk z) {τ} = ⊤)
    (f g : X.functionFieldˣ) (hf : (f : X.functionField) • AlgebraicGeometry.Scheme.Modules.moduleStalkToGenericFiber X L z σ = s)
    (hg : (g : X.functionField) • AlgebraicGeometry.Scheme.Modules.moduleStalkToGenericFiber X N z τ = t)
    (hL : L.RationalSectionGeneratesAt s w) (hN : N.RationalSectionGeneratesAt t w) :
    X.keyFormulaTameCycle w hw hfin f g = 0 := by
  obtain ⟨σw, hσw, hσws⟩ := hL
  obtain ⟨τw, hτw, hτwt⟩ := hN
  obtain ⟨a, -, ha⟩ := exists_units_mul_eq_of_generators L hwz σ hσ σw hσw (f : X.functionField) 1 hf
    (by rw [one_smul]; exact hσws)
  obtain ⟨b, -, hb⟩ := exists_units_mul_eq_of_generators N hwz τ hτ τw hτw (g : X.functionField) 1 hg
    (by rw [one_smul]; exact hτwt)
  have hf' : f = Units.map (algebraMap (X.presheaf.stalk w) X.functionField).toMonoidHom a :=
    Units.ext (by rw [ha, mul_one]; rfl)
  have hg' : g = Units.map (algebraMap (X.presheaf.stalk w) X.functionField).toMonoidHom b :=
    Units.ext (by rw [hb, mul_one]; rfl)
  rw [hf', hg']
  unfold keyFormulaTameCycle
  rw [X.keyFormulaTameSymbol_unit_unit w hw hfin a b, Scheme.principalCycle_one]
  exact map_zero (AlgebraicCycle.properPushforwardHom (X.pointClosureι w))

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-- A Stacks 02RW generator of `ratEquivZero X p` is a `p`-cycle when `X` is locally of finite type over a
field: `div(f)` on `W_w` (of dimension `height w = p + 1`) is a `p`-cycle by the dimension formula 0A21
(`principalCycle_mem_cycleSubgroup`), and closed immersions preserve heights. -/
theorem IsRatEquivGen.mem_cycleSubgroup (K : Type u) [Field K] (π : X ⟶ Spec (CommRingCat.of K))
    [LocallyOfFiniteType π] {p : ℕ} {w : X} {c : AlgebraicCycle X ℤ} (h : IsRatEquivGen X p w c) :
    c ∈ cycleSubgroup X p := by
  obtain ⟨hw, hint, hci, hLN, f, rfl⟩ := h
  have hdim := Scheme.topologicalKrullDim_pointClosure w hw
  have hγ := Scheme.principalCycle_mem_cycleSubgroup (X.pointClosureι w ≫ π) hdim f
  exact properPushforward_mem_cycleSubgroup_of_isClosedImmersion (X.pointClosureι w) p hγ

/-- A nonzero coefficient of a Stacks 02RW generator of `ratEquivZero X p` sits at a point of height `p`. -/
theorem IsRatEquivGen.height_eq_of_ne_zero (K : Type u) [Field K] (π : X ⟶ Spec (CommRingCat.of K))
    [LocallyOfFiniteType π] {p : ℕ} {w : X} {c : AlgebraicCycle X ℤ} (h : IsRatEquivGen X p w c)
    {z : X} (hz : c z ≠ 0) : Order.height z = (p : ℕ∞) :=
  h.mem_cycleSubgroup K π z hz

variable [IsIntegral X]

/-- (Ga′) On an integral scheme of dimension `n + 2` locally of finite type over a field, a point of
coheight `1` has height `n + 1` (Stacks 0A21). -/
theorem height_eq_of_coheight_eq_one (K : Type u) [Field K] (π : X ⟶ Spec (CommRingCat.of K))
    [LocallyOfFiniteType π] (n : ℕ) (hX : X.dimension = n + 2) {w : X} (hw : Order.coheight w = 1) :
    Order.height w = ((n + 1 : ℕ) : ℕ∞) := by
  let _ : X.Over (Spec (CommRingCat.of K)) := ⟨π⟩
  have : LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K)) := inferInstanceAs (LocallyOfFiniteType π)
  have hdim : topologicalKrullDim X = ((n + 2 : ℕ) : WithBot ℕ∞) :=
    topologicalKrullDim_eq_of_dimension_pos (m := n + 1) hX
  have hadd := height_add_coheight_eq_of_locallyOfFiniteType (k := K) X (n + 2) hdim w
  rw [hw] at hadd
  have hne : Order.height w ≠ ⊤ := by
    intro ht; rw [ht, top_add] at hadd
    exact ENat.natCast_ne_top _ hadd.symm
  lift Order.height w to ℕ using hne with m hm
  have : m + 1 = n + 2 := by exact_mod_cast hadd
  have : m = n + 1 := by omega
  exact_mod_cast this

/-- On an integral scheme of dimension `n + 2` locally of finite type over a field, a point of height `n`
has coheight `2` (Stacks 0A21). -/
theorem coheight_eq_two_of_height_eq (K : Type u) [Field K] (π : X ⟶ Spec (CommRingCat.of K))
    [LocallyOfFiniteType π] (n : ℕ) (hX : X.dimension = n + 2) {z : X} (hz : Order.height z = (n : ℕ∞)) :
    Order.coheight z = 2 := by
  let _ : X.Over (Spec (CommRingCat.of K)) := ⟨π⟩
  have : LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K)) := inferInstanceAs (LocallyOfFiniteType π)
  have hdim : topologicalKrullDim X = ((n + 2 : ℕ) : WithBot ℕ∞) :=
    topologicalKrullDim_eq_of_dimension_pos (m := n + 1) hX
  have hadd := height_add_coheight_eq_of_locallyOfFiniteType (k := K) X (n + 2) hdim z
  rw [hz] at hadd
  have hne : Order.coheight z ≠ ⊤ := by
    intro ht; rw [ht, add_top] at hadd
    exact ENat.natCast_ne_top _ hadd.symm
  lift Order.coheight z to ℕ using hne with m hm
  have : n + m = n + 2 := by exact_mod_cast hadd
  have : m = 2 := by omega
  exact_mod_cast this

end AlgebraicGeometry

end
