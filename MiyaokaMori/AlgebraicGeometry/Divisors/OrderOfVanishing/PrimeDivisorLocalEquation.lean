import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Smooth.RegularScheme
import MiyaokaMori.AlgebraicGeometry.Divisors.OrderOfVanishing.OrdZeroStalkUnit
import MiyaokaMori.AlgebraicGeometry.Divisors.OrderOfVanishing.OrdFiniteOnNoetherianOpen
import Mathlib.AlgebraicGeometry.OrderOfVanishing
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.Ideal.UFD
import Mathlib.RingTheory.Ideal.Height
import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-! # Local equations of prime divisors on a locally factorial scheme

Local equations of a prime divisor on a regular integral scheme whose local rings are UFDs: given a prime
divisor `Z` (a point of coheight `1`) and a point `x ∈ closure {Z}`, there are a rational function `g ≠ 0`
and an open neighbourhood `U` of `x` such that `ord_z(g) = [z = Z]` for every point `z` of coheight `1` in
`U`.

Source: Hartshorne, *Algebraic Geometry*, Prop. II.6.11, second paragraph of the proof ("Conversely, let
`D` be a Weil divisor … at each point `x`, the local ring `O_x` is a UFD, so `D` restricted to `Spec O_x`
is principal"), with II.6.2 (height-one primes of a UFD are principal, Stacks 0AFT). Only a single prime
divisor `Z` is treated (`D = Z`); a general Weil divisor reduces to the generators of the free abelian
group (see the surjectivity proof of the Cartier–Weil isomorphism).

Proof (`exists_functionField_ord_eq_ite`): take an affine open neighbourhood `V` of `x`, `A := Γ(V, O_X)`;
`Z ⤳ x`, so `Z ∈ V`. Let `𝔪 = primeIdealOf x`, `𝔭 = primeIdealOf Z`; then `𝔭 ≤ 𝔪` (the open immersion
`fromSpec` preserves specialization, and on `Spec` specialization is inclusion) and
`ht 𝔭 = coheight Z = 1` (`idealHeight_eq_coheight`, `coheight_eq_of_isOpenImmersion`). `B := O_{X,x} = A_𝔪`
is a UFD and `𝔮 := 𝔭B` a height-one prime (`IsLocalization.height_map_of_disjoint`), hence principal,
`𝔮 = (π)` (Stacks 0AFT, `UniqueFactorizationMonoid.isPrincipal_of_height_eq_one`); write `π = a/s` with
`a ∈ A`, `s ∈ A ∖ 𝔪`, so `𝔮 = (a)` (`s` is a unit of `B`), `a ∈ 𝔭` and `a ≠ 0`. Put `g := a/s ∈ K(X)`.

For a point `z` of coheight `1` with `z ⤳ x` (`𝔭_z ≤ 𝔪`): `s ∉ 𝔭_z`, so `ord_z(s) = 0` and
`ord_z(g) = ord_z(a)`.
* `z = Z`: in the DVR `O_{X,Z} = A_𝔭`, `a` generates the maximal ideal `𝔭A_𝔭` (localize `𝔭B = aB` at `𝔭`),
  so `a` is a uniformizer and `ord_Z(a) = 1` (`Ring.ordFrac_irreducible`).
* `z ≠ Z`: if `a ∈ 𝔭_z`, then `(a) = 𝔮 ≤ 𝔭_z B`, both height-one primes of `B`, hence equal; intersecting
  with `A` gives `𝔭 = 𝔭_z`, i.e. `Z = z`, a contradiction. So `a ∉ 𝔭_z`, `a` is a unit of `O_{X,z}` and
  `ord_z(a) = 0`.

Bad points not specializing to `x`: `{z ∈ V | z ≠ Z, ord_z(g) ≠ 0}` is finite
(`finite_ord_ne_zero_inter_opens`, `V` Noetherian), and no bad point `z` satisfies `z ⤳ x` (otherwise
the previous paragraph gives `ord_z(g) = 0`). Let `U := V ∖ ⋃ closure {bad points}`; then `x ∈ U`, and a
point `z` of coheight `1` in `U` is either `Z` (`ord = 1`) or not bad (`ord = 0`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme

variable {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsIntegral X]
  [AlgebraicGeometry.IsLocallyNoetherian X]

/-- `ord_z(1) = 0`. -/
theorem ord_one_eq_zero (z : X) : X.ord (1 : X.functionField) z = 0 := by
  have : Nonempty (⊤ : X.Opens) := ⟨⟨z, trivial⟩⟩
  have h := AlgebraicGeometry.Scheme.ord_of_isUnit (X := X) (U := ⊤) (f := (1 : Γ(X, ⊤)))
    isUnit_one (x := z) trivial
  rwa [map_one] at h

/-- `ord_z(f⁻¹) = -ord_z(f)`. -/
theorem ord_inv_eq_neg {f : X.functionField} (hf : f ≠ 0) (z : X) :
    X.ord f⁻¹ z = -X.ord f z := by
  have h := AlgebraicGeometry.Scheme.ord_mul (X := X) (x := z) hf (inv_ne_zero hf)
  rw [mul_inv_cancel₀ hf, ord_one_eq_zero] at h
  linarith

/-- `ord_z(f / g) = ord_z(f) - ord_z(g)`. -/
theorem ord_div_eq_sub {f g : X.functionField} (hf : f ≠ 0) (hg : g ≠ 0) (z : X) :
    X.ord (f / g) z = X.ord f z - X.ord g z := by
  rw [div_eq_mul_inv, AlgebraicGeometry.Scheme.ord_mul hf (inv_ne_zero hg), ord_inv_eq_neg hg,
    sub_eq_add_neg]

/-- A section `a` over an affine open `V` that does not lie in the prime of a point `z` has `ord_z(a) = 0`
(`a` is a unit of `O_{X,z}`). -/
theorem ord_germToFunctionField_eq_zero_of_not_mem_primeIdealOf {V : X.Opens}
    (hV : AlgebraicGeometry.IsAffineOpen V) [Nonempty V] {z : X} (hz : z ∈ V) (a : Γ(X, V))
    (ha : a ∉ (hV.primeIdealOf ⟨z, hz⟩).asIdeal) :
    X.ord (X.germToFunctionField V a) z = 0 := by
  by_cases hc : Order.coheight z = 1
  · have : Ring.KrullDimLE 1 (X.presheaf.stalk z) :=
      AlgebraicGeometry.krullDimLE_of_coheight_le hc.le
    let _ : Algebra Γ(X, V) (X.presheaf.stalk z) := X.presheaf.algebra_section_stalk ⟨z, hz⟩
    have : IsLocalization.AtPrime (X.presheaf.stalk z) (hV.primeIdealOf ⟨z, hz⟩).asIdeal :=
      hV.isLocalization_stalk ⟨z, hz⟩
    have hunit : IsUnit (algebraMap Γ(X, V) (X.presheaf.stalk z) a) :=
      (IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk z)
        (hV.primeIdealOf ⟨z, hz⟩).asIdeal a).mpr ha
    have ha0 : X.germToFunctionField V a ≠ 0 := by
      intro h0
      apply hunit.ne_zero
      apply IsFractionRing.injective (X.presheaf.stalk z) X.functionField
      rw [map_zero]
      exact (X.algebraMap_germ_eq_germToFunctionField hz a).trans h0
    rw [AlgebraicGeometry.Scheme.ord_eq_iff hc ha0]
    change Ring.ordFrac (X.presheaf.stalk z) (X.germToFunctionField V a) = _
    rw [← X.algebraMap_germ_eq_germToFunctionField hz a]
    exact (Ring.ordFrac_of_isUnit hunit).trans rfl
  · exact AlgebraicGeometry.Scheme.ord_eq_zero_of_coheight_neq_one hc _

/-- If the germ of a section `a` at `z` generates the maximal ideal of the DVR `O_{X,z}`, then `ord_z(a) = 1`. -/
theorem ord_germToFunctionField_eq_one_of_span_germ_eq_maximalIdeal {V : X.Opens} [Nonempty V]
    {z : X} (hz : z ∈ V) (hc : Order.coheight z = 1)
    [IsDiscreteValuationRing (X.presheaf.stalk z)] (a : Γ(X, V))
    (ha : Ideal.span {X.presheaf.germ V z hz a} = IsLocalRing.maximalIdeal (X.presheaf.stalk z)) :
    X.ord (X.germToFunctionField V a) z = 1 := by
  have : Ring.KrullDimLE 1 (X.presheaf.stalk z) :=
    AlgebraicGeometry.krullDimLE_of_coheight_le hc.le
  have hirr : Irreducible (X.presheaf.germ V z hz a) :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr ha.symm
  have ha0 : X.germToFunctionField V a ≠ 0 := by
    intro h0
    apply hirr.ne_zero
    apply IsFractionRing.injective (X.presheaf.stalk z) X.functionField
    rw [map_zero]
    exact (X.algebraMap_germ_eq_germToFunctionField hz a).trans h0
  rw [AlgebraicGeometry.Scheme.ord_eq_iff hc ha0]
  change Ring.ordFrac (X.presheaf.stalk z) (X.germToFunctionField V a) = _
  rw [← X.algebraMap_germ_eq_germToFunctionField hz a,
    Ring.ordFrac_irreducible hirr]
  rfl

/-- **Main lemma**: a prime divisor `Z` is cut out near a point `x` of its closure by a single rational
function `g` (`ord_z(g) = [z = Z]`). -/
theorem exists_functionField_ord_eq_ite [X.IsRegular]
    (hufd : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x))
    {Z x : X} (hZ : Order.coheight Z = 1) (hZx : Z ⤳ x) :
    ∃ g : X.functionField, g ≠ 0 ∧ ∃ U : X.Opens, x ∈ U ∧
      ∀ z ∈ U, Order.coheight z = 1 → (z = Z → X.ord g z = 1) ∧ (z ≠ Z → X.ord g z = 0) := by
  classical
  obtain ⟨V, hV, hxV, -⟩ :=
    AlgebraicGeometry.exists_isAffineOpen_mem_and_subset (U := ⊤) (x := x) trivial
  have hZV : Z ∈ V := hZx.mem_open V.isOpen hxV
  have : Nonempty V := ⟨⟨x, hxV⟩⟩
  have hAdom : IsDomain Γ(X, V) := inferInstance
  -- the primes
  set m : Ideal Γ(X, V) := (hV.primeIdealOf ⟨x, hxV⟩).asIdeal with hm
  set pZ : Ideal Γ(X, V) := (hV.primeIdealOf ⟨Z, hZV⟩).asIdeal with hpZ
  have hmP : m.IsPrime := (hV.primeIdealOf ⟨x, hxV⟩).isPrime
  have hpZP : pZ.IsPrime := (hV.primeIdealOf ⟨Z, hZV⟩).isPrime
  -- specialization implies inclusion
  have hspec : ∀ {z : X} (hz : z ∈ V), z ⤳ x →
      (hV.primeIdealOf ⟨z, hz⟩).asIdeal ≤ m := by
    intro z hz hzx
    have hsp : hV.primeIdealOf ⟨z, hz⟩ ⤳ hV.primeIdealOf ⟨x, hxV⟩ := by
      have h1 : hV.fromSpec (hV.primeIdealOf ⟨z, hz⟩) ⤳ hV.fromSpec (hV.primeIdealOf ⟨x, hxV⟩) := by
        rw [hV.fromSpec_primeIdealOf, hV.fromSpec_primeIdealOf]
        exact hzx
      exact hV.fromSpec.isOpenEmbedding.isInducing.specializes_iff.mp h1
    exact (PrimeSpectrum.asIdeal_le_asIdeal _ _).mpr
      ((PrimeSpectrum.le_iff_specializes _ _).mpr hsp)
  -- coheight 1 implies height 1
  have hheight : ∀ {z : X} (hz : z ∈ V), Order.coheight z = 1 →
      (hV.primeIdealOf ⟨z, hz⟩).asIdeal.height = 1 := by
    intro z hz hc
    have h1 := AlgebraicGeometry.coheight_eq_of_isOpenImmersion hV.fromSpec
      (x := hV.primeIdealOf ⟨z, hz⟩)
    rw [hV.fromSpec_primeIdealOf] at h1
    have h2 := AlgebraicGeometry.idealHeight_eq_coheight Γ(X, V) (hV.primeIdealOf ⟨z, hz⟩)
    exact h2.trans (h1.symm.trans hc)
  have hle : pZ ≤ m := hspec hZV hZx
  have hpZh : pZ.height = 1 := hheight hZV hZ
  -- B = O_{X,x} = A_𝔪 is a UFD
  let _ : Algebra Γ(X, V) (X.presheaf.stalk x) := X.presheaf.algebra_section_stalk ⟨x, hxV⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk x) m := hV.isLocalization_stalk ⟨x, hxV⟩
  have : UniqueFactorizationMonoid (X.presheaf.stalk x) := hufd x
  have hdisj : ∀ {p : Ideal Γ(X, V)}, p ≤ m → Disjoint (m.primeCompl : Set Γ(X, V)) (p : Set Γ(X, V)) :=
    fun hp => Set.disjoint_left.mpr fun t ht ht' => ht (hp ht')
  have hinjB : Function.Injective (algebraMap Γ(X, V) (X.presheaf.stalk x)) :=
    IsLocalization.injective (X.presheaf.stalk x) (M := m.primeCompl)
      (fun t ht => mem_nonZeroDivisors_of_ne_zero (fun h0 => ht (h0 ▸ m.zero_mem)))
  set q : Ideal (X.presheaf.stalk x) := pZ.map (algebraMap Γ(X, V) (X.presheaf.stalk x)) with hq
  have hqP : q.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint m.primeCompl (X.presheaf.stalk x) pZ hpZP (hdisj hle)
  have hqh : q.height = 1 :=
    (IsLocalization.height_map_of_disjoint m.primeCompl pZ (hdisj hle)).trans hpZh
  have hqprin : q.IsPrincipal := UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hqh
  obtain ⟨π, hπ⟩ := hqprin.principal
  obtain ⟨⟨a, s⟩, has⟩ := IsLocalization.surj m.primeCompl π
  -- has : π * algebraMap s = algebraMap a
  have hqa : q = Ideal.span {algebraMap Γ(X, V) (X.presheaf.stalk x) a} := by
    rw [hπ, ← has, Ideal.span_singleton_mul_right_unit (IsLocalization.map_units _ s)]
  have haZ : a ∈ pZ := by
    have h1 : algebraMap Γ(X, V) (X.presheaf.stalk x) a ∈ q := by
      rw [hqa]; exact Ideal.mem_span_singleton_self _
    have h2 := IsLocalization.under_map_of_isPrime_disjoint m.primeCompl (X.presheaf.stalk x)
      hpZP (hdisj hle)
    rw [← h2]
    exact h1
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply Ideal.ne_bot_of_height_eq_one hqh
    rw [hqa, map_zero, Ideal.span_singleton_eq_bot]
  have hs0 : (s : Γ(X, V)) ≠ 0 := fun h0 => s.2 (h0 ▸ m.zero_mem)
  have hga0 : X.germToFunctionField V a ≠ 0 :=
    (map_ne_zero_iff _ (AlgebraicGeometry.Scheme.germToFunctionField_injective X V)).mpr ha0
  have hgs0 : X.germToFunctionField V (s : Γ(X, V)) ≠ 0 :=
    (map_ne_zero_iff _ (AlgebraicGeometry.Scheme.germToFunctionField_injective X V)).mpr hs0
  set g : X.functionField := X.germToFunctionField V a / X.germToFunctionField V (s : Γ(X, V))
    with hg
  have hg0 : g ≠ 0 := div_ne_zero hga0 hgs0
  -- the computation at points of coheight 1 specializing to x
  have hkey : ∀ z ∈ V, Order.coheight z = 1 → z ⤳ x →
      (z = Z → X.ord g z = 1) ∧ (z ≠ Z → X.ord g z = 0) := by
    intro z hzV hzc hzx
    have hpz : (hV.primeIdealOf ⟨z, hzV⟩).asIdeal ≤ m := hspec hzV hzx
    have hsz : (s : Γ(X, V)) ∉ (hV.primeIdealOf ⟨z, hzV⟩).asIdeal := fun hs => s.2 (hpz hs)
    have hords : X.ord (X.germToFunctionField V (s : Γ(X, V))) z = 0 :=
      ord_germToFunctionField_eq_zero_of_not_mem_primeIdealOf hV hzV _ hsz
    rw [hg, ord_div_eq_sub hga0 hgs0, hords, sub_zero]
    constructor
    · intro hzZ
      subst hzZ
      have : IsDiscreteValuationRing (X.presheaf.stalk z) :=
        isDiscreteValuationRing_stalk_of_isRegular z hzc
      apply ord_germToFunctionField_eq_one_of_span_germ_eq_maximalIdeal hzV hzc
      -- a generates the maximal ideal of O_{X,z} = A_𝔭
      let _ : Algebra Γ(X, V) (X.presheaf.stalk z) := X.presheaf.algebra_section_stalk ⟨z, hzV⟩
      have : IsLocalization.AtPrime (X.presheaf.stalk z) pZ := hV.isLocalization_stalk ⟨z, hzV⟩
      have hmax := IsLocalization.AtPrime.map_eq_maximalIdeal pZ (X.presheaf.stalk z)
      rw [← hmax]
      change Ideal.span {algebraMap Γ(X, V) (X.presheaf.stalk z) a} = _
      apply le_antisymm
      · rw [Ideal.span_singleton_le_iff_mem]
        exact Ideal.mem_map_of_mem _ haZ
      · rw [Ideal.map_le_iff_le_comap]
        intro y hy
        rw [Ideal.mem_comap, Ideal.mem_span_singleton']
        -- y ∈ 𝔭 ⇒ algebraMap y ∈ q = (a) in B
        have hyq : algebraMap Γ(X, V) (X.presheaf.stalk x) y ∈ q := Ideal.mem_map_of_mem _ hy
        rw [hqa, Ideal.mem_span_singleton'] at hyq
        obtain ⟨c, hc⟩ := hyq
        obtain ⟨⟨c₀, t⟩, hct⟩ := IsLocalization.surj m.primeCompl c
        -- hct : c * algebraMap t = algebraMap c₀
        have hA : y * (t : Γ(X, V)) = c₀ * a := by
          apply hinjB
          rw [map_mul, map_mul, ← hc, ← hct]
          ring
        have htz : (t : Γ(X, V)) ∉ pZ := fun ht => t.2 (hle ht)
        have htu : IsUnit (algebraMap Γ(X, V) (X.presheaf.stalk z) (t : Γ(X, V))) :=
          (IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk z) pZ _).mpr htz
        obtain ⟨tu, htu⟩ := htu
        refine ⟨algebraMap Γ(X, V) (X.presheaf.stalk z) c₀ * (tu⁻¹ : (X.presheaf.stalk z)ˣ), ?_⟩
        have hA' := congrArg (algebraMap Γ(X, V) (X.presheaf.stalk z)) hA
        rw [map_mul, map_mul, ← htu] at hA'
        calc algebraMap Γ(X, V) (X.presheaf.stalk z) c₀ * (tu⁻¹ : (X.presheaf.stalk z)ˣ) *
              algebraMap Γ(X, V) (X.presheaf.stalk z) a
            = (algebraMap Γ(X, V) (X.presheaf.stalk z) c₀ *
                algebraMap Γ(X, V) (X.presheaf.stalk z) a) * (tu⁻¹ : (X.presheaf.stalk z)ˣ) := by
              ring
          _ = (algebraMap Γ(X, V) (X.presheaf.stalk z) y * tu) * (tu⁻¹ : (X.presheaf.stalk z)ˣ) := by
              rw [hA']
          _ = algebraMap Γ(X, V) (X.presheaf.stalk z) y := by
              rw [mul_assoc, Units.mul_inv, mul_one]
    · intro hzZ
      apply ord_germToFunctionField_eq_zero_of_not_mem_primeIdealOf hV hzV
      intro haz
      apply hzZ
      -- (a) = q ≤ 𝔭_z B, two height-one primes, hence equal, hence 𝔭 = 𝔭_z and Z = z
      set pz : Ideal Γ(X, V) := (hV.primeIdealOf ⟨z, hzV⟩).asIdeal with hpz_def
      have hpzP : pz.IsPrime := (hV.primeIdealOf ⟨z, hzV⟩).isPrime
      set q' : Ideal (X.presheaf.stalk x) := pz.map (algebraMap Γ(X, V) (X.presheaf.stalk x))
        with hq'
      have hq'P : q'.IsPrime :=
        IsLocalization.isPrime_of_isPrime_disjoint m.primeCompl (X.presheaf.stalk x) pz hpzP
          (hdisj hpz)
      have hq'h : q'.height = 1 :=
        (IsLocalization.height_map_of_disjoint m.primeCompl pz (hdisj hpz)).trans (hheight hzV hzc)
      have hqq' : q ≤ q' := by
        rw [hqa, Ideal.span_singleton_le_iff_mem]
        exact Ideal.mem_map_of_mem _ haz
      have hqeq : q = q' := by
        by_contra hne
        have hlt : q < q' := lt_of_le_of_ne hqq' hne
        have := Ideal.height_add_one_le_of_lt_of_isPrime hlt
        rw [hqh, hq'h] at this
        norm_num at this
      have hpp : pZ = pz := by
        rw [← IsLocalization.under_map_of_isPrime_disjoint m.primeCompl (X.presheaf.stalk x)
          hpZP (hdisj hle),
          ← IsLocalization.under_map_of_isPrime_disjoint m.primeCompl (X.presheaf.stalk x)
          hpzP (hdisj hpz)]
        exact congrArg (fun I => Ideal.under Γ(X, V) I) hqeq
      have hpp' : hV.primeIdealOf ⟨z, hzV⟩ = hV.primeIdealOf ⟨Z, hZV⟩ := PrimeSpectrum.ext hpp.symm
      have e1 : hV.fromSpec (hV.primeIdealOf ⟨z, hzV⟩) = z := hV.fromSpec_primeIdealOf ⟨z, hzV⟩
      have e2 : hV.fromSpec (hV.primeIdealOf ⟨Z, hZV⟩) = Z := hV.fromSpec_primeIdealOf ⟨Z, hZV⟩
      rw [← e1, ← e2, hpp']
  -- finitely many bad points; remove their closures
  have : IsNoetherianRing Γ(X, V) :=
    AlgebraicGeometry.IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have : TopologicalSpace.NoetherianSpace V :=
    AlgebraicGeometry.noetherianSpace_of_isAffineOpen V hV
  have hfin : {z : X | z ∈ V ∧ z ≠ Z ∧ X.ord g z ≠ 0}.Finite :=
    (finite_ord_ne_zero_inter_opens V g).subset fun z hz => ⟨hz.1, hz.2.2⟩
  let C : Set X := ⋃ z ∈ {z : X | z ∈ V ∧ z ≠ Z ∧ X.ord g z ≠ 0}, closure ({z} : Set X)
  have hC : IsClosed C := hfin.isClosed_biUnion fun z _ => isClosed_closure
  refine ⟨g, hg0, V ⊓ ⟨Cᶜ, hC.isOpen_compl⟩, ⟨hxV, ?_⟩, ?_⟩
  · -- x ∉ C
    intro hxC
    simp only [C, Set.mem_iUnion, exists_prop] at hxC
    obtain ⟨z, ⟨hzV, hzZ, hzord⟩, hxz⟩ := hxC
    have hzx : z ⤳ x := specializes_iff_mem_closure.mpr hxz
    have hzc : Order.coheight z = 1 := by
      by_contra hc
      exact hzord (AlgebraicGeometry.Scheme.ord_eq_zero_of_coheight_neq_one hc g)
    exact hzord ((hkey z hzV hzc hzx).2 hzZ)
  · intro z hzU hzc
    obtain ⟨hzV, hzC⟩ := hzU
    refine ⟨fun hzZ => ?_, fun hzZ => ?_⟩
    · subst hzZ
      exact (hkey z hzV hzc hZx).1 rfl
    · by_contra hne
      apply hzC
      simp only [C, Set.mem_iUnion, exists_prop]
      exact ⟨z, ⟨hzV, hzZ, hne⟩, subset_closure rfl⟩

end AlgebraicGeometry.Scheme

end
