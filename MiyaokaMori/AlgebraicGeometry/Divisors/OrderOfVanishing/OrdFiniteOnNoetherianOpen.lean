import Mathlib.AlgebraicGeometry.OrderOfVanishing
import Mathlib.AlgebraicGeometry.Noetherian

/-! # Finiteness of the order of vanishing on a Noetherian open

Let `W` be integral and locally Noetherian, `V` an open of `W` whose underlying space is Noetherian (e.g.
an affine open), and `f ∈ K(W)`. Then `{x ∈ V | ord_x(f) ≠ 0}` is finite. Consequently every point has a
neighbourhood meeting the support of `Scheme.ord f` in a finite set (the support of `Scheme.ord` is
locally finite); quasi-compactness of `W` is not needed.

Proof (the argument of `AlgebraicGeometry.Divisors.finite_codimensionOneOutside` on the open subspace):
1. If `f = 0` the set is empty. If `f ≠ 0`, take an affine open `U` (Mathlib `exists_isUnit_germ_eq`) on
   which `f` is the germ of a unit of `Γ(W, U)`; then `x ∈ U` implies `ord_x f = 0`, and `coheight x ≠ 1`
   implies `ord_x f = 0`. So the set is contained in `{x ∈ V | x ∉ U ∧ coheight x = 1}`.
2. `Z := {x : ↥V | x ∉ U}` is closed in `↥V`; since `↥V` is Noetherian, `Z` is a finite union of
   irreducible closed sets `t`, each with a generic point `η_t ∈ V`.
3. Let `x ∈ Z` with `coheight_W x = 1` and take `x ∈ t`; then `η_t ⤳ x` (in `↥V`, hence in `W`), i.e.
   `x ≤ η_t`. Now `η_t ∉ U` while the generic point `⊤` of `W` lies in `U` (`U` nonempty, `W`
   irreducible), so `η_t < ⊤` and `coheight η_t > 0`; also `coheight η_t ≤ coheight x = 1`. If `x < η_t`
   then `coheight η_t < coheight x = 1`, i.e. `= 0`, a contradiction. Hence `x = η_t`.
4. So the set is contained in the finite set `{η_t}`.

Source: Stacks 02SE (local finiteness of `div_L(s)`).

The finiteness of `{x | ord_x f ≠ 0}` is proved once, in `finite_ord_ne_zero_inter_opens` (locally
Noetherian, no quasi-compactness). The quasi-compact case `V = ⊤` is a one-line consequence:
`AlgebraicGeometry.Divisors.finite_support_ord` (integral and Noetherian; `Function.support (X.ord f)` is finite) at the end
of this file, and `AlgebraicGeometry.Scheme.finite_ord_ne_zero` (`{Z | IsPrimeDivisor Z ∧ ord f Z ≠ 0}` is
finite) in `PrincipalDivisorFiniteness`. `AlgebraicGeometry.Divisors.finite_codimensionOneOutside` (`CodimensionOneFinite`)
is the purely topological statement "finitely many codimension-one points outside a nonempty open",
without rational functions; steps 2–4 above repeat it on the open subspace `V`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory Opposite TopologicalSpace Set
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme

variable {W : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsIntegral W]
  [AlgebraicGeometry.IsLocallyNoetherian W]

/-- On a Noetherian open subspace, a rational function has only finitely many points of nonzero order. -/
theorem finite_ord_ne_zero_inter_opens (V : W.Opens) [TopologicalSpace.NoetherianSpace V]
    (f : W.functionField) : {x : W | x ∈ V ∧ W.ord f x ≠ 0}.Finite := by
  classical
  by_cases hf : f = 0
  · refine Set.Finite.subset (Set.finite_empty) ?_
    intro x hx
    exact absurd (by rw [hf]; simp) hx.2
  obtain ⟨U, -, g, hUne, hgf, hg⟩ := AlgebraicGeometry.exists_isUnit_germ_eq W f hf
  have : Nonempty U := hUne
  -- the generic point of W lies in U
  have htopU : (⊤ : W) ∈ U := by
    obtain ⟨u, hu⟩ := (inferInstance : Nonempty U)
    exact (genericPoint_specializes u).mem_open U.isOpen hu
  -- Z := the points of V not in U; closed in ↥V
  set Z : Set V := {x : V | (x : W) ∉ U} with hZdef
  have hZclosed : IsClosed Z := by
    have : Z = ((↑) : V → W) ⁻¹' ((U : Set W)ᶜ) := rfl
    rw [this]
    exact (isClosed_compl_iff.mpr U.isOpen).preimage continuous_subtype_val
  obtain ⟨S, hSfin, hSclosed, hSirred, hSsup⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hZclosed
  have : Finite S := hSfin
  let p : S → W := fun t => ((hSirred t.1 t.2).genericPoint).val
  apply (Set.finite_range p).subset
  rintro x ⟨hxV, hxord⟩
  -- x ∉ U and coheight x = 1
  have hxU : (x : W) ∉ U := by
    intro hxU
    exact hxord (hgf ▸ AlgebraicGeometry.Scheme.ord_of_isUnit hg hxU)
  have hxco : Order.coheight x = 1 := by
    by_contra h
    exact hxord (AlgebraicGeometry.Scheme.ord_eq_zero_of_coheight_neq_one h f)
  have hxZ : (⟨x, hxV⟩ : V) ∈ Z := hxU
  obtain ⟨t, ht, hxt⟩ := Set.mem_sUnion.mp (hSsup ▸ hxZ)
  refine ⟨⟨t, ht⟩, ?_⟩
  show ((hSirred t ht).genericPoint).val = x
  set η' := (hSirred t ht).genericPoint with hη'
  have hηgeneric : IsGenericPoint η' t :=
    (hSirred t ht).isGenericPoint_genericPoint (hSclosed t ht)
  have ht_sub : t ⊆ Z := by
    intro y hy
    rw [hSsup]
    exact Set.subset_sUnion_of_mem ht hy
  have hηZ : η' ∈ Z := ht_sub hηgeneric.mem
  have hηU : η'.val ∉ U := hηZ
  have hηnotTop : ¬(⊤ : W) ≤ η'.val := by
    intro hη
    exact hηU ((AlgebraicGeometry.Scheme.le_iff_specializes.mp hη).mem_open U.isOpen htopU)
  have hηpos : 0 < Order.coheight (η'.val) :=
    Order.coheight_pos_of_lt_top (lt_of_le_not_ge le_top hηnotTop)
  have hspec : η'.val ⤳ x := (hηgeneric.specializes hxt).map continuous_subtype_val
  have hle : x ≤ η'.val := AlgebraicGeometry.Scheme.le_iff_specializes.mpr hspec
  have hηle : Order.coheight (η'.val) ≤ 1 := by
    rw [← hxco]
    exact Order.coheight_anti hle
  by_cases hback : η'.val ≤ x
  · exact ((AlgebraicGeometry.Scheme.le_iff_specializes.mp hle).antisymm
      (AlgebraicGeometry.Scheme.le_iff_specializes.mp hback)).eq
  · exfalso
    have hlt : x < η'.val := lt_of_le_not_ge hle hback
    have hηlt : Order.coheight (η'.val) < Order.coheight x :=
      Order.coheight_strictAnti hlt (hηle.trans_lt (by simp))
    rw [hxco] at hηlt
    exact absurd (Order.lt_one_iff.mp hηlt) (ne_of_gt hηpos)

/-- Every point has an affine open neighbourhood `V` with `{x ∈ V | ord_x f ≠ 0}` finite; `V` may be
required to lie inside a given open `O`. -/
theorem exists_isOpen_finite_ord_ne_zero (f : W.functionField) (z : W) (O : W.Opens) (hz : z ∈ O) :
    ∃ V : W.Opens, z ∈ V ∧ V ≤ O ∧ {x : W | x ∈ V ∧ W.ord f x ≠ 0}.Finite := by
  obtain ⟨-, ⟨V, hV, rfl⟩, hzV, hVO⟩ :=
    W.isBasis_affineOpens.exists_subset_of_mem_open (a := z) hz O.isOpen
  have : IsNoetherianRing Γ(W, V) :=
    AlgebraicGeometry.IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have : TopologicalSpace.NoetherianSpace V :=
    AlgebraicGeometry.noetherianSpace_of_isAffineOpen V hV
  exact ⟨V, hzV, hVO, finite_ord_ne_zero_inter_opens V f⟩

end AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.Divisors

/-- The actual local orders of a nonzero rational function have finite support on an integral
Noetherian scheme. Special case `V = ⊤` of `AlgebraicGeometry.Scheme.finite_ord_ne_zero_inter_opens`
(the nonzero hypothesis is not needed for finiteness — `ord 0 = 0` — but is kept for the statement's users, which
compare with an additive valuation whose value at zero is infinity). -/
theorem finite_support_ord (X : AlgebraicGeometry.Scheme.{u}) [AlgebraicGeometry.IsIntegral X]
    [AlgebraicGeometry.IsNoetherian X]
    (f : X.functionField) (_hf : f ≠ 0) : (Function.support (X.ord f)).Finite := by
  haveI : TopologicalSpace.NoetherianSpace (⊤ : X.Opens) :=
    TopologicalSpace.NoetherianSpace.set ((⊤ : X.Opens) : Set X)
  refine (AlgebraicGeometry.Scheme.finite_ord_ne_zero_inter_opens (⊤ : X.Opens) f).subset ?_
  intro x hx
  exact ⟨trivial, hx⟩

end AlgebraicGeometry.Divisors

end
