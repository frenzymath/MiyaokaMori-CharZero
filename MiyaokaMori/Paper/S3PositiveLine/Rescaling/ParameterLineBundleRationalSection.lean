import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.VarietyLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleNonvanishingLocus
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.WeightedOrder
import MiyaokaMori.AlgebraicGeometry.Varieties.Surfaces.FiberDivisorSupport
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.CurveStalkDVR
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.PointDivisor
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.SurfaceIntersectionPairingWeilCycleSection
import MiyaokaMori.AlgebraicGeometry.Divisors.RationalSections.RationalSectionOrdGenerator

/-! # The parameter line `L = O_{C̃}(Σ_y w_y [y])` and its canonical rational section
(step 2 of the paper's
second paragraph, Lemma 3.1 of the paper)

> Only finitely many `w_y` are nonzero, so they define `L = O_{C̃}(Σ_y w_y [y])`. Let `s_L` be its
> canonical rational section. In a local frame `ε` of `L`, write `s_L = γ ε`. Then `ord_y(γ) = w_y`.

This module isolates the line-bundle side of the construction from the jets: from a finitely
supported integer weight function `w` on a smooth projective curve it produces `L` and a nonzero
element `s` of the stalk of `L` at the generic point (the rational section `s_L`) such that the
coefficient `γ` of `s` in **any** frame `e` of `L` on any open `U ∋ η` has `ord_z γ = w z` at every
codimension-one point `z ∈ U`. It also proves the two facts about orders needed to feed this into
`normalized_coefficients_regular_and_unit` : a rational function with
nonnegative order at every point of an open `U` is regular on `U`
(`SmoothProjectiveCurve.exists_section_of_forall_ord_nonneg`), and every order is `0` at the generic
point.

-/
set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- Every element of the stalk of a line bundle at a point of a frame's domain is a multiple of the
germ of the frame (`IsFrame.span_germ_eq_top` + `Submodule.mem_span_singleton`). -/
theorem IsFrame.exists_smul_germ_eq {M : X.Modules} {W : X.Opens} {e : Γ(M, W)}
    (hf : IsFrame M W e) {y : X} (hy : y ∈ W) (s : M.stalk y) :
    ∃ γ : X.presheaf.stalk y, s = γ • (M.presheaf.germ W y hy e : M.stalk y) := by
  have hs : s ∈ Submodule.span (X.presheaf.stalk y)
      ({(M.presheaf.germ W y hy e : M.stalk y)} : Set (M.stalk y)) := by
    rw [hf.span_germ_eq_top hy]; exact Submodule.mem_top
  obtain ⟨γ, hγ⟩ := Submodule.mem_span_singleton.mp hs
  exact ⟨γ, hγ.symm⟩

end AlgebraicGeometry.Scheme.Modules

variable {k : Type u} [Field k]

/-- The generic point of a smooth projective curve has coheight `0` (it is the top element of the
specialization order: `genericPoint_specializes`). -/
theorem SmoothProjectiveCurve.coheight_genericPoint (Ct : SmoothProjectiveCurve k) :
    Order.coheight (genericPoint Ct.toScheme) = 0 :=
  Order.coheight_eq_zero.mpr fun b _ => genericPoint_specializes b

/-- Orders of vanishing are `0` at the generic point (`Scheme.ord` is `0` off coheight `1`). -/
theorem SmoothProjectiveCurve.ord_genericPoint (Ct : SmoothProjectiveCurve k)
    (γ : Ct.toScheme.functionField) : Ct.toScheme.ord γ (genericPoint Ct.toScheme) = 0 :=
  AlgebraicGeometry.Scheme.ord_eq_zero_of_coheight_neq_one
    (by rw [Ct.coheight_genericPoint]; decide) γ

/-- The weighted order of any nonzero tuple is `0` at the generic point (all orders are `0` there). -/
theorem weightedOrder_genericPoint {Ct : SmoothProjectiveCurve k} {n κ : ℕ}
    (a : Fin (n + 1) → Fin κ → Ct.toScheme.functionField) (hne : ∃ i q, a i q ≠ 0) :
    weightedOrderQ a hne (genericPoint Ct.toScheme) = 0 := by
  obtain ⟨p, -, hp⟩ := weightedOrder_attained a hne (genericPoint Ct.toScheme)
  rw [hp, Ct.ord_genericPoint]
  simp

/-- **Rational functions with nonnegative orders are regular** (Hartshorne II.6.3A for a smooth curve,
in the form actually needed: `O(U) = ⋂_{z ∈ U} O_{C̃,z}` inside `K(C̃)`). Let `U` be a nonempty open of a
smooth projective curve and `γ ∈ K(C̃)` with `ord_z γ ≥ 0` for every `z ∈ U`. Then `γ` is the germ
of a section `r ∈ O(U)`.

Natural-language proof. If `γ = 0` take `r = 0`. Otherwise, for each `z ∈ U` with `coheight z = 1`
the stalk `O_{C̃,z}` is a discrete valuation ring (`SmoothProjectiveCurve.isDiscreteValuationRing_stalk`) with fraction field `K(C̃)`, and `ord_z γ = ordFrac(γ) ≥ 0`
(`Scheme.ord_eq_iff`, Mathlib `Ring.ordFrac`) says exactly that `γ = algebraMap a_z` for some
`a_z ∈ O_{C̃,z}` (in a DVR `R ⊆ K`, `ordFrac x ≥ 0 ↔ x ∈ R`: write `x = u ϖ^n` with `n = ordFrac x`).
For `z` with `coheight z ≠ 1`, `z` is the generic point (`SmoothProjectiveCurve.eq_genericPoint_of_coheight_ne_one`)
and `O_{C̃,η} = K(C̃)`, so again `γ = algebraMap a_η`. Each `a_z` is the germ of a section `r_z` on some
open `W_z ∋ z`, `W_z ≤ U` (`TopCat.Presheaf.germ_exist` and restriction), and
`germToFunctionField W_z r_z = algebraMap a_z = γ` (`Scheme.algebraMap_germ_eq_germToFunctionField`).
On `W_z ⊓ W_{z'}` the restrictions of `r_z` and `r_{z'}` have the same image `γ` in `K(C̃)`, hence agree
(`Scheme.germToFunctionField_injective`, the curve being integral). The `W_z` cover `U`, so the sheaf
condition (`Ct.toScheme.sheaf.existsUnique_gluing'`) glues the `r_z` to `r ∈ O(U)` with `r|_{W_z} = r_z`;
its germ at `η` is that of `r_η`, i.e. `γ`. ∎

Proof: the DVR criterion is Mathlib's
`IsDiscreteValuationRing.exists_lift_of_le_one` after `Scheme.le_ord_iff` and
`Ring.ordFrac_eq_valuation_inv`; the generic point is handled by `TopCat.Presheaf.stalkSpecializes_refl`;
gluing by `existsUnique_gluing'` with compatibility from `germToFunctionField_injective`.

Edge cases: `γ = 0` (trivial, `r = 0`); `U` containing only the generic point cannot occur on a curve
(every nonempty open of a curve contains closed points), but the proof does not need this. -/
theorem SmoothProjectiveCurve.exists_section_of_forall_ord_nonneg (Ct : SmoothProjectiveCurve k)
    (U : Ct.toScheme.Opens) [Nonempty U] (γ : Ct.toScheme.functionField)
    (hγ : ∀ z ∈ U, 0 ≤ Ct.toScheme.ord γ z) :
    ∃ r : Γ(Ct.toScheme, U), (Ct.toScheme.germToFunctionField U).hom r = γ := by
  classical
  by_cases hγ0 : γ = 0
  · exact ⟨0, by rw [map_zero, hγ0]⟩
  -- Step 1: `γ` lies in every stalk over `U`
  have hstalk : ∀ z ∈ U, ∃ a : Ct.toScheme.presheaf.stalk z,
      algebraMap (Ct.toScheme.presheaf.stalk z) Ct.toScheme.functionField a = γ := by
    intro z hz
    by_cases hco : Order.coheight z = 1
    · have : IsDiscreteValuationRing (Ct.toScheme.presheaf.stalk z) :=
        Ct.isDiscreteValuationRing_stalk z hco
      have : Ring.KrullDimLE 1 (Ct.toScheme.presheaf.stalk z) :=
        AlgebraicGeometry.krullDimLE_of_coheight_le hco.le
      have h1 := (AlgebraicGeometry.Scheme.le_ord_iff hco hγ0).mp (hγ z hz)
      change Multiplicative.ofAdd (0 : ℤ) ≤ Ring.ordFrac (Ct.toScheme.presheaf.stalk z) γ at h1
      rw [Ring.ordFrac_eq_valuation_inv, ofAdd_zero, WithZero.coe_one] at h1
      have hpos : 0 < (IsDiscreteValuationRing.maximalIdeal (Ct.toScheme.presheaf.stalk z)).valuation
          Ct.toScheme.functionField γ := (Valuation.pos_iff _).mpr hγ0
      exact IsDiscreteValuationRing.exists_lift_of_le_one ((one_le_inv₀ hpos).mp h1)
    · have hz' := SmoothProjectiveCurve.eq_genericPoint_of_coheight_ne_one Ct z hco
      subst hz'
      refine ⟨γ, ?_⟩
      simp [RingHom.algebraMap_toAlgebra, TopCat.Presheaf.stalkSpecializes_refl]
  -- Step 2: local sections `r z ∈ O(W z)`, `W z ≤ U`, with germ `γ` at the generic point
  have hη : ∀ W : Ct.toScheme.Opens, ∀ z ∈ W, genericPoint Ct.toScheme ∈ W := fun W z hz =>
    (genericPoint_specializes z).mem_open W.isOpen hz
  have hloc : ∀ z : U, ∃ (W : Ct.toScheme.Opens) (_ : W ≤ U) (_ : (z : Ct.toScheme) ∈ W)
      (r : Γ(Ct.toScheme, W)),
      Ct.toScheme.presheaf.germ W (genericPoint Ct.toScheme) (hη W z ‹_›) r = γ := by
    rintro ⟨z, hz⟩
    obtain ⟨a, ha⟩ := hstalk z hz
    obtain ⟨W, hWU, hzW, r, hr⟩ := Ct.toScheme.presheaf.exists_le_germ_eq a hz
    refine ⟨W, hWU, hzW, r, ?_⟩
    have : Nonempty W := ⟨⟨z, hzW⟩⟩
    have h1 := Ct.toScheme.algebraMap_germ_eq_germToFunctionField hzW r
    rw [hr, ha] at h1
    exact h1.symm
  choose W hWU hzW r hr using hloc
  -- Step 3: the `r z` agree on overlaps (same generic germ) and glue to a section on `U`
  have hcompat : TopCat.Presheaf.IsCompatible Ct.toScheme.presheaf W r := by
    intro i j
    have : Nonempty (W i ⊓ W j : Ct.toScheme.Opens) := ⟨⟨_, hη _ _ (hzW i), hη _ _ (hzW j)⟩⟩
    apply Ct.toScheme.germToFunctionField_injective (W i ⊓ W j)
    show Ct.toScheme.presheaf.germ (W i ⊓ W j) (genericPoint Ct.toScheme) _ _ =
      Ct.toScheme.presheaf.germ (W i ⊓ W j) (genericPoint Ct.toScheme) _ _
    rw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply, hr i, hr j]
  obtain ⟨s, hs, -⟩ := Ct.toScheme.sheaf.existsUnique_gluing' W U (fun i => homOfLE (hWU i))
    (fun x hx => Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hzW ⟨x, hx⟩⟩) r hcompat
  refine ⟨s, ?_⟩
  obtain ⟨z₀⟩ := (inferInstance : Nonempty U)
  have h1 := hs z₀
  have h2 := congrArg (Ct.toScheme.presheaf.germ (W z₀) (genericPoint Ct.toScheme) (hη _ _ (hzW z₀))) h1
  rw [hr z₀] at h2
  rw [← h2]
  exact (TopCat.Presheaf.germ_res_apply Ct.toScheme.presheaf (homOfLE (hWU z₀)) _ _ s).symm

open Classical in
/-- **Weil coefficient of a finite `ℤ`-combination of points** `∑ y ∈ S, c y • [y]` on a smooth
projective curve, at a closed point `z`: it is `c z` if `z ∈ S` and `0` otherwise. Proof: `weilCycle`
is additive (`CartierDivisor.weilCycle_add`, hence an `AddMonoidHom` after composing with evaluation
at `z`), and `Divisor.ofPoint_weilCycle` gives the cycle of `[y]` for closed `y` (for non-closed `y`,
`Divisor.ofPoint y = 0`, and `z ≠ y` since `z` is closed). -/
theorem weilCycle_sum_zsmul_ofPoint (Ct : SmoothProjectiveCurve k) (S : Finset Ct.toScheme)
    (c : Ct.toScheme → ℤ) (z : Ct.toScheme) (hz : IsClosed ({z} : Set Ct.toScheme)) :
    (CartierDivisor.weilCycle Ct.toVariety (∑ y ∈ S, c y • Divisor.ofPoint y) :
        AlgebraicGeometry.AlgebraicCycle Ct.toScheme ℤ) z = if z ∈ S then c z else 0 := by
  classical
  have hzero : (CartierDivisor.weilCycle Ct.toVariety (0 : CartierDivisor Ct.toVariety) :
      AlgebraicGeometry.AlgebraicCycle Ct.toScheme ℤ) = 0 := by
    have h := congrArg Subtype.val (CartierDivisor.weilCycle_add Ct.toVariety 0 0)
    have h' : (CartierDivisor.weilCycle Ct.toVariety (0 : CartierDivisor Ct.toVariety) :
        AlgebraicGeometry.AlgebraicCycle Ct.toScheme ℤ) +
        (CartierDivisor.weilCycle Ct.toVariety (0 : CartierDivisor Ct.toVariety) :
          AlgebraicGeometry.AlgebraicCycle Ct.toScheme ℤ) =
        (CartierDivisor.weilCycle Ct.toVariety (0 : CartierDivisor Ct.toVariety) :
          AlgebraicGeometry.AlgebraicCycle Ct.toScheme ℤ) := by
      simpa using h.symm
    exact add_eq_left.mp h'
  let Wh : CartierDivisor Ct.toVariety →+ AlgebraicGeometry.AlgebraicCycle Ct.toScheme ℤ :=
    { toFun := fun D => (CartierDivisor.weilCycle Ct.toVariety D :
        AlgebraicGeometry.AlgebraicCycle Ct.toScheme ℤ)
      map_zero' := hzero
      map_add' := fun D E => congrArg Subtype.val (CartierDivisor.weilCycle_add Ct.toVariety D E) }
  let ev : AlgebraicGeometry.AlgebraicCycle Ct.toScheme ℤ →+ ℤ :=
    { toFun := fun d => d z
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hterm : ∀ y : Ct.toScheme, (ev.comp Wh) (Divisor.ofPoint y) = if z = y then 1 else 0 := by
    intro y
    by_cases hy : IsClosed ({y} : Set Ct.toScheme)
    · exact Divisor.ofPoint_weilCycle y hy z
    · have hne : z ≠ y := fun h => hy (h ▸ hz)
      rw [Divisor.ofPoint_of_not_isClosed y hy, map_zero, if_neg hne]
  change (ev.comp Wh) (∑ y ∈ S, c y • Divisor.ofPoint y) = _
  rw [map_sum]
  simp_rw [map_zsmul, hterm]
  simp [Finset.sum_ite_eq]

/-- **The line bundle of a finitely supported weight function and its canonical rational section**
(Lemma 3.1 of the paper; Hartshorne II.6.13). Let `w : C̃ → ℤ` have finite
support. Then there are a line bundle `L` on `C̃` — namely `L = O_{C̃}(D)` with `D = Σ_y w_y [y]` — and a
nonzero element `s` of the stalk `L_η` at the generic point (the canonical rational section `s_L`)
such that for every open `U ∋ η`, every frame `e` of `L` on `U` and the coefficient `γ ∈ K(C̃)` with
`s = γ • e_η`: `ord_z γ = w z` at every point `z ∈ U` of coheight `1`.

Proof (the library contains Hartshorne II.6.13 in section form):
1. **The divisor.** `D := ∑ y ∈ supp w, w y • Divisor.ofPoint y` (`Divisor.ofPoint`;
   a genuine `Finset` sum since `w` has finite support), `L := D.lineBundle`
   (`CartierDivisor.lineBundle`). Its Weil cycle has coefficient `w z` at
   every closed `z` (`weilCycle_sum_zsmul_ofPoint` above: additivity of `CartierDivisor.weilCycle` +
   `Divisor.ofPoint_weilCycle`).
2. **The rational section.** `CartierDivisor.exists_rationalSectionDivisor_eq_weilCycle`
   (Hartshorne II.6.13 in section form) gives a
   nonzero `s ∈ L_η` with `div_L(s) = [D]` as algebraic cycles, i.e. `rationalSectionOrd L s z =
   [D]_z` for every `z` (`rationalSectionDivisor_apply`).
3. **Orders of the coefficient.** For a frame `e` of `L` on `U ∋ η, z`, the germ `e_z` generates `L_z`
   (`IsFrame.span_germ_eq_top`) and its image in `L_η` is `e_η` (`moduleStalkToGenericFiber_germ`);
   `s = γ • e_η` therefore gives `rationalSectionOrd L s z = ord_z γ`
   (`rationalSectionOrd_eq_ord_of_generator`, , the
   independence of `ord_{z,L}(s)` from the chosen generator). A point of coheight `1` on the curve is
   closed (`AlgebraicGeometry.Intersection.isClosed_singleton_of_coheight_eq_one` with `dim C̃ = 1`), so step 1
   gives `ord_z γ = [D]_z = w z`. ∎

Edge cases: `w = 0` (then `D = 0`, `L = O(0)`, `s` is a nonzero rational section with `div(s) = 0`,
so every frame coefficient has order `0`); `w η ≠ 0` is allowed by the statement (`Divisor.ofPoint η = 0`
since `η` is not closed, and the conclusion only speaks about coheight-`1` points); `U` need not be
affine. -/
theorem exists_lineBundle_rationalSection_of_weightFunction (Ct : SmoothProjectiveCurve k)
    (w : Ct.toScheme → ℤ) (hw : (Function.support w).Finite) :
    ∃ (L : LineBundle Ct.toVariety) (s : L.toModules.stalk (genericPoint Ct.toScheme)),
      s ≠ 0 ∧
      ∀ (U : Ct.toScheme.Opens) (hηU : genericPoint Ct.toScheme ∈ U) (e : Γ(L.toModules, U))
        (_ : AlgebraicGeometry.Scheme.Modules.IsFrame L.toModules U e)
        (γ : Ct.toScheme.functionField),
        s = γ • (L.toModules.presheaf.germ U (genericPoint Ct.toScheme) hηU e :
          L.toModules.stalk (genericPoint Ct.toScheme)) →
        ∀ z ∈ U, Order.coheight z = 1 → Ct.toScheme.ord γ z = w z := by
  classical
  let D : CartierDivisor Ct.toVariety := ∑ y ∈ hw.toFinset, w y • Divisor.ofPoint y
  have hD : ∀ z : Ct.toScheme, IsClosed ({z} : Set Ct.toScheme) →
      (CartierDivisor.weilCycle Ct.toVariety D :
        AlgebraicGeometry.AlgebraicCycle Ct.toScheme ℤ) z = w z := by
    intro z hz
    rw [weilCycle_sum_zsmul_ofPoint Ct hw.toFinset w z hz]
    split_ifs with hmem
    · rfl
    · rw [Set.Finite.mem_toFinset, Function.mem_support, not_not] at hmem
      exact hmem.symm
  obtain ⟨s, hs, hdiv⟩ := CartierDivisor.exists_rationalSectionDivisor_eq_weilCycle Ct.toVariety D
  refine ⟨D.lineBundle, s, hs, ?_⟩
  intro U hηU e he γ hγ z hz hco
  have hzc : IsClosed ({z} : Set Ct.toScheme) :=
    AlgebraicGeometry.Intersection.isClosed_singleton_of_coheight_eq_one (le_of_eq Ct.dim_one) z hco
  have hgen := he.span_germ_eq_top hz
  have hord := AlgebraicGeometry.Scheme.Modules.rationalSectionOrd_eq_ord_of_generator
    D.lineBundle.toModules z _ hgen γ s hs
    (by rw [AlgebraicGeometry.Scheme.Modules.moduleStalkToGenericFiber_germ]; exact hγ.symm)
  rw [← hord, ← AlgebraicGeometry.Scheme.Modules.rationalSectionDivisor_apply, hdiv, hD z hzc]

end
