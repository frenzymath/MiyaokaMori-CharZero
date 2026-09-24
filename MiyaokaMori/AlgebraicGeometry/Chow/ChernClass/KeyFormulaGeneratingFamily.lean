import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.KeyFormulaCapPointLemmas
import MiyaokaMori.AlgebraicGeometry.Divisors.RationalSections.RationalSectionGeneratingLocus

/-! # Key formula cycle core, indexed by the non-generating locus (Stacks 0AYC, steps (G1)(G2)(G3))

This is the corrected form of `exists_keyFormula_principalFamily_of_normalizationFinite`
(`CycleIdentitySplit.lean`): the family `c_w` is indexed by the Stacks index set
`J := {w | coheight w = 1 ∧ ¬ (s generates L at w ∧ t generates N at w)}`
(chow.tex, "The key formula": "a locally finite set of irreducible closed subsets of codimension 1 such
that `s` and `t` are generators outside them"), instead of by `Supp div_L(s) ∪ Supp div_N(t)`. The two
agree at normal codimension-1 points, but at a non-normal `w` the length-based `ord_w` can vanish on a
non-unit coordinate, and then the support-indexed statement is false (counterexample in the docstring of
`exists_keyFormula_principalFamily_of_normalizationFinite`). With the Stacks index set the proof of 0AYC
goes through verbatim; the two mathematical inputs are the black boxes
`keyFormula_finsum_tameCycle_eq_zero` (scheme-level 0EAX) and the hypothesis `hnorm` (finite normalization
of the stalks, `keyFormula_module_finite_integralClosure_stalk`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry

open Scheme.Modules MiyaokaMori.FirstChernCapPointGeneric

attribute [local instance] Scheme.isLocallyNoetherian_pointClosure

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]

/-- **(G3), one point `w` at a time (Stacks 0AYC, third paragraph).**

Fix `w` of coheight `1` and height `n + 1`, generators `s_w, t_w` of `L_w, N_w` with coordinates
`s = f_w • j(s_w)`, `t = g_w • j(t_w)`, and `φ, ψ ∈ K(W_w)^*` with (G1a)
`firstChernCapPoint L w = (ι_w)_* div_{ι^*L}(s_w|) + (ι_w)_* div φ` (likewise `N, t_w, ψ`). Fix also a point
`z` with generators `σ, τ` of `L_z, N_z` and coordinates `s = f • j(σ)`, `t = g • j(τ)`. Then, with
`c_w := (ι_w)_* div(∂_w(f_w, g_w) · ψ^{ord f_w} · φ^{-ord g_w})`,
`  [div_L(s) w · (c_1(N) ∩ [W_w])(z)] − [div_N(t) w · (c_1(L) ∩ [W_w])(z)] = c_w(z) − ((ι_w)_* div ∂_w(f, g))(z)`.

Proof. If `¬ w ⤳ z` every term is `0` (all four cycles are pushforwards from `W_w = closure {w}`). If
`w ⤳ z`: `σ|_w, τ|_w` generate `L_w, N_w`, so `s_w = a • σ|_w`, `t_w = b • τ|_w` with `a, b ∈ O_{X,w}^*`
and `f = a f_w`, `g = b g_w` (`exists_units_mul_eq_of_generators`); `div_L(s) w = ord_w f_w`
(`rationalSectionOrd_eq_ord_of_generator`); `((ι_w)_* div_{ι^*N}(t_w|))(z) = ((ι_w)_* div b̄)(z)`
(`keyFormula_pullback_generator_coeff`); and `∂_w(f, g) = ∂_w(f_w, g_w) · ā^{ord g_w} · b̄^{-ord f_w}`
(`keyFormulaTameSymbol_unit_mul`). Expanding `div` of products and powers, both sides equal
`ord f_w · (Ψ + B) − ord g_w · (Φ + A)` where `Φ, Ψ, A, B` are the coefficients at `z` of
`(ι_w)_* div φ, ψ, ā, b̄`. -/
theorem keyFormula_pointwise_identity (K : Type u) [Field K] (π : X ⟶ Spec (CommRingCat.of K))
    [LocallyOfFiniteType π] (L N : X.Modules) [L.IsLineBundle] [N.IsLineBundle] (n : ℕ)
    (s : L.stalk (genericPoint X)) (t : N.stalk (genericPoint X)) (hs : s ≠ 0) (ht : t ≠ 0)
    {w z : X} (hw : Order.coheight w = 1)
    (hfin : Module.Finite (X.presheaf.stalk w) (integralClosure (X.presheaf.stalk w) X.functionField))
    (hht : Order.height w = ((n + 1 : ℕ) : ℕ∞))
    (sw : L.presheaf.stalk w) (hsw : Submodule.span (X.presheaf.stalk w) {sw} = ⊤)
    (fw : X.functionField) (hfw : fw • AlgebraicGeometry.Scheme.Modules.moduleStalkToGenericFiber X L w sw = s) (hfw0 : fw ≠ 0)
    (tw : N.presheaf.stalk w) (htw : Submodule.span (X.presheaf.stalk w) {tw} = ⊤)
    (gw : X.functionField) (hgw : gw • AlgebraicGeometry.Scheme.Modules.moduleStalkToGenericFiber X N w tw = t) (hgw0 : gw ≠ 0)
    (φ ψ : (X.pointClosure w).functionFieldˣ)
    (hφ : firstChernCapPoint L w
        = AlgebraicGeometry.AlgebraicCycle.properPushforward (X.pointClosureι w)
            (((Scheme.Modules.pullback (X.pointClosureι w)).obj L).rationalSectionDivisor
              (AlgebraicGeometry.Scheme.Modules.modulePullbackStalkUnit (X.pointClosureι w) L (genericPoint (X.pointClosure w))
                (AlgebraicGeometry.Scheme.Modules.moduleStalkSpecializes X L (specializes_of_eq (Scheme.pointClosureι_genericPoint w)) sw)))
          + AlgebraicGeometry.AlgebraicCycle.properPushforward (X.pointClosureι w) ((X.pointClosure w).principalCycle φ))
    (hψ : firstChernCapPoint N w
        = AlgebraicGeometry.AlgebraicCycle.properPushforward (X.pointClosureι w)
            (((Scheme.Modules.pullback (X.pointClosureι w)).obj N).rationalSectionDivisor
              (AlgebraicGeometry.Scheme.Modules.modulePullbackStalkUnit (X.pointClosureι w) N (genericPoint (X.pointClosure w))
                (AlgebraicGeometry.Scheme.Modules.moduleStalkSpecializes X N (specializes_of_eq (Scheme.pointClosureι_genericPoint w)) tw)))
          + AlgebraicGeometry.AlgebraicCycle.properPushforward (X.pointClosureι w) ((X.pointClosure w).principalCycle ψ))
    (σ : L.presheaf.stalk z) (hσ : Submodule.span (X.presheaf.stalk z) {σ} = ⊤)
    (f : X.functionField) (hf : f • AlgebraicGeometry.Scheme.Modules.moduleStalkToGenericFiber X L z σ = s) (hf0 : f ≠ 0)
    (τ : N.presheaf.stalk z) (hτ : Submodule.span (X.presheaf.stalk z) {τ} = ⊤)
    (g : X.functionField) (hg : g • AlgebraicGeometry.Scheme.Modules.moduleStalkToGenericFiber X N z τ = t) (hg0 : g ≠ 0) :
    firstChernCapTerm N (n + 1) (L.rationalSectionDivisor s) z w
        - firstChernCapTerm L (n + 1) (N.rationalSectionDivisor t) z w
      = AlgebraicGeometry.AlgebraicCycle.properPushforward (X.pointClosureι w) ((X.pointClosure w).principalCycle
            (X.keyFormulaTameSymbol w hw hfin (Units.mk0 fw hfw0) (Units.mk0 gw hgw0) *
              ψ ^ X.ord fw w * (φ ^ X.ord gw w)⁻¹)) z
        - X.keyFormulaTameCycle w hw hfin (Units.mk0 f hf0) (Units.mk0 g hg0) z := by
  -- expand `div` of the product on the right
  have hexp : ∀ (A B C : (X.pointClosure w).functionFieldˣ) (m k : ℤ),
      AlgebraicGeometry.AlgebraicCycle.properPushforward (X.pointClosureι w)
          ((X.pointClosure w).principalCycle (A * B ^ m * (C ^ k)⁻¹)) z
        = AlgebraicGeometry.AlgebraicCycle.properPushforward (X.pointClosureι w) ((X.pointClosure w).principalCycle A) z
          + m * AlgebraicGeometry.AlgebraicCycle.properPushforward (X.pointClosureι w) ((X.pointClosure w).principalCycle B) z
          - k * AlgebraicGeometry.AlgebraicCycle.properPushforward (X.pointClosureι w) ((X.pointClosure w).principalCycle C) z := by
    intro A B C m k
    rw [Scheme.principalCycle_mul, Scheme.principalCycle_mul, Scheme.principalCycle_inv,
      Scheme.principalCycle_zpow, Scheme.principalCycle_zpow, properPushforward_add, properPushforward_add,
      AlgebraicCycle.properPushforward_neg, AlgebraicCycle.properPushforward_zsmul,
      AlgebraicCycle.properPushforward_zsmul]
    simp only [Function.locallyFinsuppWithin.coe_add, Function.locallyFinsuppWithin.coe_neg, Pi.add_apply,
      Pi.neg_apply, AlgebraicCycle.zsmul_apply]
    ring
  -- the terms of the linear extension
  unfold firstChernCapTerm
  rw [if_pos hht, if_pos hht]
  by_cases hwz : w ⤳ z
  · -- coordinate change from `z` to `w`
    obtain ⟨a, hsa, hfa⟩ := exists_units_mul_eq_of_generators L hwz σ hσ sw hsw f fw hf hfw
    obtain ⟨b, htb, hgb⟩ := exists_units_mul_eq_of_generators N hwz τ hτ tw htw g gw hg hgw
    -- (G1a) + `keyFormula_pullback_generator_coeff`
    have hcapL : firstChernCapPoint L w z
        = X.residueUnitCycle w a z
          + AlgebraicGeometry.AlgebraicCycle.properPushforward (X.pointClosureι w) ((X.pointClosure w).principalCycle φ) z := by
      rw [hφ, Function.locallyFinsuppWithin.coe_add, Pi.add_apply, hsa]
      congr 1
      exact X.keyFormula_pullback_generator_coeff L hwz hw σ hσ a
    have hcapN : firstChernCapPoint N w z
        = X.residueUnitCycle w b z
          + AlgebraicGeometry.AlgebraicCycle.properPushforward (X.pointClosureι w) ((X.pointClosure w).principalCycle ψ) z := by
      rw [hψ, Function.locallyFinsuppWithin.coe_add, Pi.add_apply, htb]
      congr 1
      exact X.keyFormula_pullback_generator_coeff N hwz hw τ hτ b
    -- the orders
    have hordL : L.rationalSectionDivisor s w = X.ord fw w :=
      rationalSectionOrd_eq_ord_of_generator L w sw hsw fw s hs hfw
    have hordN : N.rationalSectionDivisor t w = X.ord gw w :=
      rationalSectionOrd_eq_ord_of_generator N w tw htw gw t ht hgw
    -- the tame symbol of the `z`-coordinates
    have hfu : Units.mk0 f hf0
        = Units.map (algebraMap (X.presheaf.stalk w) X.functionField).toMonoidHom a * Units.mk0 fw hfw0 :=
      Units.ext (by rw [Units.val_mul, Units.val_mk0, Units.val_mk0, Units.coe_map]; exact hfa)
    have hgu : Units.mk0 g hg0
        = Units.map (algebraMap (X.presheaf.stalk w) X.functionField).toMonoidHom b * Units.mk0 gw hgw0 :=
      Units.ext (by rw [Units.val_mul, Units.val_mk0, Units.val_mk0, Units.coe_map]; exact hgb)
    have htame : X.keyFormulaTameCycle w hw hfin (Units.mk0 f hf0) (Units.mk0 g hg0) z
        = AlgebraicGeometry.AlgebraicCycle.properPushforward (X.pointClosureι w) ((X.pointClosure w).principalCycle
            (X.keyFormulaTameSymbol w hw hfin (Units.mk0 fw hfw0) (Units.mk0 gw hgw0))) z
          + X.ord gw w * X.residueUnitCycle w a z - X.ord fw w * X.residueUnitCycle w b z := by
      rw [hfu, hgu]
      unfold Scheme.keyFormulaTameCycle
      rw [X.keyFormulaTameSymbol_unit_mul w hw hfin a b (Units.mk0 fw hfw0) (Units.mk0 gw hgw0),
        Units.val_mk0, Units.val_mk0, hexp]
      rfl
    rw [hcapL, hcapN, hordL, hordN, htame, hexp]
    ring
  · -- `w` does not specialize to `z`: everything vanishes
    have h1 : firstChernCapPoint L w z = 0 := by
      by_contra h; exact hwz (firstChernCapPoint_specializes L h)
    have h2 : firstChernCapPoint N w z = 0 := by
      by_contra h; exact hwz (firstChernCapPoint_specializes N h)
    have h3 : AlgebraicGeometry.AlgebraicCycle.properPushforward (X.pointClosureι w) ((X.pointClosure w).principalCycle
        (X.keyFormulaTameSymbol w hw hfin (Units.mk0 fw hfw0) (Units.mk0 gw hgw0) *
          ψ ^ X.ord fw w * (φ ^ X.ord gw w)⁻¹)) z = 0 := by
      by_contra h; exact hwz (properPushforward_pointClosure_specializes _ h)
    have h4 : X.keyFormulaTameCycle w hw hfin (Units.mk0 f hf0) (Units.mk0 g hg0) z = 0 := by
      by_contra h
      exact hwz ((X.isRatEquivGen_keyFormulaTameCycle w hw hfin _ _ n hht).specializes h)
    rw [h1, h2, h3, h4]
    ring

/-- **Key formula cycle core, Stacks index set (Stacks 0AYC, steps (G1)(G2)(G3); given finite normalization
of the stalks).**

Statement. `X` integral, locally of finite type over a field `K`, `dim X = n + 2`; `L, N` line bundles with
nonzero rational sections `s, t`; every stalk has finite normalization in `K(X)` (`hnorm`). Let
`J := {w | coheight w = 1 ∧ ¬ (s generates L at w ∧ t generates N at w)}` (Stacks: the codimension-1 points
`ξ_i` of the `Z_i`; `Supp div_L(s) ∪ Supp div_N(t) ⊆ J` by `RationalSectionGeneratesAt.rationalSectionOrd_eq_zero`). Then
there is a family `c : J → Z_n(X)` of Stacks 02RW generators, `c_w = (ι_w)_* div(h_w)`, `h_w ∈ K(W_w)^*`,
with `c_1(N) ∩ div_L(s) − c_1(L) ∩ div_N(t) = Σ_{w ∈ J} c_w` pointwise.

Proof (Stacks 0AYC; all steps are named declarations of this library).
* (Ga′) `w ∈ J ⇒ height w = n + 1` (`height_eq_of_coheight_eq_one`, 0A21).
* (G1) For `w ∈ J` choose generators `s_w, t_w` of `L_w, N_w` (`exists_stalk_generator`), coordinates
  `f_w, g_w ∈ K(X)^*` (`exists_smul_toGenericFiber_eq`), and by (G1b) + (G1a)
  (`modulePullbackStalkUnit_genericPoint_ne_zero`, `exists_firstChernCapPoint_eq_add_principalCycle`)
  `φ_w, ψ_w ∈ K(W_w)^*` with `firstChernCapPoint L w = (ι_w)_* div_{ι^*L}(s_w|) + (ι_w)_* div φ_w`, etc.
* (G2) `h_w := ∂_w(f_w, g_w) · ψ_w^{ord f_w} · φ_w^{-ord g_w}` (`keyFormulaTameSymbol`, needs `coheight w = 1`
  and `hnorm w`); `c_w := (ι_w)_* div(h_w)` is `IsRatEquivGen X n w` by definition and (Ga′).
* (G3) Fix `z`; choose generators `σ, τ` of `L_z, N_z` and coordinates `f, g`. By
  `keyFormula_pointwise_identity`, for every `w ∈ J`:
  `term_N(w) − term_L(w) = c_w(z) − ((ι_w)_* div ∂_w(f, g))(z)`, where `term_N(w)` is the `w`-summand of
  `(c_1(N) ∩ div_L(s))(z)`. Summing over `w` (the `w`-summands vanish off `J`, since `ord_w s ≠ 0` forces
  `coheight w = 1` and `¬ RationalSectionGeneratesAt L s w`; all supports are finite by `firstChernCapTerm_support_finite`):
  `LHS(z) = Σ_{w∈J} c_w(z) − Σ_{w∈J} ((ι_w)_* div ∂_w(f, g))(z)`. The last sum is `0`:
  - if `height z = n`, then `coheight z = 2` (0A21) and the sum over `J` equals the sum over all
    `w ⤳ z` of coheight `1` (for `w ∉ J`, `f, g ∈ O_{X,w}^*`, so `∂_w(f, g) = 1`:
    `keyFormulaTameCycle_eq_zero_of_generatesAt`; for `w` not specializing to `z` the coefficient is `0`),
    which is `0` by the scheme-level Key Lemma `keyFormula_finsum_tameCycle_eq_zero` (Stacks 0EAX);
  - if `height z ≠ n`, every summand is `0` (`IsRatEquivGen.height_eq_of_ne_zero`).
Edge cases: `J = ∅` (`s, t` generate everywhere in codimension 1): both sides are `0`. `L = N, s = t`: fine.
`n = 0`: `z` a closed point of a surface. Non-normal `w ∈ J` with `ord_w s = ord_w t = 0`: this is exactly where
the support-indexed statement fails and the present index set is needed.

Users: the parent `keyFormula_cycle_identity` / `keyFormula_ratEquivZero` should be re-indexed by `J`; the only
new obligation is that `J` is a locally finite family of points (the codimension-1 points of the closed
non-generating locus), proved in `KeyFormulaNonGeneratingLocusLocallyFinite.lean`. -/
theorem exists_keyFormula_principalFamily_generating_of_normalizationFinite
    (K : Type u) [Field K] (π : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType π]
    (L N : X.Modules) [L.IsLineBundle] [N.IsLineBundle] (n : ℕ) (hX : X.dimension = n + 2)
    (s : L.stalk (genericPoint X)) (t : N.stalk (genericPoint X)) (hs : s ≠ 0) (ht : t ≠ 0)
    (hnorm : ∀ x : X, Module.Finite (X.presheaf.stalk x)
      (integralClosure (X.presheaf.stalk x) X.functionField)) :
    ∃ c : ↥{w : X | Order.coheight w = 1 ∧ ¬ (L.RationalSectionGeneratesAt s w ∧ N.RationalSectionGeneratesAt t w)} → AlgebraicCycle X ℤ,
      (∀ w, IsRatEquivGen X n w.1 (c w)) ∧
      ∀ z : X,
        (firstChernCapCycleAux N (n + 1) (L.rationalSectionDivisor s)
          - firstChernCapCycleAux L (n + 1) (N.rationalSectionDivisor t)) z = ∑ᶠ w, c w z := by
  set Jset : Set X := {w : X | Order.coheight w = 1 ∧ ¬ (L.RationalSectionGeneratesAt s w ∧ N.RationalSectionGeneratesAt t w)} with hJset
  have hJ : ∀ w : Jset, Order.coheight w.1 = 1 ∧ ¬ (L.RationalSectionGeneratesAt s w.1 ∧ N.RationalSectionGeneratesAt t w.1) :=
    fun w => w.2
  have hht : ∀ w : Jset, Order.height w.1 = ((n + 1 : ℕ) : ℕ∞) :=
    fun w => height_eq_of_coheight_eq_one K π n hX (hJ w).1
  -- (G1) generators and coordinates at `w`
  choose sw hsw using fun w : Jset => exists_stalk_generator L w.1
  choose fw hfw using fun w : Jset => exists_smul_toGenericFiber_eq L w.1 (sw w) (hsw w) s
  choose tw htw using fun w : Jset => exists_stalk_generator N w.1
  choose gw hgw using fun w : Jset => exists_smul_toGenericFiber_eq N w.1 (tw w) (htw w) t
  have hfw0 : ∀ w, fw w ≠ 0 := fun w h => hs (by rw [← hfw w, h, zero_smul]; rfl)
  have hgw0 : ∀ w, gw w ≠ 0 := fun w h => ht (by rw [← hgw w, h, zero_smul]; rfl)
  -- (G1b): the generators restrict to nonzero elements of the generic stalks on `W_w`
  have hgen : ∀ (M : X.Modules) [M.IsLineBundle] (w : X) (m : M.presheaf.stalk w)
      (hm : Submodule.span (X.presheaf.stalk w) {m} = ⊤),
      ∀ τ : M.presheaf.stalk ((X.pointClosureι w).base (genericPoint (X.pointClosure w))),
        ∃ r : X.presheaf.stalk ((X.pointClosureι w).base (genericPoint (X.pointClosure w))),
          τ = r • AlgebraicGeometry.Scheme.Modules.moduleStalkSpecializes X M
            (specializes_of_eq (Scheme.pointClosureι_genericPoint w)) m := by
    intro M _ w m hm τ
    have h := span_moduleStalkSpecializes_eq_top M
      (specializes_of_eq (Scheme.pointClosureι_genericPoint w)) m hm
    have hτ : τ ∈ Submodule.span (X.presheaf.stalk ((X.pointClosureι w).base (genericPoint (X.pointClosure w))))
        {AlgebraicGeometry.Scheme.Modules.moduleStalkSpecializes X M (specializes_of_eq (Scheme.pointClosureι_genericPoint w)) m} := by
      rw [h]; trivial
    obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.mp hτ
    exact ⟨r, hr.symm⟩
  -- (G1a)
  choose φ hφ using fun w : Jset => exists_firstChernCapPoint_eq_add_principalCycle L w.1 _
    (modulePullbackStalkUnit_genericPoint_ne_zero L w.1 _ (hgen L w.1 (sw w) (hsw w)))
  choose ψ hψ using fun w : Jset => exists_firstChernCapPoint_eq_add_principalCycle N w.1 _
    (modulePullbackStalkUnit_genericPoint_ne_zero N w.1 _ (hgen N w.1 (tw w) (htw w)))
  -- (G2) the family
  let hsym : ∀ w : Jset, (X.pointClosure w.1).functionFieldˣ := fun w =>
    X.keyFormulaTameSymbol w.1 (hJ w).1 (hnorm w.1) (Units.mk0 (fw w) (hfw0 w)) (Units.mk0 (gw w) (hgw0 w)) *
      ψ w ^ X.ord (fw w) w.1 * (φ w ^ X.ord (gw w) w.1)⁻¹
  refine ⟨fun w => AlgebraicGeometry.AlgebraicCycle.properPushforward (X.pointClosureι w.1)
    ((X.pointClosure w.1).principalCycle (hsym w)), fun w => ?_, fun z => ?_⟩
  · exact ⟨hht w, Scheme.isIntegral_pointClosure w.1, inferInstance,
      Scheme.isLocallyNoetherian_pointClosure w.1, hsym w, rfl⟩
  -- (G3) at `z`
  obtain ⟨σ, hσ⟩ := exists_stalk_generator L z
  obtain ⟨f, hf⟩ := exists_smul_toGenericFiber_eq L z σ hσ s
  obtain ⟨τ, hτ⟩ := exists_stalk_generator N z
  obtain ⟨g, hg⟩ := exists_smul_toGenericFiber_eq N z τ hτ t
  have hf0 : f ≠ 0 := fun h => hs (by rw [← hf, h, zero_smul]; rfl)
  have hg0 : g ≠ 0 := fun h => ht (by rw [← hg, h, zero_smul]; rfl)
  set fu := Units.mk0 f hf0 with hfu
  set gu := Units.mk0 g hg0 with hgu
  -- the pointwise identity for each `w ∈ J`
  have hstar : ∀ w : Jset,
      firstChernCapTerm N (n + 1) (L.rationalSectionDivisor s) z w.1
          - firstChernCapTerm L (n + 1) (N.rationalSectionDivisor t) z w.1
        = AlgebraicGeometry.AlgebraicCycle.properPushforward (X.pointClosureι w.1)
            ((X.pointClosure w.1).principalCycle (hsym w)) z
          - X.keyFormulaTameCycle w.1 (hJ w).1 (hnorm w.1) fu gu z := fun w =>
    keyFormula_pointwise_identity K π L N n s t hs ht (hJ w).1 (hnorm w.1) (hht w) (sw w) (hsw w) (fw w)
      (hfw w) (hfw0 w) (tw w) (htw w) (gw w) (hgw w) (hgw0 w) (φ w) (ψ w) (hφ w) (hψ w) σ hσ f hf hf0 τ hτ
      g hg hg0
  -- the tame-symbol sum vanishes (Stacks 0EAX)
  let G : X → ℤ := fun w => if h : Order.coheight w = 1 then X.keyFormulaTameCycle w h (hnorm w) fu gu z else 0
  have hGpos : ∀ (w : X) (hw : Order.coheight w = 1), G w = X.keyFormulaTameCycle w hw (hnorm w) fu gu z :=
    fun w hw => by simp only [G]; rw [dif_pos hw]
  have hGneg : ∀ (w : X), ¬ Order.coheight w = 1 → G w = 0 :=
    fun w hw => by simp only [G]; rw [dif_neg hw]
  have hGJ : ∀ w : Jset, X.keyFormulaTameCycle w.1 (hJ w).1 (hnorm w.1) fu gu z = G w.1 :=
    fun w => (hGpos w.1 (hJ w).1).symm
  have hGsupp : ∀ w, G w ≠ 0 → w ∈ Jset ∧ w ⤳ z := by
    intro w hGw
    by_cases hw : Order.coheight w = 1
    · have hne : X.keyFormulaTameCycle w hw (hnorm w) fu gu z ≠ 0 := by
        rwa [hGpos w hw] at hGw
      have hwz : w ⤳ z := by
        by_contra h
        exact hne (by
          by_contra h'
          exact h (properPushforward_pointClosure_specializes _ h'))
      refine ⟨⟨hw, fun hLN => hne ?_⟩, hwz⟩
      rw [keyFormulaTameCycle_eq_zero_of_generatesAt L N hwz hw (hnorm w) σ hσ τ hτ fu gu hf hg hLN.1 hLN.2]
      rfl
    · exact absurd (hGneg w hw) hGw
  have hGfin : (Function.support fun w : Jset => G w.1).Finite ∧ (∑ᶠ w : Jset, G w.1) = 0 := by
    by_cases hz : Order.height z = (n : ℕ∞)
    · have hz2 : Order.coheight z = 2 := coheight_eq_two_of_height_eq K π n hX hz
      obtain ⟨hPfin, hPsum⟩ := X.keyFormula_finsum_tameCycle_eq_zero hnorm z hz2 fu gu
      set Pset : Set X := {w : X | w ⤳ z ∧ Order.coheight w = 1} with hPset
      have hGP : ∀ w : Pset, X.keyFormulaTameCycle w.1 w.2.2 (hnorm w.1) fu gu z = G w.1 :=
        fun w => (hGpos w.1 w.2.2).symm
      have hsuppG : Function.support G ⊆ Subtype.val '' (Function.support fun w : Pset => G w.1) := by
        intro w hw
        have hw' := hGsupp w hw
        exact ⟨⟨w, hw'.2, (hGsupp w hw).1.1⟩, hw, rfl⟩
      have hGfin' : (Function.support fun w : Pset => G w.1).Finite := by
        refine hPfin.subset ?_
        intro w hw
        rw [Function.mem_support] at hw ⊢
        rw [hGP w]
        exact hw
      refine ⟨((hGfin'.image Subtype.val).subset hsuppG).preimage Subtype.val_injective.injOn, ?_⟩
      have hinter : Jset ∩ Function.support G = Pset ∩ Function.support G := by
        ext w
        constructor
        · rintro ⟨-, hw⟩; exact ⟨⟨(hGsupp w hw).2, (hGsupp w hw).1.1⟩, hw⟩
        · rintro ⟨-, hw⟩; exact ⟨(hGsupp w hw).1, hw⟩
      calc (∑ᶠ w : Jset, G w.1) = ∑ᶠ w ∈ Jset, G w := finsum_set_coe_eq_finsum_mem Jset
        _ = ∑ᶠ w ∈ Pset, G w := finsum_mem_inter_support_eq G Jset Pset hinter
        _ = ∑ᶠ w : Pset, G w.1 := (finsum_set_coe_eq_finsum_mem Pset).symm
        _ = ∑ᶠ w : Pset, X.keyFormulaTameCycle w.1 w.2.2 (hnorm w.1) fu gu z := finsum_congr fun w => (hGP w).symm
        _ = 0 := hPsum
    · have hG0 : ∀ w, G w = 0 := by
        intro w
        by_contra hGw
        have hw := (hGsupp w hGw).1.1
        have hne : X.keyFormulaTameCycle w hw (hnorm w) fu gu z ≠ 0 := by
          rwa [hGpos w hw] at hGw
        exact hz ((X.isRatEquivGen_keyFormulaTameCycle w hw (hnorm w) fu gu n
          (height_eq_of_coheight_eq_one K π n hX hw)).height_eq_of_ne_zero K π hne)
      refine ⟨?_, finsum_eq_zero_of_forall_eq_zero fun w => hG0 w.1⟩
      convert Set.finite_empty
      ext w
      simp [hG0]
  -- the linear extension is a sum over `J`
  have hconv : ∀ F : X → ℤ, Function.support F ⊆ Jset → ∑ᶠ w, F w = ∑ᶠ w : Jset, F w.1 := by
    intro F hF
    rw [← finsum_mem_univ, finsum_mem_inter_support_eq F Set.univ Jset
      (by rw [Set.univ_inter, Set.inter_eq_right.mpr hF]), ← finsum_set_coe_eq_finsum_mem]
  have hsuppN : Function.support (firstChernCapTerm N (n + 1) (L.rationalSectionDivisor s) z) ⊆ Jset := by
    intro w hw
    have hα := (firstChernCapTerm_ne_zero N hw).2.1
    refine ⟨rationalSectionDivisor_support L s w hα, fun h => hα ?_⟩
    exact h.1.rationalSectionOrd_eq_zero L
  have hsuppL : Function.support (firstChernCapTerm L (n + 1) (N.rationalSectionDivisor t) z) ⊆ Jset := by
    intro w hw
    have hα := (firstChernCapTerm_ne_zero L hw).2.1
    refine ⟨rationalSectionDivisor_support N t w hα, fun h => hα ?_⟩
    exact h.2.rationalSectionOrd_eq_zero N
  have hfinN : (Function.support fun w : Jset =>
      firstChernCapTerm N (n + 1) (L.rationalSectionDivisor s) z w.1).Finite :=
    (firstChernCapTerm_support_finite N (n + 1) _ z).preimage Subtype.val_injective.injOn
  have hfinL : (Function.support fun w : Jset =>
      firstChernCapTerm L (n + 1) (N.rationalSectionDivisor t) z w.1).Finite :=
    (firstChernCapTerm_support_finite L (n + 1) _ z).preimage Subtype.val_injective.injOn
  have hfinc : (Function.support fun w : Jset => AlgebraicGeometry.AlgebraicCycle.properPushforward (X.pointClosureι w.1)
      ((X.pointClosure w.1).principalCycle (hsym w)) z).Finite := by
    refine ((hfinN.union hfinL).union hGfin.1).subset ?_
    intro w hw
    by_contra hcon
    simp only [Set.mem_union, Function.mem_support, not_or, not_not] at hcon
    apply hw
    have h := hstar w
    rw [hGJ w, hcon.1.1, hcon.1.2, hcon.2, sub_zero, sub_zero] at h
    exact h.symm
  show (∑ᶠ w : X, firstChernCapTerm N (n + 1) (L.rationalSectionDivisor s) z w)
      - (∑ᶠ w : X, firstChernCapTerm L (n + 1) (N.rationalSectionDivisor t) z w) = _
  rw [hconv _ hsuppN, hconv _ hsuppL, ← finsum_sub_distrib hfinN hfinL, finsum_congr hstar,
    finsum_sub_distrib hfinc (by rw [show (fun w : Jset => X.keyFormulaTameCycle w.1 (hJ w).1 (hnorm w.1) fu gu z)
      = fun w : Jset => G w.1 from funext hGJ]; exact hGfin.1),
    finsum_congr hGJ, hGfin.2, sub_zero]

end AlgebraicGeometry

end
