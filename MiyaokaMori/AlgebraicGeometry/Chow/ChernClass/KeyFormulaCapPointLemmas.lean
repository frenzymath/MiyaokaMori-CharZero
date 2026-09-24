import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.FirstChernCapCycle
import MiyaokaMori.AlgebraicGeometry.Divisors.RationalSections.RationalSectionDivisor
import MiyaokaMori.AlgebraicGeometry.Chow.RationalEquivalence.RationalEquivalenceX
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.SchemeDimension
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.FirstChernCapPointClosurePushforward
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModulePullbackStalkTensorBijective
import MiyaokaMori.AlgebraicGeometry.Divisors.RationalSections.RationalSectionPullbackDominant
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.FirstChernCapFundamentalCycle
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.TameSymbolOnPointClosure
import MiyaokaMori.AlgebraicGeometry.Varieties.Normalization.StalkNormalizationFiniteOverField

/-! # Pointwise lemmas for the key formula

Auxiliary lemmas for the geometric side of the key formula (Stacks 0AYC):

* (G1a) `AlgebraicGeometry.exists_firstChernCapPoint_eq_add_principalCycle`: `firstChernCapPoint L w` can be
  computed with **any** nonzero rational section, up to the pushforward of a principal cycle (02SH).
* (G1b) `AlgebraicGeometry.modulePullbackStalkUnit_genericPoint_ne_zero`: a stalk generator stays nonzero in
  the pulled-back stalk.
* (Ga) `AlgebraicGeometry.keyFormula_height_eq`: the points of `S` all have height `n + 1`.
* (G3a) `AlgebraicGeometry.keyFormula_lhs_apply_eq_zero_of_height_ne`: at a point `z` of height `≠ n` the
  coefficient of the left side is `0`.

Note that a version of the key formula indexed by `S = Supp div_L(s) ∪ Supp div_N(t)` is false: the index
set of Stacks 0AYC is the set `J` of codimension-one points outside which `s`, `t` are generators, and at a
non-normal codimension-one point `ord` (a length) being `0` does not imply that the coordinate is a unit (a
counterexample is a pinched surface). The correct version is `KeyFormulaGeneratingFamily.lean`
(`exists_keyFormula_principalFamily_generating_of_normalizationFinite`) and
`KeyFormulaNonGeneratingLocusLocallyFinite.lean` (`keyFormula_ratEquivZero_generating`).

Source: Stacks 0AYC (chow-lemma-key-formula); 02SH; 0A21 (dimension formula).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

open MiyaokaMori.FirstChernCapPointClosurePushforward

/-- **(G1a)**: `firstChernCapPoint L w` can be computed with **any** nonzero element of the stalk of `ι_w^*L` at
the generic point of `W_w`, up to the pushforward of a principal cycle (Stacks 02SH).

Proof: `exists_firstChernCapPoint_eq` gives some nonzero `s₀` with `firstChernCapPoint L w = (ι_w)_* div(s₀)`;
`exists_rationalSectionDivisor_eq_add_principalCycle` (02SH) replaces `div(s₀)` by `div(s) + div(φ)`;
transport with `properPushforward_add`.

Edge cases: the same holds for `L` trivial; when `W_w` is a point (`w` closed) all divisors are `0` and `φ = 1`. -/
theorem AlgebraicGeometry.exists_firstChernCapPoint_eq_add_principalCycle {X : Scheme.{u}} [IsLocallyNoetherian X]
    (L : X.Modules) [L.IsLineBundle] (w : X) [IsLocallyNoetherian (X.pointClosure w)]
    (s : ((Scheme.Modules.pullback (X.pointClosureι w)).obj L).stalk
      (genericPoint (X.pointClosure w))) (hs : s ≠ 0) :
    ∃ φ : (X.pointClosure w).functionFieldˣ,
      firstChernCapPoint L w
        = AlgebraicGeometry.AlgebraicCycle.properPushforward (X.pointClosureι w)
            (((Scheme.Modules.pullback (X.pointClosureι w)).obj L).rationalSectionDivisor s)
          + AlgebraicGeometry.AlgebraicCycle.properPushforward (X.pointClosureι w)
            ((X.pointClosure w).principalCycle φ) := by
  haveI : IsIntegral (X.pointClosure w) := Scheme.isIntegral_pointClosure w
  obtain ⟨s₀, hs₀, h0⟩ := exists_firstChernCapPoint_eq L w
  obtain ⟨φ, hφ⟩ := exists_rationalSectionDivisor_eq_add_principalCycle
    ((Scheme.Modules.pullback (X.pointClosureι w)).obj L) s₀ s hs₀ hs
  refine ⟨φ, ?_⟩
  rw [h0, hφ]
  exact AlgebraicGeometry.properPushforward_add _ _ _

/-- **(G1b) Stalk generators map to nonzero elements of the pulled-back stalk.**

Let `w ∈ X`, `η` the generic point of `W_w = X.pointClosure w`, and `σ` a generator of the stalk of `N` at
`ι_w(η)` (a local generator of the line bundle). Then the image of `σ` under the pullback stalk unit
`AlgebraicGeometry.Scheme.Modules.modulePullbackStalkUnit` in `(ι_w^*N).stalk η` is nonzero.

Source: Stacks 01J3 (point closures) and sheaves.tex `lemma-stalk-pullback-modules` (the pulled-back stalk is
the stalk tensored with the residue ring).

Proof:
1. `hσ` is `Submodule.span {σ} = ⊤` (`Submodule.mem_span_singleton_self` + `smul_mem`).
2. `Scheme.Modules.span_modulePullbackStalkUnit_eq_top` (valid for any morphism): if `σ` generates
   `N_{ι_w η}` then `unit(σ)` generates `(ι_w^*N)_η`; internally it writes `(ι_w^*N)_η` as
   `O_{W_w,η} ⊗ N_{ι_w η}` by `modulePullbackStalkTensorMap_bijective`.
3. `Scheme.Modules.exists_ne_zero_of_trivialization`: on the integral scheme `W_w`
   (`Scheme.isIntegral_pointClosure`) the line bundle `ι_w^*N` (instance `IsLineBundle.pullback`) has a
   nonzero element `v` in the stalk at the generic point.
4. If `unit(σ) = 0` then `span {unit σ} = ⊥` contains `v`, a contradiction.

Edge cases: the same argument for `N` trivial; if `w` is closed (`W_w` a point), `O_{W_w,η} = κ(w)` is still
a field; `σ = 0` does not satisfy the generating condition (unless `N_{ι_w η} = 0`, impossible for a line
bundle).

**Use**: together with (G1a), write `firstChernCapPoint N w` as
`(ι_w)_* div_{ι_w^*N}(σ|_{W_w}) + (ι_w)_* div(φ_w)`. -/
theorem AlgebraicGeometry.modulePullbackStalkUnit_genericPoint_ne_zero {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] (N : X.Modules) [N.IsLineBundle] (w : X)
    [IsLocallyNoetherian (X.pointClosure w)]
    (σ : N.presheaf.stalk ((X.pointClosureι w).base (genericPoint (X.pointClosure w))))
    (hσ : ∀ τ : N.presheaf.stalk ((X.pointClosureι w).base (genericPoint (X.pointClosure w))),
      ∃ r : X.presheaf.stalk ((X.pointClosureι w).base (genericPoint (X.pointClosure w))),
        τ = r • σ) :
    AlgebraicGeometry.Scheme.Modules.modulePullbackStalkUnit (X.pointClosureι w) N
        (genericPoint (X.pointClosure w)) σ ≠ 0 := by
  haveI : IsIntegral (X.pointClosure w) := Scheme.isIntegral_pointClosure w
  -- `σ` generates `N_{ι_w η}`
  have hτ : Submodule.span
      (X.presheaf.stalk ((X.pointClosureι w).base (genericPoint (X.pointClosure w)))) {σ} = ⊤ := by
    rw [eq_top_iff]
    rintro τ -
    obtain ⟨r, hr⟩ := hσ τ
    rw [hr]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  -- hence `unit σ` generates `(ι_w^*N)_η` (Stacks sheaves.tex lemma-stalk-pullback-modules)
  have hgen := Scheme.Modules.span_modulePullbackStalkUnit_eq_top (X.pointClosureι w) N
    (genericPoint (X.pointClosure w)) σ hτ
  -- and `(ι_w^*N)_η`, the generic stalk of a line bundle on an integral scheme, is nonzero
  obtain ⟨v, hv⟩ := Scheme.Modules.exists_ne_zero_of_trivialization
    ((Scheme.Modules.pullback (X.pointClosureι w)).obj N)
  intro h0
  apply hv
  have hv' : v ∈ Submodule.span ((X.pointClosure w).presheaf.stalk (genericPoint (X.pointClosure w)))
      {AlgebraicGeometry.Scheme.Modules.modulePullbackStalkUnit (X.pointClosureι w) N (genericPoint (X.pointClosure w)) σ} := by
    rw [hgen]; trivial
  rw [h0, Submodule.span_singleton_eq_bot.mpr rfl] at hv'
  exact (Submodule.mem_bot _).mp hv'

/-- **(Ga) Heights of the support points.**

Let `X` be integral, locally of finite type over a field `K`, `dim X = n + 2`; `s`, `t` nonzero rational
sections of `L`, `N`. Then every point `w` of `S = Supp div_L(s) ∪ Supp div_N(t)` has `Order.height` equal to
`n + 1`.

Source: Stacks 0A21 (catenarity + dimension formula `height w + coheight w = dim X` for `X` integral and
locally of finite type over a field); `AlgebraicGeometry.Scheme.Modules.rationalSectionOrd_eq_zero_of_coheight_ne_one`.

Proof: `w ∈ S ⇒ div_L(s) w ≠ 0` or `div_N(t) w ≠ 0`; `rationalSectionDivisor_support` (the contrapositive of
`rationalSectionOrd_eq_zero_of_coheight_ne_one`: `ord = 0` at coheight `≠ 1`) gives `coheight w = 1`. Make `π`
an `X.Over (Spec K)` instance; `topologicalKrullDim_eq_of_dimension_pos` turns `X.dimension = n + 2` into
`topologicalKrullDim X = n + 2`; the dimension formula of 0A21
(`height_add_coheight_eq_of_locallyOfFiniteType`) gives `height w + 1 = n + 2`, and after lifting to `ℕ`,
`omega` gives `height w = n + 1`.

Edge cases: for `S = ∅` the statement is vacuous; for `n = 0` (`X` a surface) `height w = 1`, `w` the generic
point of a curve; `X` a point has `dim X = 0`, contradicting `dim X = n + 2`. -/
theorem AlgebraicGeometry.keyFormula_height_eq {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
    (K : Type u) [Field K] (π : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType π]
    (L N : X.Modules) [L.IsLineBundle] [N.IsLineBundle] (n : ℕ) (hX : X.dimension = n + 2)
    (s : L.stalk (genericPoint X)) (t : N.stalk (genericPoint X)) (hs : s ≠ 0) (ht : t ≠ 0)
    (w : ↥(Function.support (L.rationalSectionDivisor s : X → ℤ) ∪
      Function.support (N.rationalSectionDivisor t : X → ℤ))) :
    Order.height w.1 = ((n + 1 : ℕ) : ℕ∞) := by
  -- w ∈ S ⇒ coheight w = 1
  have hco : Order.coheight w.1 = 1 := by
    rcases w.2 with h | h
    · exact Scheme.Modules.rationalSectionDivisor_support L s w.1 h
    · exact Scheme.Modules.rationalSectionDivisor_support N t w.1 h
  -- the dimension formula of 0A21
  letI : X.Over (Spec (CommRingCat.of K)) := ⟨π⟩
  haveI : LocallyOfFiniteType (X ↘ Spec (CommRingCat.of K)) :=
    inferInstanceAs (LocallyOfFiniteType π)
  have hdim : topologicalKrullDim X = ((n + 2 : ℕ) : WithBot ℕ∞) :=
    topologicalKrullDim_eq_of_dimension_pos (m := n + 1) hX
  have hadd := height_add_coheight_eq_of_locallyOfFiniteType (k := K) X (n + 2) hdim w.1
  rw [hco] at hadd
  have hne : Order.height w.1 ≠ ⊤ := by
    intro ht; rw [ht, top_add] at hadd
    exact ENat.coe_ne_top _ hadd.symm
  lift Order.height w.1 to ℕ using hne with m hm
  have : m + 1 = n + 2 := by exact_mod_cast hadd
  have : m = n + 1 := by omega
  exact_mod_cast this

/-- **(G3a) The coefficient vanishes at points of height `≠ n`.**

If `Order.height z ≠ n`, then `(c_1(N) ∩ div_L(s) − c_1(L) ∩ div_N(t)) z = 0`.

Source: the first sentence of the proof of Stacks 0AYC ("both sides are cycles of dimension n").

Proof: this is `firstChernCapCycleAux_mem`: `firstChernCapCycleAux M (n+1) α ∈ cycleSubgroup X ((n+1) − 1)`,
i.e. nonzero coefficients sit at height `n` (the summands are nonzero only for `height w = n + 1`, and
`firstChernCapPoint_height` via `firstChernCapPoint_ne_zero` + 0A21 gives `height z = (n+1) − 1`). Apply it
to the `L` and `N` terms; `sub_mem` puts the difference in `cycleSubgroup X n`, so the coefficient at
`height z ≠ n` is `0`. `hX`, `hs`, `ht` are not used (the statement matches the parent theorem).

Edge cases: at `z` the generic point (`height = dim X = n + 2 ≠ n`) both sides are `0`; for `n = 0` the case
of a closed point `z` of height `0` is as usual. -/
theorem AlgebraicGeometry.keyFormula_lhs_apply_eq_zero_of_height_ne {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] (K : Type u) [Field K] (π : X ⟶ Spec (CommRingCat.of K))
    [LocallyOfFiniteType π] (L N : X.Modules) [L.IsLineBundle] [N.IsLineBundle] (n : ℕ)
    (hX : X.dimension = n + 2) (s : L.stalk (genericPoint X)) (t : N.stalk (genericPoint X))
    (hs : s ≠ 0) (ht : t ≠ 0) (z : X) (hz : Order.height z ≠ (n : ℕ∞)) :
    (firstChernCapCycleAux N (n + 1) (L.rationalSectionDivisor s)
      - firstChernCapCycleAux L (n + 1) (N.rationalSectionDivisor t)) z = 0 := by
  have hX' : X.IsLocallyOfFiniteTypeOverField := ⟨K, inferInstance, π, inferInstance⟩
  -- both sides are `n`-cycles (`firstChernCapCycleAux_mem`, the dimension formula of 0A21), hence so is the
  -- difference
  have h3 := sub_mem (firstChernCapCycleAux_mem hX' N (n + 1) (L.rationalSectionDivisor s))
    (firstChernCapCycleAux_mem hX' L (n + 1) (N.rationalSectionDivisor t))
  by_contra h
  have h4 := h3 z h
  simp only [Nat.add_sub_cancel] at h4
  exact hz h4

end
