import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.FunctionField.GenericFiberIntegralCurve
import MiyaokaMori.AlgebraicGeometry.Divisors.OrderOfVanishing.OrdOpenImmersion
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.VarietyHeightAddCoheight
import MiyaokaMori.AlgebraicGeometry.Divisors.Weil.PrincipalDivisor
import MiyaokaMori.AlgebraicGeometry.Morphisms.ResidueDegreeComposition

/-! # The pushforward of a principal divisor through the generic fiber

Third paragraph of the proof of Stacks 02S2: for `p : W → W'` proper and dominant with
`dim W' = dim W − 1` and `η` the generic point of `W'`, the coefficient of `p_*div_W(f)` at `[W']` equals
`Σ_ξ [κ(ξ):κ(η)]·ord_ξ(f_η)` on the generic fiber `W_η` (a proper integral curve over `κ(η)` with function
field `R(W)`; the codimension-one integral closed subschemes of `W` dominating `W'` correspond to the closed
points of `W_η`, with the same local rings).

Source: the third paragraph of the proof of Stacks 02S2 (the case `dim W' = dim W − 1`).

Proof:
1. Unfold the coefficient (`AlgebraicCycle.map` / `Function.locallyFinsupp.map_apply`, equal by definition):
   `(p_* div f)(η) = Σᶠ_{x ∈ p⁻¹{η}} ord_x(f) · m_p(x)`, with `m_p(x) = [κ(x):κ(η)]` if
   `height x = height η` and `0` otherwise.
2. The weight is always the residue degree: `ord_x(f) ≠ 0 ⇒ coheight x = 1`, and the dimension formula for
   varieties (`Variety.height_add_coheight`) gives `height x + 1 = dim W = dim W' + 1 = height η + 1` (`η`
   is maximal, so `coheight η = 0`); cancel in `ℕ∞` to get `height x = height η`.
3. The generic fiber `F := p.fiber η` and the fiber embedding `ι := p.fiberι η` (Mathlib: `range ι = p⁻¹{η}`,
   `ι` is a topological embedding and a preimmersion); the generic fiber is an integral curve whose stalk
   maps are isomorphisms. `ι` sends the generic point of `F` to the generic point of `W` (the unique maximal
   point of `p⁻¹{η}`), and the stalk isomorphism gives the function field isomorphism `e : R(W) ≃ R(F)`
   (`functionFieldEquivOfIsIsoStalkMap`, the `e` of the conclusion).
4. Termwise correspondence: `coheight_F ξ = dim O_{F,ξ} = dim O_{W,ιξ} = coheight_W (ιξ)` (Mathlib's
   `ringKrullDim_stalk_eq_coheight` + ring isomorphism); `ord_ξ(e f) = ord_{ιξ}(f)` (`Ring.ordFrac_ringEquiv`,
   `ord` is invariant under stalk isomorphisms, `ord_functionFieldMap_of_isIso_stalkMap`); residue degrees:
   `ι ≫ p = q ≫ s` (`fiber_fac`, `q = fiberToSpecResidueField`, `s = fromSpecResidueField`), apply
   `residueDegree_comp` on both sides, and the preimmersions `ι`, `s` have residue degree `1`
   (`residueDegree_eq_one_of_isPreimmersion`), so `residueDegree q ξ = residueDegree p (ιξ)`.
5. Reindex the `finsum` along the injective `ι` (`finsum_mem_range`); the sum of step 2 becomes
   `Σᶠ_{ξ ∈ F} ord_ξ(e f)·residueDegree(q, ξ)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry

/-- A preimmersion (surjective stalk maps) has residue degree `1`: `residueFieldMap` is a surjective
homomorphism of fields, hence bijective. -/
theorem Scheme.Hom.residueDegree_eq_one_of_isPreimmersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsPreimmersion f] (x : X) : f.residueDegree x = 1 := by
  let : Algebra (Y.residueField (f.base x)) (X.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  change Module.finrank (Y.residueField (f.base x)) (X.residueField x) = 1
  apply Module.finrank_of_bijective_algebraMap
  refine ⟨(f.residueFieldMap x).hom.injective, ?_⟩
  intro y
  obtain ⟨s, rfl⟩ := IsLocalRing.residue_surjective y
  obtain ⟨r, rfl⟩ := f.stalkMap_surjective x s
  refine ⟨IsLocalRing.residue _ r, ?_⟩
  change IsLocalRing.ResidueField.map (f.stalkMap x).hom (IsLocalRing.residue _ r) = _
  exact IsLocalRing.ResidueField.map_residue _ r

/-- A morphism `g` whose stalk maps are all isomorphisms preserves coheights (Mathlib's
`ringKrullDim_stalk_eq_coheight`). -/
theorem Scheme.Hom.coheight_eq_of_isIso_stalkMap {F W : Scheme.{u}} (g : F ⟶ W)
    (hiso : ∀ ξ : F, IsIso (g.stalkMap ξ)) (ξ : F) :
    Order.coheight (g.base ξ) = Order.coheight ξ := by
  have := hiso ξ
  have h := ringKrullDim_eq_of_ringEquiv (asIso (g.stalkMap ξ)).commRingCatIsoToRingEquiv
  rw [ringKrullDim_stalk_eq_coheight, ringKrullDim_stalk_eq_coheight] at h
  exact WithBot.coe_injective h

section FunctionFieldEquiv

variable {F W : Scheme.{u}} [IsIntegral F] [IsIntegral W] (g : F ⟶ W)
  (hg : g.base (genericPoint F) = genericPoint W)

/-- The map of function fields `K(W) → K(F)` induced by a morphism `g : F ⟶ W` sending the generic point to
the generic point (`O_{W,η_W} = O_{W,g η_F} → O_{F,η_F}`). -/
def Scheme.Hom.functionFieldMapOfGenericPoint : W.functionField →+* F.functionField :=
  ((W.presheaf.stalkCongr (Inseparable.of_eq hg.symm)).hom ≫ g.stalkMap (genericPoint F)).hom

theorem Scheme.Hom.functionFieldMapOfGenericPoint_algebraMap (ξ : F)
    (r : W.presheaf.stalk (g.base ξ)) :
    g.functionFieldMapOfGenericPoint hg (algebraMap (W.presheaf.stalk (g.base ξ)) W.functionField r)
      = algebraMap (F.presheaf.stalk ξ) F.functionField (g.stalkMap ξ r) := by
  have hF : genericPoint F ⤳ ξ := genericPoint_specializes ξ
  have h1 := Scheme.Hom.stalkSpecializes_stalkMap_apply g (genericPoint F) ξ hF r
  have h2 := congrArg (fun φ => φ.hom r) (W.presheaf.stalkSpecializes_comp
    (specializes_of_eq hg) (genericPoint_specializes (g.base ξ)))
  change g.stalkMap (genericPoint F) (W.presheaf.stalkSpecializes (specializes_of_eq hg)
    (W.presheaf.stalkSpecializes (genericPoint_specializes (g.base ξ)) r))
    = F.presheaf.stalkSpecializes hF (g.stalkMap ξ r)
  rw [← h1]
  exact congrArg _ h2

/-- When all stalk maps are isomorphisms, `functionFieldMapOfGenericPoint` is an isomorphism of function
fields `K(W) ≃+* K(F)`. -/
def Scheme.Hom.functionFieldEquivOfIsIsoStalkMap (hiso : ∀ ξ : F, IsIso (g.stalkMap ξ)) :
    W.functionField ≃+* F.functionField :=
  haveI := hiso (genericPoint F)
  (asIso ((W.presheaf.stalkCongr (Inseparable.of_eq hg.symm)).hom ≫
    g.stalkMap (genericPoint F))).commRingCatIsoToRingEquiv

theorem Scheme.Hom.functionFieldEquivOfIsIsoStalkMap_apply (hiso : ∀ ξ : F, IsIso (g.stalkMap ξ))
    (r : W.functionField) :
    g.functionFieldEquivOfIsIsoStalkMap hg hiso r = g.functionFieldMapOfGenericPoint hg r := rfl

/-- The order of vanishing is invariant under stalk isomorphisms: `ord_ξ(g^♯ r) = ord_{g ξ}(r)`. -/
theorem Scheme.Hom.ord_functionFieldMapOfGenericPoint [IsLocallyNoetherian F]
    [IsLocallyNoetherian W] (hiso : ∀ ξ : F, IsIso (g.stalkMap ξ)) (r : W.functionField) (ξ : F) :
    F.ord (g.functionFieldMapOfGenericPoint hg r) ξ = W.ord r (g.base ξ) := by
  have hco : Order.coheight (g.base ξ) = Order.coheight ξ := g.coheight_eq_of_isIso_stalkMap hiso ξ
  by_cases hz : Order.coheight ξ = 1
  · have hz' : Order.coheight (g.base ξ) = 1 := hco.trans hz
    rw [Scheme.ord_eq_ordHom_of_coheight_eq_one hz, Scheme.ord_eq_ordHom_of_coheight_eq_one hz']
    congr 2
    have := hiso ξ
    have : Ring.KrullDimLE 1 (F.presheaf.stalk ξ) := krullDimLE_of_coheight_le hz.le
    have : Ring.KrullDimLE 1 (W.presheaf.stalk (g.base ξ)) := krullDimLE_of_coheight_le hz'.le
    exact Ring.ordFrac_ringEquiv
      (asIso (g.stalkMap ξ)).commRingCatIsoToRingEquiv (g.functionFieldMapOfGenericPoint hg)
      (g.functionFieldMapOfGenericPoint_algebraMap hg ξ) r
  · rw [Scheme.ord_eq_zero_of_coheight_neq_one hz,
      Scheme.ord_eq_zero_of_coheight_neq_one (by rwa [hco])]

end FunctionFieldEquiv

/-- The residue degree over `κ(η)` on the fiber equals the residue degree of `p` at `ι ξ`
(`ι ≫ p = q ≫ s`, with `ι`, `s` preimmersions). -/
theorem Scheme.Hom.residueDegree_fiberToSpecResidueField {X Y : Scheme.{u}} (p : X ⟶ Y) (y : Y)
    (ξ : p.fiber y) :
    (p.fiberToSpecResidueField y).residueDegree ξ = p.residueDegree ((p.fiberι y).base ξ) := by
  have h1 := AlgebraicGeometry.Intersection.residueDegree_comp (p.fiberι y) p ξ
  have h2 := AlgebraicGeometry.Intersection.residueDegree_comp (p.fiberToSpecResidueField y)
    (Y.fromSpecResidueField y) ξ
  rw [Scheme.Hom.fiber_fac] at h1
  rw [h1, Scheme.Hom.residueDegree_eq_one_of_isPreimmersion (p.fiberι y),
    Scheme.Hom.residueDegree_eq_one_of_isPreimmersion (Y.fromSpecResidueField y)] at h2
  omega

end AlgebraicGeometry

/-- Third paragraph of the proof of Stacks 02S2 (`dim W' = dim W − 1`): the coefficient of `p_* div_W(f)` at
the generic point `η` of `W'` equals `Σ_ξ ord_ξ(e f)·[κ(ξ):κ(η)]` on the generic fiber `W_η = p.fiber η`,
where `e : K(W) ≃+* K(W_η)` is the isomorphism of function fields induced at the generic point by the
stalk isomorphisms of the fiber embedding (`functionFieldEquivOfIsIsoStalkMap`). See the module docstring
for the proof; the input is the component "the stalk maps of the fiber embedding are isomorphisms" of
`genericFiber_structure`. -/
theorem properPushforward_principalDivisor_coeff_eq_genericFiber {k : Type*} [Field k]
    {W W' : Variety k} (p : W.toScheme ⟶ W'.toScheme)
    [p.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))] [AlgebraicGeometry.IsProper p]
    (hp : p.base (genericPoint W.toScheme) = genericPoint W'.toScheme)
    (hdim : W'.toScheme.dimension + 1 = W.toScheme.dimension) (f : W.toScheme.functionFieldˣ)
    [AlgebraicGeometry.IsIntegral (p.fiber (genericPoint W'.toScheme))]
    [AlgebraicGeometry.IsLocallyNoetherian (p.fiber (genericPoint W'.toScheme))] :
    ∃ e : W.toScheme.functionField ≃+* (p.fiber (genericPoint W'.toScheme)).functionField,
      AlgebraicGeometry.AlgebraicCycle.properPushforward p
          (principalDivisor W f : AlgebraicGeometry.AlgebraicCycle W.toScheme ℤ)
          (genericPoint W'.toScheme)
        = ∑ᶠ ξ : p.fiber (genericPoint W'.toScheme),
            AlgebraicGeometry.Scheme.ord (e (f : W.toScheme.functionField)) ξ *
              ((AlgebraicGeometry.Scheme.Hom.residueDegree
                  (p.fiberToSpecResidueField (genericPoint W'.toScheme)) ξ : ℕ) : ℤ) := by
  classical
  obtain ⟨-, -, -, -, hstalk⟩ := AlgebraicGeometry.genericFiber_structure p hp
  set η := genericPoint W'.toScheme with hη
  set ι := p.fiberι η with hι
  -- `ι` sends the generic point of the fiber to the generic point of `W`
  have hιgen : ι.base (genericPoint (p.fiber η)) = genericPoint W.toScheme := by
    have hmem : genericPoint W.toScheme ∈ Set.range ι.base := by
      rw [hι, AlgebraicGeometry.Scheme.Hom.range_fiberι]
      exact hp
    obtain ⟨x₁, hx₁⟩ := hmem
    have h1 : ι.base (genericPoint (p.fiber η)) ⤳ ι.base x₁ :=
      (genericPoint_specializes x₁).map ι.continuous
    rw [hx₁] at h1
    exact (h1.antisymm (genericPoint_specializes _)).eq
  refine ⟨ι.functionFieldEquivOfIsIsoStalkMap hιgen hstalk, ?_⟩
  simp only [AlgebraicGeometry.AlgebraicCycle.properPushforward, AlgebraicGeometry.AlgebraicCycle.properPushforward,
    AlgebraicGeometry.AlgebraicCycle.map, Function.locallyFinsupp.map_apply]
  rw [← AlgebraicGeometry.Scheme.Hom.range_fiberι, finsum_mem_range ι.isEmbedding.injective]
  refine finsum_congr fun ξ => ?_
  rw [AlgebraicGeometry.Scheme.Hom.functionFieldEquivOfIsIsoStalkMap_apply,
    AlgebraicGeometry.Scheme.Hom.ord_functionFieldMapOfGenericPoint ι hιgen hstalk,
    AlgebraicGeometry.Scheme.Hom.residueDegree_fiberToSpecResidueField]
  change W.toScheme.ord (f : W.toScheme.functionField) (ι.base ξ) *
      ((AlgebraicGeometry.AlgebraicCycle.mapCoeff p Order.height Order.height (ι.base ξ) : ℕ) : ℤ)
    = W.toScheme.ord (f : W.toScheme.functionField) (ι.base ξ) * ((p.residueDegree (ι.base ξ) : ℕ) : ℤ)
  by_cases h0 : W.toScheme.ord (f : W.toScheme.functionField) (ι.base ξ) = 0
  · rw [h0, zero_mul, zero_mul]
  congr 2
  -- ord ≠ 0 ⇒ coheight (ι ξ) = 1 ⇒ height (ι ξ) = dim W − 1 = dim W' = height η
  have hco : Order.coheight (ι.base ξ) = 1 := by
    by_contra h
    exact h0 (AlgebraicGeometry.Scheme.ord_eq_zero_of_coheight_neq_one h _)
  have hpι : p.base (ι.base ξ) = η := by
    have hmem : ι.base ξ ∈ Set.range ι.base := Set.mem_range_self ξ
    rw [hι, AlgebraicGeometry.Scheme.Hom.range_fiberι] at hmem
    exact hmem
  have hhx : Order.height (ι.base ξ) + 1 = (W.toScheme.dimension : ℕ∞) := by
    have h := Variety.height_add_coheight W (ι.base ξ)
    rwa [hco] at h
  have hcoη : Order.coheight η = 0 := by
    rw [Order.coheight_eq_zero]
    intro b _
    exact genericPoint_specializes b
  have hhη : Order.height η = (W'.toScheme.dimension : ℕ∞) := by
    have h := Variety.height_add_coheight W' η
    rwa [hcoη, add_zero] at h
  have hheight : Order.height (ι.base ξ) = Order.height (p.base (ι.base ξ)) := by
    rw [hpι, hhη]
    have h2 : Order.height (ι.base ξ) + 1 = (W'.toScheme.dimension : ℕ∞) + 1 := by
      rw [hhx, ← hdim, Nat.cast_add, Nat.cast_one]
    exact ENat.add_left_injective_of_ne_top ENat.one_ne_top h2
  unfold AlgebraicGeometry.AlgebraicCycle.mapCoeff
  rw [if_pos hheight]

end
