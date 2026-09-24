import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.FunctionField.GenericFiberIntegralCurve
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.PrincipalDivisorDegreeZero
import MiyaokaMori.AlgebraicGeometry.Chow.Pushforward.PushforwardDivisorViaGenericFiber
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.VarietyHeightAddCoheight
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.CurveDimensionOne
import MiyaokaMori.AlgebraicGeometry.Chow.Pushforward.PushforwardPreservesDimension
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Divisors.Weil.PrincipalDivisor

/-! # Pushforward of a principal divisor vanishes when the dimension drops

Let `W`, `W'` be `k`-varieties and `p : W → W'` a proper dominant `k`-morphism with `dim W' < dim W`.
Then `p_* div_W(r) = 0` for every `r ∈ K(W)^×` (the dimension-drop case in the proof of Stacks 02S2 /
Fulton, Intersection Theory, Thm 1.4).

Proof:
1. `c := p_* div(r) ∈ Z_{dim W − 1}(W')` (`properPushforward_mem_cycleGroup`, and `principalDivisor`
   lies in `Z_{dim W −1}`), so `c(y) ≠ 0 ⇒ height y = dim W − 1`.
2. On a variety `height y + coheight y = dim W'` (`Variety.height_add_coheight`), so
   `dim W − 1 ≤ dim W' < dim W`, whence `dim W' + 1 = dim W` and `coheight y = 0`, i.e. `y` is maximal,
   `y = η'` the generic point of `W'` (`OrderTop` of an integral scheme).
3. At `η'`: `PushforwardDivisorViaGenericFiber.lean` writes the coefficient as
   `Σ_ξ ord_ξ(r)·[κ(ξ):κ(η')]` on the generic fiber `W_{η'}` (a proper integral one-dimensional scheme
   over `κ(η')`, `GenericFiberIntegralCurve`), which vanishes by the degree-zero property of
   principal divisors (Stacks 02RU).
4. When `dim W' < dim W − 1`, step 2 is already contradictory, so `c = 0`.

Source: Stacks 02S2, second and third paragraphs of the proof; Fulton, Thm 1.4, Case 1.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- `p_* div_W(r) = 0` for a proper dominant morphism `p : W → W'` of varieties with `dim W' < dim W`. -/
theorem properPushforward_principalDivisor_eq_zero_of_dimension_lt {k : Type u} [Field k]
    {W W' : Variety k} (p : W.toScheme ⟶ W'.toScheme)
    [p.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))] [AlgebraicGeometry.IsProper p]
    (hp : p.base (genericPoint W.toScheme) = genericPoint W'.toScheme)
    (hdim : W'.toScheme.dimension < W.toScheme.dimension) (r : W.toScheme.functionFieldˣ) :
    AlgebraicGeometry.AlgebraicCycle.properPushforward p
        (principalDivisor W r : AlgebraicGeometry.AlgebraicCycle W.toScheme ℤ) = 0 := by
  set c := AlgebraicGeometry.AlgebraicCycle.properPushforward p
        (principalDivisor W r : AlgebraicGeometry.AlgebraicCycle W.toScheme ℤ) with hc
  have hmem : c ∈ CycleGroup W' (W.toScheme.dimension - 1) :=
    properPushforward_mem_cycleGroup p _ (principalDivisor W r).2
  ext y
  by_contra hy
  have hht : Order.height y = ((W.toScheme.dimension - 1 : ℕ) : ℕ∞) := hmem y hy
  have hadd := Variety.height_add_coheight W' y
  rw [hht] at hadd
  -- `dim W' + 1 = dim W` and `coheight y = 0`
  have hle : W.toScheme.dimension - 1 ≤ W'.toScheme.dimension := by
    have : ((W.toScheme.dimension - 1 : ℕ) : ℕ∞) ≤ (W'.toScheme.dimension : ℕ∞) :=
      hadd ▸ le_self_add
    exact_mod_cast this
  have hdim' : W'.toScheme.dimension + 1 = W.toScheme.dimension := by omega
  have hco : Order.coheight y = 0 := by
    have h1 : W.toScheme.dimension - 1 = W'.toScheme.dimension := by omega
    rw [h1] at hadd
    have h2 : ((W'.toScheme.dimension : ℕ) : ℕ∞) + Order.coheight y
        = ((W'.toScheme.dimension : ℕ) : ℕ∞) + 0 := by rw [hadd, add_zero]
    exact ENat.add_right_injective_of_ne_top (ENat.natCast_ne_top _) h2
  have hyη : y = genericPoint W'.toScheme := by
    have hmax : IsMax y := Order.coheight_eq_zero.mp hco
    have h1 : genericPoint W'.toScheme ⤳ y := genericPoint_specializes y
    have h2 : y ⤳ genericPoint W'.toScheme := hmax (b := genericPoint W'.toScheme) h1
    exact (h2.antisymm h1).eq
  subst hyη
  obtain ⟨hint, hnoeth, hkd, -, -⟩ := AlgebraicGeometry.genericFiber_structure p hp
  obtain ⟨e, he⟩ := properPushforward_principalDivisor_coeff_eq_genericFiber p hp hdim' r
  apply hy
  rw [hc, he]
  let _ : (p.fiber (genericPoint W'.toScheme)).Over
      (AlgebraicGeometry.Spec (CommRingCat.of (W'.toScheme.residueField (genericPoint W'.toScheme)))) :=
    ⟨p.fiberToSpecResidueField (genericPoint W'.toScheme)⟩
  have : AlgebraicGeometry.IsProper ((p.fiber (genericPoint W'.toScheme)) ↘
      AlgebraicGeometry.Spec (CommRingCat.of (W'.toScheme.residueField (genericPoint W'.toScheme)))) :=
    inferInstanceAs (AlgebraicGeometry.IsProper (pullback.snd p _))
  have hone : SchemeIsOneDimensional (p.fiber (genericPoint W'.toScheme)) := by
    rw [SchemeIsOneDimensional, hkd]
    have : W.toScheme.dimension - W'.toScheme.dimension = 1 := by omega
    rw [this]; rfl
  exact principalDivisor_degree_eq_zero
    (K := W'.toScheme.residueField (genericPoint W'.toScheme))
    (p.fiber (genericPoint W'.toScheme)) hone (Units.map e.toMonoidHom r)

end
