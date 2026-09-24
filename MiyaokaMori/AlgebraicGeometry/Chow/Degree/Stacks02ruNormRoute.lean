import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.VarietyHeightAddCoheight
import MiyaokaMori.AlgebraicGeometry.Divisors.Weil.PrincipalDivisor
import MiyaokaMori.AlgebraicGeometry.Chow.Pushforward.Stacks02r5
import MiyaokaMori.AlgebraicGeometry.Chow.Pushforward.Stacks02rt

/-! # Degree zero of principal divisors on curves via the norm (Stacks 02RU)

The core of the one-dimensional case of Stacks 02RU (a principal divisor on a proper integral curve has
degree zero): if `p : Y → X` is proper and birational, `q : Y → P` is proper and dominant (all three
one-dimensional varieties over a field `K`, with `X`, `P` proper), and every principal divisor on `P` has
degree zero, then every principal divisor on `X` has degree zero. The proof uses only 02RT (proper
pushforward commutes with principal divisors: `p_* div(g) = div(Nm g)`) twice and 02R5 (functoriality
of the pushforward): `c_* div_X(f) = c_* p_* div_Y(f) = c'_* q_* div_Y(f) = c'_* div_P(Nm f)`.

Difference from the Stacks proof: Stacks uses `q_* q^* = d` (02RH) together with
`div_Y(f) = q^*([0] − [∞])`, which needs 02KB, 02RH, flat pullback, the finite flatness of `q` and steps
4–5 of 02RQ; here 02RT replaces all this and the relation between `q` and `f` is not used, so 02RQ only
needs "there is a proper dominant model over `P¹`" and the case distinction for constant functions
disappears. The price is that degrees on `P` must be computed for **arbitrary** rational functions (Stacks
only needs `div(t) = [0] − [∞]`).

Source: Stacks 02RU, 02RT, 02R5.
-/

set_option autoImplicit false

universe u

open AlgebraicGeometry CategoryTheory

noncomputable section

namespace AlgebraicGeometry.AlgebraicCycle

/-- The pushforward depends only on the morphism (the `IsProper` instance is a proposition). -/
theorem properPushforward_congr {X W : Scheme.{u}} {g g' : X ⟶ W} [IsProper g] [IsProper g']
    (h : g = g') (α : AlgebraicCycle X ℤ) : properPushforward g α = properPushforward g' α := by
  subst h; rfl

/-- A commutative square `p ≫ c = q ≫ c'` gives `c_* p_* = c'_* q_*` (02R5 applied twice). -/
theorem properPushforward_comp_eq_of_comm {X Y Z W : Scheme.{u}} (p : X ⟶ Y) (c : Y ⟶ W)
    (q : X ⟶ Z) (c' : Z ⟶ W) [IsProper p] [IsProper c] [IsProper q] [IsProper c']
    (h : p ≫ c = q ≫ c') (α : AlgebraicCycle X ℤ) :
    properPushforward c (properPushforward p α) = properPushforward c' (properPushforward q α) := by
  rw [properPushforward_comp, properPushforward_comp]
  exact properPushforward_congr h α

end AlgebraicGeometry.AlgebraicCycle

variable {K : Type u} [Field K]

/-- First step of 02RU: the coefficient at the base point of the pushforward from a one-dimensional variety
is `Σ_x ord_x(f)·[κ(x):K]`. -/
theorem Variety.properPushforward_principalDivisor_toBase_apply (X : Variety K)
    [IsProper (X.toScheme ↘ Spec (CommRingCat.of K))] (hX : X.toScheme.dimension = 1)
    (f : X.toScheme.functionFieldˣ) (pt : Spec (CommRingCat.of K)) :
    AlgebraicGeometry.AlgebraicCycle.properPushforward (X.toScheme ↘ Spec (CommRingCat.of K))
        (principalDivisor X f : AlgebraicCycle X.toScheme ℤ) pt =
      ∑ᶠ x : X.toScheme, Scheme.ord (f : X.toScheme.functionField) x *
        ((Scheme.Hom.residueDegree (X.toScheme ↘ Spec (CommRingCat.of K)) x : ℕ) : ℤ) := by
  classical
  change ∑ᶠ x ∈ (X.toScheme ↘ Spec (CommRingCat.of K)).base ⁻¹' {pt},
      X.toScheme.principalCycle f x *
      ((AlgebraicCycle.mapCoeff (X.toScheme ↘ Spec (CommRingCat.of K))
        (Order.height (α := X.toScheme))
        (Order.height (α := Spec (CommRingCat.of K))) x : ℕ) : ℤ) = _
  have hpre : (X.toScheme ↘ Spec (CommRingCat.of K)).base ⁻¹' {pt} = Set.univ := by
    ext x
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    exact Subsingleton.elim _ _
  rw [hpre, finsum_mem_univ]
  refine finsum_congr fun x => ?_
  rw [Scheme.principalCycle_apply]
  by_cases hx : Order.coheight x = 1
  · have h1 := Variety.height_add_coheight X x
    rw [hx, hX] at h1
    have hx0 : Order.height x = 0 := by
      have : Order.height x + 1 = 0 + 1 := by simpa using h1
      exact ENat.add_left_injective_of_ne_top (by simp) this
    have hpt0 : Order.height ((X.toScheme ↘ Spec (CommRingCat.of K)).base x) = 0 :=
      Order.height_eq_zero.mpr (fun y _ => le_of_eq (Subsingleton.elim _ _))
    unfold AlgebraicCycle.mapCoeff
    rw [if_pos (hx0.trans hpt0.symm)]
  · rw [Scheme.ord_eq_zero_of_coheight_neq_one hx, zero_mul, zero_mul]

/-- **The core of 02RU.** `p : Y → X` proper birational, `q : Y → P` proper dominant, all three
one-dimensional varieties with `X`, `P` proper over `K`; if every principal divisor on `P` has degree zero,
then so does every principal divisor on `X`. -/
theorem Variety.sum_ord_mul_residueDegree_eq_zero_of_dominant {X Y P : Variety K}
    [IsProper (X.toScheme ↘ Spec (CommRingCat.of K))]
    [IsProper (P.toScheme ↘ Spec (CommRingCat.of K))]
    (hX : X.toScheme.dimension = 1) (hY : Y.toScheme.dimension = 1) (hP : P.toScheme.dimension = 1)
    (p : Y.toScheme ⟶ X.toScheme) [p.IsOver (Spec (CommRingCat.of K))] [IsProper p]
    (hp : p.base (genericPoint Y.toScheme) = genericPoint X.toScheme)
    (hbir : letI : Algebra X.toScheme.functionField Y.toScheme.functionField :=
        ((X.toScheme.presheaf.stalkCongr (Inseparable.of_eq hp.symm)).hom ≫
          p.stalkMap (genericPoint Y.toScheme)).hom.toAlgebra
      Module.finrank X.toScheme.functionField Y.toScheme.functionField = 1)
    (q : Y.toScheme ⟶ P.toScheme) [q.IsOver (Spec (CommRingCat.of K))] [IsProper q]
    (hq : q.base (genericPoint Y.toScheme) = genericPoint P.toScheme)
    (hdeg : ∀ h : P.toScheme.functionFieldˣ,
      ∑ᶠ y : P.toScheme, Scheme.ord (h : P.toScheme.functionField) y *
        ((Scheme.Hom.residueDegree (P.toScheme ↘ Spec (CommRingCat.of K)) y : ℕ) : ℤ) = 0)
    (f : X.toScheme.functionFieldˣ) :
    ∑ᶠ x : X.toScheme, Scheme.ord (f : X.toScheme.functionField) x *
      ((Scheme.Hom.residueDegree (X.toScheme ↘ Spec (CommRingCat.of K)) x : ℕ) : ℤ) = 0 := by
  let algp : Algebra X.toScheme.functionField Y.toScheme.functionField :=
    ((X.toScheme.presheaf.stalkCongr (Inseparable.of_eq hp.symm)).hom ≫
      p.stalkMap (genericPoint Y.toScheme)).hom.toAlgebra
  let algq : Algebra P.toScheme.functionField Y.toScheme.functionField :=
    ((P.toScheme.presheaf.stalkCongr (Inseparable.of_eq hq.symm)).hom ≫
      q.stalkMap (genericPoint Y.toScheme)).hom.toAlgebra
  -- `g` := the image of `f` in `K(Y)`; birational ⇒ `Nm(g) = f`
  let g : Y.toScheme.functionFieldˣ :=
    Units.map (algebraMap X.toScheme.functionField Y.toScheme.functionField).toMonoidHom f
  have hnorm : Units.map (Algebra.norm X.toScheme.functionField) g = f := by
    ext
    simp only [g, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
    rw [Algebra.norm_algebraMap, hbir, pow_one]
  have h1 := properPushforward_principalDivisor p hp (hY.trans hX.symm) g
  have h2 := properPushforward_principalDivisor q hq (hY.trans hP.symm) g
  rw [hnorm] at h1
  obtain ⟨pt⟩ : Nonempty (Spec (CommRingCat.of K)) := inferInstance
  have hsq : p ≫ (X.toScheme ↘ Spec (CommRingCat.of K)) =
      q ≫ (P.toScheme ↘ Spec (CommRingCat.of K)) :=
    (comp_over p (Spec (CommRingCat.of K))).trans (comp_over q (Spec (CommRingCat.of K))).symm
  have hcomm := AlgebraicCycle.properPushforward_comp_eq_of_comm p
    (X.toScheme ↘ Spec (CommRingCat.of K)) q (P.toScheme ↘ Spec (CommRingCat.of K)) hsq
    (principalDivisor Y g : AlgebraicCycle Y.toScheme ℤ)
  have e1 := Variety.properPushforward_principalDivisor_toBase_apply X hX f pt
  have e2 := Variety.properPushforward_principalDivisor_toBase_apply P hP
    (Units.map (Algebra.norm P.toScheme.functionField) g) pt
  rw [← h1] at e1
  rw [← h2] at e2
  rw [← e1, ← hdeg (Units.map (Algebra.norm P.toScheme.functionField) g), ← e2]
  exact congrFun (congrArg DFunLike.coe hcomm) pt

end
