import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.Weil.PrincipalDivisor
import MiyaokaMori.RingTheory.OrderOfVanishing.Stacks02mj
import MiyaokaMori.AlgebraicGeometry.Varieties.FunctionField.Stacks02r1
import MiyaokaMori.AlgebraicGeometry.Morphisms.FiniteLocalModel

/-! # Pushforward of a principal divisor is the divisor of the norm (Stacks 02RT)

Stacks 02RT: if `X`, `Y` are integral of the same dimension, `p : X → Y` is dominant and proper,
`f ∈ R(X)^*` and `g = Nm_{R(X)/R(Y)}(f)`, then `p_*div(f) = div(g)`. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open AlgebraicGeometry in
/-- Comparison of the coefficients at a codimension-one point `z` (the core of Stacks 02RT, from 02MJ
and the finite local model). -/
private theorem coeff_eq_of_coheight_eq_one {k : Type*} [Field k] {X Y : Variety k}
    (p : X.toScheme ⟶ Y.toScheme) [p.IsOver (Spec (CommRingCat.of k))] [IsProper p]
    (hp : p.base (genericPoint X.toScheme) = genericPoint Y.toScheme)
    (hdim : X.toScheme.dimension = Y.toScheme.dimension) (f : X.toScheme.functionFieldˣ)
    (z : Y.toScheme) (hz : Order.coheight z = 1) :
    letI := functionFieldAlgebra p hp
    ∑ᶠ x ∈ p.base ⁻¹' {z}, X.toScheme.ord (f : X.toScheme.functionField) x *
        ((AlgebraicCycle.mapCoeff p (Order.height (α := X.toScheme))
          (Order.height (α := Y.toScheme)) x : ℕ) : ℤ) =
      Y.toScheme.ord (Algebra.norm Y.toScheme.functionField (f : X.toScheme.functionField)) z := by
  classical
  let algKL : Algebra Y.toScheme.functionField X.toScheme.functionField :=
    functionFieldAlgebra p hp
  let algAL : Algebra (Y.toScheme.presheaf.stalk z) X.toScheme.functionField :=
    stalkToFunctionFieldAlgebraOfHom p hp z
  have hfinK := Variety.residueFieldMap_genericPoint_finite_of_dim_eq p hp hdim
  obtain ⟨B, _, _, _, _, _, _, _, _, e, he⟩ := exists_finite_local_model p hp hfinK z hz
  have : IsScalarTower (Y.toScheme.presheaf.stalk z) Y.toScheme.functionField
      X.toScheme.functionField := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Ring.KrullDimLE 1 (Y.toScheme.presheaf.stalk z) := krullDimLE_of_coheight_le hz.le
  have hMS : Finite (MaximalSpectrum B) :=
    Ring.finite_maximalSpectrum_of_finite (A := Y.toScheme.presheaf.stalk z)
  have hfib : (p.base ⁻¹' {z}).Finite := by
    have hfin' : Finite {x : X.toScheme // p.base x = z} := Finite.of_equiv _ e
    exact Set.finite_coe_iff.mp hfin'
  have hLfin : Module.Finite Y.toScheme.functionField X.toScheme.functionField :=
    Module.Finite.of_isLocalization (Y.toScheme.presheaf.stalk z) B
      (nonZeroDivisors (Y.toScheme.presheaf.stalk z))
  set w : X.toScheme → ℤ := fun x => ((AlgebraicCycle.mapCoeff p
    (Order.height (α := X.toScheme)) (Order.height (α := Y.toScheme)) x : ℕ) : ℤ) with hw
  set Fsum : X.toScheme.functionField → ℤ := fun φ =>
    ∑ᶠ x ∈ p.base ⁻¹' {z}, X.toScheme.ord φ x * w x with hFsum
  have hFmul : ∀ φ ψ : X.toScheme.functionField, φ ≠ 0 → ψ ≠ 0 →
      Fsum (φ * ψ) = Fsum φ + Fsum ψ := by
    intro φ ψ hφ hψ
    simp only [hFsum]
    rw [← finsum_mem_add_distrib hfib]
    refine finsum_mem_congr rfl fun x _ => ?_
    rw [Scheme.ord_mul hφ hψ, add_mul]
  have hnorm : ∀ φ : X.toScheme.functionField, φ ≠ 0 →
      Algebra.norm Y.toScheme.functionField φ ≠ 0 := fun φ hφ =>
    (Algebra.norm_ne_zero_iff (R := Y.toScheme.functionField)).mpr hφ
  have hGmul : ∀ φ ψ : X.toScheme.functionField, φ ≠ 0 → ψ ≠ 0 →
      Y.toScheme.ord (Algebra.norm Y.toScheme.functionField (φ * ψ)) z =
        Y.toScheme.ord (Algebra.norm Y.toScheme.functionField φ) z +
          Y.toScheme.ord (Algebra.norm Y.toScheme.functionField ψ) z := by
    intro φ ψ hφ hψ
    rw [map_mul, Scheme.ord_mul (hnorm φ hφ) (hnorm ψ hψ)]
  -- the case of an integral element: 02MJ
  have hB : ∀ b : B, b ≠ 0 → Fsum (algebraMap B X.toScheme.functionField b) =
      Y.toScheme.ord (Algebra.norm Y.toScheme.functionField
        (algebraMap B X.toScheme.functionField b)) z := by
    intro b hb
    have hb' : algebraMap B X.toScheme.functionField b ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective B X.toScheme.functionField)).mpr hb
    symm
    rw [Scheme.ord_eq_iff hz (hnorm _ hb')]
    change Ring.ordFrac (Y.toScheme.presheaf.stalk z) _ = _
    rw [Ring.ordFrac_norm_eq_sum_inertiaDeg_mul_ord b hb]
    change WithZero.exp _ = WithZero.exp _
    congr 1
    simp only [hFsum]
    have h1 : ∑ᶠ x ∈ p.base ⁻¹' {z},
        X.toScheme.ord (algebraMap B X.toScheme.functionField b) x * w x =
        ∑ᶠ x : {x : X.toScheme // p.base x = z},
          X.toScheme.ord (algebraMap B X.toScheme.functionField b) x.1 * w x.1 :=
      (finsum_subtype_eq_finsum_cond (fun x : X.toScheme => p.base x = z)).symm
    rw [h1, ← finsum_comp_equiv e]
    refine finsum_congr fun m => ?_
    obtain ⟨hco, hdeg, hord⟩ := he m
    have hheight : Order.height (e m).1 = Order.height (p.base (e m).1) := by
      have h1 := Variety.height_add_coheight X (e m).1
      have h2 := Variety.height_add_coheight Y (p.base (e m).1)
      rw [(e m).2, hz, ← hdim, ← h1, hco] at h2
      rw [(e m).2]
      exact (ENat.add_left_injective_of_ne_top ENat.one_ne_top h2).symm
    have hwm : w (e m).1 = (Ideal.inertiaDeg'
        (IsLocalRing.maximalIdeal (Y.toScheme.presheaf.stalk z)) m.asIdeal : ℤ) := by
      simp only [hw]
      unfold AlgebraicCycle.mapCoeff
      rw [if_pos hheight, hdeg]
    rw [hord b hb, hwm, mul_comm]
  -- the general case `f ∈ L^*`: both sides are multiplicative on `L^*` (`hFmul`, `hGmul`) and agree on
  -- `B \ 0` (`hB`), so `Ring.eq_of_mul_of_eq_on_algebraMap` gives the equality.
  change Fsum (f : X.toScheme.functionField) = _
  exact Ring.eq_of_mul_of_eq_on_algebraMap (B := B) (F := Fsum)
    (G := fun φ => Y.toScheme.ord (Algebra.norm Y.toScheme.functionField φ) z)
    hFmul hGmul hB f.ne_zero

theorem properPushforward_principalDivisor {k : Type*} [Field k] {X Y : Variety k}
    (p : X.toScheme ⟶ Y.toScheme) [p.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.IsProper p]
    (hp : p.base (genericPoint X.toScheme) = genericPoint Y.toScheme)
    (hdim : X.toScheme.dimension = Y.toScheme.dimension) (f : X.toScheme.functionFieldˣ) :
    letI : Algebra Y.toScheme.functionField X.toScheme.functionField :=
      ((Y.toScheme.presheaf.stalkCongr (Inseparable.of_eq hp.symm)).hom ≫
        p.stalkMap (genericPoint X.toScheme)).hom.toAlgebra
    AlgebraicGeometry.AlgebraicCycle.properPushforward p
        (principalDivisor X f : AlgebraicGeometry.AlgebraicCycle X.toScheme ℤ)
      = (principalDivisor Y (Units.map (Algebra.norm Y.toScheme.functionField) f) :
          AlgebraicGeometry.AlgebraicCycle Y.toScheme ℤ) := by
  classical
  ext z
  change ∑ᶠ x ∈ p.base ⁻¹' {z}, X.toScheme.principalCycle f x *
      ((AlgebraicGeometry.AlgebraicCycle.mapCoeff p (Order.height (α := X.toScheme))
        (Order.height (α := Y.toScheme)) x : ℕ) : ℤ) = Y.toScheme.principalCycle _ z
  simp only [AlgebraicGeometry.Scheme.principalCycle_apply, Units.coe_map]
  by_cases hz : Order.coheight z = 1
  · exact coeff_eq_of_coheight_eq_one p hp hdim f z hz
  · rw [AlgebraicGeometry.Scheme.ord_eq_zero_of_coheight_neq_one hz]
    refine finsum_mem_eq_zero_of_forall_eq_zero fun x hx => ?_
    have hxz : p.base x = z := hx
    by_cases hx1 : Order.coheight x = 1
    · have hne : Order.height x ≠ Order.height (p.base x) := by
        intro heq
        apply hz
        have h1 := Variety.height_add_coheight X x
        have h2 := Variety.height_add_coheight Y z
        rw [hx1, hdim, ← h2, heq, hxz] at h1
        have hfinite : Order.height z ≠ ⊤ :=
          ne_top_of_le_ne_top (ENat.natCast_ne_top _) (le_self_add.trans_eq h2)
        exact (ENat.add_right_injective_of_ne_top hfinite h1).symm
      unfold AlgebraicGeometry.AlgebraicCycle.mapCoeff
      rw [if_neg hne]
      simp
    · rw [AlgebraicGeometry.Scheme.ord_eq_zero_of_coheight_neq_one hx1, zero_mul]

end
