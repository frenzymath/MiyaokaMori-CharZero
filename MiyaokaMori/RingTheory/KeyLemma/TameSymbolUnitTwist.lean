import MiyaokaMori.Prelude
import MiyaokaMori.RingTheory.KeyLemma.TameSymbol

/-! # Twisting the arguments of the tame symbol by units

For a one-dimensional Noetherian local domain `A` (with finite normalization), `u, v ∈ A^*` and
`f, g ∈ K^*`: `∂_A(uf, vg) = ∂_A(f, g) · ū^{ord_A g} · v̄^{−ord_A f}`. This is the change of the tame
symbol when the local generators `s_i`, `t_i` are replaced by unit multiples in the proof of Stacks 0AYC
(independence of the normalization).

Reference: second paragraph of the proof of Stacks 0AYC ("if we replace s_i by u s_i … this follows from
0EAS(4)(6)"); bimultiplicativity 0EAS + 0EAN.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

noncomputable section

theorem Ring.tameSymbol_unit_mul (A : Type u) [CommRing A] [IsDomain A] [IsLocalRing A]
    [IsNoetherianRing A] [Ring.KrullDimLE 1 A] {K : Type u} [Field K] [Algebra A K] [IsFractionRing A K]
    (hfin : Module.Finite A (integralClosure A K)) (u v : Aˣ) (f g : Kˣ) :
    Ring.tameSymbol A hfin (Units.map (algebraMap A K).toMonoidHom u * f)
        (Units.map (algebraMap A K).toMonoidHom v * g)
      = Ring.tameSymbol A hfin f g *
        (IsLocalRing.residue A (u : A)) ^
          Multiplicative.toAdd (WithZero.unzero ((map_ne_zero (Ring.ordFrac A (K := K))).mpr g.ne_zero)) *
        ((IsLocalRing.residue A (v : A)) ^
          Multiplicative.toAdd
            (WithZero.unzero ((map_ne_zero (Ring.ordFrac A (K := K))).mpr f.ne_zero)))⁻¹ := by
  set U := Units.map (algebraMap A K).toMonoidHom u with hU
  set V := Units.map (algebraMap A K).toMonoidHom v with hV
  -- ∂(U, V) = 1: ord_A(v) = 0
  have hUV : Ring.tameSymbol A hfin U V = 1 := by
    rw [hU, Ring.tameSymbol_unit_left]
    have h1 : Ring.ordFrac A (K := K) ((V : Kˣ) : K) = 1 := Ring.ordFrac_of_isUnit v.isUnit
    have h2 : WithZero.unzero ((map_ne_zero (Ring.ordFrac A (K := K))).mpr V.ne_zero) = 1 := by
      apply WithZero.coe_injective
      rw [WithZero.coe_unzero, h1, WithZero.coe_one]
    rw [h2, toAdd_one, zpow_zero]
  have hfV : Ring.tameSymbol A hfin f V = (Ring.tameSymbol A hfin V f)⁻¹ :=
    eq_inv_of_mul_eq_one_left (Ring.tameSymbol_mul_swap A hfin f V)
  rw [Ring.tameSymbol_mul_left, Ring.tameSymbol_mul_right, Ring.tameSymbol_mul_right A hfin f, hUV,
    hfV, hV, Ring.tameSymbol_unit_left, Ring.tameSymbol_unit_left]
  ring

end
