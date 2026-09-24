import MiyaokaMori.Prelude
import MiyaokaMori.RingTheory.Dimension.FiniteLocalModelAlgebra
import Mathlib.RingTheory.OrderOfVanishing.Basic
import Mathlib.AlgebraicGeometry.OrderOfVanishing
import Mathlib.AlgebraicGeometry.Properties

/-! # The order of vanishing along an open immersion

(1) A ring isomorphism `e : R ≃ S` preserves `Ring.ordMonoidWithZeroHom`; if moreover a field homomorphism
`ψ : K → K′` (`K`, `K′` the fraction fields of `R`, `S`) is compatible with `e`, then
`Ring.ordFrac S (ψ y) = Ring.ordFrac R y`. (2) If `f : W → X` is an open immersion of integral locally
Noetherian schemes (in particular an isomorphism) and `functionFieldMap f : K(X) → K(W)` the induced map
of function fields, then `ord_{z′}(f^♯ g) = ord_{f z′}(g)` for all `g ∈ K(X)` and `z′ ∈ W`.

Proof:
1. (1): `Ring.ord_ringEquiv` (lengths of quotient rings are invariant under ring isomorphisms) gives the
   equality of `ord`; nonzerodivisors correspond under multiplicative isomorphisms
   (`MulEquivClass.map_nonZeroDivisors`), so the `ordMonoidWithZeroHom`s agree; write elements of the
   fraction field as `a/b` (`IsFractionRing.div_surjective`) and use `map_div₀` and `Ring.ordFrac_eq_ord`.
2. (2): `f η_W = η_X` (Mathlib `genericPoint_eq_of_isOpenImmersion`), and `functionFieldMap f` is the
   specialization map `O_{X,η_X} → O_{X,f η_W}` composed with `f.stalkMap η_W`. It is compatible with
   `O_{X,f z′} → K(X)` and `O_{W,z′} → K(W)` (`Scheme.Hom.stalkSpecializes_stalkMap_apply`,
   `stalkSpecializes_comp`). Open immersions preserve coheight (Mathlib `coheight_eq_of_isOpenImmersion`);
   at coheight `1`, `Scheme.ord` is `Ring.ordFrac` and (1) applies with `e :=` the inverse of
   `f.stalkMap z′`; otherwise both sides are `0`.
(Stacks 02MD: `ord` depends only on the local ring, and open immersions do not change local rings.)
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

open WithZero

noncomputable section

variable {R S : Type*} [CommRing R] [CommRing S]

/-- A ring isomorphism preserves `Ring.ordMonoidWithZeroHom`. -/
theorem Ring.ordMonoidWithZeroHom_ringEquiv [Nontrivial R] [Nontrivial S] (e : R ≃+* S) (x : R) :
    Ring.ordMonoidWithZeroHom S (e x) = Ring.ordMonoidWithZeroHom R x := by
  have hmem : e x ∈ nonZeroDivisors S ↔ x ∈ nonZeroDivisors R := by
    rw [← MulEquivClass.map_nonZeroDivisors e, Submonoid.mem_map]
    constructor
    · rintro ⟨y, hy, hyx⟩
      rwa [← e.injective hyx]
    · intro h
      exact ⟨x, h, rfl⟩
  by_cases hx : x ∈ nonZeroDivisors R
  · rw [Ring.ordMonoidWithZeroHom_eq_ord hx, Ring.ordMonoidWithZeroHom_eq_ord (hmem.mpr hx),
      Ring.ord_ringEquiv]
  · rw [Ring.ordMonoidWithZeroHom_eq_zero hx, Ring.ordMonoidWithZeroHom_eq_zero (mt hmem.mp hx)]

/-- At the level of fraction fields: a ring isomorphism `e : R ≃ S` with a compatible field homomorphism
`ψ : K → K'` preserves `ordFrac`. -/
theorem Ring.ordFrac_ringEquiv {K K' : Type*} [Field K] [Field K'] [IsDomain R] [IsDomain S]
    [IsNoetherianRing R] [Ring.KrullDimLE 1 R] [IsNoetherianRing S] [Ring.KrullDimLE 1 S]
    [Algebra R K] [IsFractionRing R K] [Algebra S K'] [IsFractionRing S K']
    (e : R ≃+* S) (ψ : K →+* K')
    (hψ : ∀ r : R, ψ (algebraMap R K r) = algebraMap S K' (e r)) (y : K) :
    Ring.ordFrac S (ψ y) = Ring.ordFrac R y := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) y
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have heb0 : e b ≠ 0 := (map_ne_zero_iff e e.injective).mpr hb0
  rw [map_div₀, hψ, hψ, map_div₀, map_div₀]
  by_cases ha0 : a = 0
  · simp [ha0]
  have hea0 : e a ≠ 0 := (map_ne_zero_iff e e.injective).mpr ha0
  rw [Ring.ordFrac_eq_ord S (K := K') hea0, Ring.ordFrac_eq_ord S (K := K') heb0,
    Ring.ordFrac_eq_ord R (K := K) ha0, Ring.ordFrac_eq_ord R (K := K) hb0,
    Ring.ordMonoidWithZeroHom_ringEquiv, Ring.ordMonoidWithZeroHom_ringEquiv]


namespace MiyaokaMori.OrdOpenImmersion
open AlgebraicGeometry CategoryTheory
universe u
variable {W X : Scheme.{u}} (f : W ⟶ X) [IsOpenImmersion f] [IsIntegral W] [IsIntegral X]

/-- The map of function fields `K(X) → K(W)` induced by an open immersion (through `f η_W = η_X`). -/
noncomputable def functionFieldMap : X.functionField →+* W.functionField :=
  ((X.presheaf.stalkSpecializes
      (specializes_of_eq (genericPoint_eq_of_isOpenImmersion f))) ≫ f.stalkMap (genericPoint W)).hom

theorem functionFieldMap_algebraMap (z' : W) (r : X.presheaf.stalk (f z')) :
    functionFieldMap f (algebraMap (X.presheaf.stalk (f z')) X.functionField r) =
      algebraMap (W.presheaf.stalk z') W.functionField (f.stalkMap z' r) := by
  have hW : genericPoint W ⤳ z' := (genericPoint_spec W).specializes trivial
  have h1 := Scheme.Hom.stalkSpecializes_stalkMap_apply f (genericPoint W) z' hW r
  have h2 := congrArg (fun φ => φ.hom r) (X.presheaf.stalkSpecializes_comp
    (specializes_of_eq (genericPoint_eq_of_isOpenImmersion f))
    ((genericPoint_spec X).specializes (Set.mem_univ (f z'))))
  change f.stalkMap (genericPoint W) (X.presheaf.stalkSpecializes _
    (X.presheaf.stalkSpecializes _ r)) = W.presheaf.stalkSpecializes hW (f.stalkMap z' r)
  rw [← h1]
  exact congrArg _ h2

/-- Along an open immersion `f`, `ord_{z′}(f^♯ g) = ord_{f z′}(g)`. -/
theorem ord_functionFieldMap [IsLocallyNoetherian W] [IsLocallyNoetherian X]
    (g : X.functionField) (z' : W) :
    W.ord (functionFieldMap f g) z' = X.ord g (f z') := by
  have hco : Order.coheight (f z') = Order.coheight z' := coheight_eq_of_isOpenImmersion f
  by_cases hz : Order.coheight z' = 1
  · have hz' : Order.coheight (f z') = 1 := hco.trans hz
    rw [Scheme.ord_eq_ordHom_of_coheight_eq_one hz, Scheme.ord_eq_ordHom_of_coheight_eq_one hz']
    congr 2
    haveI : Ring.KrullDimLE 1 (W.presheaf.stalk z') := krullDimLE_of_coheight_le hz.le
    haveI : Ring.KrullDimLE 1 (X.presheaf.stalk (f z')) := krullDimLE_of_coheight_le hz'.le
    exact Ring.ordFrac_ringEquiv
      (asIso (f.stalkMap z')).commRingCatIsoToRingEquiv (functionFieldMap f)
      (functionFieldMap_algebraMap f z') g
  · rw [Scheme.ord_eq_zero_of_coheight_neq_one hz,
      Scheme.ord_eq_zero_of_coheight_neq_one (by rwa [hco])]

end MiyaokaMori.OrdOpenImmersion

end
