import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.EulerCharRestrictionEffectiveCartier
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleOfModules
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleZpowAddIso
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.Stacks01ct
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.RationalSectionDegree
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.RationalSectionDivisorTensor
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.PrincipalDivisorDegreeZero
import MiyaokaMori.AlgebraicGeometry.Divisors.RationalSections.LineBundleSectionGermGenericNeZero
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.ZeroSchemeCycleApplyOfCoheightEqOne
import MiyaokaMori.AlgebraicGeometry.Divisors.Effective.ZeroSchemeCycleApplyOfCoheightNeOne
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.TopSelfIntersectionCurve

/-! # Degree of a difference of effective Cartier divisors on a curve

Let `X` be a proper integral one-dimensional scheme over a field `k`, `A`, `B` effective Cartier
divisors and `M ≅ O_X(A) ⊗ O_X(B)^∨` a line bundle. Then
`topSelfIntersection X hX M = deg_k A − deg_k B`, where `topSelfIntersection` is the curve degree
`deg(c₁(M) ∩ [X])` and `deg_k D = D.degreeOver k`.

Proof: `topSelfIntersection_eq_degree_rationalSectionDivisor` gives
`topSelfIntersection X hX L = deg div_L(s)` for every nonzero rational section `s`, so it remains to
compute degrees.
1. `deg` is additive on zero cycles (`X` proper, so supports are finite;
   `AlgebraicCycle.degree_add_of_isProperOver`).
2. Additivity under tensor products (Stacks 02SL): for nonzero rational sections `s`, `t` of `L`, `N`,
   `exists_rationalSectionDivisor_tensor` gives a nonzero `u ∈ (L ⊗ N)_η` with
   `div(u) = div(s) + div(t)`; take degrees (`topSelfIntersection_tensor`).
3. The trivial line bundle has degree zero (Stacks 02RU): if `M ≅ O_X` then `div_M(s)` is a
   principal cycle (`rationalSectionDivisor_eq_principalCycle_of_iso_unit`), and a principal divisor
   on a proper integral curve has degree zero (`principalDivisor_degree_eq_zero`;
   `topSelfIntersection_eq_zero_of_iso_unit`).
4. `deg O(D) = deg_k D` (Stacks 02SQ; Fulton §2.3): the canonical section `1_D` is nonzero
   (`canonicalSection_ne_zero`) with nonzero generic germ (`germ_genericPoint_ne_zero`), its divisor
   equals pointwise the zero-scheme cycle `[Z(1_D)]_0` (`idealSheafOfSection_cycle_apply_of_coheight_eq_one`
   / `_ne_one`), and `Z(1_D) = D` (`idealSheafOfSection_canonicalSection`), so `div(1_D) = D.idealSheaf.cycle 0`
   whose degree is `D.degreeOver k` (`EffectiveCartierDivisor.topSelfIntersection_lineBundle`).
5. Assemble: `deg(O(B) ⊗ O(B)^∨) = deg O(B) + deg O(B)^∨` (step 2), `O(B) ⊗ O(B)^∨ ≅ O_X`
   (`LineBundle.contraction`) has degree `0` (step 3), so `deg O(B)^∨ = −deg_k B`; then
   `deg(O(A) ⊗ O(B)^∨) = deg_k A − deg_k B` (steps 2, 4), and the isomorphism `e`
   (`topSelfIntersection_congr`) gives the equation for `M`.

Sources: Stacks 0AZ3 (`chow-lemma-degree-vector-bundle`), 02SQ, 02SL, 02RU. This is the
Riemann–Roch route behind `LineBundle.degree_eq_topSelfIntersection` (`LineBundleDegree`).
-/

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))]

/-- The `k`-degree of zero cycles is additive on a proper scheme (supports are finite, so the `finsum`
fallback is not triggered). -/
theorem AlgebraicCycle.degree_add_of_isProperOver (hX : IsProperOver k X)
    (A B : AlgebraicCycle X ℤ) :
    AlgebraicCycle.degree (k := k) (A + B) =
      AlgebraicCycle.degree (k := k) A + AlgebraicCycle.degree (k := k) B := by
  have : IsProper (X ↘ Spec (CommRingCat.of k)) := hX
  have hA' : (Function.support A).Finite :=
    AlgebraicGeometry.Intersection.properCycle_finiteSupport (X ↘ Spec (CommRingCat.of k)) A
  have hB' : (Function.support B).Finite :=
    AlgebraicGeometry.Intersection.properCycle_finiteSupport (X ↘ Spec (CommRingCat.of k)) B
  have hAdeg : Function.HasFiniteSupport
      (fun x : X => A x * ((X ↘ Spec (CommRingCat.of k)).residueDegree x : ℤ)) :=
    Function.HasFiniteSupport.mul_left hA' _
  have hBdeg : Function.HasFiniteSupport
      (fun x : X => B x * ((X ↘ Spec (CommRingCat.of k)).residueDegree x : ℤ)) :=
    Function.HasFiniteSupport.mul_left hB' _
  unfold AlgebraicCycle.degree
  change (∑ᶠ x : X, (A x + B x) * ((X ↘ Spec (CommRingCat.of k)).residueDegree x : ℤ)) = _
  rw [show (fun x : X => (A x + B x) * ((X ↘ Spec (CommRingCat.of k)).residueDegree x : ℤ)) =
      (fun x : X => A x * ((X ↘ Spec (CommRingCat.of k)).residueDegree x : ℤ) +
        B x * ((X ↘ Spec (CommRingCat.of k)).residueDegree x : ℤ)) by
    funext x
    ring]
  exact finsum_add_distrib hAdeg hBdeg

variable [IsIntegral X] [IsLocallyNoetherian X]

open MiyaokaMori.TopSelfIntersectionCurve in
/-- **Stacks 02SL**: on a proper integral one-dimensional `k`-scheme the top self-intersection (the
curve degree) is additive under tensor products. -/
theorem topSelfIntersection_tensor (hX : IsProperOver k X) (hdim : X.dimension = 1)
    (L N : X.Modules) [L.IsLineBundle] [N.IsLineBundle] :
    topSelfIntersection X hX (Scheme.Modules.tensor L N) =
      topSelfIntersection X hX L + topSelfIntersection X hX N := by
  obtain ⟨s, hs⟩ := Scheme.Modules.exists_stalk_genericPoint_ne_zero L
  obtain ⟨t, ht⟩ := Scheme.Modules.exists_stalk_genericPoint_ne_zero N
  obtain ⟨u, hu, hdiv⟩ := Scheme.Modules.exists_rationalSectionDivisor_tensor L N s t hs ht
  rw [topSelfIntersection_eq_degree_rationalSectionDivisor hX hdim (Scheme.Modules.tensor L N) u hu,
    topSelfIntersection_eq_degree_rationalSectionDivisor hX hdim L s hs,
    topSelfIntersection_eq_degree_rationalSectionDivisor hX hdim N t ht, hdiv,
    AlgebraicCycle.degree_add_of_isProperOver hX]

open MiyaokaMori.TopSelfIntersectionCurve in
/-- **Stacks 02RU**: a line bundle isomorphic to `O_X` has degree zero (the divisor of a rational
section is a principal cycle, and a principal divisor on a proper integral curve has degree zero). -/
theorem topSelfIntersection_eq_zero_of_iso_unit (hX : IsProperOver k X)
    (hdim : X.dimension = 1) (M : X.Modules) [M.IsLineBundle]
    (e : M ≅ SheafOfModules.unit X.ringCatSheaf) :
    topSelfIntersection X hX M = 0 := by
  have : IsProper (X ↘ Spec (CommRingCat.of k)) := hX
  have hkd : SchemeIsOneDimensional X := schemeIsOneDimensional_of_dimension_eq_one hdim
  obtain ⟨s, hs⟩ := Scheme.Modules.exists_stalk_genericPoint_ne_zero M
  obtain ⟨g, hg⟩ := Scheme.Modules.rationalSectionDivisor_eq_principalCycle_of_iso_unit M e s hs
  rw [topSelfIntersection_eq_degree_rationalSectionDivisor hX hdim M s hs, hg]
  unfold AlgebraicCycle.degree
  change (∑ᶠ x : X, X.ord (g : X.functionField) x *
    ((X ↘ Spec (CommRingCat.of k)).residueDegree x : ℤ)) = 0
  exact principalDivisor_degree_eq_zero X hkd g

open MiyaokaMori.TopSelfIntersectionCurve in
/-- **Stacks 02SQ; Fulton §2.3**: the degree of `O_X(D)` is `deg_k D = deg [D]_0`: the generic germ of
the canonical section `1_D` is nonzero, and its divisor equals pointwise the zero-scheme cycle
`[Z(1_D)]_0 = [D]_0`. -/
theorem EffectiveCartierDivisor.topSelfIntersection_lineBundle (hX : IsProperOver k X)
    (hdim : X.dimension = 1) (D : EffectiveCartierDivisor X) :
    topSelfIntersection X hX D.lineBundle = D.degreeOver k := by
  have : IsProper (X ↘ Spec (CommRingCat.of k)) := hX
  have hXd : X.dimension = 0 + 1 := hdim
  have hne : Nonempty X := ⟨genericPoint X⟩
  have hσ : D.canonicalSection ≠ 0 := D.canonicalSection_ne_zero
  have hgerm := Scheme.Modules.germ_genericPoint_ne_zero D.lineBundle D.canonicalSection hσ
  have hcyc : D.lineBundle.rationalSectionDivisor
      (D.lineBundle.presheaf.germ ⊤ (genericPoint X) trivial
        (show Γ(D.lineBundle, ⊤) from D.canonicalSection)) =
      (Scheme.idealSheafOfSection D.lineBundle D.canonicalSection).cycle 0 := by
    ext z
    by_cases hz : Order.coheight z = 1
    · exact (Scheme.idealSheafOfSection_cycle_apply_of_coheight_eq_one (k := k) D.lineBundle
        D.canonicalSection hσ 0 hXd z hz).symm
    · rw [Scheme.idealSheafOfSection_cycle_apply_of_coheight_ne_one D.lineBundle D.canonicalSection
        hσ 0 z hz]
      exact Scheme.Modules.rationalSectionOrd_eq_zero_of_coheight_ne_one D.lineBundle _ hz
  have hI : (Scheme.idealSheafOfSection D.lineBundle D.canonicalSection).cycle 0 =
      D.idealSheaf.cycle 0 :=
    congrArg (fun I : X.IdealSheafData => I.cycle 0) D.idealSheafOfSection_canonicalSection
  rw [topSelfIntersection_eq_degree_rationalSectionDivisor hX hdim D.lineBundle _ hgerm, hcyc, hI]
  rfl

/-- `M ≅ O_X(A) ⊗ O_X(B)^∨` implies `topSelfIntersection X hX M = deg_k A − deg_k B`. -/
theorem topSelfIntersection_of_iso_tensor_dual_effectiveCartier
    (hX : IsProperOver k X) (hdim : X.dimension = 1)
    (A B : EffectiveCartierDivisor X) (M : X.Modules) [M.IsLineBundle]
    (e : M ≅ Scheme.Modules.tensor A.lineBundle (Scheme.Modules.dual B.lineBundle)) :
    topSelfIntersection X hX M = A.degreeOver k - B.degreeOver k := by
  have hP : IsProper (X ↘ Spec (CommRingCat.of k)) := hX
  have : IsOfFiniteType (X ↘ Spec (CommRingCat.of k)) := {}
  -- O(B) ⊗ O(B)^∨ ≅ O_X, hence deg O(B) + deg O(B)^∨ = 0
  let V : Variety k := { carrier := X }
  let LB : LineBundle V := LineBundle.ofModules (X := V) B.lineBundle
  have eBB : Scheme.Modules.tensor B.lineBundle (Scheme.Modules.dual B.lineBundle) ≅
      SheafOfModules.unit X.ringCatSheaf :=
    Scheme.Modules.tensorIsoTensorObj B.lineBundle (Scheme.Modules.dual B.lineBundle) ≪≫
      LB.contraction
  have h0 := topSelfIntersection_eq_zero_of_iso_unit hX hdim _ eBB
  rw [topSelfIntersection_tensor hX hdim, EffectiveCartierDivisor.topSelfIntersection_lineBundle hX hdim] at h0
  -- O(A) ⊗ O(B)^∨
  rw [AlgebraicGeometry.topSelfIntersection_congr X hX M _ e, topSelfIntersection_tensor hX hdim,
    EffectiveCartierDivisor.topSelfIntersection_lineBundle hX hdim]
  linarith

end AlgebraicGeometry

end
