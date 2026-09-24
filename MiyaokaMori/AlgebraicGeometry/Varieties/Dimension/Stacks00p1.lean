import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.Stacks00ot
import MiyaokaMori.RingTheory.Dimension.FiniteTypeDomainHeightAddQuotientDim
import MiyaokaMori.RingTheory.Dimension.FiniteTypeDomainDimension

/-! # Dimension at a point, local ring and transcendence degree (Stacks 00P1)

Stacks 00P1: let `k` be a field, `S` a finitely generated `k`-algebra and `p ∈ Spec S`. Then
`dim_p Spec S = dim S_p + trdeg_k κ(p)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The topological dimension of `V(I)` as a subspace equals `dim S/I`. -/
private theorem topologicalKrullDim_zeroLocus_eq {S : Type u} [CommRing S] (I : Ideal S) :
    topologicalKrullDim (PrimeSpectrum.zeroLocus (R := S) I) = ringKrullDim (S ⧸ I) := by
  rw [ringKrullDim_quotient]
  exact Order.krullDim_orderDual.symm.trans
    (Order.krullDim_eq_of_orderIso (PrimeSpectrum.zeroLocusEquivIrreducibleCloseds (I : Set S)).symm)

/-- For primes `q ≤ p`, the height of `p/q` in `S/q` equals the height of `p` in the subposet `V(q)`. -/
private theorem height_map_quotient_eq {S : Type u} [CommRing S] (q p : Ideal S) [q.IsPrime]
    [hp : p.IsPrime] (hqp : q ≤ p) :
    (p.map (Ideal.Quotient.mk q)).height =
      Order.height (⟨⟨p, hp⟩, (PrimeSpectrum.mem_zeroLocus _ _).mpr hqp⟩ :
        PrimeSpectrum.zeroLocus (R := S) q) := by
  have hp' : (p.map (Ideal.Quotient.mk q)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hqp)
  let e := q.primeSpectrumQuotientOrderIsoZeroLocus
  have he : e ⟨p.map (Ideal.Quotient.mk q), hp'⟩ =
      ⟨⟨p, hp⟩, (PrimeSpectrum.mem_zeroLocus _ _).mpr hqp⟩ := by
    apply Subtype.ext
    apply PrimeSpectrum.ext
    change (p.map (Ideal.Quotient.mk q)).comap (Ideal.Quotient.mk q) = p
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      Ideal.mk_ker]
    exact sup_eq_left.mpr hqp
  rw [PrimeSpectrum.height_eq_orderHeight
      (⟨p.map (Ideal.Quotient.mk q), hp'⟩ : PrimeSpectrum (S ⧸ q)),
    ← Order.height_orderIso e, he]

/-- In a finitely generated `k`-algebra, for primes `q ≤ p`: `dim S/q = dim S/p + ht(p/q)` (the
catenarity of Stacks 00OS). -/
private theorem ringKrullDim_quotient_eq_add_height {k : Type u} [Field k] (S : Type u)
    [CommRing S] [Algebra k S] [Algebra.FiniteType k S] (q p : Ideal S) [hq : q.IsPrime]
    [hp : p.IsPrime] (hqp : q ≤ p) :
    ringKrullDim (S ⧸ q) =
      ringKrullDim (S ⧸ p) + ((p.map (Ideal.Quotient.mk q)).height : WithBot ℕ∞) := by
  have : IsDomain (S ⧸ q) := Ideal.Quotient.isDomain q
  have : Algebra.FiniteType k (S ⧸ q) := Algebra.FiniteType.quotient k q
  have hp' : (p.map (Ideal.Quotient.mk q)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hqp)
  rw [← ringKrullDim_quotient_add_height_eq (k := k) (S ⧸ q) (p.map (Ideal.Quotient.mk q)),
    ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hqp)]

/-- Stacks 00P1: `dim_p Spec S = dim S_p + trdeg_k κ(p)`. -/
theorem stacks_00P1 {k : Type u} [Field k] (S : Type u) [CommRing S] [Algebra k S] [Algebra.FiniteType k S]
    (p : PrimeSpectrum S) :
    (⨅ U ∈ {U : TopologicalSpace.Opens (PrimeSpectrum S) | p ∈ U}, topologicalKrullDim U) =
      ringKrullDim (Localization.AtPrime p.asIdeal) +
        (Cardinal.toENat (Algebra.trdeg k p.asIdeal.ResidueField) : WithBot ℕ∞) := by
  have hNoeth : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
  rw [(stacks_00OT (k := k) S p).1, ← MiyaokaMori.RingTheory.quotient_ringKrullDim_eq_residue_trdeg k S p.asIdeal,
    IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal (Localization.AtPrime p.asIdeal),
    add_comm]
  apply le_antisymm
  · -- for every component `V(q)` through `p`: `dim S/q = dim S/p + ht(p/q) ≤ dim S/p + ht p`
    refine iSup₂_le fun Z hZ => ?_
    obtain ⟨hZc, hpZ⟩ := hZ
    rw [← PrimeSpectrum.zeroLocus_minimalPrimes] at hZc
    obtain ⟨q, hq, rfl⟩ := hZc
    have hqprime : q.IsPrime := hq.1.1
    have hqp : q ≤ p.asIdeal := (PrimeSpectrum.mem_zeroLocus _ _).mp hpZ
    change topologicalKrullDim (PrimeSpectrum.zeroLocus (R := S) q) ≤ _
    rw [topologicalKrullDim_zeroLocus_eq, ringKrullDim_quotient_eq_add_height (k := k) S q p.asIdeal hqp]
    refine add_le_add_right (WithBot.coe_le_coe.mpr ?_) _
    rw [height_map_quotient_eq q p.asIdeal hqp, PrimeSpectrum.height_eq_orderHeight p]
    exact Order.height_le_height_apply_of_strictMono _ (Subtype.strictMono_coe _) _
  · -- take a chain of length `ht p` and a minimal prime `q` below its bottom
    have hfin : Order.height p ≠ ⊤ := by
      rw [← PrimeSpectrum.height_eq_orderHeight p]
      exact Ideal.height_ne_top_of_isPrime
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfin
    obtain ⟨l, hlast, hlen⟩ := Order.exists_series_of_height_eq_coe p hn.symm
    obtain ⟨q, hq, hql⟩ := Ideal.exists_minimalPrimes_le
      (I := (⊥ : Ideal S)) (J := (l.head : PrimeSpectrum S).asIdeal) bot_le
    have hqprime : q.IsPrime := hq.1.1
    have hqp : q ≤ p.asIdeal := le_trans hql (hlast ▸ l.head_le_last)
    have hZc : PrimeSpectrum.zeroLocus (R := S) q ∈ irreducibleComponents (PrimeSpectrum S) := by
      rw [← PrimeSpectrum.zeroLocus_minimalPrimes]
      exact ⟨q, hq, rfl⟩
    refine le_trans ?_ (le_iSup₂ (f := fun (Z : Set (PrimeSpectrum S))
      (_ : Z ∈ {Z ∈ irreducibleComponents (PrimeSpectrum S) | p ∈ Z}) => topologicalKrullDim Z)
      (PrimeSpectrum.zeroLocus (R := S) q) ⟨hZc, (PrimeSpectrum.mem_zeroLocus _ _).mpr hqp⟩)
    rw [topologicalKrullDim_zeroLocus_eq, ringKrullDim_quotient_eq_add_height (k := k) S q p.asIdeal hqp]
    refine add_le_add_right (WithBot.coe_le_coe.mpr ?_) _
    rw [height_map_quotient_eq q p.asIdeal hqp, PrimeSpectrum.height_eq_orderHeight p, ← hn, ← hlen]
    let l' : LTSeries (PrimeSpectrum.zeroLocus (R := S) q) :=
      { length := l.length
        toFun := fun i => ⟨(l i : PrimeSpectrum S), (PrimeSpectrum.mem_zeroLocus _ _).mpr
          (le_trans hql (l.head_le i))⟩
        step := fun i => l.step i }
    refine Order.length_le_height (p := l') ?_
    change l.last ≤ p
    exact hlast.le

end
