import MiyaokaMori.Prelude
import MiyaokaMori.RingTheory.Dimension.Stacks00os

/-! # Dimension at a point of a finite type algebra over a field (Stacks 00OT)

Stacks 00OT: let `k` be a field, `S` a finitely generated `k`-algebra and `p ∈ Spec S`. Then
(1) `dim_p Spec S` (the infimum of the dimensions of the opens containing `p`) equals (2) the
maximum of the dimensions of the irreducible components through `p`, which equals (3) the minimum
of `dim S_m` over the maximal ideals `m ∋ p`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

section aux

variable {S : Type u} [CommRing S]

/-- The coheight of an irreducible closed subset of `Spec S` equals the height of the corresponding
prime ideal (its generic point). -/
private theorem coheight_pointsEquiv (x : PrimeSpectrum S) :
    Order.coheight (OrderDual.ofDual (PrimeSpectrum.pointsEquivIrreducibleCloseds S x)) =
      Order.height x := by
  rw [← Order.height_orderIso (PrimeSpectrum.pointsEquivIrreducibleCloseds S) x]
  rfl

private theorem coe_pointsEquiv (x : PrimeSpectrum S) :
    ((OrderDual.ofDual (PrimeSpectrum.pointsEquivIrreducibleCloseds S x) :
      IrreducibleCloseds (PrimeSpectrum S)) : Set (PrimeSpectrum S)) = closure {x} := rfl

/-- The height of every point of an open set `U` is at most `dim U`. -/
private theorem height_le_topologicalKrullDim_opens (U : Opens (PrimeSpectrum S))
    (x : PrimeSpectrum S) (hx : x ∈ U) :
    ((Order.height x : ℕ∞) : WithBot ℕ∞) ≤ topologicalKrullDim U := by
  have hf : Topology.IsOpenEmbedding (Subtype.val : U → PrimeSpectrum S) :=
    U.2.isOpenEmbedding_subtypeVal
  let W : IrreducibleCloseds (PrimeSpectrum S) :=
    OrderDual.ofDual (PrimeSpectrum.pointsEquivIrreducibleCloseds S x)
  have hne : ((Subtype.val : U → PrimeSpectrum S) ⁻¹' (W : Set (PrimeSpectrum S))).Nonempty :=
    ⟨⟨x, hx⟩, by
      change x ∈ (W : Set (PrimeSpectrum S))
      rw [coe_pointsEquiv]
      exact subset_closure rfl⟩
  have hW : W = IrreducibleCloseds.map Subtype.val hf.continuous
      ((IrreducibleCloseds.orderIsoOfIsOpenEmbedding _ hf).symm ⟨W, hne⟩) :=
    congrArg Subtype.val
      ((IrreducibleCloseds.orderIsoOfIsOpenEmbedding _ hf).apply_symm_apply ⟨W, hne⟩).symm
  rw [← coheight_pointsEquiv x]
  change ((Order.coheight W : ℕ∞) : WithBot ℕ∞) ≤ _
  rw [hW, hf.coheight_map]
  exact Order.coheight_le_krullDim _

/-- `dim U` is bounded by any upper bound for the heights of the points of `U`. -/
private theorem topologicalKrullDim_opens_le (U : Opens (PrimeSpectrum S)) (B : WithBot ℕ∞)
    (h : ∀ x ∈ U, ((Order.height x : ℕ∞) : WithBot ℕ∞) ≤ B) :
    topologicalKrullDim U ≤ B := by
  have hf : Topology.IsOpenEmbedding (Subtype.val : U → PrimeSpectrum S) :=
    U.2.isOpenEmbedding_subtypeVal
  rw [topologicalKrullDim, Order.krullDim_eq_iSup_coheight]
  refine iSup_le fun Z => ?_
  rw [← hf.coheight_map Z]
  set W := IrreducibleCloseds.map Subtype.val hf.continuous Z with hWdef
  let x : PrimeSpectrum S := (PrimeSpectrum.pointsEquivIrreducibleCloseds S).symm (OrderDual.toDual W)
  have hWx : OrderDual.ofDual (PrimeSpectrum.pointsEquivIrreducibleCloseds S x) = W := by
    simp [x]
  have hxU : x ∈ U := by
    obtain ⟨y, hy⟩ := Z.isIrreducible.nonempty
    have hyW : (y : PrimeSpectrum S) ∈ (W : Set (PrimeSpectrum S)) :=
      subset_closure ⟨y, hy, rfl⟩
    rw [← hWx, coe_pointsEquiv, ← specializes_iff_mem_closure] at hyW
    exact hyW.mem_open U.2 y.2
  rw [← hWx, coheight_pointsEquiv]
  exact h x hxU

/-- The topological dimension of `V(I)` as a subspace equals `dim S/I`. -/
private theorem topologicalKrullDim_zeroLocus (I : Ideal S) :
    topologicalKrullDim (PrimeSpectrum.zeroLocus (R := S) I) = ringKrullDim (S ⧸ I) := by
  rw [ringKrullDim_quotient]
  exact Order.krullDim_orderDual.symm.trans
    (Order.krullDim_eq_of_orderIso (PrimeSpectrum.zeroLocusEquivIrreducibleCloseds (I : Set S)).symm)

end aux

/-- In a finitely generated `k`-algebra, if a prime `q` is contained in a maximal ideal `m` then
`dim S/q ≤ height m` (Stacks 00OS). -/
private theorem ringKrullDim_quotient_le_height_of_isMaximal {k : Type u} [Field k] (S : Type u)
    [CommRing S] [Algebra k S] [Algebra.FiniteType k S] (q m : Ideal S) [hq : q.IsPrime]
    [hm : m.IsMaximal] (hqm : q ≤ m) :
    ringKrullDim (S ⧸ q) ≤ ((m.height : ℕ∞) : WithBot ℕ∞) := by
  let B := S ⧸ q
  have : IsDomain B := Ideal.Quotient.isDomain q
  have : Algebra.FiniteType k B := Algebra.FiniteType.quotient k q
  have hm' : (m.map (Ideal.Quotient.mk q)).IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
      (by rw [Ideal.mk_ker]; exact hqm)
  let e := q.primeSpectrumQuotientOrderIsoZeroLocus
  have he : (e ⟨m.map (Ideal.Quotient.mk q), hm'.isPrime⟩ : PrimeSpectrum S) =
      ⟨m, hm.isPrime⟩ := by
    apply PrimeSpectrum.ext
    change (m.map (Ideal.Quotient.mk q)).comap (Ideal.Quotient.mk q) = m
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      Ideal.mk_ker]
    exact sup_eq_left.mpr hqm
  have h1 : (m.map (Ideal.Quotient.mk q)).height ≤ m.height := by
    rw [PrimeSpectrum.height_eq_orderHeight
        (⟨m.map (Ideal.Quotient.mk q), hm'.isPrime⟩ : PrimeSpectrum B),
      PrimeSpectrum.height_eq_orderHeight (⟨m, hm.isPrime⟩ : PrimeSpectrum S),
      ← Order.height_orderIso e, ← he]
    exact Order.height_le_height_apply_of_strictMono _ (Subtype.strictMono_coe _) _
  rw [← stacks_00OS (k := k) B (m.map (Ideal.Quotient.mk q)),
    IsLocalization.AtPrime.ringKrullDim_eq_height (m.map (Ideal.Quotient.mk q))]
  exact WithBot.coe_le_coe.mpr h1

/-- Stacks 00OT: the local dimension of `Spec S` at `p` equals the maximum of the dimensions of the
irreducible components through `p`, and also the minimum of `dim S_m` over the maximal ideals
`m ∋ p`. -/
theorem stacks_00OT {k : Type u} [Field k] (S : Type u) [CommRing S] [Algebra k S] [Algebra.FiniteType k S]
    (p : PrimeSpectrum S) :
    (⨅ U ∈ {U : TopologicalSpace.Opens (PrimeSpectrum S) | p ∈ U}, topologicalKrullDim U) =
        ⨆ Z ∈ {Z ∈ irreducibleComponents (PrimeSpectrum S) | p ∈ Z}, topologicalKrullDim Z ∧
      (⨅ U ∈ {U : TopologicalSpace.Opens (PrimeSpectrum S) | p ∈ U}, topologicalKrullDim U) =
        ⨅ (m : PrimeSpectrum S) (_ : m.asIdeal.IsMaximal) (_ : p ≤ m),
          ringKrullDim (Localization.AtPrime m.asIdeal) := by
  have hNoeth : IsNoetherianRing S := Algebra.FiniteType.isNoetherianRing k S
  have hJac : IsJacobsonRing S := isJacobsonRing_of_finiteType (A := k)
  -- (3) ≤ (1)
  have h31 : (⨅ (m : PrimeSpectrum S) (_ : m.asIdeal.IsMaximal) (_ : p ≤ m),
      ringKrullDim (Localization.AtPrime m.asIdeal)) ≤
      ⨅ U ∈ {U : TopologicalSpace.Opens (PrimeSpectrum S) | p ∈ U}, topologicalKrullDim U := by
    refine le_iInf₂ fun U hU => ?_
    obtain ⟨m, ⟨hmU, hmp⟩, hmcl⟩ := nonempty_inter_closedPoints
      (Z := (U : Set (PrimeSpectrum S)) ∩ closure {p}) ⟨p, hU, subset_closure rfl⟩
      (U.2.isLocallyClosed.inter isClosed_closure.isLocallyClosed)
    have hmax : m.asIdeal.IsMaximal := (PrimeSpectrum.isClosed_singleton_iff_isMaximal m).mp hmcl
    have hpm : p ≤ m := (PrimeSpectrum.le_iff_specializes p m).mpr
      (specializes_iff_mem_closure.mpr hmp)
    refine iInf_le_of_le m (iInf_le_of_le hmax (iInf_le_of_le hpm ?_))
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height m.asIdeal,
      PrimeSpectrum.height_eq_orderHeight m]
    exact height_le_topologicalKrullDim_opens U m hmU
  -- (2) ≤ (3)
  have h23 : (⨆ Z ∈ {Z ∈ irreducibleComponents (PrimeSpectrum S) | p ∈ Z},
      topologicalKrullDim Z) ≤
      ⨅ (m : PrimeSpectrum S) (_ : m.asIdeal.IsMaximal) (_ : p ≤ m),
        ringKrullDim (Localization.AtPrime m.asIdeal) := by
    refine iSup₂_le fun Z hZ => le_iInf fun m => le_iInf fun hm => le_iInf fun hpm => ?_
    obtain ⟨hZc, hpZ⟩ := hZ
    rw [← PrimeSpectrum.zeroLocus_minimalPrimes] at hZc
    obtain ⟨q, hq, rfl⟩ := hZc
    have hqprime : q.IsPrime := hq.1.1
    have hqm : q ≤ m.asIdeal := fun a ha => hpm (hpZ ha)
    change topologicalKrullDim (PrimeSpectrum.zeroLocus (R := S) q) ≤ _
    rw [topologicalKrullDim_zeroLocus,
      IsLocalization.AtPrime.ringKrullDim_eq_height m.asIdeal (Localization.AtPrime m.asIdeal)]
    exact ringKrullDim_quotient_le_height_of_isMaximal (k := k) S q m.asIdeal hqm
  -- (1) ≤ (2)
  have h12 : (⨅ U ∈ {U : TopologicalSpace.Opens (PrimeSpectrum S) | p ∈ U},
      topologicalKrullDim U) ≤
      ⨆ Z ∈ {Z ∈ irreducibleComponents (PrimeSpectrum S) | p ∈ Z}, topologicalKrullDim Z := by
    let T : Set (PrimeSpectrum S) := ⋃₀ {Z ∈ irreducibleComponents (PrimeSpectrum S) | p ∉ Z}
    have hTfin : {Z ∈ irreducibleComponents (PrimeSpectrum S) | p ∉ Z}.Finite :=
      TopologicalSpace.NoetherianSpace.finite_irreducibleComponents.subset fun Z hZ => hZ.1
    have hTcl : IsClosed T := by
      change IsClosed (⋃₀ {Z ∈ irreducibleComponents (PrimeSpectrum S) | p ∉ Z})
      rw [Set.sUnion_eq_biUnion]
      exact hTfin.isClosed_biUnion fun Z hZ => isClosed_of_mem_irreducibleComponents Z hZ.1
    have hpT : p ∉ T := by
      rintro ⟨Z, hZ, hpZ⟩
      exact hZ.2 hpZ
    let U₀ : Opens (PrimeSpectrum S) := ⟨Tᶜ, hTcl.isOpen_compl⟩
    refine (iInf₂_le U₀ (show p ∈ U₀ from hpT)).trans ?_
    refine topologicalKrullDim_opens_le U₀ _ fun x hx => ?_
    rw [Order.height_eq_krullDim_Iic, Order.krullDim]
    refine iSup_le fun l => ?_
    -- take a minimal prime `q` below the bottom of the chain
    obtain ⟨q, hq, hql⟩ := Ideal.exists_minimalPrimes_le
      (I := (⊥ : Ideal S)) (J := (l.head : PrimeSpectrum S).asIdeal) bot_le
    have hqprime : q.IsPrime := hq.1.1
    have hZc : PrimeSpectrum.zeroLocus (R := S) q ∈ irreducibleComponents (PrimeSpectrum S) := by
      rw [← PrimeSpectrum.zeroLocus_minimalPrimes]
      exact ⟨q, hq, rfl⟩
    have hqx : (⟨q, hqprime⟩ : PrimeSpectrum S) ≤ x :=
      le_trans (show (⟨q, hqprime⟩ : PrimeSpectrum S) ≤ (l.head : PrimeSpectrum S) from hql)
        l.head.2
    have hqU : (⟨q, hqprime⟩ : PrimeSpectrum S) ∈ U₀ :=
      ((PrimeSpectrum.le_iff_specializes _ _).mp hqx).mem_open U₀.2 hx
    have hpZ : p ∈ PrimeSpectrum.zeroLocus (R := S) q := by
      by_contra hp
      exact hqU ⟨_, ⟨hZc, hp⟩, (PrimeSpectrum.mem_zeroLocus _ _).mpr (le_refl q)⟩
    refine le_trans ?_ (le_iSup₂ (f := fun (Z : Set (PrimeSpectrum S))
      (_ : Z ∈ {Z ∈ irreducibleComponents (PrimeSpectrum S) | p ∈ Z}) => topologicalKrullDim Z)
      (PrimeSpectrum.zeroLocus (R := S) q) ⟨hZc, hpZ⟩)
    rw [topologicalKrullDim_zeroLocus, ringKrullDim_quotient]
    let l' : LTSeries (PrimeSpectrum.zeroLocus (R := S) q) :=
      { length := l.length
        toFun := fun i => ⟨(l i : PrimeSpectrum S), (PrimeSpectrum.mem_zeroLocus _ _).mpr
          (le_trans hql (l.head_le i))⟩
        step := fun i => l.step i }
    exact Order.LTSeries.length_le_krullDim l'
  exact ⟨le_antisymm h12 (h23.trans h31), le_antisymm (h12.trans h23) h31⟩

end
