import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProperOverField
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.SchemeDimension
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.SchemeFundamentalCycle
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.ModulesFiniteTypeInstances
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.ModulesQuasicoherentClosure
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorUnitIso
import MiyaokaMori.AlgebraicGeometry.Chow.Snapper.Stacks0ben
import MiyaokaMori.AlgebraicGeometry.Chow.Snapper.Stacks0bep

/-! # Decomposition of the Snapper intersection number along irreducible components

Stacks 0BES: the intersection number defined through `χ` decomposes along the `d`-dimensional
irreducible components: `(L_1⋯L_d·X) = Σ m_i (L_1⋯L_d·X_i)`, where the `X_i` are the `d`-dimensional
components (reduced integral closed subschemes) and `m_i` is the length at the generic point — the
coefficients of the fundamental cycle `[X]_d = Σ m_i[X_i]`.

Source: Stacks 0BES; Lazarsfeld, Positivity in Algebraic Geometry I, §1.1.C, footnote 7; used in the
proof that the Snapper intersection number equals the Chow one.

## Proof

The theorem is assembled from Stacks 0BEN (`exists_snapper_sub_components_totalDegree_lt`,
`Stacks0ben.lean`) applied to `F = O_X`, `r = d`, plus the following pieces:

* `MvPolynomial.sum_neg_one_pow_eval_indicator_eq_zero`: the mixed difference
  `Σ_S (-1)^(d-|S|) P(1_S)` of a polynomial of total degree `< d` in `d` variables vanishes.
  (Each monomial `X^v` with `Σ v_i < d` misses some variable `i₀`; by `Fintype.prod_add`
  the alternating sum of `∏_i (1_S i)^{v_i}` equals `∏_i (1 - 0^{v_i})`, whose `i₀`-factor is `0`.)
* `mem_genericPoints_of_pointClosureDimension_eq`: in a scheme of finite Krull dimension `d`, a point
  whose closure has dimension `d` is the generic point of an irreducible component
  (`height ξ + coheight ξ ≤ krullDim X = d = height ξ` forces `coheight ξ = 0`, i.e. `ξ` is maximal
  for specialization).
* `Scheme.Modules.support_unit`: `Supp O_X = X` (stalks of `O_X` are nontrivial local rings).
* `length_unit_stalk_toNat_eq`: at a generic point the coefficient of 0BEN,
  `length_{O_{X,ξ}} (O_X)_ξ`, is the coefficient `integralFundamentalMultiplicity X ξ` of
  `X.fundamentalCycle` (via `unitStalkLinearEquiv`).
* `sheafEulerCharacteristic_of_isEmpty`: on the empty scheme `χ = 0` (`Γ(X,⊤) = Γ(X,⊥)` is the zero
  ring, so every cohomology module is trivial). This handles `X = ∅`, where 0BEN does not apply
  (`dim Supp O_X = ⊥ ≠ 0 = d`).

The index set `ι` is `Fin n` for `n = #{ξ | dim closure{ξ} = d}` (finite, since these are generic
points of components of the Noetherian scheme `X`), `Z_j = X.pointClosure ξ_j`,
`e_j = X.pointClosureι ξ_j`, `m_j = integralFundamentalMultiplicity X ξ_j`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The mixed finite difference `Σ_{S ⊆ Fin d} (-1)^(d - |S|) P(1_S)` kills every polynomial `P` in
`d` variables of total degree `< d` (and `P = 0`). Proof: expand `P` into monomials; a monomial
`c·X^v` with `Σ_i v_i < d` has some `v_{i₀} = 0`; `(1_S)^v = ∏_i (1_S i)^{v_i}` and
`Σ_S (-1)^{d-|S|} ∏_i (1_S i)^{v_i} = ∏_i (1 - 0^{v_i})` (`Fintype.prod_add`), whose factor at `i₀`
is `1 - 0^0 = 0`. -/
theorem MvPolynomial.sum_neg_one_pow_eval_indicator_eq_zero {d : ℕ}
    (P : MvPolynomial (Fin d) ℚ) (hP : P = 0 ∨ P.totalDegree < d) :
    ∑ S : Finset (Fin d), (-1 : ℚ) ^ (d - S.card) *
      MvPolynomial.eval (fun i => if i ∈ S then (1 : ℚ) else 0) P = 0 := by
  classical
  rcases hP with rfl | hP
  · simp
  have key : ∀ v ∈ P.support, ∑ S : Finset (Fin d), (-1 : ℚ) ^ (d - S.card) *
      MvPolynomial.eval (fun i => if i ∈ S then (1 : ℚ) else 0)
        (MvPolynomial.monomial v (MvPolynomial.coeff v P)) = 0 := by
    intro v hv
    have hdeg : (v.sum fun _ e => e) < d := lt_of_le_of_lt (MvPolynomial.le_totalDegree hv) hP
    obtain ⟨i₀, hi₀⟩ : ∃ i, v i = 0 := by
      by_contra h
      push Not at h
      have : d ≤ v.sum fun _ e => e := by
        rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
        calc d = ∑ _i : Fin d, 1 := by simp
          _ ≤ ∑ i, v i := Finset.sum_le_sum fun i _ => Nat.one_le_iff_ne_zero.mpr (h i)
      exact absurd hdeg (not_lt.mpr this)
    simp_rw [MvPolynomial.eval_monomial]
    have hprod : ∀ S : Finset (Fin d),
        (v.prod fun n e => (if n ∈ S then (1 : ℚ) else 0) ^ e)
          = ∏ i, (if i ∈ S then (1 : ℚ) else 0) ^ (v i) :=
      fun S => Finsupp.prod_fintype _ _ (fun _ => pow_zero _)
    simp_rw [hprod]
    have hterm : ∀ S : Finset (Fin d),
        (-1 : ℚ) ^ (d - S.card) * ∏ i, (if i ∈ S then (1 : ℚ) else 0) ^ (v i)
          = (∏ i ∈ S, (1 : ℚ)) * ∏ i ∈ Sᶜ, (-(0 : ℚ) ^ (v i)) := by
      intro S
      rw [Finset.prod_neg, Finset.prod_const_one, one_mul, Finset.card_compl, Fintype.card_fin]
      congr 1
      rw [← Finset.prod_mul_prod_compl S,
        Finset.prod_eq_one (fun i hi => by rw [if_pos hi, one_pow]), one_mul]
      exact Finset.prod_congr rfl fun i hi => by rw [if_neg (Finset.mem_compl.mp hi)]
    have hsum : ∑ S : Finset (Fin d), (-1 : ℚ) ^ (d - S.card) *
        ∏ i, (if i ∈ S then (1 : ℚ) else 0) ^ (v i) = 0 := by
      simp_rw [hterm]
      rw [← Fintype.prod_add]
      exact Finset.prod_eq_zero (Finset.mem_univ i₀) (by rw [hi₀, pow_zero]; ring)
    calc ∑ S : Finset (Fin d), (-1 : ℚ) ^ (d - S.card) *
          (MvPolynomial.coeff v P * ∏ i, (if i ∈ S then (1 : ℚ) else 0) ^ (v i))
        = MvPolynomial.coeff v P * ∑ S : Finset (Fin d), (-1 : ℚ) ^ (d - S.card) *
            ∏ i, (if i ∈ S then (1 : ℚ) else 0) ^ (v i) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun S _ => by ring
      _ = 0 := by rw [hsum, mul_zero]
  conv_lhs => rw [P.as_sum]
  simp_rw [map_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_eq_zero fun v hv => key v hv

/-- In a scheme `X` of finite topological Krull dimension `d`, a point `ξ` whose closure has
dimension `d` is the generic point of an irreducible component (`ξ ∈ genericPoints X`).
Proof: `dim closure{ξ} = height ξ` in the specialization order (`pointClosureDimension_eq_height`),
`height ξ + coheight ξ ≤ krullDim X = d`, so `coheight ξ = 0`, i.e. `ξ` is maximal: every
generalization `η ⤳ ξ` satisfies `ξ ⤳ η`. Hence any irreducible `t ⊇ closure{ξ}` has (quasi-sober)
generic point `η` of `closure t` with `η ⤳ ξ`, so `ξ ⤳ η`, `closure t = closure{η} ⊆ closure{ξ}`. -/
theorem AlgebraicGeometry.mem_genericPoints_of_pointClosureDimension_eq
    (X : AlgebraicGeometry.Scheme.{u}) {d : ℕ} (hX : topologicalKrullDim X = (d : WithBot ℕ∞))
    (ξ : X) (hξ : AlgebraicGeometry.Intersection.pointClosureDimension X ξ = (d : WithBot ℕ∞)) :
    ξ ∈ genericPoints X := by
  have hh : (Order.height ξ : ℕ∞) = d := by
    have := (AlgebraicGeometry.Intersection.pointClosureDimension_eq_height X ξ).symm.trans hξ
    exact_mod_cast this
  have : Nonempty X := ⟨ξ⟩
  have hle : Order.height ξ + Order.coheight ξ ≤ (d : ℕ∞) := by
    have h1 : ((Order.height ξ + Order.coheight ξ : ℕ∞) : WithBot ℕ∞) ≤ Order.krullDim X := by
      rw [Order.krullDim_eq_iSup_height_add_coheight_of_nonempty]
      exact WithBot.coe_le_coe.mpr (le_iSup (fun a : X => Order.height a + Order.coheight a) ξ)
    rw [AlgebraicGeometry.krullDim_eq_topologicalKrullDim, hX] at h1
    exact_mod_cast h1
  have hco : Order.coheight ξ = 0 := by
    rw [hh] at hle
    have h2 : (d : ℕ∞) + Order.coheight ξ ≤ (d : ℕ∞) + 0 := by simpa using hle
    exact le_antisymm ((ENat.add_le_add_iff_left (ENat.natCast_ne_top d)).mp h2) bot_le
  have hmax : IsMax ξ := Order.coheight_eq_zero.mp hco
  show closure ({ξ} : Set X) ∈ irreducibleComponents X
  refine ⟨isIrreducible_singleton.closure, fun t ht hsub => ?_⟩
  have hη : IsGenericPoint ht.genericPoint (closure t) := ht.isGenericPoint_genericPoint_closure
  have hξt : ξ ∈ closure t := subset_closure (hsub (subset_closure rfl))
  have hηξ : ht.genericPoint ⤳ ξ := hη.specializes hξt
  have hle' : ξ ≤ ht.genericPoint := hηξ
  have hge : ht.genericPoint ≤ ξ := hmax hle'
  have hξη : ξ ⤳ ht.genericPoint := hge
  calc t ⊆ closure t := subset_closure
    _ = closure {ht.genericPoint} := hη.def.symm
    _ ⊆ closure {ξ} := closure_minimal (Set.singleton_subset_iff.mpr
        (specializes_iff_mem_closure.mp hξη)) isClosed_closure

/-- The support of the structure sheaf is everything: every stalk `(O_X)_x ≅ O_{X,x}` is a nontrivial
(local) ring. -/
theorem AlgebraicGeometry.Scheme.Modules.support_unit (X : AlgebraicGeometry.Scheme.{u}) :
    AlgebraicGeometry.Scheme.Modules.support (X := X) (SheafOfModules.unit X.ringCatSheaf) = Set.univ := by
  refine Set.eq_univ_of_forall fun x => ?_
  show Nontrivial (AlgebraicGeometry.Scheme.Modules.stalk (X := X) (SheafOfModules.unit X.ringCatSheaf) x)
  letI := AlgebraicGeometry.Scheme.Modules.moduleStalkModule X (SheafOfModules.unit X.ringCatSheaf) x
  exact (AlgebraicGeometry.Divisors.LineGenericCoordinates.unitStalkLinearEquiv X x).toEquiv.nontrivial

/-- At a generic point `ξ` of an irreducible component, the 0BEN coefficient
`length_{O_{X,ξ}} (O_X)_ξ` equals the coefficient `integralFundamentalMultiplicity X ξ`
(`= length_{O_{X,ξ}} O_{X,ξ}`) of the fundamental cycle. -/
theorem AlgebraicGeometry.length_unit_stalk_toNat_eq (X : AlgebraicGeometry.Scheme.{u})
    [AlgebraicGeometry.IsLocallyNoetherian X] (ξ : X) (hξ : ξ ∈ genericPoints X) :
    (Module.length (X.presheaf.stalk ξ)
        (AlgebraicGeometry.Scheme.Modules.stalk (X := X) (SheafOfModules.unit X.ringCatSheaf) ξ)).toNat
      = (AlgebraicGeometry.Intersection.integralFundamentalMultiplicity X ξ).toNat := by
  have h1 : (AlgebraicGeometry.Intersection.integralFundamentalMultiplicity X ξ).toNat
      = (AlgebraicGeometry.Intersection.fundamentalMultiplicity X ξ).toNat := by
    unfold AlgebraicGeometry.Intersection.integralFundamentalMultiplicity
    rw [Int.toNat_natCast, ENat.lift_eq_toNat_of_lt_top]
  rw [h1, AlgebraicGeometry.Intersection.fundamentalMultiplicity_of_generic X ξ hξ]
  unfold AlgebraicGeometry.Intersection.stalkLength
  congr 1
  letI := AlgebraicGeometry.Scheme.Modules.moduleStalkModule X (SheafOfModules.unit X.ringCatSheaf) ξ
  exact (AlgebraicGeometry.Divisors.LineGenericCoordinates.unitStalkLinearEquiv X ξ).length_eq

/-- `X.dimension` of the reduced point closure is the dimension of `closure {ξ}`. -/
theorem AlgebraicGeometry.Scheme.pointClosure_dimension_eq (X : AlgebraicGeometry.Scheme.{u})
    (ξ : X) {d : ℕ} (h : AlgebraicGeometry.Intersection.pointClosureDimension X ξ = (d : WithBot ℕ∞)) :
    (X.pointClosure ξ).dimension = d := by
  have hk : topologicalKrullDim (X.pointClosure ξ) = (d : WithBot ℕ∞) :=
    (AlgebraicGeometry.Intersection.pointClosureDimension_eq_topologicalKrullDim_closure X ξ).symm.trans h
  unfold AlgebraicGeometry.Scheme.dimension
  rw [hk]
  simp

/-- On the empty scheme every Euler characteristic is `0`: `(⊤ : X.Opens) = ⊥`, so `Γ(X, ⊤)` is the
zero ring and every `Γ(X, ⊤)`-module (in particular every `sheafCohomology X M i`) is trivial. -/
theorem AlgebraicGeometry.sheafEulerCharacteristic_of_isEmpty {k : Type u} [Field k]
    (X : AlgebraicGeometry.Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [IsEmpty X] (M : X.Modules) :
    AlgebraicGeometry.sheafEulerCharacteristic (k := k) X M = 0 := by
  have htop : (⊤ : X.Opens) = ⊥ := by
    ext x
    exact (IsEmpty.false x).elim
  have hsub : Subsingleton Γ(X, ⊤) := by rw [htop]; infer_instance
  unfold AlgebraicGeometry.sheafEulerCharacteristic
  refine finsum_eq_zero_of_forall_eq_zero fun i => ?_
  have : Subsingleton (AlgebraicGeometry.sheafCohomology X M i) :=
    Module.subsingleton Γ(X, ⊤) _
  rw [Module.finrank_zero_of_subsingleton]
  simp

open Classical in

theorem AlgebraicGeometry.snapperIntersection_eq_sum_components {k : Type u} [Field k]
    (X : AlgebraicGeometry.Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (hX : IsProperOver k X) [AlgebraicGeometry.IsLocallyNoetherian X]
    {d : ℕ} (hd : X.dimension = d) (L : Fin d → X.Modules) [∀ i, (L i).IsLineBundle] :
    ∃ (ι : Type) (_ : Fintype ι) (m : ι → ℕ) (Z : ι → AlgebraicGeometry.Scheme.{u})
      (e : ∀ j, Z j ⟶ X) (_ : ∀ j, AlgebraicGeometry.IsClosedImmersion (e j))
      (_ : ∀ j, AlgebraicGeometry.IsIntegral (Z j)) (hdZ : ∀ j, (Z j).dimension = d),
      (∀ x : X, X.fundamentalCycle d x
          = ∑ j, (m j : ℤ) * (if x = (e j).base (genericPoint (Z j)) then 1 else 0)) ∧
      AlgebraicGeometry.snapperIntersection X hX hd L
        = ∑ j, (m j : ℚ) *
            (letI : (Z j).Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
              ⟨e j ≫ (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
             AlgebraicGeometry.snapperIntersection (Z j) (isProperOver_of_closedImmersion hX (e j)) (hdZ j)
              (fun i => (AlgebraicGeometry.Scheme.Modules.pullback (e j)).obj (L i))) := by
  by_cases hne : Nonempty X
  swap
  · -- the empty scheme: `d = 0`, no components, both sides vanish
    have hE : IsEmpty X := not_nonempty_iff.mp hne
    have hd0 : d = 0 := by
      rw [← hd]
      unfold AlgebraicGeometry.Scheme.dimension
      rw [← AlgebraicGeometry.krullDim_eq_topologicalKrullDim, Order.krullDim_eq_bot]
      simp
    subst hd0
    refine ⟨Fin 0, inferInstance, fun j => j.elim0, fun j => j.elim0, fun j => j.elim0,
      fun j => j.elim0, fun j => j.elim0, fun j => j.elim0, fun x => (IsEmpty.false x).elim, ?_⟩
    rw [Finset.univ_eq_empty, Finset.sum_empty]
    unfold AlgebraicGeometry.snapperIntersection
    simp [AlgebraicGeometry.sheafEulerCharacteristic_of_isEmpty]
  -- main case: `X` nonempty, Noetherian, of finite dimension `d`
  have hprop : AlgebraicGeometry.IsProper (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := hX
  have hcpt : CompactSpace X :=
    AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace
      (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
  have : AlgebraicGeometry.IsNoetherian X := ⟨⟩
  have hntop : topologicalKrullDim X ≠ ⊤ :=
    AlgebraicGeometry.topologicalKrullDim_ne_top_of_isProperOver X hX
  have hkX : topologicalKrullDim X = (d : WithBot ℕ∞) := by
    rw [X.topologicalKrullDim_eq_dimension hntop, hd]
  -- the finite set of generic points of the `d`-dimensional components
  set T : Set X := {ξ | AlgebraicGeometry.Intersection.pointClosureDimension X ξ = (d : WithBot ℕ∞)}
    with hT
  have hTgen : T ⊆ genericPoints X := fun ξ hξ =>
    AlgebraicGeometry.mem_genericPoints_of_pointClosureDimension_eq X hkX ξ hξ
  have hTfin : T.Finite :=
    (genericPoints.finite AlgebraicGeometry.finite_irreducibleComponents_of_isNoetherian).subset
      hTgen
  set s : Finset X := hTfin.toFinset with hs
  let φ : Fin s.card ≃ s := s.equivFin.symm
  obtain ⟨ξ, hξdef⟩ : ∃ ξ : Fin s.card → X, ∀ j, ξ j = (φ j).1 := ⟨_, fun _ => rfl⟩
  have hξT : ∀ j, ξ j ∈ T := fun j => by rw [hξdef]; exact hTfin.mem_toFinset.mp (φ j).2
  have hξdim : ∀ j, AlgebraicGeometry.Intersection.pointClosureDimension X (ξ j) = (d : WithBot ℕ∞) :=
    fun j => hξT j
  refine ⟨Fin s.card, inferInstance,
    fun j => (AlgebraicGeometry.Intersection.integralFundamentalMultiplicity X (ξ j)).toNat,
    fun j => X.pointClosure (ξ j), fun j => X.pointClosureι (ξ j),
    fun j => inferInstanceAs (AlgebraicGeometry.IsClosedImmersion
      (AlgebraicGeometry.Scheme.IdealSheafData.vanishingIdeal
        ⟨closure {ξ j}, isClosed_closure⟩).subschemeι),
    fun j => inferInstance, fun j => X.pointClosure_dimension_eq (ξ j) (hξdim j), ?_, ?_⟩
  · -- the fundamental cycle
    intro x
    show (if AlgebraicGeometry.Intersection.pointClosureDimension X x = (d : WithBot ℕ∞)
        then AlgebraicGeometry.Intersection.integralFundamentalMultiplicity X x else 0) = _
    simp_rw [AlgebraicGeometry.Scheme.pointClosureι_genericPoint]
    have hm : ∀ j, (((AlgebraicGeometry.Intersection.integralFundamentalMultiplicity X (ξ j)).toNat : ℕ) : ℤ)
        = AlgebraicGeometry.Intersection.integralFundamentalMultiplicity X (ξ j) := fun j =>
      Int.toNat_of_nonneg (AlgebraicGeometry.Intersection.integralFundamentalMultiplicity_nonneg X (ξ j))
    simp_rw [hm, mul_ite, mul_one, mul_zero]
    have hsum : ∑ j, (if x = ξ j then AlgebraicGeometry.Intersection.integralFundamentalMultiplicity X (ξ j)
        else 0) = ∑ y ∈ s, (if x = y then AlgebraicGeometry.Intersection.integralFundamentalMultiplicity X y
        else 0) := by
      rw [← Finset.sum_coe_sort s]
      exact Fintype.sum_equiv φ _ _ fun j => by rw [hξdef]
    rw [hsum, Finset.sum_ite_eq]
    have hmem : x ∈ s ↔ AlgebraicGeometry.Intersection.pointClosureDimension X x = (d : WithBot ℕ∞) :=
      hTfin.mem_toFinset
    by_cases hx : AlgebraicGeometry.Intersection.pointClosureDimension X x = (d : WithBot ℕ∞)
    · rw [if_pos hx, if_pos (hmem.mpr hx)]
    · rw [if_neg hx, if_neg (fun h => hx (hmem.mp h))]
  · -- the intersection numbers
    have hcoh : AlgebraicGeometry.Scheme.Modules.IsCoherent (X := X)
        (SheafOfModules.unit X.ringCatSheaf) := by
      have hq := AlgebraicGeometry.Scheme.Modules.unit_isQuasicoherent X
      rw [← AlgebraicGeometry.Scheme.Modules.unit_eq_tensorUnit X] at hq
      exact ⟨hq, inferInstance⟩
    have hsupp : topologicalKrullDim
        (AlgebraicGeometry.Scheme.Modules.support (X := X) (SheafOfModules.unit X.ringCatSheaf)) = (d : WithBot ℕ∞) := by
      rw [AlgebraicGeometry.Scheme.Modules.support_unit, ← hkX]
      exact (Homeomorph.Set.univ X).isHomeomorph.topologicalKrullDim_eq
    obtain ⟨P, hP, hPn⟩ := AlgebraicGeometry.exists_snapper_sub_components_totalDegree_lt X hX
      (SheafOfModules.unit X.ringCatSheaf) L d hsupp
    -- finsum over `T` → finite sum over `s`
    have hTeq : {ζ : X | topologicalKrullDim (closure {ζ} : Set X) = (d : WithBot ℕ∞)} = T := by
      ext ζ
      simp only [Set.mem_setOf_eq]
      rw [← AlgebraicGeometry.Intersection.pointClosureDimension_eq_topologicalKrullDim_closure]
      exact Iff.rfl
    have hfs : ∀ g : X → ℚ,
        ∑ᶠ (ζ : X) (_ : topologicalKrullDim (closure {ζ} : Set X) = (d : WithBot ℕ∞)), g ζ
          = ∑ ζ ∈ s, g ζ := fun g =>
      (finsum_mem_congr hTeq fun _ _ => rfl).trans (finsum_mem_eq_finite_toFinset_sum g hTfin)
    have hcast : ∀ S : Finset (Fin d),
        (fun i : Fin d => (((if i ∈ S then (1 : ℤ) else 0) : ℤ) : ℚ))
          = fun i => if i ∈ S then (1 : ℚ) else 0 := by
      intro S
      funext i
      split_ifs <;> simp
    have hχ : ∀ S : Finset (Fin d),
        (AlgebraicGeometry.sheafEulerCharacteristic (k := k) X
          ((List.finRange d).foldl
            (fun (G : X.Modules) (i : Fin d) => G.tensor (L i ^ (if i ∈ S then (1 : ℤ) else 0)))
            (SheafOfModules.unit X.ringCatSheaf)) : ℚ)
        = ∑ ζ ∈ s, ((Module.length (X.presheaf.stalk ζ)
              (AlgebraicGeometry.Scheme.Modules.stalk (X := X) (SheafOfModules.unit X.ringCatSheaf) ζ)).toNat : ℚ) *
              (letI : (AlgebraicGeometry.Scheme.pointClosure ζ).Over
                    (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
                  ⟨AlgebraicGeometry.Scheme.pointClosureι ζ ≫
                    (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
               (AlgebraicGeometry.sheafEulerCharacteristic (k := k)
                  (AlgebraicGeometry.Scheme.pointClosure ζ)
                  ((List.finRange d).foldl
                    (fun (G : (AlgebraicGeometry.Scheme.pointClosure ζ).Modules) (i : Fin d) =>
                      G.tensor ((AlgebraicGeometry.Scheme.Modules.pullback
                        (AlgebraicGeometry.Scheme.pointClosureι ζ)).obj (L i) ^
                          (if i ∈ S then (1 : ℤ) else 0)))
                    (SheafOfModules.unit (AlgebraicGeometry.Scheme.pointClosure ζ).ringCatSheaf)) : ℚ))
          + MvPolynomial.eval (fun i => if i ∈ S then (1 : ℚ) else 0) P := by
      intro S
      have h := hPn (fun i => if i ∈ S then (1 : ℤ) else 0)
      rw [hfs, hcast] at h
      exact sub_eq_iff_eq_add'.mp h
    unfold AlgebraicGeometry.snapperIntersection
    simp_rw [hχ, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    rw [MvPolynomial.sum_neg_one_pow_eval_indicator_eq_zero P hP, add_zero, Finset.sum_comm,
      ← Finset.sum_coe_sort s]
    refine (Fintype.sum_equiv φ _ _ fun j => ?_).symm
    rw [← hξdef j]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [AlgebraicGeometry.length_unit_stalk_toNat_eq X (ξ j) (hTgen (hξT j))]
    ring

end
