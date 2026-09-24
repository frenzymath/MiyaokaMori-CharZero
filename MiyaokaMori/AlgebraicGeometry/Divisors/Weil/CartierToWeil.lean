import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.TrivialLineBundle
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.VarietyHeightAddCoheight
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierDivisor
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierDivisorLocalData
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.CycleGroup
import MiyaokaMori.AlgebraicGeometry.Divisors.OrderOfVanishing.PrincipalDivisorFiniteness
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietyLocallyNoetherian
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietySchemeAccessors
import MiyaokaMori.AlgebraicGeometry.Divisors.Weil.PrincipalDivisor
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.SchemeDimension
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.VarietyDimension
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.VarietyQcqs
import MiyaokaMori.AlgebraicGeometry.Divisors.Weil.CartierToWeilUniqueHelpers
import MiyaokaMori.AlgebraicGeometry.Divisors.Weil.CartierToWeilGermOrder
import MiyaokaMori.AlgebraicGeometry.Divisors.OrderOfVanishing.StalkUnitOrder

/-! # The Weil cycle of a Cartier divisor

The Weil cycle `[D] ∈ Z_{n-1}(V)` induced by a Cartier divisor `D` on an `n`-dimensional variety `V`: at each
codimension-one point, the order of vanishing of a local equation (Fulton §2.1).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Adapter: explicit local equations `(U, f)` (`IsLocalData`) give a `AlgebraicGeometry.Intersection.CartierLocalData`.
Since `V` is quasi-compact, a finite subcover provides the required local finiteness. The transition
condition (`f_i / f_j` is a unit section of `O(U_i ∩ U_j)` on overlaps) follows from the stalkwise unit
condition (on an integral scheme a rational function lying in every stalk is a section). -/

noncomputable def CartierDivisor.authorLocalData {k : Type u} [Field k] {V : Variety k} {ι : Type u}
    (U : ι → V.toScheme.Opens) (f : ι → (V.toScheme.functionField)ˣ)
    (hUf : CartierDivisor.IsLocalData U f) : AlgebraicGeometry.Intersection.CartierLocalData V.toScheme :=
  have hfin : ∃ s : Finset ι, Set.univ ⊆ ⋃ i ∈ s, (U i : Set V.toScheme) :=
    isCompact_univ.elim_finite_subcover (fun i => (U i : Set V.toScheme)) (fun i => (U i).isOpen)
      (fun x _ => by
        have hx : x ∈ (⨆ i, U i : V.toScheme.Opens) := by rw [hUf.1]; trivial
        simpa [TopologicalSpace.Opens.mem_iSup] using hx)
  let s := Classical.choose hfin
  { index := s
    opens := fun i => U i.1
    cover := by
      refine Set.eq_univ_of_univ_subset ((Classical.choose_spec hfin).trans ?_)
      intro x hx
      simp only [Set.mem_iUnion] at hx ⊢
      obtain ⟨i, hi, hx⟩ := hx
      exact ⟨⟨i, hi⟩, hx⟩
    locallyFinite := locallyFinite_of_finite _
    equation := fun i => (f i.1 : V.toScheme.functionField)
    equation_ne_zero := fun i => (f i.1).ne_zero
    ratio_unit := by
      intro i j hU
      letI : Nonempty (↑(U i.1 ⊓ U j.1) : Type _) := hU
      obtain ⟨t, ht⟩ := AlgebraicGeometry.Scheme.exists_unit_section_of_stalkwise_unit
        (X := V.toScheme) (U := U i.1 ⊓ U j.1)
        ((f i.1 : V.toScheme.functionField) / (f j.1 : V.toScheme.functionField)) (by
          intro x
          obtain ⟨a, ha⟩ := (hUf.2 i.1 j.1 x.1 x.2).1
          have hdiv : ((f i.1 / f j.1 : (V.toScheme.functionField)ˣ) :
              V.toScheme.functionField) =
              (f i.1 : V.toScheme.functionField) /
                (f j.1 : V.toScheme.functionField) := by
            simpa only [div_eq_mul_inv, Units.val_mul, Units.val_inv_eq_inv_val]
          exact ⟨a, ha.trans hdiv⟩)
      exact ⟨(t : Γ(V.toScheme, U i.1 ⊓ U j.1)), t.isUnit, ht⟩ }

/-- The coefficient relation of `[D]` at a point `x`: `n` is the order of vanishing at `x` of the equation, on
some open containing `x`, of some local data of `D`. A property; no local equation is chosen. -/

def CartierDivisor.HasWeilCoefficient {k : Type u} [Field k] {V : Variety k}
    (D : CartierDivisor V) (x : V.toScheme) (n : ℤ) : Prop :=
  ∃ (ι : Type u) (U : ι → V.toScheme.Opens) (f : ι → (V.toScheme.functionField)ˣ),
    CartierDivisor.IsLocalData U f ∧ D = CartierDivisor.ofLocalData U f ∧
    ∃ i, x ∈ U i ∧ V.toScheme.ord (f i : V.toScheme.functionField) x = n

/-- Existence: from the existence of local equations (`cartierDivisor_exists_localData`). -/

theorem CartierDivisor.hasWeilCoefficient_exists {k : Type u} [Field k] {V : Variety k}
    (D : CartierDivisor V) (x : V.toScheme) : ∃ n : ℤ, CartierDivisor.HasWeilCoefficient D x n := by
  obtain ⟨ι, U, f, hUf, hD⟩ := cartierDivisor_exists_localData V D
  have hx : x ∈ (⨆ i, U i : V.toScheme.Opens) := by rw [hUf.1]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  exact ⟨_, ι, U, f, hUf, hD, i, hi, rfl⟩

private abbrev CartierDivisor.I {k : Type u} [Field k] (V : Variety k) :=
  AlgebraicGeometry.Scheme.unitsSheafToRationalFunctionsUnits V.toScheme

private abbrev CartierDivisor.Q {k : Type u} [Field k] (V : Variety k) :=
  TopCat.Sheaf.quotient (CartierDivisor.I V)

private abbrev CartierDivisor.qpi {k : Type u} [Field k] (V : Variety k) :=
  TopCat.Sheaf.quotientπ (CartierDivisor.I V)

private lemma CartierDivisor.units_res {k : Type u} [Field k] {V : Variety k}
    (U W : V.toScheme.Opens) (hWU : W ≤ U)
    [Nonempty U] [Nonempty W]
    (t : V.toScheme.rationalFunctionsUnitsSheaf.val.obj (op U)) :
    V.toScheme.rationalUnitsSectionToFunctionField W
        (V.toScheme.rationalFunctionsUnitsSheaf.val.map (homOfLE hWU).op t) =
      V.toScheme.rationalUnitsSectionToFunctionField U t := by
  apply Units.ext
  change (V.toScheme.rationalSectionToFunctionField W).hom
      ((V.toScheme.rationalFunctionsSheaf.val.map (homOfLE hWU).op).hom t.val) =
    (V.toScheme.rationalSectionToFunctionField U).hom t.val
  have hn := congrArg (fun z => z t.val)
    (V.toScheme.rationalSectionToFunctionField_res U W hWU)
  simpa only [CategoryTheory.comp_apply, ConcreteCategory.comp_apply] using hn

private lemma CartierDivisor.restrict_comp {k : Type u} [Field k] {V : Variety k}
    {U W : V.toScheme.Opens} (hWU : W ≤ U)
    (s : (TopCat.Sheaf.quotient
      (AlgebraicGeometry.Scheme.unitsSheafToRationalFunctionsUnits V.toScheme)).val.obj (op ⊤)) :
    (TopCat.Sheaf.quotient
      (AlgebraicGeometry.Scheme.unitsSheafToRationalFunctionsUnits V.toScheme)).val.map
        (homOfLE hWU).op
        ((TopCat.Sheaf.quotient
          (AlgebraicGeometry.Scheme.unitsSheafToRationalFunctionsUnits V.toScheme)).val.map
          (homOfLE (show U ≤ ⊤ from le_top)).op s) =
      (TopCat.Sheaf.quotient
        (AlgebraicGeometry.Scheme.unitsSheafToRationalFunctionsUnits V.toScheme)).val.map
        (homOfLE (show W ≤ ⊤ from le_top)).op s := by
  let Q := TopCat.Sheaf.quotient
    (AlgebraicGeometry.Scheme.unitsSheafToRationalFunctionsUnits V.toScheme)
  have heq : Q.val.map (homOfLE (show W ≤ ⊤ from le_top)).op =
      Q.val.map (homOfLE (show U ≤ ⊤ from le_top)).op ≫ Q.val.map (homOfLE hWU).op := by
    rw [← Functor.map_comp]
    congr 1
  exact (congrArg (fun q => q.hom s) heq).symm

/-- Uniqueness (well-definedness): two local equations differ near `x` by a unit of `O_{V,x}`, so they have the
same `ord_x`. -/

theorem CartierDivisor.hasWeilCoefficient_unique {k : Type u} [Field k] {V : Variety k}
    (D : CartierDivisor V) (x : V.toScheme) {n n' : ℤ}
    (h : CartierDivisor.HasWeilCoefficient D x n) (h' : CartierDivisor.HasWeilCoefficient D x n') : n = n' := by
  rcases h with ⟨ι, U, f, hUf, hD, i, hxi, hn⟩
  rcases h' with ⟨ι', U', f', hUf', hD', j, hxj, hn'⟩
  obtain ⟨ti, hti, hqi⟩ :=
    CartierToWeilLocalSection.local_section_ofLocalData U f hUf x i hxi
  obtain ⟨tj, htj, hqj⟩ :=
    CartierToWeilLocalSection.local_section_ofLocalData U' f' hUf' x j hxj
  let W : V.toScheme.Opens := U i ⊓ U' j
  have hxW : x ∈ W := ⟨hxi, hxj⟩
  letI : Nonempty (U i) := ⟨⟨x, hxi⟩⟩
  letI : Nonempty (U' j) := ⟨⟨x, hxj⟩⟩
  letI : Nonempty W := ⟨⟨x, hxW⟩⟩
  let hWi : W ≤ U i := inf_le_left
  let hWj : W ≤ U' j := inf_le_right
  let gi : V.toScheme.rationalFunctionsUnitsSheaf.val.obj (op W) :=
    V.toScheme.rationalFunctionsUnitsSheaf.val.map (homOfLE hWi).op ti
  let gj : V.toScheme.rationalFunctionsUnitsSheaf.val.obj (op W) :=
    V.toScheme.rationalFunctionsUnitsSheaf.val.map (homOfLE hWj).op tj
  have hgi : V.toScheme.rationalUnitsSectionToFunctionField W gi = f i := by
    exact (CartierDivisor.units_res (V := V) (U i) W hWi ti).trans hti
  have hgj : V.toScheme.rationalUnitsSectionToFunctionField W gj = f' j := by
    exact (CartierDivisor.units_res (V := V) (U' j) W hWj tj).trans htj
  have hnat_i :
      (CartierDivisor.Q V).val.map (homOfLE hWi).op
          ((CartierDivisor.qpi V).hom.app (op (U i)) ti) =
        (CartierDivisor.qpi V).hom.app (op W) gi := by
    have hn := congrArg (fun z => z ti)
      ((CartierDivisor.qpi V).hom.naturality (homOfLE hWi).op)
    simpa only [gi, CategoryTheory.comp_apply, ConcreteCategory.comp_apply] using hn.symm
  have hnat_j :
      (CartierDivisor.Q V).val.map (homOfLE hWj).op
          ((CartierDivisor.qpi V).hom.app (op (U' j)) tj) =
        (CartierDivisor.qpi V).hom.app (op W) gj := by
    have hn := congrArg (fun z => z tj)
      ((CartierDivisor.qpi V).hom.naturality (homOfLE hWj).op)
    simpa only [gj, CategoryTheory.comp_apply, ConcreteCategory.comp_apply] using hn.symm
  have hglobal : Additive.toMul (CartierDivisor.ofLocalData U f) =
      Additive.toMul (CartierDivisor.ofLocalData U' f') := by
    exact congrArg Additive.toMul (hD.symm.trans hD')
  have hq : (CartierDivisor.qpi V).hom.app (op W) gi =
      (CartierDivisor.qpi V).hom.app (op W) gj := by
    calc
      (CartierDivisor.qpi V).hom.app (op W) gi =
          (CartierDivisor.Q V).val.map (homOfLE hWi).op
            ((CartierDivisor.qpi V).hom.app (op (U i)) ti) := hnat_i.symm
      _ = (CartierDivisor.Q V).val.map (homOfLE hWi).op
          ((CartierDivisor.Q V).val.map (homOfLE (show U i ≤ ⊤ from le_top)).op
            (Additive.toMul (CartierDivisor.ofLocalData U f))) := congrArg _ hqi.symm
      _ = (CartierDivisor.Q V).val.map (homOfLE (show W ≤ ⊤ from le_top)).op
            (Additive.toMul (CartierDivisor.ofLocalData U f)) :=
          CartierDivisor.restrict_comp (V := V) hWi _
      _ = (CartierDivisor.Q V).val.map (homOfLE (show W ≤ ⊤ from le_top)).op
            (Additive.toMul (CartierDivisor.ofLocalData U' f')) := congrArg _ hglobal
      _ = (CartierDivisor.Q V).val.map (homOfLE hWj).op
          ((CartierDivisor.Q V).val.map (homOfLE (show U' j ≤ ⊤ from le_top)).op
            (Additive.toMul (CartierDivisor.ofLocalData U' f'))) :=
          (CartierDivisor.restrict_comp (V := V) hWj _).symm
      _ = (CartierDivisor.Q V).val.map (homOfLE hWj).op
          ((CartierDivisor.qpi V).hom.app (op (U' j)) tj) := congrArg _ hqj
      _ = (CartierDivisor.qpi V).hom.app (op W) gj := hnat_j
  obtain ⟨W', hW'W, hxW', a, ha⟩ :=
    CartierToWeilQuotientUnitRatio.local_unit_ratio_eq (V := V) inferInstance x hxW gi gj hq
  rw [hgi, hgj] at ha
  have hord := AlgebraicGeometry.Divisors.StalkUnitOrder.ord_eq_of_div_eq_algebraMap_unit x
    (f i).ne_zero (f' j).ne_zero a (by
      simpa [div_eq_mul_inv, Units.val_mul, Units.val_inv_eq_inv_val] using ha.symm)
  exact hn.symm.trans (hord.trans hn')

open Classical in
/-- The coefficient of `[D]` at `x` (canonical definition): at points of coheight `1`, the order
`quotientOrd x D` of `D ∈ Γ(V, 𝒦^*/O^*)` at `x` — the value on `⊤` of the sheaf morphism
`𝒦^*/O^* ⟶ skyscraper_x(ℤ)` (`t ↦ ord_x(t|_η)` on stalks, descended through the universal property of the
cokernel, `CartierToWeilGermOrder`); no local equation is chosen and no `Classical.epsilon` or inverse of a
bijection is used. At other points the coefficient is `0` (as for Mathlib's `Scheme.ord` and
`CartierLocalData.coefficient`: the Weil cycle `[D]` has coefficients only at codimension-one points). It
agrees with `Classical.epsilon (HasWeilCoefficient D x)` (`weilCoefficient_eq_epsilon`); the local equation
formula is `weilCoefficient_ofLocalData`. -/
noncomputable def CartierDivisor.weilCoefficient {k : Type u} [Field k] {V : Variety k}
    (D : CartierDivisor V) (x : V.toScheme) : ℤ :=
  if Order.coheight x = 1 then V.toScheme.quotientOrd x (Additive.toMul D) else 0

/-- The local equation formula: `D = ofLocalData U f` and `x ∈ U i` give `weilCoefficient D x = ord_x(f i)`.
Proof: `local_section_ofLocalData` gives `t ∈ 𝒦^*(U i)` with `t|_η = f i` and `D|_{U i} = π(t)`;
`quotientOrd_eq_of_restrict_eq` computes `quotientOrd` as `ord_x(t|_η)`. At coheight `≠ 1` both sides are `0`. -/

theorem CartierDivisor.weilCoefficient_ofLocalData {k : Type u} [Field k] {V : Variety k}
    {ι : Type u} (U : ι → V.toScheme.Opens) (f : ι → (V.toScheme.functionField)ˣ)
    (hUf : CartierDivisor.IsLocalData U f) (i : ι) (x : V.toScheme) (hx : x ∈ U i) :
    CartierDivisor.weilCoefficient (CartierDivisor.ofLocalData U f) x =
      V.toScheme.ord (f i : V.toScheme.functionField) x := by
  by_cases hco : Order.coheight x = 1
  · obtain ⟨t, ht, hq⟩ := CartierToWeilLocalSection.local_section_ofLocalData U f hUf x i hx
    rw [CartierDivisor.weilCoefficient, if_pos hco,
      V.toScheme.quotientOrd_eq_of_restrict_eq x (U i) hx _ t hq, ht]
  · rw [CartierDivisor.weilCoefficient, if_neg hco,
      AlgebraicGeometry.Scheme.ord_eq_zero_of_coheight_neq_one hco]

/-- The coefficient satisfies `HasWeilCoefficient` (take any local data and use `weilCoefficient_ofLocalData`). -/

theorem CartierDivisor.hasWeilCoefficient_weilCoefficient {k : Type u} [Field k] {V : Variety k}
    (D : CartierDivisor V) (x : V.toScheme) :
    CartierDivisor.HasWeilCoefficient D x (CartierDivisor.weilCoefficient D x) := by
  obtain ⟨ι, U, f, hUf, hD⟩ := cartierDivisor_exists_localData V D
  have hx : x ∈ (⨆ i, U i : V.toScheme.Opens) := by rw [hUf.1]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  refine ⟨ι, U, f, hUf, hD, i, hi, ?_⟩
  rw [hD]
  exact (CartierDivisor.weilCoefficient_ofLocalData U f hUf i x hi).symm

/-- The coefficient equals `Classical.epsilon (HasWeilCoefficient D x)`, by uniqueness. -/

theorem CartierDivisor.weilCoefficient_eq_epsilon {k : Type u} [Field k] {V : Variety k}
    (D : CartierDivisor V) (x : V.toScheme) :
    CartierDivisor.weilCoefficient D x =
      if Order.coheight x = 1 then Classical.epsilon (CartierDivisor.HasWeilCoefficient D x) else 0 := by
  by_cases hco : Order.coheight x = 1
  · rw [if_pos hco]
    exact CartierDivisor.hasWeilCoefficient_unique D x
      (CartierDivisor.hasWeilCoefficient_weilCoefficient D x)
      (Classical.epsilon_spec (CartierDivisor.hasWeilCoefficient_exists D x))
  · rw [if_neg hco, CartierDivisor.weilCoefficient, if_neg hco]

/-- `[D] ∈ Z_{dim-1}(V)`: the cycle with coefficient function `weilCoefficient D`. Local finiteness of the
support follows from the existence of local equations and `CartierLocalData.algebraicCycle_support_finite`;
the coefficients are nonzero only at points of coheight `1`, and on a variety `height + coheight = dim`, so
the cycle lies in `Z_{dim-1}`. -/

noncomputable def CartierDivisor.weilCycle {k : Type u} [Field k] (V : Variety k)
    (D : CartierDivisor V) : CycleGroup V (V.toScheme.dimension - 1) :=
  ⟨{ toFun := CartierDivisor.weilCoefficient D
     supportWithinDomain' := Set.subset_univ _
     supportLocallyFiniteWithinDomain' := by
       letI : AlgebraicGeometry.IsNoetherian V.toScheme := {}
       obtain ⟨ι, U, f, hUf, hD⟩ := cartierDivisor_exists_localData V D
       let A := CartierDivisor.authorLocalData U f hUf
       intro x _
       refine ⟨Set.univ, Filter.univ_mem, ?_⟩
       apply (AlgebraicGeometry.Intersection.CartierLocalData.algebraicCycle_support_finite A).subset
       intro y hy
       change A.algebraicCycle y ≠ 0
       let iA := A.indexAt y
       have hyiA : y ∈ A.opens iA := A.indexAt_mem y
       have hcoeff : CartierDivisor.weilCoefficient D y =
           V.toScheme.ord (f iA.1 : V.toScheme.functionField) y := by
         rw [hD]
         exact CartierDivisor.weilCoefficient_ofLocalData U f hUf iA.1 y hyiA
       rw [AlgebraicGeometry.Intersection.CartierLocalData.algebraicCycle_apply_eq_ord_of_mem
         A y iA hyiA]
       exact hcoeff ▸ hy.2 }, fun x hx => by
    have h1 : Order.coheight x = 1 := by
      by_contra h
      exact hx (if_neg h)
    have h2 := Variety.height_add_coheight V x
    rw [h1] at h2
    have hne : Order.height x ≠ ⊤ := fun h => by simp [h] at h2
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hne
    rw [← hn] at h2 ⊢
    have h3 : n + 1 = V.toScheme.dimension := by exact_mod_cast h2
    simp [← h3]⟩

/-- Comparison: for any local data `(U, f)`, the underlying cycle of `[ofLocalData U f]` is
`CartierLocalData.algebraicCycle` of the adapted data `authorLocalData`. -/

theorem CartierDivisor.weilCycle_eq_authorAlgebraicCycle {k : Type u} [Field k] (V : Variety k)
    {ι : Type u} (U : ι → V.toScheme.Opens) (f : ι → (V.toScheme.functionField)ˣ)
    (hUf : CartierDivisor.IsLocalData U f) :
    letI : AlgebraicGeometry.IsNoetherian V.toScheme := {}
    (CartierDivisor.weilCycle V (CartierDivisor.ofLocalData U f) :
        AlgebraicGeometry.AlgebraicCycle V.toScheme ℤ)
      = (CartierDivisor.authorLocalData U f hUf).algebraicCycle := by
  letI : AlgebraicGeometry.IsNoetherian V.toScheme := {}
  apply Function.locallyFinsuppWithin.ext
  intro x
  let A := CartierDivisor.authorLocalData U f hUf
  let iA := A.indexAt x
  have hxiA : x ∈ A.opens iA := A.indexAt_mem x
  have hxi : x ∈ U iA.1 := hxiA
  rw [AlgebraicGeometry.Intersection.CartierLocalData.algebraicCycle_apply_eq_ord_of_mem
    A x iA hxiA]
  exact CartierDivisor.weilCoefficient_ofLocalData U f hUf iA.1 x hxi

/-- The local equation formula: `D = ofLocalData U f` and `z ∈ U i` give coefficient `ord_z(f i)` of `[D]` at `z`. -/

theorem CartierDivisor.weilCycle_ofLocalData {k : Type u} [Field k] (V : Variety k)
    {ι : Type u} (U : ι → V.toScheme.Opens) (f : ι → (V.toScheme.functionField)ˣ)
    (hUf : CartierDivisor.IsLocalData U f)
    (i : ι) (z : V.toScheme) (hz : z ∈ U i) :
    (CartierDivisor.weilCycle V (CartierDivisor.ofLocalData U f) :
        AlgebraicGeometry.AlgebraicCycle V.toScheme ℤ) z
      = V.toScheme.ord (f i : V.toScheme.functionField) z := by
  exact CartierDivisor.weilCoefficient_ofLocalData U f hUf i z hz

private lemma CartierDivisor.isLocalData_mul {k : Type u} [Field k] {V : Variety k}
    {ι ι' : Type u} (U : ι → V.toScheme.Opens)
    (f : ι → (V.toScheme.functionField)ˣ)
    (U' : ι' → V.toScheme.Opens)
    (g : ι' → (V.toScheme.functionField)ˣ)
    (hUf : CartierDivisor.IsLocalData U f)
    (hUg : CartierDivisor.IsLocalData U' g) :
    CartierDivisor.IsLocalData
      (fun p : ι × ι' => U p.1 ⊓ U' p.2)
      (fun p : ι × ι' => f p.1 * g p.2) := by
  constructor
  · apply le_antisymm le_top
    intro x _
    have hxU : x ∈ (⨆ i, U i : V.toScheme.Opens) := by rw [hUf.1]; trivial
    have hxU' : x ∈ (⨆ j, U' j : V.toScheme.Opens) := by rw [hUg.1]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hxU
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.mp hxU'
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨(i, j), ⟨hi, hj⟩⟩
  · intro p q x hx
    constructor
    · obtain ⟨a, ha⟩ := (hUf.2 p.1 q.1 x ⟨hx.1.1, hx.2.1⟩).1
      obtain ⟨b, hb⟩ := (hUg.2 p.2 q.2 x ⟨hx.1.2, hx.2.2⟩).1
      refine ⟨a * b, ?_⟩
      change algebraMap (V.toScheme.presheaf.stalk x) V.toScheme.functionField
          (a : V.toScheme.presheaf.stalk x) = _ at ha
      change algebraMap (V.toScheme.presheaf.stalk x) V.toScheme.functionField
          (b : V.toScheme.presheaf.stalk x) = _ at hb
      change algebraMap (V.toScheme.presheaf.stalk x) V.toScheme.functionField
          ((a : V.toScheme.presheaf.stalk x) * (b : V.toScheme.presheaf.stalk x)) = _
      rw [map_mul, ha, hb]
      simp only [Units.val_mul, div_eq_mul_inv]
      rw [mul_inv_rev]
      simp only [Units.val_mul]
      ring
    · obtain ⟨a, ha⟩ := (hUf.2 q.1 p.1 x ⟨hx.2.1, hx.1.1⟩).1
      obtain ⟨b, hb⟩ := (hUg.2 q.2 p.2 x ⟨hx.2.2, hx.1.2⟩).1
      refine ⟨a * b, ?_⟩
      change algebraMap (V.toScheme.presheaf.stalk x) V.toScheme.functionField
          (a : V.toScheme.presheaf.stalk x) = _ at ha
      change algebraMap (V.toScheme.presheaf.stalk x) V.toScheme.functionField
          (b : V.toScheme.presheaf.stalk x) = _ at hb
      change algebraMap (V.toScheme.presheaf.stalk x) V.toScheme.functionField
          ((a : V.toScheme.presheaf.stalk x) * (b : V.toScheme.presheaf.stalk x)) = _
      rw [map_mul, ha, hb]
      simp only [Units.val_mul, div_eq_mul_inv]
      rw [mul_inv_rev]
      simp only [Units.val_mul]
      ring

private theorem CartierDivisor.ofLocalData_mul {k : Type u} [Field k] {V : Variety k}
    {ι ι' : Type u} (U : ι → V.toScheme.Opens)
    (f : ι → (V.toScheme.functionField)ˣ)
    (U' : ι' → V.toScheme.Opens)
    (g : ι' → (V.toScheme.functionField)ˣ)
    (hUf : CartierDivisor.IsLocalData U f)
    (hUg : CartierDivisor.IsLocalData U' g) :
    CartierDivisor.ofLocalData
        (fun p : ι × ι' => U p.1 ⊓ U' p.2)
        (fun p : ι × ι' => f p.1 * g p.2) =
      CartierDivisor.ofLocalData U f + CartierDivisor.ofLocalData U' g := by
  classical
  let W : ι × ι' → V.toScheme.Opens := fun p => U p.1 ⊓ U' p.2
  let h : ι × ι' → (V.toScheme.functionField)ˣ := fun p => f p.1 * g p.2
  have hWh : CartierDivisor.IsLocalData W h :=
    CartierDivisor.isLocalData_mul U f U' g hUf hUg
  change Additive.toMul (CartierDivisor.ofLocalData W h) =
    Additive.toMul (CartierDivisor.ofLocalData U f) *
      Additive.toMul (CartierDivisor.ofLocalData U' g)
  apply (CartierDivisor.Q V).eq_of_locally_eq' W ⊤
    (fun p => homOfLE (show W p ≤ ⊤ from le_top))
  · rw [hWh.1]
  · intro p
    by_cases hWp : Nonempty (W p)
    · let x := Classical.choice hWp
      have hxW : x.1 ∈ W p := x.2
      let hWi : W p ≤ U p.1 := inf_le_left
      let hWj : W p ≤ U' p.2 := inf_le_right
      letI : Nonempty (W p) := hWp
      letI : Nonempty (U p.1) := ⟨⟨x.1, hWi hxW⟩⟩
      letI : Nonempty (U' p.2) := ⟨⟨x.1, hWj hxW⟩⟩
      obtain ⟨tp, htp, hqp⟩ :=
        CartierToWeilLocalSection.local_section_ofLocalData W h hWh x.1 p hxW
      obtain ⟨ti, hti, hqi⟩ :=
        CartierToWeilLocalSection.local_section_ofLocalData U f hUf x.1 p.1 (hWi hxW)
      obtain ⟨tj, htj, hqj⟩ :=
        CartierToWeilLocalSection.local_section_ofLocalData U' g hUg x.1 p.2 (hWj hxW)
      let ri : V.toScheme.rationalFunctionsUnitsSheaf.val.obj (op (W p)) :=
        V.toScheme.rationalFunctionsUnitsSheaf.val.map (homOfLE hWi).op ti
      let rj : V.toScheme.rationalFunctionsUnitsSheaf.val.obj (op (W p)) :=
        V.toScheme.rationalFunctionsUnitsSheaf.val.map (homOfLE hWj).op tj
      have hri : V.toScheme.rationalUnitsSectionToFunctionField (W p) ri = f p.1 := by
        exact (CartierDivisor.units_res (V := V) (U p.1) (W p) hWi ti).trans hti
      have hrj : V.toScheme.rationalUnitsSectionToFunctionField (W p) rj = g p.2 := by
        exact (CartierDivisor.units_res (V := V) (U' p.2) (W p) hWj tj).trans htj
      have hsec : tp = ri * rj := by
        have hinj : Function.Injective
            (V.toScheme.rationalUnitsSectionToFunctionField (W p)) := by
          intro a b hab
          apply Units.ext
          have hv := congrArg Units.val hab
          unfold AlgebraicGeometry.Scheme.rationalUnitsSectionToFunctionField at hv
          change (V.toScheme.rationalSectionToFunctionField (W p)).hom a.val =
            (V.toScheme.rationalSectionToFunctionField (W p)).hom b.val at hv
          exact (AlgebraicGeometry.Scheme.rationalSectionToFunctionField_bijective
            V.toScheme (W p)).1 hv
        apply hinj
        calc
          V.toScheme.rationalUnitsSectionToFunctionField (W p) tp = h p := htp
          _ = f p.1 * g p.2 := rfl
          _ = V.toScheme.rationalUnitsSectionToFunctionField (W p) ri *
              V.toScheme.rationalUnitsSectionToFunctionField (W p) rj := by rw [hri, hrj]
          _ = V.toScheme.rationalUnitsSectionToFunctionField (W p) (ri * rj) :=
            (map_mul _ _ _).symm
      have hnat_i :
          (CartierDivisor.Q V).val.map (homOfLE hWi).op
              ((CartierDivisor.qpi V).hom.app (op (U p.1)) ti) =
            (CartierDivisor.qpi V).hom.app (op (W p)) ri := by
        have hn := congrArg (fun z => z ti)
          ((CartierDivisor.qpi V).hom.naturality (homOfLE hWi).op)
        simpa only [ri, CategoryTheory.comp_apply, ConcreteCategory.comp_apply] using hn.symm
      have hnat_j :
          (CartierDivisor.Q V).val.map (homOfLE hWj).op
              ((CartierDivisor.qpi V).hom.app (op (U' p.2)) tj) =
            (CartierDivisor.qpi V).hom.app (op (W p)) rj := by
        have hn := congrArg (fun z => z tj)
          ((CartierDivisor.qpi V).hom.naturality (homOfLE hWj).op)
        simpa only [rj, CategoryTheory.comp_apply, ConcreteCategory.comp_apply] using hn.symm
      have hres_i :
          (CartierDivisor.Q V).val.map (homOfLE (show W p ≤ ⊤ from le_top)).op
              (Additive.toMul (CartierDivisor.ofLocalData U f)) =
            (CartierDivisor.qpi V).hom.app (op (W p)) ri := by
        calc
          _ = (CartierDivisor.Q V).val.map (homOfLE hWi).op
                ((CartierDivisor.Q V).val.map
                  (homOfLE (show U p.1 ≤ ⊤ from le_top)).op
                  (Additive.toMul (CartierDivisor.ofLocalData U f))) :=
              (CartierDivisor.restrict_comp (V := V) hWi _).symm
          _ = (CartierDivisor.Q V).val.map (homOfLE hWi).op
                ((CartierDivisor.qpi V).hom.app (op (U p.1)) ti) := congrArg _ hqi
          _ = _ := hnat_i
      have hres_j :
          (CartierDivisor.Q V).val.map (homOfLE (show W p ≤ ⊤ from le_top)).op
              (Additive.toMul (CartierDivisor.ofLocalData U' g)) =
            (CartierDivisor.qpi V).hom.app (op (W p)) rj := by
        calc
          _ = (CartierDivisor.Q V).val.map (homOfLE hWj).op
                ((CartierDivisor.Q V).val.map
                  (homOfLE (show U' p.2 ≤ ⊤ from le_top)).op
                  (Additive.toMul (CartierDivisor.ofLocalData U' g))) :=
              (CartierDivisor.restrict_comp (V := V) hWj _).symm
          _ = (CartierDivisor.Q V).val.map (homOfLE hWj).op
                ((CartierDivisor.qpi V).hom.app (op (U' p.2)) tj) := congrArg _ hqj
          _ = _ := hnat_j
      calc
        (CartierDivisor.Q V).val.map (homOfLE (show W p ≤ ⊤ from le_top)).op
            (Additive.toMul (CartierDivisor.ofLocalData W h)) =
          (CartierDivisor.qpi V).hom.app (op (W p)) tp := hqp
        _ = (CartierDivisor.qpi V).hom.app (op (W p)) (ri * rj) := congrArg _ hsec
        _ = (CartierDivisor.qpi V).hom.app (op (W p)) ri *
            (CartierDivisor.qpi V).hom.app (op (W p)) rj := map_mul _ _ _
        _ = (CartierDivisor.Q V).val.map (homOfLE (show W p ≤ ⊤ from le_top)).op
              (Additive.toMul (CartierDivisor.ofLocalData U f)) *
            (CartierDivisor.Q V).val.map (homOfLE (show W p ≤ ⊤ from le_top)).op
              (Additive.toMul (CartierDivisor.ofLocalData U' g)) := by rw [hres_i, hres_j]
        _ = (CartierDivisor.Q V).val.map (homOfLE (show W p ≤ ⊤ from le_top)).op
              (Additive.toMul (CartierDivisor.ofLocalData U f) *
                Additive.toMul (CartierDivisor.ofLocalData U' g)) := (map_mul _ _ _).symm
    · have hbot : W p = ⊥ := by
        apply le_antisymm
        · intro x hx
          exact (hWp ⟨⟨x, hx⟩⟩).elim
        · exact bot_le
      have hterm := (CartierDivisor.Q V).isTerminalOfEqEmpty hbot
      have hzero : IsZero ((CartierDivisor.Q V).obj.obj (op (W p))) :=
        IsZero.of_iso (isZero_zero CommGrpCat.{u})
          (hterm.uniqueUpToIso (isZero_zero CommGrpCat.{u}).isTerminal)
      haveI : Subsingleton ((CartierDivisor.Q V).val.obj (op (W p))) :=
        CommGrpCat.subsingleton_of_isZero hzero
      exact Subsingleton.elim _ _

theorem CartierDivisor.weilCycle_add {k : Type u} [Field k] (V : Variety k) (D E : CartierDivisor V) :
    CartierDivisor.weilCycle V (D + E) = CartierDivisor.weilCycle V D + CartierDivisor.weilCycle V E := by
  obtain ⟨ι, U, f, hUf, hD⟩ := cartierDivisor_exists_localData V D
  obtain ⟨ι', U', g, hUg, hE⟩ := cartierDivisor_exists_localData V E
  let W : ι × ι' → V.toScheme.Opens := fun p => U p.1 ⊓ U' p.2
  let h : ι × ι' → (V.toScheme.functionField)ˣ := fun p => f p.1 * g p.2
  have hWh : CartierDivisor.IsLocalData W h :=
    CartierDivisor.isLocalData_mul U f U' g hUf hUg
  have hDE : D + E = CartierDivisor.ofLocalData W h := by
    calc
      D + E = CartierDivisor.ofLocalData U f + CartierDivisor.ofLocalData U' g :=
        congrArg₂ (fun A B : CartierDivisor V => A + B) hD hE
      _ = CartierDivisor.ofLocalData W h :=
        (CartierDivisor.ofLocalData_mul U f U' g hUf hUg).symm
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro x
  have hxW : x ∈ (⨆ p, W p : V.toScheme.Opens) := by rw [hWh.1]; trivial
  obtain ⟨p, hxp⟩ := TopologicalSpace.Opens.mem_iSup.mp hxW
  have hsum := CartierDivisor.weilCycle_ofLocalData V W h hWh p x hxp
  have hleft := CartierDivisor.weilCycle_ofLocalData V U f hUf p.1 x hxp.1
  have hright := CartierDivisor.weilCycle_ofLocalData V U' g hUg p.2 x hxp.2
  change CartierDivisor.weilCoefficient (CartierDivisor.ofLocalData W h) x =
    V.toScheme.ord (h p : V.toScheme.functionField) x at hsum
  change CartierDivisor.weilCoefficient (CartierDivisor.ofLocalData U f) x =
    V.toScheme.ord (f p.1 : V.toScheme.functionField) x at hleft
  change CartierDivisor.weilCoefficient (CartierDivisor.ofLocalData U' g) x =
    V.toScheme.ord (g p.2 : V.toScheme.functionField) x at hright
  have hord : V.toScheme.ord (h p : V.toScheme.functionField) x =
      V.toScheme.ord (f p.1 : V.toScheme.functionField) x +
        V.toScheme.ord (g p.2 : V.toScheme.functionField) x := by
    simpa only [h, Units.val_mul] using
      V.toScheme.ord_mul (f p.1).ne_zero (g p.2).ne_zero (x := x)
  change CartierDivisor.weilCoefficient (D + E) x =
    CartierDivisor.weilCoefficient D x + CartierDivisor.weilCoefficient E x
  rw [hDE, hD, hE, hsum, hleft, hright]
  exact hord

end
