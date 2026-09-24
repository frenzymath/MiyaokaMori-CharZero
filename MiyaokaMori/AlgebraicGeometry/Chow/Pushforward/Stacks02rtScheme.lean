import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.Weil.PrincipalDivisor
import MiyaokaMori.RingTheory.OrderOfVanishing.Stacks02mj
import MiyaokaMori.AlgebraicGeometry.Varieties.FunctionField.Stacks02r1
import MiyaokaMori.AlgebraicGeometry.Morphisms.FiniteLocalModel

/-! # Pushforward of a principal divisor is the divisor of the norm (Stacks 02RT, scheme version)

The **scheme version** of Stacks 02RT (integral schemes locally of finite type over a field `k`, neither
separated nor quasi-compact): `X`, `Y` integral of the same dimension `d` (`topologicalKrullDim`),
`p : X → Y` a dominant proper `k`-morphism, `f ∈ R(X)^*`; then `p_*div_X(f) = div_Y(Nm_{R(X)/R(Y)} f)`.

`Stacks02rt.lean` (`properPushforward_principalDivisor`) states 02RT only for `Variety k` (separated, of
finite type); the pushforward formulas of Stacks 02ST and of the pullback of rational sections along
dominant morphisms are stated for integral schemes locally of finite type over a field, so 02RT and the
02R1 it uses (finiteness of the function field extension) are generalized here verbatim: the variety
structure entered the original proof only in two places — `Variety.height_add_coheight` (replaced by
`height_add_coheight_eq_of_locallyOfFiniteType`, Stacks 0A21) and "the transcendence degree of the
coordinate ring of an affine open equals the dimension" (the same argument with `topologicalKrullDim = d`
as hypothesis); separatedness and quasi-compactness were never used. The comparison of coefficients at
codimension-one points (02MJ + the finite local model `exists_finite_local_model`) is a statement about
general schemes and is unchanged.

Source: Stacks 02RT (lemma-proper-pushforward-alteration), 02R1 (lemma-dimension-finite-over).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry

/-- The transcendence degree over `k` of the coordinate ring of a nonempty affine open of an integral
scheme locally of finite type equals its dimension. -/
theorem trdeg_affine_eq_of_locallyOfFiniteType {k : Type u} [Field k] (X : Scheme.{u})
    [X.Over (Spec (CommRingCat.of k))] [IsIntegral X]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))] (d : ℕ) (hd : topologicalKrullDim X = d)
    {U : X.Opens} (hU : IsAffineOpen U) (hne : (U : Set X).Nonempty) :
    letI : Algebra k Γ(X, U) := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
      (X ↘ Spec (CommRingCat.of k)).appLE ⊤ U le_top).hom.toAlgebra
    Algebra.trdeg k Γ(X, U) = (d : Cardinal.{u}) := by
  let Y := X
  let g := Y ↘ Spec (CommRingCat.of k)
  let φ : k →+* Γ(Y, U) := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ g.appLE ⊤ U le_top).hom
  have hφ : φ.FiniteType := by
    have h1 : (g.appLE ⊤ U le_top).hom.FiniteType :=
      g.finiteType_appLE (isAffineOpen_top _) hU _
    have h2 : ((Scheme.ΓSpecIso (CommRingCat.of k)).inv).hom.FiniteType :=
      RingHom.FiniteType.of_surjective _
        (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv.surjective
    exact h1.comp h2
  letI : Algebra k Γ(Y, U) := φ.toAlgebra
  have : Algebra.FiniteType k Γ(Y, U) := hφ
  have : Nonempty U := hne.to_subtype
  show Algebra.trdeg k Γ(Y, U) = (d : Cardinal.{u})
  -- the transcendence degree is a natural number
  obtain ⟨n, hn⟩ : ∃ n : ℕ, Algebra.trdeg k Γ(Y, U) = (n : Cardinal.{u}) := by
    obtain ⟨n, a, ha, hint⟩ := exists_integral_inj_algHom_of_fg k Γ(Y, U)
    let P := MvPolynomial (Fin n) k
    let _ : Algebra P Γ(Y, U) := a.toRingHom.toAlgebra
    have : Algebra.IsIntegral P Γ(Y, U) := ⟨hint⟩
    have : FaithfulSMul P Γ(Y, U) := (faithfulSMul_iff_algebraMap_injective P _).mpr ha
    have : IsScalarTower k P Γ(Y, U) := IsScalarTower.of_algHom a
    have htr0 : Algebra.trdeg P Γ(Y, U) = 0 := trdeg_eq_zero
    have hpoly : Algebra.trdeg k P = (n : Cardinal.{u}) := by simp [P]
    exact ⟨n, by simpa only [htr0, hpoly, add_zero] using (trdeg_add_eq k P (A := Γ(Y, U))).symm⟩
  have hdim : topologicalKrullDim Y = (n : WithBot ℕ∞) := by
    rw [← topologicalKrullDim_opens_eq_of_irreducible (k := k) Y U hne,
      IsHomeomorph.topologicalKrullDim_eq _ hU.isoSpec.hom.homeomorph.isHomeomorph]
    erw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim Γ(Y, U)]
    rw [MiyaokaMori.RingTheory.finiteTypeDomain_ringKrullDim_eq_trdeg k Γ(Y, U), hn]
    simp
  have hnd : (n : WithBot ℕ∞) = (d : WithBot ℕ∞) := hdim.symm.trans hd
  have hnd' : n = d := by exact_mod_cast hnd
  rw [hn, hnd']

theorem residueFieldMap_genericPoint_finite_of_locallyOfFiniteType {k : Type u} [Field k]
    {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))] [Y.Over (Spec (CommRingCat.of k))]
    [IsIntegral X] [IsIntegral Y]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k))]
    (p : X ⟶ Y) [p.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (hp : p.base (genericPoint X) = genericPoint Y)
    (d : ℕ) (hX : topologicalKrullDim X = d) (hY : topologicalKrullDim Y = d) :
    (p.residueFieldMap (genericPoint X)).hom.Finite := by
  open AlgebraicGeometry in
  classical
  let S := Spec (CommRingCat.of k)
  have hcomp : p ≫ (Y ↘ S) = X ↘ S := comp_over p S
  have hlft : LocallyOfFiniteType p := by
    have : LocallyOfFiniteType (p ≫ (Y ↘ S)) := by rw [hcomp]; infer_instance
    exact locallyOfFiniteType_of_comp p (Y ↘ S)
  -- affine opens `U ⊆ Y`, `V ⊆ p⁻¹U`, both nonempty
  obtain ⟨_, ⟨U, hU, rfl⟩, hηU, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (genericPoint Y)) isOpen_univ
  have hηpU : genericPoint X ∈ p ⁻¹ᵁ U := by
    show p.base _ ∈ U
    rw [hp]; exact hηU
  obtain ⟨_, ⟨V, hV, rfl⟩, hηV, e⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    hηpU (p ⁻¹ᵁ U).2
  have e' : V ≤ p ⁻¹ᵁ U := e
  have hinj := appLE_injective_of_genericPoint p hp U V e' hηV
  -- `k`-algebra structures and the tower
  letI algR : Algebra k Γ(Y, U) := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
      (Y ↘ S).appLE ⊤ U le_top).hom.toAlgebra
  letI algC : Algebra k Γ(X, V) := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
      (X ↘ S).appLE ⊤ V le_top).hom.toAlgebra
  letI algRC : Algebra Γ(Y, U) Γ(X, V) := (p.appLE U V e').hom.toAlgebra
  have htower : IsScalarTower k Γ(Y, U) Γ(X, V) := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    have h1 : (Y ↘ S).appLE ⊤ U le_top ≫ p.appLE U V e' =
        (X ↘ S).appLE ⊤ V le_top := by
      rw [Scheme.Hom.appLE_comp_appLE p (Y ↘ S) ⊤ U V le_top e']
      simp only [hcomp]
    simp only [RingHom.algebraMap_toAlgebra]
    rw [← CommRingCat.hom_comp, Category.assoc, h1]
  have hfs : FaithfulSMul Γ(Y, U) Γ(X, V) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  have : Nonempty U := ⟨⟨_, hηU⟩⟩
  have : Nonempty V := ⟨⟨_, hηV⟩⟩
  have hR := trdeg_affine_eq_of_locallyOfFiniteType (k := k) Y d hY hU ⟨_, hηU⟩
  have hC := trdeg_affine_eq_of_locallyOfFiniteType (k := k) X d hX hV ⟨_, hηV⟩
  have halgRC : Algebra.IsAlgebraic Γ(Y, U) Γ(X, V) := by
    rw [← trdeg_eq_zero_iff]
    have h2 := trdeg_add_eq k Γ(Y, U) (A := Γ(X, V))
    rw [hR, hC] at h2
    have hlt : Algebra.trdeg Γ(Y, U) Γ(X, V) < Cardinal.aleph0 := by
      by_contra hge
      rw [not_lt] at hge
      have : Cardinal.aleph0 ≤ (d : Cardinal.{u}) := by
        rw [← h2]; exact hge.trans (self_le_add_left _ _)
      exact absurd this (not_le.mpr (Cardinal.natCast_lt_aleph0))
    obtain ⟨m, hm⟩ := Cardinal.lt_aleph0.mp hlt
    rw [hm] at h2 ⊢
    have : d + m = d := by exact_mod_cast h2
    have : m = 0 := by omega
    simp [this]
  -- `κ(η_X)` is algebraic over `κ(pη_X)`
  let ηX := genericPoint X
  letI algRk := (Y.evaluation U (p ηX) (e' hηV)).hom.toAlgebra
  letI algkl := (p.residueFieldMap ηX).hom.toAlgebra
  letI algCl := (X.evaluation V ηX hηV).hom.toAlgebra
  letI algRl : Algebra Γ(Y, U) (X.residueField ηX) :=
    ((p.residueFieldMap ηX).hom.comp (Y.evaluation U (p ηX) (e' hηV)).hom).toAlgebra
  have t1 : IsScalarTower Γ(Y, U) (Y.residueField (p ηX))
      (X.residueField ηX) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have t2 : IsScalarTower Γ(Y, U) Γ(X, V) (X.residueField ηX) :=
    IsScalarTower.of_algebraMap_eq fun a ↦
      residueFieldMap_evaluation_eq_evaluation_appLE p U V e' _ hηV a
  have halgCl : Algebra.IsAlgebraic Γ(X, V) (X.residueField ηX) := by
    letI := X.presheaf.algebra_section_stalk ⟨ηX, hηV⟩
    have hfrac : IsFractionRing Γ(X, V) X.functionField :=
      functionField_isFractionRing_of_isAffineOpen X V hV
    have halg : Algebra.IsAlgebraic Γ(X, V) (X.presheaf.stalk ηX) :=
      IsLocalization.isAlgebraic _ (nonZeroDivisors Γ(X, V))
    let ψ : X.presheaf.stalk ηX →ₐ[Γ(X, V)] X.residueField ηX :=
      { (X.residue ηX).hom with commutes' := fun _ ↦ rfl }
    refine ⟨fun t ↦ ?_⟩
    obtain ⟨s, rfl⟩ := X.residue_surjective ηX t
    exact (halg.isAlgebraic s).algHom ψ
  have halgRl : Algebra.IsAlgebraic Γ(Y, U) (X.residueField ηX) :=
    Algebra.IsAlgebraic.trans _ Γ(X, V) _
  have halgkl : Algebra.IsAlgebraic (Y.residueField (p ηX))
      (X.residueField ηX) :=
    have hinjRk : ∀ (y : Y) (hy : y ∈ U), y = genericPoint Y →
        Function.Injective (Y.evaluation U y hy) := by
      rintro y hy rfl
      exact evaluation_genericPoint_injective U hy
    ⟨fun t ↦ (halgRl.isAlgebraic t).extendScalars (hinjRk _ (e' hηV) hp)⟩
  have hess : Algebra.EssFiniteType (Y.residueField (p ηX))
      (X.residueField ηX) := by
    have h1 := RingHom.EssFiniteType.residueFieldMap (LocallyOfFiniteType.stalkMap p ηX)
    exact h1
  exact Algebra.finite_of_essFiniteType_of_isAlgebraic (F := Y.residueField (p ηX))
    (E := X.residueField ηX)

open AlgebraicGeometry in
/-- Comparison of the coefficients at a codimension-one point `z` (the core of Stacks 02RT, from 02MJ and
the finite local model). -/
private theorem coeff_eq_of_coheight_eq_one' {k : Type u} [Field k]
    {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))] [Y.Over (Spec (CommRingCat.of k))]
    [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (CommRingCat.of k))] [IsProper p]
    (hp : p.base (genericPoint X) = genericPoint Y)
    (d : ℕ) (hX : topologicalKrullDim X = d) (hY : topologicalKrullDim Y = d) (f : X.functionFieldˣ)
    (z : Y) (hz : Order.coheight z = 1) :
    letI := functionFieldAlgebra p hp
    ∑ᶠ x ∈ p.base ⁻¹' {z}, X.ord (f : X.functionField) x *
        ((AlgebraicCycle.mapCoeff p (Order.height (α := X))
          (Order.height (α := Y)) x : ℕ) : ℤ) =
      Y.ord (Algebra.norm Y.functionField (f : X.functionField)) z := by
  classical
  let algKL : Algebra Y.functionField X.functionField :=
    functionFieldAlgebra p hp
  let algAL : Algebra (Y.presheaf.stalk z) X.functionField :=
    stalkToFunctionFieldAlgebraOfHom p hp z
  have hfinK := residueFieldMap_genericPoint_finite_of_locallyOfFiniteType (k := k) p hp d hX hY
  obtain ⟨B, _, _, _, _, _, _, _, _, e, he⟩ := exists_finite_local_model p hp hfinK z hz
  have : IsScalarTower (Y.presheaf.stalk z) Y.functionField
      X.functionField := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : Ring.KrullDimLE 1 (Y.presheaf.stalk z) := krullDimLE_of_coheight_le hz.le
  have hMS : Finite (MaximalSpectrum B) :=
    Ring.finite_maximalSpectrum_of_finite (A := Y.presheaf.stalk z)
  have hfib : (p.base ⁻¹' {z}).Finite := by
    have hfin' : Finite {x : X // p.base x = z} := Finite.of_equiv _ e
    exact Set.finite_coe_iff.mp hfin'
  have hLfin : Module.Finite Y.functionField X.functionField :=
    Module.Finite.of_isLocalization (Y.presheaf.stalk z) B
      (nonZeroDivisors (Y.presheaf.stalk z))
  set w : X → ℤ := fun x => ((AlgebraicCycle.mapCoeff p
    (Order.height (α := X)) (Order.height (α := Y)) x : ℕ) : ℤ) with hw
  set Fsum : X.functionField → ℤ := fun φ =>
    ∑ᶠ x ∈ p.base ⁻¹' {z}, X.ord φ x * w x with hFsum
  have hFmul : ∀ φ ψ : X.functionField, φ ≠ 0 → ψ ≠ 0 →
      Fsum (φ * ψ) = Fsum φ + Fsum ψ := by
    intro φ ψ hφ hψ
    simp only [hFsum]
    rw [← finsum_mem_add_distrib hfib]
    refine finsum_mem_congr rfl fun x _ => ?_
    rw [Scheme.ord_mul hφ hψ, add_mul]
  have hnorm : ∀ φ : X.functionField, φ ≠ 0 →
      Algebra.norm Y.functionField φ ≠ 0 := fun φ hφ =>
    (Algebra.norm_ne_zero_iff (R := Y.functionField)).mpr hφ
  have hGmul : ∀ φ ψ : X.functionField, φ ≠ 0 → ψ ≠ 0 →
      Y.ord (Algebra.norm Y.functionField (φ * ψ)) z =
        Y.ord (Algebra.norm Y.functionField φ) z +
          Y.ord (Algebra.norm Y.functionField ψ) z := by
    intro φ ψ hφ hψ
    rw [map_mul, Scheme.ord_mul (hnorm φ hφ) (hnorm ψ hψ)]
  -- the case of an integral element: 02MJ
  have hB : ∀ b : B, b ≠ 0 → Fsum (algebraMap B X.functionField b) =
      Y.ord (Algebra.norm Y.functionField
        (algebraMap B X.functionField b)) z := by
    intro b hb
    have hb' : algebraMap B X.functionField b ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective B X.functionField)).mpr hb
    symm
    rw [Scheme.ord_eq_iff hz (hnorm _ hb')]
    change Ring.ordFrac (Y.presheaf.stalk z) _ = _
    rw [Ring.ordFrac_norm_eq_sum_inertiaDeg_mul_ord b hb]
    change WithZero.exp _ = WithZero.exp _
    congr 1
    simp only [hFsum]
    have h1 : ∑ᶠ x ∈ p.base ⁻¹' {z},
        X.ord (algebraMap B X.functionField b) x * w x =
        ∑ᶠ x : {x : X // p.base x = z},
          X.ord (algebraMap B X.functionField b) x.1 * w x.1 :=
      (finsum_subtype_eq_finsum_cond (fun x : X => p.base x = z)).symm
    rw [h1, ← finsum_comp_equiv e]
    refine finsum_congr fun m => ?_
    obtain ⟨hco, hdeg, hord⟩ := he m
    have hheight : Order.height (e m).1 = Order.height (p.base (e m).1) := by
      have h1 := height_add_coheight_eq_of_locallyOfFiniteType (k := k) X d hX (e m).1
      have h2 := height_add_coheight_eq_of_locallyOfFiniteType (k := k) Y d hY (p.base (e m).1)
      rw [(e m).2, hz, ← h1, hco] at h2
      rw [(e m).2]
      exact (ENat.add_left_injective_of_ne_top ENat.one_ne_top h2).symm
    have hwm : w (e m).1 = (Ideal.inertiaDeg'
        (IsLocalRing.maximalIdeal (Y.presheaf.stalk z)) m.asIdeal : ℤ) := by
      simp only [hw]
      unfold AlgebraicCycle.mapCoeff
      rw [if_pos hheight, hdeg]
    rw [hord b hb, hwm, mul_comm]
  -- the general case `f ∈ L^*`: both sides are multiplicative on `L^*` (`hFmul`, `hGmul`) and agree on
  -- `B \ 0` (`hB`), so `Ring.eq_of_mul_of_eq_on_algebraMap` gives the equality
  change Fsum (f : X.functionField) = _
  exact Ring.eq_of_mul_of_eq_on_algebraMap (B := B) (F := Fsum)
    (G := fun φ => Y.ord (Algebra.norm Y.functionField φ) z)
    hFmul hGmul hB f.ne_zero

open AlgebraicGeometry in
/-- **Stacks 02RT (for integral schemes locally of finite type over a field)**: `X`, `Y` integral, locally
of finite type over a field `k`, of the same dimension `d`, `p : X → Y` a dominant proper `k`-morphism,
`f ∈ R(X)^*`; then `p_*div(f) = div(Nm_{R(X)/R(Y)} f)`. -/
theorem properPushforward_principalCycle_of_locallyOfFiniteType {k : Type u} [Field k]
    {X Y : Scheme.{u}} [X.Over (Spec (CommRingCat.of k))] [Y.Over (Spec (CommRingCat.of k))]
    [IsIntegral X] [IsIntegral Y] [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k))] [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k))]
    (p : X ⟶ Y) [p.IsOver (Spec (CommRingCat.of k))] [IsProper p]
    (hp : p.base (genericPoint X) = genericPoint Y)
    (d : ℕ) (hX : topologicalKrullDim X = d) (hY : topologicalKrullDim Y = d) (f : X.functionFieldˣ) :
    letI := functionFieldAlgebra p hp
    AlgebraicGeometry.AlgebraicCycle.properPushforward p (X.principalCycle f)
      = Y.principalCycle (Units.map (Algebra.norm Y.functionField) f) := by
  classical
  letI := functionFieldAlgebra p hp
  ext z
  change ∑ᶠ x ∈ p.base ⁻¹' {z}, X.principalCycle f x *
      ((AlgebraicGeometry.AlgebraicCycle.mapCoeff p (Order.height (α := X))
        (Order.height (α := Y)) x : ℕ) : ℤ) = Y.principalCycle _ z
  simp only [AlgebraicGeometry.Scheme.principalCycle_apply, Units.coe_map]
  by_cases hz : Order.coheight z = 1
  · exact coeff_eq_of_coheight_eq_one' (k := k) p hp d hX hY f z hz
  · rw [AlgebraicGeometry.Scheme.ord_eq_zero_of_coheight_neq_one hz]
    refine finsum_mem_eq_zero_of_forall_eq_zero fun x hx => ?_
    have hxz : p.base x = z := hx
    by_cases hx1 : Order.coheight x = 1
    · have hne : Order.height x ≠ Order.height (p.base x) := by
        intro heq
        apply hz
        have h1 := height_add_coheight_eq_of_locallyOfFiniteType (k := k) X d hX x
        have h2 := height_add_coheight_eq_of_locallyOfFiniteType (k := k) Y d hY z
        rw [hx1, ← h2, heq, hxz] at h1
        have hfinite : Order.height z ≠ ⊤ :=
          ne_top_of_le_ne_top (ENat.natCast_ne_top _) (le_self_add.trans_eq h2)
        exact (ENat.add_right_injective_of_ne_top hfinite h1).symm
      unfold AlgebraicGeometry.AlgebraicCycle.mapCoeff
      rw [if_neg hne]
      simp
    · rw [AlgebraicGeometry.Scheme.ord_eq_zero_of_coheight_neq_one hx1, zero_mul]

end AlgebraicGeometry

end
