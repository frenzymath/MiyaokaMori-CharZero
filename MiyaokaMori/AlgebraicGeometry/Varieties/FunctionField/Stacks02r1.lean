import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.SchemeDimension
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.Stacks0a213
import MiyaokaMori.AlgebraicGeometry.Varieties.FunctionField.DominantAffineAlgebraic
import MiyaokaMori.RingTheory.Dimension.FiniteTypeDomainDimension

/-! # A dominant morphism between varieties of equal dimension has finite function field extension

Stacks 02R1, for varieties: if `X`, `Y` are varieties over `k` of the same dimension and
`p : X → Y` is a dominant `k`-morphism, then the function field extension `R(X)/R(Y)` is finite.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.style.haveILetI false

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open AlgebraicGeometry in
/-- The transcendence degree over `k` of the coordinate ring of a nonempty affine open of a variety
equals the dimension of the variety. -/
private theorem trdeg_affine_eq_dimension {k : Type u} [Field k] (X : Variety k)
    {U : X.toScheme.Opens} (hU : IsAffineOpen U) (hne : (U : Set X.toScheme).Nonempty) :
    letI : Algebra k Γ(X.toScheme, U) := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
      (X.toScheme ↘ Spec (CommRingCat.of k)).appLE ⊤ U le_top).hom.toAlgebra
    Algebra.trdeg k Γ(X.toScheme, U) = (X.toScheme.dimension : Cardinal.{u}) := by
  let Y := X.toScheme
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
  show Algebra.trdeg k Γ(Y, U) = (Y.dimension : Cardinal.{u})
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
  rw [hn]
  congr 1
  unfold Scheme.dimension
  rw [hdim]
  simp

/-- Stacks 02R1: a dominant morphism between varieties of the same dimension induces a finite
extension of function fields. -/
theorem Variety.residueFieldMap_genericPoint_finite_of_dim_eq {k : Type u} [Field k]
    {X Y : Variety k} (p : X.toScheme ⟶ Y.toScheme)
    [p.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (hp : p.base (genericPoint X.toScheme) = genericPoint Y.toScheme)
    (hdim : X.toScheme.dimension = Y.toScheme.dimension) :
    (p.residueFieldMap (genericPoint X.toScheme)).hom.Finite := by
  open AlgebraicGeometry in
  classical
  let S := Spec (CommRingCat.of k)
  have hcomp : p ≫ (Y.toScheme ↘ S) = X.toScheme ↘ S := comp_over p S
  have hlft : LocallyOfFiniteType p := by
    have : LocallyOfFiniteType (p ≫ (Y.toScheme ↘ S)) := by rw [hcomp]; infer_instance
    exact locallyOfFiniteType_of_comp p (Y.toScheme ↘ S)
  -- affine opens `U ⊆ Y` and `V ⊆ p⁻¹U`, both nonempty
  obtain ⟨_, ⟨U, hU, rfl⟩, hηU, -⟩ := Y.toScheme.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (genericPoint Y.toScheme)) isOpen_univ
  have hηpU : genericPoint X.toScheme ∈ p ⁻¹ᵁ U := by
    show p.base _ ∈ U
    rw [hp]; exact hηU
  obtain ⟨_, ⟨V, hV, rfl⟩, hηV, e⟩ := X.toScheme.isBasis_affineOpens.exists_subset_of_mem_open
    hηpU (p ⁻¹ᵁ U).2
  have e' : V ≤ p ⁻¹ᵁ U := e
  have hinj := appLE_injective_of_genericPoint p hp U V e' hηV
  -- the `k`-algebra structures and the tower
  letI algR : Algebra k Γ(Y.toScheme, U) := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
      (Y.toScheme ↘ S).appLE ⊤ U le_top).hom.toAlgebra
  letI algC : Algebra k Γ(X.toScheme, V) := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
      (X.toScheme ↘ S).appLE ⊤ V le_top).hom.toAlgebra
  letI algRC : Algebra Γ(Y.toScheme, U) Γ(X.toScheme, V) := (p.appLE U V e').hom.toAlgebra
  have htower : IsScalarTower k Γ(Y.toScheme, U) Γ(X.toScheme, V) := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    have h1 : (Y.toScheme ↘ S).appLE ⊤ U le_top ≫ p.appLE U V e' =
        (X.toScheme ↘ S).appLE ⊤ V le_top := by
      rw [Scheme.Hom.appLE_comp_appLE p (Y.toScheme ↘ S) ⊤ U V le_top e']
      simp only [hcomp]
    simp only [RingHom.algebraMap_toAlgebra]
    rw [← CommRingCat.hom_comp, Category.assoc, h1]
  have hfs : FaithfulSMul Γ(Y.toScheme, U) Γ(X.toScheme, V) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  have : Nonempty U := ⟨⟨_, hηU⟩⟩
  have : Nonempty V := ⟨⟨_, hηV⟩⟩
  have hR := trdeg_affine_eq_dimension Y hU ⟨_, hηU⟩
  have hC := trdeg_affine_eq_dimension X hV ⟨_, hηV⟩
  have halgRC : Algebra.IsAlgebraic Γ(Y.toScheme, U) Γ(X.toScheme, V) := by
    rw [← trdeg_eq_zero_iff]
    have h2 := trdeg_add_eq k Γ(Y.toScheme, U) (A := Γ(X.toScheme, V))
    rw [hR, hC, hdim] at h2
    have hlt : Algebra.trdeg Γ(Y.toScheme, U) Γ(X.toScheme, V) < Cardinal.aleph0 := by
      by_contra hge
      rw [not_lt] at hge
      have : Cardinal.aleph0 ≤ (Y.toScheme.dimension : Cardinal.{u}) := by
        rw [← h2]; exact hge.trans (self_le_add_left _ _)
      exact absurd this (not_le.mpr (Cardinal.natCast_lt_aleph0))
    obtain ⟨m, hm⟩ := Cardinal.lt_aleph0.mp hlt
    rw [hm] at h2 ⊢
    have : Y.toScheme.dimension + m = Y.toScheme.dimension := by exact_mod_cast h2
    have : m = 0 := by omega
    simp [this]
  -- `κ(η_X)` is algebraic over `κ(p η_X)`
  let ηX := genericPoint X.toScheme
  letI algRk := (Y.toScheme.evaluation U (p ηX) (e' hηV)).hom.toAlgebra
  letI algkl := (p.residueFieldMap ηX).hom.toAlgebra
  letI algCl := (X.toScheme.evaluation V ηX hηV).hom.toAlgebra
  letI algRl : Algebra Γ(Y.toScheme, U) (X.toScheme.residueField ηX) :=
    ((p.residueFieldMap ηX).hom.comp (Y.toScheme.evaluation U (p ηX) (e' hηV)).hom).toAlgebra
  have t1 : IsScalarTower Γ(Y.toScheme, U) (Y.toScheme.residueField (p ηX))
      (X.toScheme.residueField ηX) := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have t2 : IsScalarTower Γ(Y.toScheme, U) Γ(X.toScheme, V) (X.toScheme.residueField ηX) :=
    IsScalarTower.of_algebraMap_eq fun a ↦
      residueFieldMap_evaluation_eq_evaluation_appLE p U V e' _ hηV a
  have halgCl : Algebra.IsAlgebraic Γ(X.toScheme, V) (X.toScheme.residueField ηX) := by
    letI := X.toScheme.presheaf.algebra_section_stalk ⟨ηX, hηV⟩
    have hfrac : IsFractionRing Γ(X.toScheme, V) X.toScheme.functionField :=
      functionField_isFractionRing_of_isAffineOpen X.toScheme V hV
    have halg : Algebra.IsAlgebraic Γ(X.toScheme, V) (X.toScheme.presheaf.stalk ηX) :=
      IsLocalization.isAlgebraic _ (nonZeroDivisors Γ(X.toScheme, V))
    let ψ : X.toScheme.presheaf.stalk ηX →ₐ[Γ(X.toScheme, V)] X.toScheme.residueField ηX :=
      { (X.toScheme.residue ηX).hom with commutes' := fun _ ↦ rfl }
    refine ⟨fun t ↦ ?_⟩
    obtain ⟨s, rfl⟩ := X.toScheme.residue_surjective ηX t
    exact (halg.isAlgebraic s).algHom ψ
  have halgRl : Algebra.IsAlgebraic Γ(Y.toScheme, U) (X.toScheme.residueField ηX) :=
    Algebra.IsAlgebraic.trans _ Γ(X.toScheme, V) _
  have halgkl : Algebra.IsAlgebraic (Y.toScheme.residueField (p ηX))
      (X.toScheme.residueField ηX) :=
    have hinjRk : ∀ (y : Y.toScheme) (hy : y ∈ U), y = genericPoint Y.toScheme →
        Function.Injective (Y.toScheme.evaluation U y hy) := by
      rintro y hy rfl
      exact evaluation_genericPoint_injective U hy
    ⟨fun t ↦ (halgRl.isAlgebraic t).extendScalars (hinjRk _ (e' hηV) hp)⟩
  have hess : Algebra.EssFiniteType (Y.toScheme.residueField (p ηX))
      (X.toScheme.residueField ηX) := by
    have h1 := RingHom.EssFiniteType.residueFieldMap (LocallyOfFiniteType.stalkMap p ηX)
    exact h1
  exact Algebra.finite_of_essFiniteType_of_isAlgebraic (F := Y.toScheme.residueField (p ηX))
    (E := X.toScheme.residueField ηX)

end
