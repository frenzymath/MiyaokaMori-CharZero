import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.Stacks0a213
import MiyaokaMori.RingTheory.Dimension.FiniteTypeDomainDimension

/-! # Finiteness of the dimension of a variety

The dimension of a variety over `k` is finite and equals the transcendence degree of its function
field over `k`: `topologicalKrullDim X = trdeg k K(X) < ⊤`, so it can be taken to be a natural
number (Stacks 0A21 (4)).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- The transcendence degree of a finitely generated domain over a field is a natural number
(Noether normalization). -/
private theorem exists_trdeg_eq_nat (k A : Type u) [Field k] [CommRing A] [IsDomain A]
    [Algebra k A] [Algebra.FiniteType k A] :
    ∃ n : ℕ, Algebra.trdeg k A = (n : Cardinal.{u}) := by
  obtain ⟨n, g, hg, hint⟩ := exists_integral_inj_algHom_of_fg k A
  let P := MvPolynomial (Fin n) k
  let _ : Algebra P A := g.toRingHom.toAlgebra
  have : Algebra.IsIntegral P A := ⟨hint⟩
  have : FaithfulSMul P A := (faithfulSMul_iff_algebraMap_injective P A).mpr hg
  have : IsScalarTower k P A := IsScalarTower.of_algHom g
  have htr0 : Algebra.trdeg P A = 0 := trdeg_eq_zero
  have hpoly : Algebra.trdeg k P = (n : Cardinal.{u}) := by simp [P]
  exact ⟨n, by simpa only [htr0, hpoly, add_zero] using (trdeg_add_eq k P (A := A)).symm⟩

/-- The Krull dimension of a variety equals the transcendence degree of its function field. -/
theorem Variety.topologicalKrullDim_eq_trdeg {k : Type u} [Field k] (X : Variety k) :
    letI : Algebra k X.carrier.functionField :=
      ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
        (X.carrier ↘ AlgebraicGeometry.Spec (CommRingCat.of k)).appTop ≫
        X.carrier.presheaf.germ ⊤ (genericPoint X.carrier) (by simp)).hom.toAlgebra
    topologicalKrullDim X.carrier.carrier =
      ((Algebra.trdeg k X.carrier.functionField).toNat : WithBot ℕ∞) ∧
    topologicalKrullDim X.carrier.carrier ≠ ⊤ := by
  let Y := X.carrier
  let algK : Algebra k Y.functionField :=
    ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
      (Y ↘ AlgebraicGeometry.Spec (CommRingCat.of k)).appTop ≫
      Y.presheaf.germ ⊤ (genericPoint Y) (by simp)).hom.toAlgebra
  suffices key : topologicalKrullDim Y =
      ((Algebra.trdeg k Y.functionField).toNat : WithBot ℕ∞) ∧ topologicalKrullDim Y ≠ ⊤ from key
  -- take an affine open neighbourhood `U` of the generic point
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (genericPoint Y)) isOpen_univ
  have : Nonempty U := ⟨⟨genericPoint Y, hxU⟩⟩
  let f := Y ↘ AlgebraicGeometry.Spec (CommRingCat.of k)
  let φ : k →+* Γ(Y, U) :=
    ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appLE ⊤ U le_top).hom
  have hφ : φ.FiniteType := by
    have h1 : (f.appLE ⊤ U le_top).hom.FiniteType :=
      f.finiteType_appLE (AlgebraicGeometry.isAffineOpen_top _) hU _
    have h2 : ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv).hom.FiniteType :=
      RingHom.FiniteType.of_surjective _
        (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv.surjective
    exact h1.comp h2
  let _ : Algebra k Γ(Y, U) := φ.toAlgebra
  have : Algebra.FiniteType k Γ(Y, U) := hφ
  have hfrac := AlgebraicGeometry.functionField_isFractionRing_of_isAffineOpen Y U hU
  have htower : IsScalarTower k Γ(Y, U) Y.functionField := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    ext a
    simp only [RingHom.algebraMap_toAlgebra, φ, AlgebraicGeometry.Scheme.Hom.appLE,
      CommRingCat.hom_comp, RingHom.comp_apply]
    exact (congrArg (fun g : Γ(Y, ⊤) ⟶ Y.functionField => g.hom (((Y ↘ AlgebraicGeometry.Spec (CommRingCat.of k)).appTop).hom
      (((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv).hom a)))
      (Y.presheaf.germ_res (homOfLE le_top) (genericPoint Y) hxU)).symm
  have : FaithfulSMul Γ(Y, U) Y.functionField :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (IsFractionRing.injective _ _)
  have : Algebra.IsAlgebraic Γ(Y, U) Y.functionField :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors Γ(Y, U))
  have htr : Algebra.trdeg k Y.functionField = Algebra.trdeg k Γ(Y, U) := by
    have h0 : Algebra.trdeg Γ(Y, U) Y.functionField = 0 := trdeg_eq_zero
    rw [← trdeg_add_eq k Γ(Y, U) (A := Y.functionField), h0, add_zero]
  obtain ⟨n, hn⟩ := exists_trdeg_eq_nat k Γ(Y, U)
  have hdim : topologicalKrullDim Y = (n : WithBot ℕ∞) := by
    rw [← AlgebraicGeometry.topologicalKrullDim_opens_eq_of_irreducible (k := k) Y U
        ⟨genericPoint Y, hxU⟩,
      IsHomeomorph.topologicalKrullDim_eq _ hU.isoSpec.hom.homeomorph.isHomeomorph]
    erw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim Γ(Y, U)]
    rw [MiyaokaMori.RingTheory.finiteTypeDomain_ringKrullDim_eq_trdeg k Γ(Y, U), hn]
    simp
  refine ⟨?_, ?_⟩
  · rw [hdim, htr, hn]
    simp
  · rw [hdim]
    intro h
    exact absurd (WithBot.coe_injective h) (ENat.natCast_ne_top n)
end
