import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.PointClosureDimensionTrdeg
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.Stacks0a213

/-! # Dimension equals the transcendence degree of the function field (Stacks 0A21 (6))

Stacks 0A21 (6): for an integral scheme `X` locally of finite type over a field `k` (not
necessarily separated or of finite type), `dim X = trdeg_k κ(ξ)` where `ξ` is the generic point
and `κ(ξ)` the function field. Corollary: for any point `w` of a scheme locally of finite type
over `k`, `height w` (`= dim closure {w}`) equals `trdeg_k κ(w)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Stacks 0A21 (6): the dimension of an integral scheme locally of finite type over `k` is the
transcendence degree of its function field. -/
theorem AlgebraicGeometry.topologicalKrullDim_eq_trdeg_functionField {k : Type u} [Field k]
    (X : AlgebraicGeometry.Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.IsIntegral X] :
    letI : Algebra k X.functionField :=
      ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
        (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)).appTop ≫
        X.presheaf.germ ⊤ (genericPoint X) trivial).hom.toAlgebra
    topologicalKrullDim X = (Cardinal.toENat (Algebra.trdeg k X.functionField) : WithBot ℕ∞) := by
  let algK : Algebra k X.functionField :=
    ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
      (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)).appTop ≫
      X.presheaf.germ ⊤ (genericPoint X) trivial).hom.toAlgebra
  change topologicalKrullDim X = (Cardinal.toENat (Algebra.trdeg k X.functionField) : WithBot ℕ∞)
  have : IrreducibleSpace X := AlgebraicGeometry.irreducibleSpace_of_isIntegral X
  -- take an affine open neighbourhood `U = Spec A` of the generic point; `A = Γ(X, U)` is a finitely
  -- generated `k`-domain with `Frac A` the function field
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (genericPoint X)) isOpen_univ
  have : Nonempty U := ⟨⟨genericPoint X, hxU⟩⟩
  let f := X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)
  let φ : k →+* Γ(X, U) :=
    ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appLE ⊤ U le_top).hom
  have hφ : φ.FiniteType := by
    have h1 : (f.appLE ⊤ U le_top).hom.FiniteType :=
      f.finiteType_appLE (AlgebraicGeometry.isAffineOpen_top _) hU _
    have h2 : ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv).hom.FiniteType :=
      RingHom.FiniteType.of_surjective _
        (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv.surjective
    exact h1.comp h2
  let _ : Algebra k Γ(X, U) := φ.toAlgebra
  have : Algebra.FiniteType k Γ(X, U) := hφ
  have hfrac := AlgebraicGeometry.functionField_isFractionRing_of_isAffineOpen X U hU
  have htower : IsScalarTower k Γ(X, U) X.functionField := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    ext a
    simp only [RingHom.algebraMap_toAlgebra, φ, AlgebraicGeometry.Scheme.Hom.appLE,
      CommRingCat.hom_comp, RingHom.comp_apply]
    exact (congrArg (fun g : Γ(X, ⊤) ⟶ X.functionField =>
      g.hom (((X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)).appTop).hom
        (((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv).hom a)))
      (X.presheaf.germ_res (homOfLE le_top) (genericPoint X) hxU)).symm
  have : FaithfulSMul Γ(X, U) X.functionField :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr (IsFractionRing.injective _ _)
  have : Algebra.IsAlgebraic Γ(X, U) X.functionField :=
    IsLocalization.isAlgebraic _ (nonZeroDivisors Γ(X, U))
  have htr : Algebra.trdeg k X.functionField = Algebra.trdeg k Γ(X, U) := by
    have h0 : Algebra.trdeg Γ(X, U) X.functionField = 0 := trdeg_eq_zero
    rw [← trdeg_add_eq k Γ(X, U) (A := X.functionField), h0, add_zero]
  rw [← AlgebraicGeometry.topologicalKrullDim_opens_eq_of_irreducible (k := k) X U
      ⟨genericPoint X, hxU⟩,
    IsHomeomorph.topologicalKrullDim_eq _ hU.isoSpec.hom.homeomorph.isHomeomorph]
  erw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim Γ(X, U)]
  rw [MiyaokaMori.RingTheory.finiteTypeDomain_ringKrullDim_eq_trdeg k Γ(X, U), htr]

/-- The height of a point of a scheme locally of finite type over `k` is the transcendence degree of
its residue field. -/
theorem AlgebraicGeometry.height_eq_trdeg_residueField {k : Type u} [Field k]
    (X : AlgebraicGeometry.Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.LocallyOfFiniteType (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))] (w : X) :
    letI : Algebra k (X.residueField w) :=
      ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
        (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)).appTop ≫
        X.presheaf.germ ⊤ w trivial ≫ X.residue w).hom.toAlgebra
    ((Order.height w : ℕ∞) : WithBot ℕ∞) =
      (Cardinal.toENat (Algebra.trdeg k (X.residueField w)) : WithBot ℕ∞) := by
  let X' : AlgebraicGeometry.Proj.SchemeOver k :=
    ⟨X, X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)⟩
  have hbase :
      AlgebraicGeometry.Intersection.pointBaseMap
          (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) w =
        (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
          (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)).appTop ≫
          X.presheaf.germ ⊤ w trivial ≫ X.residue w := by
    apply AlgebraicGeometry.Spec.map_injective
    simp only [AlgebraicGeometry.Intersection.pointBaseMap, AlgebraicGeometry.Spec.map_preimage,
      AlgebraicGeometry.Spec.map_comp]
    rw [AlgebraicGeometry.Scheme.fromSpecResidueField]
    simp only [Category.assoc]
    rw [← AlgebraicGeometry.Scheme.fromSpecStalk_toSpecΓ_assoc,
      ← AlgebraicGeometry.Scheme.toSpecΓ_naturality_assoc]
    simp
  have h := MiyaokaMori.PointClosureTrdeg.pointClosureDimension_eq_trdeg X' w
  rw [AlgebraicGeometry.Intersection.pointClosureDimension_eq_height] at h
  dsimp [X'] at h
  rw [hbase] at h
  exact h

end
