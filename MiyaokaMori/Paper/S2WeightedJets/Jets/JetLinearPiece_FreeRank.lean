import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetLinearPiece_Defs
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetLinearPiece_Generation
import MiyaokaMori.Paper.S2WeightedJets.Charts.JetGradedAlgebraLocalWeightedChart
import MiyaokaMori.Paper.S2WeightedJets.Charts.JetWeightPartMonomialFrame
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.DualSectionsBasisOfTrivialization
import MiyaokaMori.Paper.S2WeightedJets.Cone.ConeTangentBundleDualIsoPullbackOmega
import MiyaokaMori.Paper.S2WeightedJets.Charts.EtaleChartCotangentSpaceSections
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.QuasicoherentAffineLocal

/-! # The linear piece of the jet algebra: `Γ(U, L_{q+1})` and `Γ(U, sec^*Ω)` are free of rank `n+1`, and the
coefficient morphism is injective (Orzech)

Bijectivity of the coefficient morphism, used in `DeformedJetAlgebraFiberAtZero_LinearPieceDual`.
Notation as in `JetLinearPiece_Defs`; `U ⊆ C` affine with `E|_U = (sec^*T_{Z/C})|_U` trivial of rank `n+1`, `sec` landing
in an open `Zx` smooth of relative dimension `n+1` over `C`.

* **Pure algebra** (`MvPolynomial.exists_basis_of_weightedHomogeneous_quotient`): for weights `w : σ → ℕ` with `w s ≥ 1`, a
  weight `j ≥ 1`, and a surjective linear map `φ : P_j → N` from the weight-`j` homogeneous polynomials whose kernel is
  `(P_+)² ∩ P_j = span (reesMonomials w 2 j)` (`irrPow_weightedHomogeneousSubmodule_eq_span`), `N` has a basis indexed by
  the variables of weight `j`, namely the `φ(X_s)`. Proof: every weight-`j` polynomial is a combination of the weight-`j`
  variables plus a combination of monomials of degree `≥ 2` (`as_sum`; a weight-`j` exponent of degree `≤ 1` is a single
  variable of weight `j` since `j ≥ 1`), and an element of `span (reesMonomials w 2 j)` has zero coefficient at every
  degree-`1` exponent, so the `φ(X_s)` are independent.
* **`Γ(U, L_{q+1})` is free on the `n+1` variables `x_{a,q}` of weight `q+1`**
  (`jetLinearPiece.exists_basis_linearPiece_sections`): the chart `e : Γ(U, S) ≃+* Γ(C,U)[x_{a,q'}]`
  (`jetGradedAlgebra_localWeightedChart_of_smooth`, graded and unit-compatible) gives `Γ(U, S_{q+1}) ≃ₗ P_{q+1}`
  (`pieceLinearEquivOfChart`); `Γ(U, π_L) : Γ(U, S_{q+1}) → Γ(U, L)` is surjective (`cokernel_π_app_surjective`) with kernel the
  image of `Γ(U, I^{(2)}_{q+1})` (exactness of `Γ(U, -)` on quasi-coherent modules over affine `U`, `gammaAffine_exact_iff`),
  which corresponds under the chart to `(P_+)² ∩ P_{q+1}` (`irrelevantPow_app_range_iff` + `ReesAlgebra.map_mem_irrPow` for
  `e`, `e⁻¹`); apply the algebra lemma. The variables of weight `q+1` are the `x_{a,q}`, `a ∈ Fin (n+1)`
  (`jetLinearPiece.linearIndexEquiv`).
* **`Γ(U, sec^*Ω_{Z/C})` is free of rank `n+1`** (`jetLinearPiece.exists_basis_omega_sections`): `E^∨ ≅ sec^*Ω_{Z/C}` on the
  smooth locus (`dual_coneTangentBundle_iso_pullback_omega`) and the trivialization of `E|_U` gives a basis of `Γ(U, E^∨)`
  (`exists_basis_dual_sections_of_pullback_iso_free`).
* **Injectivity (Orzech)** (`jetLinearPiece.coefficientHom_app_injective`): with `θ.app U` surjective
  (`coefficientHom_app_surjective`) and both sides free of rank `n+1`, `θ.app U` followed by an isomorphism `Γ(U, L) ≃ Γ(U, Ω')`
  (`Module.Basis.equiv`) is a surjective endomorphism of the finitely generated module `Γ(U, Ω')`, hence injective
  (`OrzechProperty.injective_of_surjective_endomorphism`); so `θ.app U` is injective.
* `jetLinearPiece.coefficientHom_app_bijective` assembles the bijectivity statement.

Source: §2 of the paper (eq. (2.5), eq. (2.7)); Stacks 01XB; Orzech's theorem.
Edge cases: `U = ⊥` (zero ring: every family is a basis of the zero module, Orzech is trivial); `n = 0` (rank 1); `q = 0`
(`I^{(2)}_1 = 0`, the weight-1 monomials are exactly the `x_{a,0}`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-! ## Pure algebra: the quotient of the weight-`j` polynomials by the decomposables is free on the weight-`j` variables -/

namespace MvPolynomial

variable {σ : Type*} {R : Type*} [CommRing R]

/-- An exponent of degree `≤ 1` and weight `j ≥ 1` is a single variable of weight `j`. -/
theorem exists_eq_single_of_degree_le_one (w : σ → ℕ) {j : ℕ} (hj : 0 < j) (α : σ →₀ ℕ)
    (hα : Finsupp.weight w α = j) (hdeg : α.degree ≤ 1) :
    ∃ s : σ, w s = j ∧ α = Finsupp.single s 1 := by
  classical
  have hdeg1 : α.degree = 1 := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hdeg with h0 | h1
    · exfalso
      rw [Finsupp.degree_eq_zero_iff] at h0
      rw [h0, map_zero] at hα
      omega
    · exact h1
  obtain ⟨s, rfl⟩ := (Finsupp.sum_eq_one_iff α).mp hdeg1
  refine ⟨s, ?_, rfl⟩
  rw [Finsupp.weight_single, one_smul] at hα
  exact hα

/-- An element of `span (reesMonomials w 2 j)` (monomials of weight `j` and degree `≥ 2`) has zero coefficient at every
degree-one exponent `single s 1`. -/
theorem coeff_single_one_eq_zero_of_mem_span_reesMonomials (w : σ → ℕ) (j : ℕ) {p : MvPolynomial σ R}
    (hp : p ∈ Submodule.span R (reesMonomials (B := R) w 2 j)) (s : σ) :
    coeff (Finsupp.single s 1) p = 0 := by
  classical
  have hle : Submodule.span R (reesMonomials (B := R) w 2 j) ≤
      LinearMap.ker (lcoeff R (Finsupp.single s 1)) := by
    rw [Submodule.span_le]
    rintro _ ⟨α, _, hdeg, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, lcoeff_apply, coeff_monomial, if_neg]
    intro h
    rw [h, Finsupp.degree_single] at hdeg
    omega
  exact hle hp

theorem span_reesMonomials_le_weightedHomogeneousSubmodule (w : σ → ℕ) (p j : ℕ) :
    Submodule.span R (reesMonomials (B := R) w p j) ≤ weightedHomogeneousSubmodule R w j := by
  rw [Submodule.span_le]
  rintro _ ⟨α, hα, _, rfl⟩
  exact isWeightedHomogeneous_monomial _ _ _ hα

/-- A weight-`j` homogeneous polynomial (`j ≥ 1`) is a decomposable plus a combination of the weight-`j` variables. -/
theorem mem_span_reesMonomials_sup_span_X_of_isWeightedHomogeneous (w : σ → ℕ) {j : ℕ} (hj : 0 < j)
    {p : MvPolynomial σ R} (hp : p.IsWeightedHomogeneous w j) :
    p ∈ Submodule.span R (reesMonomials (B := R) w 2 j) ⊔
      Submodule.span R (Set.range fun s : {s : σ // w s = j} => (X (s : σ) : MvPolynomial σ R)) := by
  classical
  rw [p.as_sum]
  refine Submodule.sum_mem _ fun α hα => ?_
  have hαw : Finsupp.weight w α = j := hp (mem_support_iff.mp hα)
  by_cases hdeg : 2 ≤ α.degree
  · refine Submodule.mem_sup_left ?_
    have h2 : monomial α (coeff α p) = coeff α p • monomial α (1 : R) := by
      rw [smul_monomial, smul_eq_mul, mul_one]
    rw [h2]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨α, hαw, hdeg, rfl⟩)
  · obtain ⟨s, hs, rfl⟩ := exists_eq_single_of_degree_le_one w hj α hαw (by omega)
    refine Submodule.mem_sup_right ?_
    have h2 : monomial (Finsupp.single s 1) (coeff (Finsupp.single s 1) p) =
        coeff (Finsupp.single s 1) p • (X s : MvPolynomial σ R) := by
      rw [X, smul_monomial, smul_eq_mul, mul_one]
    rw [h2]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨s, hs⟩, rfl⟩)

/-- **The quotient of `P_j` by `(P_+)² ∩ P_j` is free on the weight-`j` variables.** If `φ : P_j →ₗ N` is surjective with
kernel `span (reesMonomials w 2 j)` (`j ≥ 1`, all weights `≥ 1`), then `N` has a basis indexed by `{s // w s = j}`. -/
theorem exists_basis_of_weightedHomogeneous_quotient (w : σ → ℕ) {j : ℕ} (hj : 0 < j)
    {N : Type*} [AddCommGroup N] [Module R N]
    (φ : weightedHomogeneousSubmodule R w j →ₗ[R] N) (hsurj : Function.Surjective φ)
    (hker : ∀ p : weightedHomogeneousSubmodule R w j,
      φ p = 0 ↔ (p : MvPolynomial σ R) ∈ Submodule.span R (reesMonomials (B := R) w 2 j)) :
    Nonempty (Module.Basis {s : σ // w s = j} R N) := by
  classical
  let vV : {s : σ // w s = j} → weightedHomogeneousSubmodule R w j := fun s =>
    ⟨X (s : σ), by
      have h := isWeightedHomogeneous_X R w (s : σ)
      rw [s.2] at h
      exact h⟩
  let v : {s : σ // w s = j} → N := fun s => φ (vV s)
  have hvV : ∀ s, ((vV s : weightedHomogeneousSubmodule R w j) : MvPolynomial σ R) = X (s : σ) := fun _ => rfl
  -- linear independence
  have hli : LinearIndependent R v := by
    rw [linearIndependent_iff']
    intro t g hg i hi
    have h1 : φ (∑ i ∈ t, g i • vV i) = 0 := by
      rw [map_sum]
      simpa only [map_smul] using hg
    have h2 := (hker _).mp h1
    have h3 : ((∑ i ∈ t, g i • vV i : weightedHomogeneousSubmodule R w j) : MvPolynomial σ R) =
        ∑ i ∈ t, g i • (X (i : σ) : MvPolynomial σ R) := by
      rw [Submodule.coe_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [Submodule.coe_smul, hvV]
    rw [h3] at h2
    have h4 := coeff_single_one_eq_zero_of_mem_span_reesMonomials w j h2 (i : σ)
    rw [coeff_sum] at h4
    have h5 : ∀ i' ∈ t, coeff (Finsupp.single (i : σ) 1) (g i' • (X (i' : σ) : MvPolynomial σ R)) =
        if i' = i then g i else 0 := by
      intro i' _
      rw [coeff_smul, X, coeff_monomial]
      by_cases h : i' = i
      · subst h; simp
      · have h' : Finsupp.single (i' : σ) 1 ≠ Finsupp.single (i : σ) 1 := by
          intro heq
          exact h (Subtype.ext ((Finsupp.single_left_injective one_ne_zero) heq))
        simp [h, h']
    rw [Finset.sum_congr rfl h5, Finset.sum_ite_eq' t i] at h4
    simpa [hi] using h4
  -- spanning
  have hsp : ⊤ ≤ Submodule.span R (Set.range v) := by
    rintro n -
    obtain ⟨p, rfl⟩ := hsurj n
    have hp : (p : MvPolynomial σ R).IsWeightedHomogeneous w j :=
      (mem_weightedHomogeneousSubmodule R w j (p : MvPolynomial σ R)).mp p.2
    obtain ⟨k, hk, x, hx, hkx⟩ := Submodule.mem_sup.mp
      (mem_span_reesMonomials_sup_span_X_of_isWeightedHomogeneous w hj hp)
    have hkV : k ∈ weightedHomogeneousSubmodule R w j :=
      span_reesMonomials_le_weightedHomogeneousSubmodule w 2 j hk
    have hxV : x ∈ weightedHomogeneousSubmodule R w j := by
      have : x = (p : MvPolynomial σ R) - k := by rw [← hkx]; ring
      rw [this]
      exact Submodule.sub_mem _ p.2 hkV
    have hpk : p = ⟨k, hkV⟩ + ⟨x, hxV⟩ := Subtype.ext hkx.symm
    rw [hpk, map_add, (hker _).mpr hk, zero_add]
    have hx' : (⟨x, hxV⟩ : weightedHomogeneousSubmodule R w j) ∈ Submodule.span R (Set.range vV) := by
      have hmap : x ∈ (Submodule.span R (Set.range vV)).map (weightedHomogeneousSubmodule R w j).subtype := by
        rw [Submodule.map_span, ← Set.range_comp]
        exact hx
      obtain ⟨x', hx', hxx'⟩ := hmap
      have : x' = ⟨x, hxV⟩ := Subtype.ext hxx'
      rw [← this]
      exact hx'
    have := Submodule.mem_map_of_mem (f := φ) hx'
    rw [Submodule.map_span, ← Set.range_comp] at this
    exact this
  exact ⟨Module.Basis.mk hli hsp⟩

end MvPolynomial

/-! ## The index type of the weight-`(q+1)` variables -/

namespace jetLinearPiece

/-- The variables `x_{a,q'}` of weight `q+1` (i.e. `q' = q`) are indexed by `a ∈ Fin (n+1)`. -/
def linearIndexEquiv (n r : ℕ) (q : Fin r) :
    {s : ULift.{u} (Fin (n + 1) × Fin r) // (s.down.2 : ℕ) + 1 = q.1 + 1} ≃ ULift.{u} (Fin (n + 1)) where
  toFun s := ⟨s.1.down.1⟩
  invFun a := ⟨⟨(a.down, q)⟩, rfl⟩
  left_inv s := by
    obtain ⟨⟨⟨a, q'⟩⟩, hs⟩ := s
    have : q' = q := Fin.ext (Nat.succ_injective hs)
    subst this
    rfl
  right_inv _ := rfl

end jetLinearPiece

/-! ## Geometry -/

section CoefficientHom

variable {k : Type u} [Field k] {C : SmoothProjectiveCurve k}
    (Z : CategoryTheory.Over C.toScheme) [AlgebraicGeometry.IsAffineHom Z.hom] (sec : C.toScheme ⟶ Z.left)
    (hs : sec ≫ Z.hom = CategoryTheory.CategoryStruct.id _)

namespace jetLinearPiece

/-- **`Γ(U, sec^*Ω_{Z/C})` is free of rank `n+1`** on an affine `U` with `E|_U` trivial: `E^∨ ≅ sec^*Ω_{Z/C}` on the smooth
locus (`dual_coneTangentBundle_iso_pullback_omega`) and the dual of a trivialized module has a basis of sections
(`exists_basis_dual_sections_of_pullback_iso_free`). -/
theorem exists_basis_omega_sections (Zx : Z.left.Opens) (hsZx : ∀ c, sec.base c ∈ Zx) (n : ℕ)
    [AlgebraicGeometry.SmoothOfRelativeDimension (n + 1) (Zx.ι ≫ Z.hom)] (U : C.toScheme.affineOpens)
    (htriv : Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback U.1.ι).obj (coneTangentBundle Z.hom sec hs) ≅
      SheafOfModules.free (R := U.1.toScheme.ringCatSheaf) (ULift.{u} (Fin (n + 1))))) :
    Nonempty (Module.Basis (ULift.{u} (Fin (n + 1))) Γ(C.toScheme, U.1)
      Γ((AlgebraicGeometry.Scheme.Modules.pullback sec).obj (AlgebraicGeometry.Omega Z.hom), U.1)) := by
  have : AlgebraicGeometry.Smooth (Zx.ι ≫ Z.hom) :=
    AlgebraicGeometry.SmoothOfRelativeDimension.smooth (n + 1) (Zx.ι ≫ Z.hom)
  obtain ⟨e⟩ := dual_coneTangentBundle_iso_pullback_omega Z.hom sec hs Zx hsZx
  obtain ⟨eE⟩ := htriv
  obtain ⟨b⟩ := AlgebraicGeometry.Scheme.Modules.exists_basis_dual_sections_of_pullback_iso_free
    (coneTangentBundle Z.hom sec hs) U.1 (ULift.{u} (Fin (n + 1))) eE
  exact ⟨b.map (AlgebraicGeometry.Scheme.Modules.isoSectionsLinearEquiv e U.1)⟩

variable [AlgebraicGeometry.IsClosedImmersion sec] (r : ℕ)

attribute [local instance] MvPolynomial.weightedGradedAlgebra
attribute [local instance] AlgebraicGeometry.Scheme.GradedQCAlgebra.sectionsPieceModule_ofGradedQCAlgebra

/-- Exactness of `Γ(U, I^{(2)}_{q+1}) → Γ(U, S_{q+1}) → Γ(U, L_{q+1})` on an affine `U` (Stacks 01XB). -/
theorem exact_irrelevantPow_app_cokernel_π_app (q : Fin r) (U : C.toScheme.affineOpens) :
    Function.Exact ((((jetGradedAlgebra (k := k) Z sec hs r).1).irrelevantPow 2 (q.1 + 1)).2.app U.1).hom
      ((CategoryTheory.Limits.cokernel.π
        ((jetGradedAlgebra (k := k) Z sec hs r).1.irrelevantPow 2 (q.1 + 1)).2).app U.1).hom := by
  haveI : ((jetGradedAlgebra (k := k) Z sec hs r).1.irrelevantPow 2 (q.1 + 1)).1.IsQuasicoherent :=
    (jetGradedAlgebra (k := k) Z sec hs r).1.irrelevantPow_isQuasicoherent 2 (q.1 + 1)
  haveI : ((jetGradedAlgebra (k := k) Z sec hs r).1.part (q.1 + 1)).IsQuasicoherent :=
    (jetGradedAlgebra (k := k) Z sec hs r).1.quasicoherent (q.1 + 1)
  haveI : (CategoryTheory.Limits.cokernel
      ((jetGradedAlgebra (k := k) Z sec hs r).1.irrelevantPow 2 (q.1 + 1)).2).IsQuasicoherent :=
    (AlgebraicGeometry.Scheme.Modules.isQuasicoherent_kernel _).2
  let S : CategoryTheory.ShortComplex C.toScheme.Modules :=
    CategoryTheory.ShortComplex.mk (((jetGradedAlgebra (k := k) Z sec hs r).1).irrelevantPow 2 (q.1 + 1)).2
      (CategoryTheory.Limits.cokernel.π ((jetGradedAlgebra (k := k) Z sec hs r).1.irrelevantPow 2 (q.1 + 1)).2)
      (CategoryTheory.Limits.cokernel.condition _)
  have hS : S.Exact := CategoryTheory.ShortComplex.exact_of_g_is_cokernel S
    (CategoryTheory.Limits.cokernelIsCokernel _)
  exact (AlgebraicGeometry.Scheme.Modules.gammaAffine_exact_iff S).mp hS U

/-- **`Γ(U, L_{q+1})` is free on the weight-`(q+1)` variables** of the local chart (see the module docstring). -/
theorem exists_basis_linearPiece_sections (Zx : Z.left.Opens) (hsZx : ∀ c, sec.base c ∈ Zx) (n : ℕ)
    [AlgebraicGeometry.SmoothOfRelativeDimension (n + 1) (Zx.ι ≫ Z.hom)] (q : Fin r)
    (U : C.toScheme.affineOpens)
    (htriv : Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback U.1.ι).obj (coneTangentBundle Z.hom sec hs) ≅
      SheafOfModules.free (R := U.1.toScheme.ringCatSheaf) (ULift.{u} (Fin (n + 1))))) :
    Nonempty (Module.Basis {s : ULift.{u} (Fin (n + 1) × Fin r) // (s.down.2 : ℕ) + 1 = q.1 + 1} Γ(C.toScheme, U.1)
      Γ(CategoryTheory.Limits.cokernel ((jetGradedAlgebra (k := k) Z sec hs r).1.irrelevantPow 2 (q.1 + 1)).2, U.1)) := by
  classical
  obtain ⟨e₀, hgr, hunit⟩ := jetGradedAlgebra_localWeightedChart_of_smooth Z sec hs Zx hsZx n r U htriv
  have hw : ∀ s : ULift.{u} (Fin (n + 1) × Fin r), 0 < ((s.down.2 : ℕ) + 1) := fun _ => Nat.succ_pos _
  let eq := (jetGradedAlgebra (k := k) Z sec hs r).1.pieceLinearEquivOfChart U.1
    (fun iq : ULift.{u} (Fin (n + 1) × Fin r) => (iq.down.2 : ℕ) + 1)
    (show (jetGradedAlgebra (k := k) Z sec hs r).1.sectionsRing U.1 ≃+*
      MvPolynomial (ULift.{u} (Fin (n + 1) × Fin r)) Γ(C.toScheme, U.1) from e₀) hgr hunit (q.1 + 1)
  haveI : ((jetGradedAlgebra (k := k) Z sec hs r).1.part (q.1 + 1)).IsQuasicoherent :=
    (jetGradedAlgebra (k := k) Z sec hs r).1.quasicoherent (q.1 + 1)
  haveI : ((jetGradedAlgebra (k := k) Z sec hs r).1.irrelevantPow 2 (q.1 + 1)).1.IsQuasicoherent :=
    (jetGradedAlgebra (k := k) Z sec hs r).1.irrelevantPow_isQuasicoherent 2 (q.1 + 1)
  let φ : MvPolynomial.weightedHomogeneousSubmodule Γ(C.toScheme, U.1)
      (fun iq : ULift.{u} (Fin (n + 1) × Fin r) => (iq.down.2 : ℕ) + 1) (q.1 + 1) →ₗ[Γ(C.toScheme, U.1)]
      Γ(CategoryTheory.Limits.cokernel ((jetGradedAlgebra (k := k) Z sec hs r).1.irrelevantPow 2 (q.1 + 1)).2, U.1) :=
    (AlgebraicGeometry.Scheme.Modules.Hom.appLin
      (CategoryTheory.Limits.cokernel.π ((jetGradedAlgebra (k := k) Z sec hs r).1.irrelevantPow 2 (q.1 + 1)).2) U.1) ∘ₗ
      eq.symm.toLinearMap
  have hφ : ∀ p, φ p = ((CategoryTheory.Limits.cokernel.π
      ((jetGradedAlgebra (k := k) Z sec hs r).1.irrelevantPow 2 (q.1 + 1)).2).app U.1).hom (eq.symm p) := fun _ => rfl
  have hsurj : Function.Surjective φ := by
    intro ℓ
    obtain ⟨y, hy⟩ := AlgebraicGeometry.Scheme.Modules.cokernel_π_app_surjective
      ((jetGradedAlgebra (k := k) Z sec hs r).1.irrelevantPow 2 (q.1 + 1)).2 U ℓ
    refine ⟨eq y, ?_⟩
    rw [hφ]
    exact (congrArg _ (eq.symm_apply_apply y)).trans hy
  -- the chart is graded in both directions
  have hgrE : ∀ (m : ℕ) (a : (jetGradedAlgebra (k := k) Z sec hs r).1.toGradedAffineAlgebra.toAffineAlgebra.sections
      (AlgebraicGeometry.Scheme.affineSite U)),
      a ∈ (jetGradedAlgebra (k := k) Z sec hs r).1.toGradedAffineAlgebra.gradingSubmodule
        (AlgebraicGeometry.Scheme.affineSite U) m →
        e₀ a ∈ MvPolynomial.weightedHomogeneousSubmodule Γ(C.toScheme, U.1)
          (fun iq : ULift.{u} (Fin (n + 1) × Fin r) => (iq.down.2 : ℕ) + 1) m := fun m a ha =>
    (MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).mpr ((hgr m a).mp ha)
  have hgrE' : ∀ (m : ℕ) (b : MvPolynomial (ULift.{u} (Fin (n + 1) × Fin r)) Γ(C.toScheme, U.1)),
      b ∈ MvPolynomial.weightedHomogeneousSubmodule Γ(C.toScheme, U.1)
          (fun iq : ULift.{u} (Fin (n + 1) × Fin r) => (iq.down.2 : ℕ) + 1) m →
        e₀.symm b ∈ (jetGradedAlgebra (k := k) Z sec hs r).1.toGradedAffineAlgebra.gradingSubmodule
          (AlgebraicGeometry.Scheme.affineSite U) m := by
    intro m b hb
    refine (hgr m (e₀.symm b)).mpr ?_
    have hb' := (MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).mp hb
    have : e₀ (e₀.symm b) = b := RingEquiv.apply_symm_apply e₀ b
    exact this.symm ▸ hb'
  have hex := exact_irrelevantPow_app_cokernel_π_app Z sec hs r q U
  have hker : ∀ p : MvPolynomial.weightedHomogeneousSubmodule Γ(C.toScheme, U.1)
      (fun iq : ULift.{u} (Fin (n + 1) × Fin r) => (iq.down.2 : ℕ) + 1) (q.1 + 1),
      φ p = 0 ↔ (p : MvPolynomial (ULift.{u} (Fin (n + 1) × Fin r)) Γ(C.toScheme, U.1)) ∈
        Submodule.span Γ(C.toScheme, U.1) (MvPolynomial.reesMonomials (B := Γ(C.toScheme, U.1))
          (fun iq : ULift.{u} (Fin (n + 1) × Fin r) => (iq.down.2 : ℕ) + 1) 2 (q.1 + 1)) := by
    intro p
    rw [← MvPolynomial.irrPow_weightedHomogeneousSubmodule_eq_span _ hw 2 (q.1 + 1), hφ]
    refine (hex (eq.symm p)).trans ?_
    refine Set.mem_range.trans ?_
    refine ((jetGradedAlgebra (k := k) Z sec hs r).1.irrelevantPow_app_range_iff
      (AlgebraicGeometry.Scheme.affineSite U) 2 (q.1 + 1) (eq.symm p)).trans ?_
    have h3 : e₀ ((jetGradedAlgebra (k := k) Z sec hs r).1.ofPiece U.1 (q.1 + 1) (eq.symm p)) =
        (p : MvPolynomial (ULift.{u} (Fin (n + 1) × Fin r)) Γ(C.toScheme, U.1)) :=
      congrArg Subtype.val (eq.apply_symm_apply p)
    have h4 : e₀.symm (p : MvPolynomial (ULift.{u} (Fin (n + 1) × Fin r)) Γ(C.toScheme, U.1)) =
        (jetGradedAlgebra (k := k) Z sec hs r).1.ofPiece U.1 (q.1 + 1) (eq.symm p) :=
      (RingEquiv.symm_apply_eq e₀).mpr h3.symm
    constructor
    · intro h
      have := ReesAlgebra.map_mem_irrPow _ _ e₀.toRingHom hgrE h
      rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom] at this
      exact Eq.mp (congrArg (· ∈ ReesAlgebra.irrPow (MvPolynomial.weightedHomogeneousSubmodule Γ(C.toScheme, U.1)
        (fun iq : ULift.{u} (Fin (n + 1) × Fin r) => (iq.down.2 : ℕ) + 1)) 2 (q.1 + 1)) h3) this
    · intro h
      have := ReesAlgebra.map_mem_irrPow _ _ e₀.symm.toRingHom hgrE' h
      rw [RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom] at this
      exact Eq.mp (congrArg (· ∈ ReesAlgebra.irrPow
        ((jetGradedAlgebra (k := k) Z sec hs r).1.toGradedAffineAlgebra.gradingSubmodule
          (AlgebraicGeometry.Scheme.affineSite U)) 2 (q.1 + 1)) h4) this
  exact MvPolynomial.exists_basis_of_weightedHomogeneous_quotient _ (Nat.succ_pos q.1) φ hsurj hker

/-- **Injectivity of a coefficient morphism on the sections over an affine `U` with `E|_U` trivial** (Orzech; see the
module docstring). -/
theorem coefficientHom_app_injective (Zx : Z.left.Opens) (hsZx : ∀ c, sec.base c ∈ Zx) (n : ℕ)
    [AlgebraicGeometry.SmoothOfRelativeDimension (n + 1) (Zx.ι ≫ Z.hom)] (q : Fin r)
    (U : C.toScheme.affineOpens)
    (htriv : Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback U.1.ι).obj (coneTangentBundle Z.hom sec hs) ≅
      SheafOfModules.free (R := U.1.toScheme.ringCatSheaf) (ULift.{u} (Fin (n + 1)))))
    (θ : (AlgebraicGeometry.Scheme.Modules.pullback sec).obj (AlgebraicGeometry.Omega Z.hom) ⟶
      CategoryTheory.Limits.cokernel ((jetGradedAlgebra (k := k) Z sec hs r).1.irrelevantPow 2 (q.1 + 1)).2)
    (hθ : IsCoefficientHom Z sec hs r q θ) :
    Function.Injective (θ.app U.1).hom := by
  obtain ⟨bL⟩ := exists_basis_linearPiece_sections Z sec hs r Zx hsZx n q U htriv
  obtain ⟨bΩ⟩ := exists_basis_omega_sections Z sec hs Zx hsZx n U htriv
  let E := bL.equiv bΩ (linearIndexEquiv n r q)
  let f := E.toLinearMap ∘ₗ AlgebraicGeometry.Scheme.Modules.Hom.appLin θ U.1
  have hf : Function.Surjective f :=
    E.surjective.comp (coefficientHom_app_surjective Z sec hs r q U θ hθ)
  haveI : Module.Finite Γ(C.toScheme, U.1)
      Γ((AlgebraicGeometry.Scheme.Modules.pullback sec).obj (AlgebraicGeometry.Omega Z.hom), U.1) :=
    Module.Finite.of_basis bΩ
  have hinj : Function.Injective f := OrzechProperty.injective_of_surjective_endomorphism f hf
  exact Function.Injective.of_comp (f := ⇑E) (g := ⇑(θ.app U.1).hom) hinj

/-- **The coefficient morphism is bijective on the sections over an affine `U` with `E|_U` trivial**:
`coefficientHom_app_injective` + `coefficientHom_app_surjective`. -/
theorem coefficientHom_app_bijective (Zx : Z.left.Opens) (hsZx : ∀ c, sec.base c ∈ Zx) (n : ℕ)
    [AlgebraicGeometry.SmoothOfRelativeDimension (n + 1) (Zx.ι ≫ Z.hom)] (q : Fin r)
    (U : C.toScheme.affineOpens)
    (htriv : Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback U.1.ι).obj (coneTangentBundle Z.hom sec hs) ≅
      SheafOfModules.free (R := U.1.toScheme.ringCatSheaf) (ULift.{u} (Fin (n + 1)))))
    (θ : (AlgebraicGeometry.Scheme.Modules.pullback sec).obj (AlgebraicGeometry.Omega Z.hom) ⟶
      CategoryTheory.Limits.cokernel ((jetGradedAlgebra (k := k) Z sec hs r).1.irrelevantPow 2 (q.1 + 1)).2)
    (hθ : IsCoefficientHom Z sec hs r q θ) :
    Function.Bijective (θ.app U.1).hom :=
  ⟨coefficientHom_app_injective Z sec hs r Zx hsZx n q U htriv θ hθ,
    coefficientHom_app_surjective Z sec hs r q U θ hθ⟩

end jetLinearPiece

end CoefficientHom

end
