import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S3PositiveLine.Realization.RealizationGeometricBack
import MiyaokaMori.Targets.RealizationCoefficients
import MiyaokaMori.Paper.S4Completion.SpecialFiberRationalConnected

/-! # Polynomial realization and the resolved ruled surface

**Theorem 4.2** and Corollary 4.3 of the paper.** Choose `k` with
`d h_k > 2(n+1)δa`. Then `r₀ = ⌊a e / d_L⌋ ≥ 1` (the paper's `r_k`), `δ r₀ < k`, and the based jet `ȷ`
extends to a polynomial morphism `Tot(L) → 𝒵` of fiber degree `≤ r₀`, regular near the zero section
and nonconstant on a general fiber, with `r₀ < 2(n+1)ka/(d h_k)`; the induced rational map
`W = P(O ⊕ L) ⇢ X` is regular near the whole `O`-section and is resolved by a tower of point blowups
with centers away from that section, giving `S`, `π_S`, a section `σ` and `Φ : S → X` with
`Φ ∘ σ = f ∘ ρ`, every fiber of `π_S` a connected tree of smooth rational curves, and
`1 ≤ deg(Φ^*O_X(1)|_F) ≤ r₀` on the fibers.

The single theorem `realization` covers both statements: the conjuncts on `P`, `r₀` are the theorem,
those on `S, β, π_S, σ, Φ` the corollary. Its numerical front (`realization_numeric_front`) takes
`¬ jet.IsGenericallyScalar` and `1 ≤ r₀` from Lemma 4.1
(`realization_coefficients`, `Targets/RealizationCoefficients.lean`), as the paper's proof does;
`δ r₀ < κ` is the equation-degree bound (4.3) (`delta_r0_lt_k`) and the strict bound
`r₀ < 2(n+1)ka/(d h_k)` is `r0_lt_embedding_bound`.

The **tree clause** of the corollary ("the reduced support of every fiber of `π_S` is a connected
tree of smooth rational curves") is the conjunct following the fiber-connectedness conjunct: for every
closed point `y ∈ C̃`, the fiber one-cycle `π_S^*(y)` is `Σ m_i [Γ_i]` with `m_i ≥ 1`, the `Γ_i`
integral curves covering the set-theoretic fiber, the fiber connected, and each `Γ_i` smooth rational
(`IntegralCurve.IsSmoothRational`: `Γ_i ≅ P¹` over `k`). It is `special_fiber_rational_connected`
(`Paper/S4Completion/SpecialFiberRationalConnected.lean`) applied to the blowup tower `β` (centers
away from the `O`-section, `IsBlowupTowerAvoiding`) and `π_S = β ≫ π_W`. The library states the tree
property as "connected, with smooth rational components"; the acyclicity of the dual graph is not
formalized separately, since Lemma 5.1 only needs connectedness and the component
decomposition.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/- The numerical part of the realization construction is kept local to this
   target.  In particular, the integer cutoff is the nonnegative `Int.toNat`
   representative of the quotient used by `r0_bound`. -/
private lemma realization_numeric_front {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}
    (f : C.toScheme ⟶ X.toScheme) [D : MMSetup f]
    (hf : ¬ IsConstantMorphism f) (hd : 0 < TangentBundle.pullbackDegree f)
    (κ : ℕ) (hκ1 : 1 ≤ κ)
    (hκ : (TangentBundle.pullbackDegree f : ℚ) * harmonic κ >
      2 * ((X.toVariety.dim : ℚ) + 1) * (D.δ : ℚ) *
        ((LineBundle.pullback (X := C.toVariety) f (X.OX 1)).degree : ℚ)) :
    ∃ (ρ : FiniteCover k C) (L : LineBundle ρ.source.toVariety)
      (jet : BasedJet f ρ L κ) (r₀ : ℕ),
      0 < L.degree ∧ ¬ jet.IsGenericallyScalar ∧
      (r₀ : ℤ) = (LineBundle.pullback (X := C.toVariety) f (X.OX 1)).degree *
        (ρ.degree : ℤ) / L.degree ∧ 1 ≤ r₀ ∧ D.δ * r₀ < κ ∧
      NormalizedTupleNowhereZero jet ∧
      ((r₀ : ℚ) < 2 * ((X.toVariety.dim : ℚ) + 1) * (κ : ℚ)
        * ((LineBundle.pullback (X := C.toVariety) f (X.OX 1)).degree : ℚ)
        / ((TangentBundle.pullbackDegree f : ℚ) * harmonic κ)) := by
  obtain ⟨ρ, L, jet, hnz, -, hslope, hpos⟩ := positive_line f hf hd κ hκ1
  have heNat : 0 < ρ.degree := FiniteCover.degree_pos ρ
  have he : 0 < (ρ.degree : ℤ) := by exact_mod_cast heNat
  have heq : (0 : ℚ) < (ρ.degree : ℚ) := by exact_mod_cast he
  have hratioPos : (0 : ℚ) < (L.degree : ℚ) / (ρ.degree : ℚ) :=
    lt_trans hpos hslope
  have hLq : (0 : ℚ) < (L.degree : ℚ) := by
    rcases (div_pos_iff.mp hratioPos) with h | h
    · exact h.1
    · exact False.elim ((not_lt_of_ge heq.le) h.2)
  have hL : 0 < L.degree := by exact_mod_cast hLq
  have hslopeI :
      (D.δ : ℤ) * (LineBundle.pullback (X := C.toVariety) f (X.OX 1)).degree *
          (ρ.degree : ℤ) < (κ : ℤ) * L.degree := by
    have heq' : (0 : ℚ) < (ρ.degree : ℚ) := by exact_mod_cast he
    have hkq : (0 : ℚ) < (κ : ℚ) := by
      exact_mod_cast (show 0 < κ by omega)
    have hnq : (0 : ℚ) < (2 : ℚ) * ((X.toVariety.dim : ℚ) + 1) := by
      positivity
    have hcross :
        (TangentBundle.pullbackDegree f : ℚ) * harmonic κ * (ρ.degree : ℚ) <
          (L.degree : ℚ) * (2 * ((X.toVariety.dim : ℚ) + 1) * (κ : ℚ)) := by
      exact (div_lt_div_iff₀ (mul_pos hnq hkq) heq').mp hslope
    have hscaled :
        (2 : ℚ) * ((X.toVariety.dim : ℚ) + 1) * (D.δ : ℚ) *
            ((LineBundle.pullback (X := C.toVariety) f (X.OX 1)).degree : ℚ) *
            (ρ.degree : ℚ) <
          (κ : ℚ) * (L.degree : ℚ) *
            (2 * ((X.toVariety.dim : ℚ) + 1)) := by
      calc
        (2 : ℚ) * ((X.toVariety.dim : ℚ) + 1) * (D.δ : ℚ) *
              ((LineBundle.pullback (X := C.toVariety) f (X.OX 1)).degree : ℚ) *
              (ρ.degree : ℚ) <
            (TangentBundle.pullbackDegree f : ℚ) * harmonic κ * (ρ.degree : ℚ) :=
          mul_lt_mul_of_pos_right (by linarith [hκ]) heq'
        _ < (L.degree : ℚ) * (2 * ((X.toVariety.dim : ℚ) + 1) * (κ : ℚ)) := hcross
        _ = (κ : ℚ) * (L.degree : ℚ) *
              (2 * ((X.toVariety.dim : ℚ) + 1)) := by ring
    have hfinalq :
        (D.δ : ℚ) *
            ((LineBundle.pullback (X := C.toVariety) f (X.OX 1)).degree : ℚ) *
            (ρ.degree : ℚ) < (κ : ℚ) * (L.degree : ℚ) := by
      nlinarith [hscaled]
    exact_mod_cast hfinalq
  let A : LineBundle C.toVariety := LineBundle.pullback (X := C.toVariety) f (X.OX 1)
  -- Lemma 4.1: the jet is not generically scalar and r₀ = ⌊a e / d_L⌋ ≥ 1.
  obtain ⟨-, hns, -, hr0ge⟩ := realization_coefficients f κ ρ L jet hnz hL
  let r₀ : ℕ := Int.toNat (A.degree * (ρ.degree : ℤ) / L.degree)
  have hr0ge' : (1 : ℤ) ≤ A.degree * (ρ.degree : ℤ) / L.degree := hr0ge
  have hr0cast : (r₀ : ℤ) = A.degree * (ρ.degree : ℤ) / L.degree := by
    apply Int.toNat_of_nonneg
    omega
  have hr1 : (1 : ℤ) ≤ (r₀ : ℤ) := by rw [hr0cast]; exact hr0ge'
  have hApos : 0 < A.degree := by
    have hmul := Int.ediv_mul_le (A.degree * (ρ.degree : ℤ)) hL.ne'
    rw [← hr0cast] at hmul
    have hprod : 0 < A.degree * (ρ.degree : ℤ) := by nlinarith
    by_contra hneg
    have hA_le : A.degree ≤ 0 := by omega
    have := mul_nonpos_of_nonpos_of_nonneg hA_le he.le
    omega
  refine ⟨ρ, L, jet, r₀, hL, hns, hr0cast, ?_, ?_, hnz, ?_⟩
  · exact_mod_cast hr1
  · have hi : (D.δ : ℤ) * (r₀ : ℤ) < (κ : ℤ) := by
      rw [hr0cast]
      exact delta_r0_lt_k hL he hApos.le hslopeI
    exact_mod_cast hi
  · exact r0_lt_embedding_bound (n := X.toVariety.dim) hL he hκ1 hd hApos hr0cast hslope

/-- **Polynomial realization and the resolved ruled surface** (Theorem 4.2 and
Corollary 4.3 of the paper): for `κ` with `d h_κ > 2(n+1)δa`, a finite cover `ρ`,
a line bundle `L`, a based jet extending to a polynomial tuple `P` of fiber degree `≤ r₀` with
`1 ≤ r₀`, `δ r₀ < κ`, and the resolved ruled surface `S` with `π_S`, `σ`, `Φ` such that
`Φ ∘ σ = f ∘ ρ`, the fibers are connected trees of smooth rational curves, and the general fiber `F`
satisfies `1 ≤ deg(Φ^*O_X(1)|_F) ≤ r₀`. -/
theorem realization {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}
    (f : C.toScheme ⟶ X.toScheme) [D : MMSetup f] (hf : ¬ IsConstantMorphism f)
    (hd : 0 < TangentBundle.pullbackDegree f)
    (κ : ℕ) (hκ1 : 1 ≤ κ)
    (hκ : (TangentBundle.pullbackDegree f : ℚ) * harmonic κ
        > 2 * ((X.toVariety.dim : ℚ) + 1) * (D.δ : ℚ)
          * ((LineBundle.pullback (X := C.toVariety) f (X.OX 1)).degree : ℚ)) :
    ∃ (ρ : FiniteCover k C) (L : LineBundle ρ.source.toVariety)
      (jet : BasedJet f ρ L κ) (r₀ : ℕ)
      (P : Fin (X.embDim + 1) →
        (((AlgebraicGeometry.Scheme.Modules.pullback
          (AlgebraicGeometry.Scheme.totalSpace L.toModules).hom).obj
          (seedBundlePullback f ρ).toModules).val.obj
          (Opposite.op ⊤) : Type u))
      (S : SmoothProjectiveSurface k) (β : S.toScheme ⟶ (ruledSurface L).toScheme)
      (hβ : IsBlowupTower β)
      (eW : (ruledSurface L).toScheme ≅
        (AlgebraicGeometry.Scheme.projBundle
          (CategoryTheory.Limits.biprod (C := ρ.source.toVariety.toScheme.Modules) (show ρ.source.toVariety.toScheme.Modules from SheafOfModules.unit ρ.source.toVariety.toScheme.ringCatSheaf) L.toModules)).left)
      (πS : S.toScheme ⟶ ρ.source.toScheme)
      (hπS : AlgebraicGeometry.Surjective πS)
      (σ : ρ.source.toScheme ⟶ S.toScheme) (Φ : S.toScheme ⟶ X.toScheme),
      0 < L.degree ∧
      ¬ jet.IsGenericallyScalar ∧
      (r₀ : ℤ) = (LineBundle.pullback (X := C.toVariety) f (X.OX 1)).degree * (ρ.degree : ℤ) / L.degree ∧
      1 ≤ r₀ ∧ D.δ * r₀ < κ ∧
      -- the jet extends to Tot(L) → 𝒵: a tuple of polynomials of degree ≤ r₀ in the fiber coordinate,
      -- truncating back to the jet and satisfying all the equations
      (∀ ℓ, xiDegree L (seedBundlePullback f ρ) (P ℓ)
          ≤ (r₀ : WithBot ℕ)) ∧
      (∀ ℓ, BasedJet.coneCoordinate jet ℓ
          = restrictToThickening L (seedBundlePullback f ρ) κ (P ℓ)) ∧
      (∀ j, evalHomogeneousAtSections _ (D.E.F j) (D.E.homogeneous j) P = 0) ∧
      -- the blowup tower: all centers are closed points not above the O-section Σ₀; the identification
      -- of W with P(O ⊕ L) is compatible with the projections
      IsBlowupTowerAvoiding β
        (Set.range (AlgebraicGeometry.Scheme.oSection L.toModules ≫ eW.inv).base) ∧
      Disjoint (ExceptionalCenters β hβ)
        (Set.range (AlgebraicGeometry.Scheme.oSection L.toModules ≫ eW.inv).base) ∧
      eW.hom ≫ (AlgebraicGeometry.Scheme.projBundle
          (CategoryTheory.Limits.biprod (C := ρ.source.toVariety.toScheme.Modules) (show ρ.source.toVariety.toScheme.Modules from SheafOfModules.unit ρ.source.toVariety.toScheme.ringCatSheaf) L.toModules)).hom
        = ruledSurface.π L ∧
      πS = β ≫ ruledSurface.π L ∧
      (∀ y : ρ.source.toScheme, IsClosed ({y} : Set ρ.source.toScheme) →
        _root_.IsConnected (πS.base ⁻¹' {y})) ∧
      -- the tree clause of Corollary 4.3: every closed fiber π_S^*(y) = Σ m_i Γ_i is a
      -- connected union of smooth rational curves Γ_i ≅ P¹ with multiplicities m_i ≥ 1 (`special_fiber_rational_connected`)
      (∀ y : ρ.source.toScheme, IsClosed ({y} : Set ρ.source.toScheme) →
        ∃ (ι : Type) (_ : Fintype ι) (m : ι → ℕ) (Γ : ι → IntegralCurve k S.toScheme),
          (∀ i, 0 < m i) ∧
          fiberCycle πS hπS y = ∑ i, (m i : ℤ) • (Γ i).fundamentalClass ∧
          (⋃ i, Set.range (Γ i).ι.base) = πS.base ⁻¹' {y} ∧
          _root_.IsConnected (πS.base ⁻¹' {y}) ∧
          (∀ i, (Γ i).IsSmoothRational)) ∧
      σ ≫ πS = CategoryTheory.CategoryStruct.id ρ.source.toScheme ∧
      σ ≫ β = AlgebraicGeometry.Scheme.oSection L.toModules ≫ eW.inv ∧
      σ ≫ Φ = ρ.hom ≫ f ∧
      -- Φ is a k-morphism (the k-compatibility of β, π_S, σ follows from hβ and the other conjuncts)
      Φ.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) ∧
      (∃ V : Set ρ.source.toScheme, IsOpen V ∧ V.Nonempty ∧
        ∀ y ∈ V, IsClosed ({y} : Set ρ.source.toScheme) →
          Nonempty ((πS.fiber y) ≅ (ProjectiveLine.asSmoothProjectiveCurve k).toScheme) ∧
          1 ≤ fiberDegree πS hπS (LineBundle.pullback (X := S.toVariety) Φ (X.OX 1)) y ∧
          fiberDegree πS hπS (LineBundle.pullback (X := S.toVariety) Φ (X.OX 1)) y ≤ (r₀ : ℤ)) ∧
      EmbeddingDegreeBound Φ πS hπS r₀ ∧
      ((r₀ : ℚ) < 2 * ((X.toVariety.dim : ℚ) + 1) * (κ : ℚ)
        * ((LineBundle.pullback (X := C.toVariety) f (X.OX 1)).degree : ℚ)
        / ((TangentBundle.pullbackDegree f : ℚ) * harmonic κ)) := by
  obtain ⟨ρ, L, jet, r₀, hL, hns, hr0, hr1, hδ, hnz, hbound⟩ :=
    realization_numeric_front f hf hd κ hκ1 hκ
  obtain ⟨P, S, β, hβ, eW, πS, hπS, σ, Φ, h⟩ :=
    realization_geometric_back f hf hd κ hκ1 ρ L jet r₀ hL hns hnz hr0 hr1 hδ
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩ := h
  -- the tree clause: `special_fiber_rational_connected` for the tower β (avoiding Σ₀) and π_S = β ≫ π_W
  have htree : ∀ y : ρ.source.toScheme, IsClosed ({y} : Set ρ.source.toScheme) →
      ∃ (ι : Type) (_ : Fintype ι) (m : ι → ℕ) (Γ : ι → IntegralCurve k S.toScheme),
        (∀ i, 0 < m i) ∧
        fiberCycle πS hπS y = ∑ i, (m i : ℤ) • (Γ i).fundamentalClass ∧
        (⋃ i, Set.range (Γ i).ι.base) = πS.base ⁻¹' {y} ∧
        _root_.IsConnected (πS.base ⁻¹' {y}) ∧
        (∀ i, (Γ i).IsSmoothRational) :=
    fun y hy => special_fiber_rational_connected L β hβ h4 πS h7 hπS y hy
  exact ⟨ρ, L, jet, r₀, P, S, β, hβ, eW, πS, hπS, σ, Φ, hL, hns, hr0, hr1, hδ,
    h1, h2, h3, h4, h5, h6, h7, h8, htree, h9, h10, h11, h12, h13, h14, hbound⟩

end
