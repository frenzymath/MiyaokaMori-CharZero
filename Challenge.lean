import MiyaokaMori.AlgebraicGeometry.Blowup.BlowupTowerAvoiding
import MiyaokaMori.AlgebraicGeometry.Blowup.StrictTransformTower
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.FiberDegree
import MiyaokaMori.AlgebraicGeometry.Chow.Pushforward.CyclePushforward
import MiyaokaMori.AlgebraicGeometry.Divisors.LineBundle.CanonicalDivisor
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.PullbackDegreeFiniteCover
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothRationalCurve
import MiyaokaMori.Paper.S2WeightedJets.Ygg.TautologicalTopSelfIntersection
import MiyaokaMori.Paper.S3PositiveLine.Realization.EmbeddingDegreeBound
import MiyaokaMori.Paper.S3PositiveLine.Realization.RuledSurface
import MiyaokaMori.Paper.S3PositiveLine.Rescaling.JetProjectivize

/-! # Challenge statements for Lean comparator

The statements of the nine formalized results of the paper, each with `sorry` in place of the proof.
`Solution.lean` imports the proofs; `comparator.json` lists the theorem names and the permitted axioms.
The imports above contain only the definitions these statements use: none of them reaches a proof of any
of the nine theorems. -/

set_option autoImplicit false

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Theorem 1.1 (Miyaoka–Mori). -/
theorem miyaoka_mori {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    (X : SmoothProjectiveVariety k) (C : SmoothProjectiveCurve k)
    (f : C.toScheme ⟶ X.toScheme) [f.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (hf : ¬ IsConstantMorphism f)
    (K : CartierDivisor X.toVariety) (hK : CartierDivisor.IsCanonical X K)
    (hd : 0 < intersectionNumber X (-K) (curveCycleClassPushforward f))
    (x : X.toScheme) (hxc : IsClosed ({x} : Set X.toScheme)) (hx : x ∈ Set.range f.base) :
    ∃ b : ProjectiveLine k ⟶ X.toScheme,
      b.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) ∧
      ¬ IsConstantMorphism b ∧ b.base (ProjectiveLine.zero k) = x := by
  sorry

/-- Proposition 2.4 (the weighted intersection). -/
theorem harmonic_intersection {K : Type u} [Field K] [IsAlgClosed K] [CharZero K]
    {C : SmoothProjectiveCurve K} {X : SmoothProjectiveVariety K}
    (f : C.toScheme ⟶ X.toScheme) {N δ n : ℕ}
    (e : ProjectiveEmbedding K X.toScheme N) (E : EmbeddingEquations K e δ)
    (hn : X.toVariety.dim = n) (hn1 : 1 ≤ n)
    (coord : Fin (N + 1) → ((seedLineBundle e f).val.obj (Opposite.op ⊤) : Type u))
    (hcoord : IsHomogeneousCoordinateTuple e f coord)
    (d : ℤ) (hd : TangentBundle.pullbackDegree f = d)
    (kk : ℕ) (hkk : 1 ≤ kk) (m : ℕ) (hm : 0 < m)
    (hdiv : (n + 1) * kk * jetWeight kk ∣ m) :
    let Z := twistedAffineCone (seedLineBundle e f) N E.deg E.F E.homogeneous
    let s := seedSection (seedLineBundle e f) N coord E.deg E.F E.homogeneous
      (seedSection_equations_vanish e E f coord hcoord)
    let Y := weightedJetProjectivization (k := K) Z s.1 s.2 kk
    let B : Y.left.Modules := AlgebraicGeometry.Scheme.relativeProj.twist (jetGradedAlgebra (k := K) Z s.1 s.2 kk).1 (m : ℤ)
    letI : Y.left.Over (AlgebraicGeometry.Spec (CommRingCat.of K)) :=
      ⟨Y.hom ≫ (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of K))⟩;
    ∀ (c : C.toScheme) (hc : IsClosed ({c} : Set C.toScheme))
      (hfib : letI := Y.hom.fiberOverSpecResidueField c;
        IsProperOver (C.toScheme.residueField c) (Y.hom.fiber c)) (hY : IsProperOver K Y.left),
    AlgebraicGeometry.IsIntegral Y.left ∧ Y.left.IsNormal ∧
    AlgebraicGeometry.IsProjectiveMorphism Y.hom ∧ Y.left.dimension = (n + 1) * kk ∧
    ∃ hB : B.IsLineBundle, haveI := hB; AlgebraicGeometry.Scheme.Modules.IsRelativelyVeryAmple Y.hom B ∧
    0 < AlgebraicGeometry.relativePolarizationFiberDegree Y.hom B c hfib ∧
    tautologicalTopSelfIntersection Y.left hY B m hm
      = - ((AlgebraicGeometry.relativePolarizationFiberDegree Y.hom B c hfib : ℚ) /
            (m : ℚ) ^ ((n + 1) * kk - 1))
          * (d : ℚ) * ∑ q ∈ Finset.Icc 1 kk, (1 : ℚ) / (q : ℚ) ∧
    (AlgebraicGeometry.relativePolarizationFiberDegree Y.hom B c hfib : ℚ) /
        (m : ℚ) ^ ((n + 1) * kk - 1)
      = 1 / ((kk.factorial : ℚ) ^ (n + 1)) ∧
    tautologicalTopSelfIntersection Y.left hY B m hm
      = - ((d : ℚ) / (kk.factorial : ℚ) ^ (n + 1))
          * ∑ q ∈ Finset.Icc 1 kk, (1 : ℚ) / (q : ℚ) := by
  sorry

/-- Lemma 2.5 (a negative horizontal curve). -/
theorem negative_horizontal {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}
    (f : C.toScheme ⟶ X.toScheme) [MMSetup f]
    (hd : 0 < TangentBundle.pullbackDegree f) (κ : ℕ) (hκ : 1 ≤ κ) :
    ∃ (m : ℕ) (hSD : (jetAlgebra f κ).SufficientlyDivisible m) (_ : ∀ q ∈ Finset.Icc 1 κ, q ∣ m)
      (Γ : IntegralCurve k (YGG f κ)) (Ct₀ : SmoothProjectiveCurve k)
      (ν : Ct₀.toScheme ⟶ Γ.carrier)
      (_ : AlgebraicGeometry.IsFinite ν)
      (_ : ν.base (genericPoint Ct₀.toScheme) = genericPoint Γ.carrier)
      (_ : functionFieldDegree ν = 1)
      (_ : (ν ≫ Γ.ι).IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)))
      (_ : AlgebraicGeometry.IsFinite (ν ≫ Γ.ι ≫ YGG.proj f κ))
      (_ : Function.Surjective (ν ≫ Γ.ι ≫ YGG.proj f κ).base)
      (_ : (ν ≫ Γ.ι ≫ YGG.proj f κ).base (genericPoint Ct₀.toScheme) = genericPoint C.toScheme),
      haveI : Fact ((jetAlgebra f κ).SufficientlyDivisible m) := ⟨hSD⟩
      ((TangentBundle.pullbackDegree f : ℚ) * harmonic κ) / (2 * ((X.toVariety.dim : ℚ) + 1) * κ)
        < - (Γ.degree (polarization f κ m) : ℚ)
            / ((m : ℚ) * (functionFieldDegree (ν ≫ Γ.ι ≫ YGG.proj f κ) : ℚ)) := by
  sorry

/-- Lemma 3.1 (an affine lift after finite base change). -/
theorem affine_lift_after_base_change {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}
    (f : C.toScheme ⟶ X.toScheme) [MMSetup f] (κ : ℕ) (hκ : 1 ≤ κ)
    {Ct₀ : SmoothProjectiveCurve k} (ν₀ : Ct₀.toScheme ⟶ YGG f κ)
    [ν₀.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [AlgebraicGeometry.IsFinite (ν₀ ≫ YGG.proj f κ)]
    (hsurj : Function.Surjective (ν₀ ≫ YGG.proj f κ).base)
    (hgen : (ν₀ ≫ YGG.proj f κ).base (genericPoint Ct₀.toScheme) = genericPoint C.toScheme) :
    ∃ (ρ : FiniteCover k C) (η : ρ.source.toScheme ⟶ Ct₀.toScheme)
      (_ : AlgebraicGeometry.IsFinite η)
      (_ : η.base (genericPoint ρ.source.toScheme) = genericPoint Ct₀.toScheme)
      (_ : ρ.hom = η ≫ ν₀ ≫ YGG.proj f κ)
      (L : LineBundle ρ.source.toVariety) (J : BasedJet f ρ L κ)
      (hnz : NormalizedTupleNowhereZero J),
      J.projectivize hnz = η ≫ ν₀ := by
  sorry

/-- Proposition 3.2 (realizing the inverse tautological class). -/
theorem inverse_tautological_class {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}
    (f : C.toScheme ⟶ X.toScheme) [MMSetup f] (κ m : ℕ)
    (hm : ∀ q ∈ Finset.Icc 1 κ, q ∣ m) [Fact ((jetAlgebra f κ).SufficientlyDivisible m)]
    -- data of Lemma 2.5
    (Γ : IntegralCurve k (YGG f κ))
    {Ct₀ : SmoothProjectiveCurve k} (ν : Ct₀.toScheme ⟶ Γ.carrier) [AlgebraicGeometry.IsFinite ν]
    (hνg : ν.base (genericPoint Ct₀.toScheme) = genericPoint Γ.carrier)
    (hνbir : functionFieldDegree ν = 1)
    (hg₀ : (ν ≫ Γ.ι ≫ YGG.proj f κ).base (genericPoint Ct₀.toScheme) = genericPoint C.toScheme)
    (hslope₀ : ((TangentBundle.pullbackDegree f : ℚ) * harmonic κ) / (2 * ((X.toVariety.dim : ℚ) + 1) * κ)
      < - (Γ.degree (polarization f κ m) : ℚ)
          / ((m : ℚ) * (functionFieldDegree (ν ≫ Γ.ι ≫ YGG.proj f κ) : ℚ)))
    -- data of Lemma 3.1
    (ρ : FiniteCover k C) (η : ρ.source.toScheme ⟶ Ct₀.toScheme) [AlgebraicGeometry.IsFinite η]
    (hηg : η.base (genericPoint ρ.source.toScheme) = genericPoint Ct₀.toScheme)
    (hρ : ρ.hom = η ≫ ν ≫ Γ.ι ≫ YGG.proj f κ)
    (L : LineBundle ρ.source.toVariety) (J : BasedJet f ρ L κ) (hnz : NormalizedTupleNowhereZero J)
    (hτ : J.projectivize hnz = η ≫ ν ≫ Γ.ι) :
    -- (i) the tautological identification τ^*O(m) ≅ L^{-m}
    Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback (η ≫ ν ≫ Γ.ι)).obj (polarization f κ m)
        ≅ (L.zpow (-(m : ℤ))).toModules) ∧
    -- (ii) the degree: deg L / deg ρ = −(H_κ·Γ) / deg ρ₀
    (L.degree : ℚ) / (ρ.degree : ℚ)
        = - (Γ.degree (polarization f κ m) : ℚ)
            / ((m : ℚ) * (functionFieldDegree (ν ≫ Γ.ι ≫ YGG.proj f κ) : ℚ)) ∧
    -- (iii) the slope bound transferred to L
    (L.degree : ℚ) / (ρ.degree : ℚ)
        > ((TangentBundle.pullbackDegree f : ℚ) * harmonic κ) / (2 * ((X.toVariety.dim : ℚ) + 1) * κ) := by
  sorry

/-- Lemma 4.1 (coefficient vanishing and nonconstant projection). -/
theorem realization_coefficients {k : Type u} [Field k] [IsAlgClosed k]
    {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}
    (f : C.toScheme ⟶ X.toScheme) [MMSetup f] (κ : ℕ)
    (ρ : FiniteCover k C) (L : LineBundle ρ.source.toVariety) (J : BasedJet f ρ L κ)
    (hnz : NormalizedTupleNowhereZero J) (hL : 0 < L.degree) :
    (∀ (ℓ : Fin (X.embDim + 1)) (q : ℕ),
      (LineBundle.pullback (X := C.toVariety) f (X.OX 1)).degree * (ρ.degree : ℤ) / L.degree < (q : ℤ) →
        J.coefficient ℓ q = 0) ∧
    ¬ J.IsGenericallyScalar ∧
    (∃ (ℓ : Fin (X.embDim + 1)) (q : ℕ), 1 ≤ q ∧ q ≤ κ ∧ J.coefficient ℓ q ≠ 0) ∧
    1 ≤ (LineBundle.pullback (X := C.toVariety) f (X.OX 1)).degree * (ρ.degree : ℤ) / L.degree := by
  sorry

/-- Theorem 4.2 with Corollary 4.3 (polynomial realization, ruled surface). -/
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
  sorry

/-- Lemma 5.1 (prescribed-point specialization). -/
theorem prescribed_point_specialization {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}
    (f : C.toScheme ⟶ X.toScheme) [f.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (ρ : FiniteCover k C) (L : LineBundle ρ.source.toVariety) (r₀ : ℕ)
    (S : SmoothProjectiveSurface k) (β : S.toScheme ⟶ (ruledSurface L).toScheme)
    (hβ : IsBlowupTower β)
    (eW : (ruledSurface L).toScheme ≅
      (AlgebraicGeometry.Scheme.projBundle
        (CategoryTheory.Limits.biprod (C := ρ.source.toVariety.toScheme.Modules)
          (show ρ.source.toVariety.toScheme.Modules from
            SheafOfModules.unit ρ.source.toVariety.toScheme.ringCatSheaf) L.toModules)).left)
    (πS : S.toScheme ⟶ ρ.source.toScheme) (hπS : AlgebraicGeometry.Surjective πS)
    (σ : ρ.source.toScheme ⟶ S.toScheme) (Φ : S.toScheme ⟶ X.toScheme)
    (hAvoid : IsBlowupTowerAvoiding β
      (Set.range (AlgebraicGeometry.Scheme.oSection L.toModules ≫ eW.inv).base))
    (hπfac : πS = β ≫ ruledSurface.π L)
    (hσπ : σ ≫ πS = CategoryTheory.CategoryStruct.id ρ.source.toScheme)
    (hσΦ : σ ≫ Φ = ρ.hom ≫ f)
    (hΦover : Φ.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)))
    (V : Set ρ.source.toScheme)
    (hVfib : ∀ y ∈ V, IsClosed ({y} : Set ρ.source.toScheme) →
      Nonempty ((πS.fiber y) ≅ (ProjectiveLine.asSmoothProjectiveCurve k).toScheme) ∧
      1 ≤ fiberDegree πS hπS (LineBundle.pullback (X := S.toVariety) Φ (X.OX 1)) y ∧
      fiberDegree πS hπS (LineBundle.pullback (X := S.toVariety) Φ (X.OX 1)) y ≤ (r₀ : ℤ))
    (y₀ : ρ.source.toScheme) (hy₀V : y₀ ∈ V) (hy₀ : IsClosed ({y₀} : Set ρ.source.toScheme))
    (y : ρ.source.toScheme) (hy : IsClosed ({y} : Set ρ.source.toScheme)) :
    ∃ b : ProjectiveLine k ⟶ X.toScheme,
      b.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) ∧
      ¬ IsConstantMorphism b ∧
      b.base (ProjectiveLine.zero k) = (ρ.hom ≫ f).base y ∧
      (LineBundle.pullback (X := (ProjectiveLine.asSmoothProjectiveCurve k).toVariety)
        b (X.OX 1)).degree ≤
        fiberDegree πS hπS (LineBundle.pullback (X := S.toVariety) Φ (X.OX 1)) y₀ ∧
      fiberDegree πS hπS (LineBundle.pullback (X := S.toVariety) Φ (X.OX 1)) y₀ ≤ (r₀ : ℤ) := by
  sorry

/-- The identity −K_X · f_*[C] = deg f^*T_X (§1). -/
theorem degree_identity {k : Type*} [Field k] [IsAlgClosed k]
    (X : SmoothProjectiveVariety k) (C : SmoothProjectiveCurve k)
    (f : C.toScheme ⟶ X.toScheme) [f.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (K : CartierDivisor X.toVariety) (hK : CartierDivisor.IsCanonical X K) :
    intersectionNumber X (-K) (curveCycleClassPushforward f)
      = VectorBundle.degree ((tangentBundle X).pullback f) := by
  sorry

end
