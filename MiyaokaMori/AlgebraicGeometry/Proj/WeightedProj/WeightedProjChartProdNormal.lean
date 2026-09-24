import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedProjCoordinateCover
import MiyaokaMori.AlgebraicGeometry.Varieties.Smooth.NormalScheme
import MiyaokaMori.AlgebraicGeometry.Varieties.Smooth.SpecNormalOfIntegrallyClosed
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedGradedAlgebra
import MiyaokaMori.AlgebraicGeometry.Morphisms.WeightedAwayBaseChange

/-! # Normality of the product of an affine scheme with a chart of weighted projective space

The ingredients of the purely commutative-algebraic proof that weighted projective space (and its
products with normal affine schemes) is normal — no Serre criterion, no group actions or roots of
unity, and no `[IsAlgClosed]` or `[CharZero]` hypotheses:

* `Scheme.isNormal_of_nonempty_imp`, `Scheme.IsNormal.of_iso`: two transport lemmas;
* `isIntegrallyClosed_of_Spec_isNormal`: `Spec R` normal and `R` a domain imply `R` integrally closed;
* `isNormal_pullback_Spec_of_tensor`: the fiber product of two affine schemes over an affine base
  is normal if the tensor product is an integrally closed domain;
* `weightedProjAffineChartCover`: the standard affine chart cover `D₊(x_i) = Spec k[x]_(x_i)` of
  `P(w)`;
* `weightedProjChart_prod_isNormal`: `Spec A ×_k D₊(x_i)` is normal for an integrally closed domain
  `A`. The algebraic core `A ⊗_k k[x]_(x_i) ≅ A[x]_(x_i)` is `WeightedAwayBaseChange.equiv`, and
  `A[x]` is integrally closed for arbitrary `σ` (`MvPolynomial.isIntegrallyClosed`).

The paper only needs that `U ×_k P(w)` is normal (proof of the Veronese polarization lemma).
Reference: Stacks 030A (polynomial rings over a normal ring are normal).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

attribute [local instance] MvPolynomial.weightedGradedAlgebra

noncomputable section

namespace AlgebraicGeometry

/-- The empty scheme is trivially normal, so normality may always be checked assuming the scheme is
nonempty. -/
theorem Scheme.isNormal_of_nonempty_imp {X : AlgebraicGeometry.Scheme.{u}}
    (h : Nonempty X → X.IsNormal) : X.IsNormal :=
  ⟨fun x => (h ⟨x⟩).isDomain x, fun x => (h ⟨x⟩).integrallyClosed x⟩

/-- Normality is transported along isomorphisms of schemes. -/
theorem Scheme.IsNormal.of_iso {X Y : AlgebraicGeometry.Scheme.{u}} (e : X ≅ Y)
    (hX : X.IsNormal) : Y.IsNormal := by
  constructor
  · intro y
    letI : IsDomain (X.presheaf.stalk (e.inv.base y)) := hX.isDomain _
    exact (asIso (e.inv.stalkMap y)).commRingCatIsoToRingEquiv.symm.toMulEquiv.isDomain _
  · intro y
    letI : IsIntegrallyClosed (X.presheaf.stalk (e.inv.base y)) := hX.integrallyClosed _
    exact IsIntegrallyClosed.of_equiv
      (asIso (e.inv.stalkMap y)).commRingCatIsoToRingEquiv

/-- Normality descends along open immersions to open subschemes (the stalks are isomorphic). -/
theorem Scheme.IsNormal.of_isOpenImmersion {X Y : AlgebraicGeometry.Scheme.{u}} (g : X ⟶ Y)
    [AlgebraicGeometry.IsOpenImmersion g] (hY : Y.IsNormal) : X.IsNormal := by
  constructor
  · intro x
    letI : IsDomain (Y.presheaf.stalk (g.base x)) := hY.isDomain _
    exact (asIso (g.stalkMap x)).commRingCatIsoToRingEquiv.symm.toMulEquiv.isDomain _
  · intro x
    letI : IsIntegrallyClosed (Y.presheaf.stalk (g.base x)) := hY.integrallyClosed _
    exact IsIntegrallyClosed.of_equiv (asIso (g.stalkMap x)).commRingCatIsoToRingEquiv

/-- If `Spec R` is normal and `R` is a domain, then `R` is integrally closed (integral closedness is
a local property, `IsIntegrallyClosed.of_localization_maximal`; the stalks are the localizations of
`R` at prime ideals). -/
theorem isIntegrallyClosed_of_Spec_isNormal (R : CommRingCat.{u}) [IsDomain R]
    (h : (AlgebraicGeometry.Spec R).IsNormal) : IsIntegrallyClosed R := by
  apply IsIntegrallyClosed.of_localization_maximal
  intro p _ hpm
  letI : p.IsPrime := hpm.isPrime
  letI : IsIntegrallyClosed ((AlgebraicGeometry.Spec R).presheaf.stalk
      (⟨p, hpm.isPrime⟩ : PrimeSpectrum R)) :=
    h.integrallyClosed _
  exact IsIntegrallyClosed.of_equiv
    (AlgebraicGeometry.Spec.stalkIso R (⟨p, hpm.isPrime⟩ : PrimeSpectrum R)).commRingCatIsoToRingEquiv

/-- The fiber product of two affine schemes over an affine base is `Spec` of the tensor product; so
if the tensor product is an integrally closed domain, the fiber product is normal. -/
theorem isNormal_pullback_Spec_of_tensor {R A B : CommRingCat.{u}} (a : R ⟶ A) (b : R ⟶ B)
    (hdom : letI := a.hom.toAlgebra; letI := b.hom.toAlgebra;
      IsDomain (TensorProduct R A B))
    (hic : letI := a.hom.toAlgebra; letI := b.hom.toAlgebra;
      IsIntegrallyClosed (TensorProduct R A B)) :
    (CategoryTheory.Limits.pullback (AlgebraicGeometry.Spec.map a)
      (AlgebraicGeometry.Spec.map b)).IsNormal := by
  letI := a.hom.toAlgebra
  letI := b.hom.toAlgebra
  letI : IsDomain (TensorProduct R A B) := hdom
  letI : IsIntegrallyClosed (TensorProduct R A B) := hic
  have ha : CommRingCat.ofHom (algebraMap (R : Type u) (A : Type u)) = a := by
    rw [RingHom.algebraMap_toAlgebra]; rfl
  have hb : CommRingCat.ofHom (algebraMap (R : Type u) (B : Type u)) = b := by
    rw [RingHom.algebraMap_toAlgebra]; rfl
  rw [← ha, ← hb]
  exact Scheme.IsNormal.of_iso (AlgebraicGeometry.pullbackSpecIso (R : Type u) A B).symm
    (AlgebraicGeometry.Spec_isNormal_of_isIntegrallyClosed _)

section Chart

variable (k : Type u) [Field k] {σ : Type u} (w : σ → ℕ) (hw : ∀ i, 0 < w i)

/-- A coordinate variable lies in the homogeneous component of its own weight. -/
theorem weightedProj_X_mem (i : σ) :
    MvPolynomial.X i ∈ MiyaokaMori.WeightedJets.weightedPolynomialGrading k
      (fun j : σ => (⟨w j, hw j⟩ : ℕ+)) (w i) :=
  (MvPolynomial.mem_weightedHomogeneousSubmodule k _ _ _).mpr
    (MvPolynomial.isWeightedHomogeneous_X k (fun j : σ => (w j : ℕ)) i)

/-- The standard affine chart cover of `P(w)`: `D₊(x_i) = Spec k[x]_(x_i)` (the coordinate charts of
Dolgachev, *Weighted projective varieties*, 1.3.3; the covering property is
`exists_mem_weightedCoordinateOpen`). -/
def weightedProjAffineChartCover : (weightedProjectiveSpace k w hw).AffineOpenCover where
  I₀ := σ
  X i := CommRingCat.of (HomogeneousLocalization.Away
    (MiyaokaMori.WeightedJets.weightedPolynomialGrading k (fun j : σ => (⟨w j, hw j⟩ : ℕ+)))
    (MvPolynomial.X i))
  f i := AlgebraicGeometry.Proj.awayι _ (MvPolynomial.X i) (weightedProj_X_mem k w hw i) (hw i)
  map_prop i := by
    show AlgebraicGeometry.IsOpenImmersion
      (AlgebraicGeometry.Proj.awayι _ (MvPolynomial.X i) (weightedProj_X_mem k w hw i) (hw i))
    infer_instance
  idx x := (MiyaokaMori.WeightedJets.exists_mem_weightedCoordinateOpen k
    (fun j : σ => (⟨w j, hw j⟩ : ℕ+)) x).choose
  covers x := by
    show x ∈ (AlgebraicGeometry.Proj.awayι _ _ _ _).opensRange
    rw [AlgebraicGeometry.Proj.opensRange_awayι]
    exact (MiyaokaMori.WeightedJets.exists_mem_weightedCoordinateOpen k
      (fun j : σ => (⟨w j, hw j⟩ : ℕ+)) x).choose_spec

/-- **Normality of `Spec A ×_k D₊(x_i)`**: if `A` is an integrally closed domain over `k`, then
`Spec A ×_k D₊(x_i)` is normal.

Proof:
1. `D₊(x_i) = Spec B_k` with `B_k := k[x]_(x_i) = HomogeneousLocalization.Away 𝒜_k (x_i)`, and the
   structure morphism `D₊(x_i) → Spec k` is `Spec` of `k → (𝒜_k)₀ → B_k` (`Proj.awayι_toSpecZero`).
2. Hence `Spec A ×_k D₊(x_i) ≅ Spec (A ⊗_k B_k)` (`pullbackSpecIso`).
3. `A ⊗_k B_k ≅ B_A := HomogeneousLocalization.Away 𝒜_A (x_i)`, where `𝒜_A` is the grading of the
   same weights on `A[x]`: `A` is free as a `k`-module, so `A ⊗_k −` commutes with direct sums and
   preserves injections; `A ⊗_k k[x]_{x_i} ≅ A[x]_{x_i}` (`MvPolynomial.algebraTensorAlgEquiv` and
   base change of localizations), this isomorphism is graded (`A` in degree `0`), and one takes the
   degree-zero parts. This is `WeightedAwayBaseChange.equiv` (injectivity from flatness of `A` over
   the field `k` and a left inverse of `Ψ : A ⊗_k k[x]_{x_i} → A[x]_{x_i}`, surjectivity from the
   decomposition into monomials).
4. `A[x] = MvPolynomial σ A` is an integrally closed domain (`MvPolynomial.isIntegrallyClosed` for
   arbitrary `σ` — the statement has no `[Finite σ]` — and `MvPolynomial.instIsDomain`).
5. `B_A` is integrally closed (`HomogeneousLocalization.Away.isIntegrallyClosed_of_isIntegrallyClosed`)
   and a domain (`HomogeneousLocalization.Away.isDomain`).
6. Transport back to `A ⊗_k B_k` along the isomorphism of step 3 and apply
   `isNormal_pullback_Spec_of_tensor`.

Edge cases: for `σ` empty, `P(w)` is empty and there is no `D₊(x_i)` (excluded by `i : σ`); the zero
ring `A` is excluded by `IsDomain A`; `k` need not be algebraically closed or of characteristic
zero — this is the advantage of this route over the quotient-group argument of Dolgachev. -/
theorem weightedProjChart_prod_isNormal (i : σ) (A : CommRingCat.{u}) [IsDomain A]
    [IsIntegrallyClosed A] (a : CommRingCat.of k ⟶ A) :
    (CategoryTheory.Limits.pullback (AlgebraicGeometry.Spec.map a)
      ((weightedProjAffineChartCover k w hw).f i ≫
        (weightedProjectiveSpace k w hw ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).IsNormal := by
  -- Step 1: the chart's structure morphism is `Spec` of `k → (𝒜_k)₀ → k[x]_(x_i)`.
  have hcomp : (weightedProjAffineChartCover k w hw).f i ≫
      (weightedProjectiveSpace k w hw ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      AlgebraicGeometry.Spec.map (CommRingCat.ofHom
        ((HomogeneousLocalization.fromZeroRingHom
          (MiyaokaMori.WeightedJets.weightedPolynomialGrading k (fun j : σ => (⟨w j, hw j⟩ : ℕ+)))
          (Submonoid.powers (MvPolynomial.X i))).comp
        (algebraMap k (MiyaokaMori.WeightedJets.weightedPolynomialGrading k
          (fun j : σ => (⟨w j, hw j⟩ : ℕ+)) 0)))) := by
    show AlgebraicGeometry.Proj.awayι _ (MvPolynomial.X i) (weightedProj_X_mem k w hw i) (hw i) ≫
      (AlgebraicGeometry.Proj.toSpecZero _ ≫ AlgebraicGeometry.Spec.map (CommRingCat.ofHom
        (algebraMap k (MiyaokaMori.WeightedJets.weightedPolynomialGrading k
          (fun j : σ => (⟨w j, hw j⟩ : ℕ+)) 0)))) = _
    rw [← Category.assoc, AlgebraicGeometry.Proj.awayι_toSpecZero, ← AlgebraicGeometry.Spec.map_comp]
    rfl
  rw [hcomp]
  -- Steps 2–6: the fibre product is `Spec (A ⊗_k k[x]_(x_i))`, and `A ⊗_k k[x]_(x_i) ≅ A[x]_(x_i)`
  -- is an integrally closed domain (`WeightedAwayBaseChange`).
  apply isNormal_pullback_Spec_of_tensor
  all_goals
    letI : Algebra k A := a.hom.toAlgebra
    letI : Algebra k (HomogeneousLocalization.Away
        (MvPolynomial.weightedHomogeneousSubmodule k (fun j : σ => ((⟨w j, hw j⟩ : ℕ+) : ℕ)))
        (MvPolynomial.X i)) :=
      (CommRingCat.ofHom
        ((HomogeneousLocalization.fromZeroRingHom
          (MiyaokaMori.WeightedJets.weightedPolynomialGrading k (fun j : σ => (⟨w j, hw j⟩ : ℕ+)))
          (Submonoid.powers (MvPolynomial.X i))).comp
        (algebraMap k (MiyaokaMori.WeightedJets.weightedPolynomialGrading k
          (fun j : σ => (⟨w j, hw j⟩ : ℕ+)) 0)))).hom.toAlgebra
  · exact WeightedAwayBaseChange.tensor_isDomain k (fun j : σ => ((⟨w j, hw j⟩ : ℕ+) : ℕ)) A i rfl
  · exact WeightedAwayBaseChange.tensor_isIntegrallyClosed k
      (fun j : σ => ((⟨w j, hw j⟩ : ℕ+) : ℕ)) A i rfl (hw i)

end Chart

end AlgebraicGeometry

end
