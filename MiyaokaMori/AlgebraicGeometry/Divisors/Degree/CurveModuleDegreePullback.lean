import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.RationalSectionDegree
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.IdealSheafCycleEqPushforward
import MiyaokaMori.AlgebraicGeometry.Morphisms.FiniteMorphismResidueFieldExtension
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.SchemeDimensionFinite
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.Stacks0ecg

/-!
# Finite pullback of the same Cartier line-module degree

Both degree relations below are `HasCurveModuleDegree`: the degree is computed from
an actual rational section of the specified module, its Cartier divisor, and the
residue-weighted degree of that divisor's zero cycle. The module in the conclusion
is the actual pullback along the given morphism over the same field.

The multiplier is `finiteMapFunctionFieldDegree` for this very morphism, using its
generic-stalk map to define the scalar action. Its finite-dimensionality follows
from finiteness of the scheme morphism. Neither normality nor separability is
required. In dimension zero the Cartier divisor cycles, and hence the degrees,
are zero; this boundary case is retained.

The proof obligation includes compatibility of the Cartier degree with finite
pullback. A proof through Euler characteristics must first compare that degree
with this same section-divisor degree; it cannot replace the degree relation.
No curve, section, or degree is chosen globally from an existence theorem.

Proof route (Stacks 02ST at the divisor level, then degree transport): pull the
rational section `s` of `M` back to `f^*M` (`rationalSectionPullback`), present it
by a Cartier divisor on `X`, and identify its zero cycle with the rational-section
divisor. Then `f_* div(f^*s) = [R(X):R(Y)] · div(s)`
(`properPushforward_rationalSectionDivisor_pullback`, which needs `X`, `Y` of the same
finite dimension: `f` is finite hence integral, dominant and proper hence surjective,
so `dim X = dim Y` by Stacks 0ECG), and the residue-weighted degree is preserved by
proper pushforward over the same base (`AlgebraicGeometry.Intersection.rawZeroCycleDegree_properPushforward`).
Finally `functionFieldDegree f = finiteMapFunctionFieldDegree f`, both being
`[R(X):R(Y)]` for the same generic stalk map.

Sources: the proof of Lemma 3.1 of the paper (normalization of the negative
horizontal curve and the subsequent finite-cover slope calculation); Stacks
Project `varieties.tex`, `lemma-degree-pullback-map-proper-curves` (Tag 0AYZ)
and `lemma-degree-birational-pullback` (Tag 0AYU), together with `chow.tex`,
`lemma-degree-vector-bundle` (Tag 0AZ3).
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry.Intersection

universe u

variable {k : Type u} [Field k]

/-- A dominant proper morphism is surjective: its image is closed (proper maps are closed)
and dense (dominance), hence everything. -/
theorem surjective_of_isDominant_of_isProper {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f] [IsDominant f] : Surjective f := by
  constructor
  have hclosed : IsClosedMap f.base := f.isClosedMap
  have hdense : DenseRange f.base := IsDominant.denseRange
  intro y
  have h : Set.range f.base = Set.univ := by
    rw [← hclosed.isClosed_range.closure_eq]
    exact hdense.closure_range
  exact Set.range_eq_univ.mp h y

/-- The topological Krull dimension of a nonempty scheme of dimension `≤ 1` is a natural number
(it is neither `⊥`, the scheme being nonempty, nor `⊤`, being bounded by `1`). -/
theorem exists_nat_topologicalKrullDim_eq_of_le_one (Z : Scheme.{u}) [Nonempty Z]
    (hZ : topologicalKrullDim Z ≤ 1) : ∃ d : ℕ, topologicalKrullDim Z = d := by
  obtain ⟨a, ha⟩ := WithBot.ne_bot_iff_exists.mp (AlgebraicGeometry.topologicalKrullDim_ne_bot Z)
  have ha1 : a ≤ 1 := by
    have : (a : WithBot ℕ∞) ≤ (1 : ℕ∞) := by rw [ha]; exact_mod_cast hZ
    exact_mod_cast this
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_le_ne_top ENat.one_ne_top ha1)
  exact ⟨n, by rw [← ha, ← hn]; rfl⟩

/-- Finite dominant pullback multiplies the same line module's Cartier degree
by the actual function-field degree, including inseparable maps and nonnormal curves. -/
theorem curveModuleDegree_pullback_finite (X Y : AlgebraicGeometry.Proj.SchemeOver k)
    [IsIntegral X.scheme] [IsIntegral Y.scheme]
    [IsProper X.toBase] [IsProper Y.toBase]
    (hX : topologicalKrullDim X.scheme ≤ 1) (hY : topologicalKrullDim Y.scheme ≤ 1)
    (f : X.scheme ⟶ Y.scheme) (hf : f ≫ Y.toBase = X.toBase) [IsFinite f] [IsDominant f]
    (M : Y.scheme.Modules) (hM : AlgebraicGeometry.Scheme.Modules.IsLocallyFreeRank Y M 1)
    {d : ℤ} (hd : HasCurveModuleDegree Y M d) :
    HasCurveModuleDegree X ((Scheme.Modules.pullback f).obj M)
      ((AlgebraicGeometry.Scheme.finiteMapFunctionFieldDegree f : ℤ) * d) := by
  rcases hd with ⟨hIntegralY, hNoetherianY, hProperY, hdimY, s, P, hdegree⟩
  letI : IsNoetherian X.scheme := properFieldScheme_isNoetherian X.toBase
  letI : IsNoetherian Y.scheme := properFieldScheme_isNoetherian Y.toBase
  let hMline : M.IsLineBundle := by
    refine ⟨fun y ↦ ?_⟩
    obtain ⟨U, hy, ⟨e⟩⟩ := hM.local_frame y
    exact ⟨U, hy, ⟨e ≪≫ AlgebraicGeometry.Divisors.LineGenericCoordinates.moduleFreeOneIsoUnit U.toScheme⟩⟩
  letI : M.IsLineBundle := hMline
  letI : ((Scheme.Modules.pullback f).obj M).IsLineBundle := inferInstance
  have hs : s ≠ 0 := by
    exact P.section_ne_zero
  have hcycY : M.rationalSectionDivisor s = (P.cartier.zeroCycle hY).1 := by
    ext x
    exact (MiyaokaMori.RationalSectionDegree.coefficient_eq_rationalSectionOrd
      Y M s P x).symm
  have hdegreeY : rawZeroCycleDegree Y.toBase (P.cartier.zeroCycle hY) = d := by
    simpa only [Subsingleton.elim hdimY hY] using hdegree
  have hsPull :
      AlgebraicGeometry.Scheme.Modules.rationalSectionPullback f
        (AlgebraicGeometry.Scheme.dominantMap_genericPoint f) M s ≠ 0 := by
    exact AlgebraicGeometry.Scheme.Modules.rationalSectionPullback_ne_zero
      f (AlgebraicGeometry.Scheme.dominantMap_genericPoint f) M s hs
  let sPull : ((Scheme.Modules.pullback f).obj M).stalk
      (genericPoint X.scheme) := AlgebraicGeometry.Scheme.Modules.rationalSectionPullback
    f (AlgebraicGeometry.Scheme.dominantMap_genericPoint f) M s
  obtain ⟨PX⟩ := AlgebraicGeometry.Divisors.LineCartierPresentationExistence.exists_lineCartierPresentation X
    ((Scheme.Modules.pullback f).obj M)
    (AlgebraicGeometry.Scheme.Modules.isLocallyFreeRank_pullback hM f) sPull hsPull
  have hcycX : ((Scheme.Modules.pullback f).obj M).rationalSectionDivisor sPull =
      (PX.cartier.zeroCycle hX).1 := by
    ext x
    exact (MiyaokaMori.RationalSectionDegree.coefficient_eq_rationalSectionOrd
      X ((Scheme.Modules.pullback f).obj M) sPull PX x).symm
  -- The 02ST divisor-level statement now asks for k-structures, k-morphism, finite type, and
  -- equal dimensions; all follow from the `SchemeOver` data and finiteness of `f`.
  letI : X.scheme.Over (Spec (CommRingCat.of k)) := ⟨X.toBase⟩
  letI : Y.scheme.Over (Spec (CommRingCat.of k)) := ⟨Y.toBase⟩
  haveI : f.IsOver (Spec (CommRingCat.of k)) := ⟨hf⟩
  haveI : LocallyOfFiniteType (X.scheme ↘ Spec (CommRingCat.of k)) :=
    inferInstanceAs (LocallyOfFiniteType X.toBase)
  haveI : LocallyOfFiniteType (Y.scheme ↘ Spec (CommRingCat.of k)) :=
    inferInstanceAs (LocallyOfFiniteType Y.toBase)
  haveI : Surjective f := surjective_of_isDominant_of_isProper f
  obtain ⟨dY, hdY⟩ := exists_nat_topologicalKrullDim_eq_of_le_one Y.scheme hY
  have hdX : topologicalKrullDim X.scheme = dY := by
    rw [AlgebraicGeometry.topologicalKrullDim_eq_of_isIntegralHom_of_surjective f]
    exact hdY
  have hpushRat := AlgebraicGeometry.Scheme.Modules.properPushforward_rationalSectionDivisor_pullback
    f (AlgebraicGeometry.Scheme.dominantMap_genericPoint f) (k := k) dY hdX hdY M s hs
  have hpush : dimensionProperPushforward f 0 (PX.cartier.zeroCycle hX) =
      DimensionCycle.zsmul (functionFieldDegree f : ℤ) (P.cartier.zeroCycle hY) := by
    apply Subtype.ext
    change AlgebraicGeometry.AlgebraicCycle.properPushforward f (PX.cartier.zeroCycle hX).1 =
      (functionFieldDegree f : ℤ) • (P.cartier.zeroCycle hY).1
    rw [← hcycX]
    simpa only [sPull, hcycY] using hpushRat
  have hdegX : rawZeroCycleDegree X.toBase (PX.cartier.zeroCycle hX) =
      (functionFieldDegree f : ℤ) * d := by
    calc
      rawZeroCycleDegree X.toBase (PX.cartier.zeroCycle hX) =
          rawZeroCycleDegree Y.toBase
            (dimensionProperPushforward f 0 (PX.cartier.zeroCycle hX)) := by
        rw [AlgebraicGeometry.Intersection.rawZeroCycleDegree_properPushforward Y.toBase f]
        simp only [hf]
      _ = rawZeroCycleDegree Y.toBase
          (DimensionCycle.zsmul (functionFieldDegree f : ℤ) (P.cartier.zeroCycle hY)) := by
        rw [hpush]
      _ = (functionFieldDegree f : ℤ) *
          rawZeroCycleDegree Y.toBase (P.cartier.zeroCycle hY) :=
        rawZeroCycleDegree_zsmul Y.toBase _ _
      _ = (functionFieldDegree f : ℤ) * d := by rw [hdegreeY]
  have hfield : functionFieldDegree f = AlgebraicGeometry.Scheme.finiteMapFunctionFieldDegree f := by
    have hff := functionFieldDegree_eq_finrank f (AlgebraicGeometry.Scheme.dominantMap_genericPoint f)
    unfold AlgebraicGeometry.Scheme.finiteMapFunctionFieldDegree
    rw [hff]
    let A1 : Algebra Y.scheme.functionField X.scheme.functionField :=
      @AlgebraicGeometry.Scheme.dominantFunctionFieldAlgebra X.scheme Y.scheme
        inferInstance inferInstance f inferInstance
    let A2 : Algebra Y.scheme.functionField X.scheme.functionField :=
      ((Y.scheme.functionFieldIsoResidueField.hom ≫
        (Y.scheme.residueFieldCongr (AlgebraicGeometry.Scheme.dominantMap_genericPoint f).symm).hom ≫
        f.residueFieldMap (genericPoint X.scheme) ≫
        X.scheme.functionFieldIsoResidueField.inv).hom.toAlgebra)
    have hmap : AlgebraicGeometry.Scheme.dominantFunctionFieldMap f =
        Y.scheme.functionFieldIsoResidueField.hom ≫
          (Y.scheme.residueFieldCongr (AlgebraicGeometry.Scheme.dominantMap_genericPoint f).symm).hom ≫
          f.residueFieldMap (genericPoint X.scheme) ≫
          X.scheme.functionFieldIsoResidueField.inv := by
      unfold AlgebraicGeometry.Scheme.dominantFunctionFieldMap
      apply (cancel_mono (X.scheme.residue (genericPoint X.scheme))).1
      simp only [Category.assoc]
      rw [← AlgebraicGeometry.Scheme.residue_residueFieldMap]
      rw [← Category.assoc]
      rw [← AlgebraicGeometry.Scheme.residue_residueFieldCongr]
      simp [AlgebraicGeometry.Scheme.functionFieldIsoResidueField]
      exact (AlgebraicGeometry.Scheme.dominantMap_genericPoint f).symm
    have hA : A2 = A1 := by
      apply Algebra.algebra_ext
      intro r
      change ((Y.scheme.functionFieldIsoResidueField.hom ≫
        (Y.scheme.residueFieldCongr (AlgebraicGeometry.Scheme.dominantMap_genericPoint f).symm).hom ≫
        f.residueFieldMap (genericPoint X.scheme) ≫
        X.scheme.functionFieldIsoResidueField.inv).hom r) =
        (AlgebraicGeometry.Scheme.dominantFunctionFieldMap f).hom r
      exact congrArg (fun q => q.hom r) hmap.symm
    change @Module.finrank Y.scheme.functionField X.scheme.functionField _ _
        (@Algebra.toModule _ _ _ _ A2) =
      @Module.finrank Y.scheme.functionField X.scheme.functionField _ _
        (@Algebra.toModule _ _ _ _ A1)
    rw [hA]
  refine ⟨inferInstance, inferInstance, inferInstance, hX, sPull, PX, ?_⟩
  simpa [hfield] using hdegX

end AlgebraicGeometry.Intersection
