import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ChowDegreeRatPushforward
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ZeroCycleDegreePushforward
import MiyaokaMori.AlgebraicGeometry.Varieties.FunctionField.AffineResidueFieldBase
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.TopSelfIntersectionCurve
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.SchemeDimensionFinite
import MiyaokaMori.AlgebraicGeometry.Chow.CapTrivialBundleZero
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorPower
import MiyaokaMori.AlgebraicGeometry.Morphisms.ProperOverField
import MiyaokaMori.AlgebraicGeometry.Varieties.Dimension.SchemeDimension
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.SchemeFundamentalCycle
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.TopSelfIntersection
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.TopSelfIntersectionIsoInvariant
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ZeroCycleDegreeScheme
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.FirstChernClassTensor

/-! # Helpers for the positivity of ample top self-intersections: mixed degrees `deg(c₁(M)^e ∩ α)`

Shared arithmetic for the induction in `AmpleTopSelfIntersectionPositive.lean`
(Stacks 0BEV, Chow form; used for Lemma 2.5 of the paper):

* `capDegree X hX M e α := deg(c₁(M)^e ∩ α)` for `α ∈ A_e(X)`, additive in `α`;
* `topSelfIntersection_eq_capDegree_firstChernClass`: for `dim X = e + 1`,
  `(M^{e+1}) = deg(c₁(M)^e ∩ (c₁(M) ∩ [X]))` (peel off one `c₁`);
* `firstChernClass_tensorPow_eq_nsmul`: `c₁(M^{⊗m}) = m · c₁(M)`;
* `capDegree_chowPushforward_fundamentalChowClass`: for a proper `ι' : Z' → Z` with `dim Z' = d`,
  `deg(c₁(M)^d ∩ ι'_*[Z']) = ((ι'^*M)^d)` (projection formula iterated
  `d` times + degree invariance under proper pushforward);
* `topSelfIntersection_pos_of_dimension_zero`: `dim W = 0`, `W` integral ⇒ `(L^0) = deg [W] > 0`.

The same lemmas exist (in namespace `MiyaokaMori.FiberedNegativeCurve`) in
`NegativeCurveViaFibration.lean`, which imports `AmpleTopSelfIntersectionPositive`; they are
repeated here, in namespace `MiyaokaMori.AmpleTopSelfIntersection`, so that the main theorem can use
them without an import cycle. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace MiyaokaMori.AmpleTopSelfIntersection

open AlgebraicGeometry

/-- Mixed degree `deg(c₁(M)^e ∩ α)`: apply the `e`-fold `c₁(M)`-cap to `α ∈ A_e(X)` and take the
degree of the resulting zero-cycle class. For `e = X.dimension` and `α = [X]` this is, by definition,
`AlgebraicGeometry.topSelfIntersection X hX M`. -/
noncomputable def capDegree {K : Type u} [Field K] (X : AlgebraicGeometry.Scheme.{u})
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of K))] (hX : IsProperOver K X)
    (M : X.Modules) [M.IsLineBundle] (e : ℕ) (α : AlgebraicGeometry.ChowGroup X e) : ℤ :=
  AlgebraicGeometry.ChowGroup.degreeOver K X hX
    (AlgebraicGeometry.firstChernClass.capPow M e 0
      (cast (congrArg (AlgebraicGeometry.ChowGroup X) (zero_add e).symm) α))

/-- In a field-proper scheme the underlying scheme is locally Noetherian (the route used inside the
definition of `topSelfIntersection`). -/
theorem isLocallyNoetherian_of_isProperOver {K : Type u} [Field K]
    (X : AlgebraicGeometry.Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (CommRingCat.of K))]
    (hX : IsProperOver K X) : AlgebraicGeometry.IsLocallyNoetherian X := by
  haveI : AlgebraicGeometry.IsProper (X ↘ AlgebraicGeometry.Spec (CommRingCat.of K)) := hX
  exact AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian
    (X ↘ AlgebraicGeometry.Spec (CommRingCat.of K))

/-- `cast` along `ChowGroup X m = ChowGroup X n` is additive. -/
private theorem cast_chow_add {X : AlgebraicGeometry.Scheme.{u}} {m n : ℕ} (h : m = n)
    (α β : AlgebraicGeometry.ChowGroup X m) :
    cast (congrArg (AlgebraicGeometry.ChowGroup X) h) (α + β) =
      cast (congrArg (AlgebraicGeometry.ChowGroup X) h) α +
        cast (congrArg (AlgebraicGeometry.ChowGroup X) h) β := by
  subst h; rfl

private theorem cast_chow_zero {X : AlgebraicGeometry.Scheme.{u}} {m n : ℕ} (h : m = n) :
    cast (congrArg (AlgebraicGeometry.ChowGroup X) h) (0 : AlgebraicGeometry.ChowGroup X m) = 0 := by
  subst h; rfl

theorem capDegree_add {K : Type u} [Field K] (X : AlgebraicGeometry.Scheme.{u})
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of K))] (hX : IsProperOver K X)
    (M : X.Modules) [M.IsLineBundle] (e : ℕ) (α β : AlgebraicGeometry.ChowGroup X e) :
    capDegree X hX M e (α + β) = capDegree X hX M e α + capDegree X hX M e β := by
  unfold capDegree
  rw [cast_chow_add (zero_add e).symm, map_add, map_add]

theorem capDegree_zero {K : Type u} [Field K] (X : AlgebraicGeometry.Scheme.{u})
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of K))] (hX : IsProperOver K X)
    (M : X.Modules) [M.IsLineBundle] (e : ℕ) :
    capDegree X hX M e 0 = 0 := by
  unfold capDegree
  rw [cast_chow_zero (zero_add e).symm, map_zero, map_zero]

theorem capDegree_nsmul {K : Type u} [Field K] (X : AlgebraicGeometry.Scheme.{u})
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of K))] (hX : IsProperOver K X)
    (M : X.Modules) [M.IsLineBundle] (e : ℕ) (n : ℕ) (α : AlgebraicGeometry.ChowGroup X e) :
    capDegree X hX M e (n • α) = n • capDegree X hX M e α := by
  induction n with
  | zero => rw [zero_smul, zero_smul, capDegree_zero]
  | succ n ih => rw [succ_nsmul, capDegree_add, ih, succ_nsmul]

/-- `cast` along `ChowGroup X m = ChowGroup X n` as an additive homomorphism. -/
private def castChowHom {X : AlgebraicGeometry.Scheme.{u}} {m n : ℕ} (h : m = n) :
    AlgebraicGeometry.ChowGroup X m →+ AlgebraicGeometry.ChowGroup X n :=
  AddMonoidHom.mk' (cast (congrArg (AlgebraicGeometry.ChowGroup X) h)) (cast_chow_add h)

/-- `capDegree X hX M e` as an additive homomorphism `A_e(X) →+ ℤ`. -/
noncomputable def capDegreeHom {K : Type u} [Field K] (X : AlgebraicGeometry.Scheme.{u})
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of K))] (hX : IsProperOver K X)
    (M : X.Modules) [M.IsLineBundle] (e : ℕ) : AlgebraicGeometry.ChowGroup X e →+ ℤ :=
  (AlgebraicGeometry.ChowGroup.degreeOver K X hX).comp
    ((AlgebraicGeometry.firstChernClass.capPow M e 0).comp (castChowHom (zero_add e).symm))

theorem capDegree_eq_capDegreeHom {K : Type u} [Field K] (X : AlgebraicGeometry.Scheme.{u})
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of K))] (hX : IsProperOver K X)
    (M : X.Modules) [M.IsLineBundle] (e : ℕ) (α : AlgebraicGeometry.ChowGroup X e) :
    capDegree X hX M e α = capDegreeHom X hX M e α := rfl

theorem capDegree_finset_sum {K : Type u} [Field K] (X : AlgebraicGeometry.Scheme.{u})
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of K))] (hX : IsProperOver K X)
    (M : X.Modules) [M.IsLineBundle] (e : ℕ) {ι : Type*} (s : Finset ι)
    (f : ι → AlgebraicGeometry.ChowGroup X e) :
    capDegree X hX M e (∑ i ∈ s, f i) = ∑ i ∈ s, capDegree X hX M e (f i) := by
  simp only [capDegree_eq_capDegreeHom, map_sum]

/-- `cast` commutes with proper pushforward (both sides transported along the same `m = n`). -/
private theorem cast_chowPushforward {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
    [AlgebraicGeometry.IsProper f] {m n : ℕ} (h : m = n) (α : AlgebraicGeometry.ChowGroup X m) :
    cast (congrArg (AlgebraicGeometry.ChowGroup Y) h) (AlgebraicGeometry.chowPushforward f m α) =
      AlgebraicGeometry.chowPushforward f n (cast (congrArg (AlgebraicGeometry.ChowGroup X) h) α) := by
  subst h; rfl

/-- **Mixed degree of a pushed-forward fundamental class = top self-intersection of the restriction**:
`ι' : Z' → Z` proper, `Z'` proper over `K` with `dim Z' = d`, then
`deg(c₁(M)^d ∩ ι'_*[Z']) = ((ι'^*M)^d)`.

Source: projection formula for `ι'` (`chowPushforward_firstChernClass_pullback`, iterated `d` times in
`chowPushforward_capPow_of_pullbackIso`) and invariance of the degree of zero-cycles under proper
pushforward (`degreeOver_chowPushforward`). -/
theorem capDegree_chowPushforward_fundamentalChowClass {K : Type u} [Field K]
    (Z : AlgebraicGeometry.Scheme.{u}) [Z.Over (AlgebraicGeometry.Spec (CommRingCat.of K))]
    (hZ : IsProperOver K Z) (M : Z.Modules) [M.IsLineBundle] (d : ℕ)
    (Z' : AlgebraicGeometry.Scheme.{u}) [Z'.Over (AlgebraicGeometry.Spec (CommRingCat.of K))]
    (hZ' : IsProperOver K Z') (ι' : Z' ⟶ Z) [ι'.IsOver (AlgebraicGeometry.Spec (CommRingCat.of K))]
    [AlgebraicGeometry.IsProper ι'] [AlgebraicGeometry.IsLocallyNoetherian Z']
    (hdim : Z'.dimension = d) :
    capDegree Z hZ M d (AlgebraicGeometry.chowPushforward ι' d (Z'.fundamentalChowClass d)) =
      AlgebraicGeometry.topSelfIntersection Z' hZ'
        ((AlgebraicGeometry.Scheme.Modules.pullback ι').obj M) := by
  haveI : AlgebraicGeometry.IsProper (Z ↘ AlgebraicGeometry.Spec (CommRingCat.of K)) := hZ
  haveI : AlgebraicGeometry.IsProper (Z' ↘ AlgebraicGeometry.Spec (CommRingCat.of K)) := hZ'
  rw [MiyaokaMori.TopSelfIntersectionCurve.topSelfIntersection_eq_of_dimension hZ' _ hdim]
  unfold capDegree
  rw [← MiyaokaMori.ChowDegreeRatPushforward.degreeOver_chowPushforward hZ' hZ ι',
    AlgebraicGeometry.chowPushforward_capPow_of_pullbackIso (k := K) ι' M
      ((AlgebraicGeometry.Scheme.Modules.pullback ι').obj M) ⟨Iso.refl _⟩ d 0,
    cast_chowPushforward ι' (zero_add d).symm]

/-- `c₁(N^{⊗n}) = n · c₁(N)` (by induction on `n`, using additivity of `c₁` under tensor products;
`n = 0` is the vanishing of `c₁(O_X)`). -/
theorem firstChernClass_tensorPow_eq_nsmul {K : Type u} [Field K] (X : AlgebraicGeometry.Scheme.{u})
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of K))] (hX : IsProperOver K X)
    (N : X.Modules) [N.IsLineBundle] (d n : ℕ) :
    AlgebraicGeometry.firstChernClass (AlgebraicGeometry.Scheme.Modules.tensorPow N n) (d + 1) =
      n • AlgebraicGeometry.firstChernClass N (d + 1) := by
  haveI : AlgebraicGeometry.IsProper (X ↘ AlgebraicGeometry.Spec (CommRingCat.of K)) := hX
  induction n with
  | zero =>
    rw [zero_smul]
    exact AlgebraicGeometry.firstChernClass_one X d
  | succ n ih =>
    rw [succ_nsmul, ← ih]
    exact AlgebraicGeometry.firstChernClass_tensor (k := K)
      (AlgebraicGeometry.Scheme.Modules.tensorPow N n) N (d + 1)

/-- `cast` commutes with `c₁ ∩ -` (indices transported along the same `m = n`). -/
private theorem cast_firstChernClass {X : AlgebraicGeometry.Scheme.{u}} (M : X.Modules)
    [M.IsLineBundle] {m n : ℕ} (h : m = n) (α : AlgebraicGeometry.ChowGroup X (m + 1)) :
    AlgebraicGeometry.firstChernClass M (n + 1)
        (cast (congrArg (AlgebraicGeometry.ChowGroup X) (congrArg (· + 1) h)) α) =
      cast (congrArg (AlgebraicGeometry.ChowGroup X) h)
        (AlgebraicGeometry.firstChernClass M (m + 1) α) := by
  subst h; rfl

/-- **Peeling off one `c₁`**: if `dim X = e + 1` then
`(M^{e+1}) = deg(c₁(M)^e ∩ (c₁(M) ∩ [X]))`. Immediate from the recursive definition of `capPow`. -/
theorem topSelfIntersection_eq_capDegree_firstChernClass {K : Type u} [Field K]
    (X : AlgebraicGeometry.Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (CommRingCat.of K))]
    (hX : IsProperOver K X) (M : X.Modules) [M.IsLineBundle] (e : ℕ)
    (hdim : X.dimension = e + 1) :
    haveI : AlgebraicGeometry.IsLocallyNoetherian X := isLocallyNoetherian_of_isProperOver X hX
    AlgebraicGeometry.topSelfIntersection X hX M =
      capDegree X hX M e
        (AlgebraicGeometry.firstChernClass M (e + 1) (X.fundamentalChowClass (e + 1))) := by
  haveI : AlgebraicGeometry.IsLocallyNoetherian X := isLocallyNoetherian_of_isProperOver X hX
  rw [MiyaokaMori.TopSelfIntersectionCurve.topSelfIntersection_eq_of_dimension hX M hdim]
  unfold capDegree
  congr 1
  show (AlgebraicGeometry.firstChernClass.capPow M e 0).comp
      (AlgebraicGeometry.firstChernClass M (0 + e + 1))
      (cast (congrArg (AlgebraicGeometry.ChowGroup X) (zero_add (e + 1)).symm)
        (X.fundamentalChowClass (e + 1))) = _
  rw [AddMonoidHom.comp_apply]
  congr 1
  exact cast_firstChernClass M (zero_add e).symm (X.fundamentalChowClass (e + 1))

/-- **Base case `d = 0`**: `W` integral, proper over `K`, `dim W = 0` ⇒ `(L^0) = deg [W] > 0`.

Proof: for `W.dimension = 0`, `topSelfIntersection W hW L` is by definition
`capPow L 0 0 = id` applied to `[W]_0`, then the degree, i.e.
`deg [W]_0`. `W` is integral and zero-dimensional, so its fundamental cycle is the cycle with
coefficient `1` at the unique point (which is both generic and closed), and
`AlgebraicCycle.degree` of it is `[κ(W) : K]`; this is finite
because `W` is proper over `K` (`W = Spec κ(W)`, `κ(W)/K` finite), and `≥ 1`. -/
theorem topSelfIntersection_pos_of_dimension_zero {K : Type u} [Field K]
    (W : AlgebraicGeometry.Scheme.{u}) [W.Over (AlgebraicGeometry.Spec (CommRingCat.of K))]
    [AlgebraicGeometry.IsIntegral W] (hW : IsProperOver K W) (hdim : W.dimension = 0)
    (L : W.Modules) [L.IsLineBundle] :
    0 < AlgebraicGeometry.topSelfIntersection W hW L := by
  classical
  haveI hprop : AlgebraicGeometry.IsProper (W ↘ AlgebraicGeometry.Spec (CommRingCat.of K)) := hW
  haveI : AlgebraicGeometry.IsLocallyNoetherian W := isLocallyNoetherian_of_isProperOver W hW
  have hirr : IrreducibleSpace W := AlgebraicGeometry.irreducibleSpace_of_isIntegral W
  haveI hne : Nonempty W := hirr.toNonempty
  have hfin : topologicalKrullDim W ≠ ⊤ :=
    AlgebraicGeometry.topologicalKrullDim_ne_top_of_isProperOver (k := K) W hW
  have h0 : topologicalKrullDim W = 0 :=
    AlgebraicGeometry.Scheme.topologicalKrullDim_eq_zero_of_dimension_eq_zero W hfin hdim
  haveI hsub : Subsingleton W := AlgebraicGeometry.subsingleton_of_topologicalKrullDim_eq_zero W h0
  rw [MiyaokaMori.TopSelfIntersectionCurve.topSelfIntersection_eq_of_dimension hW L hdim]
  change 0 < AlgebraicGeometry.AlgebraicCycle.degree (k := K) (W.fundamentalCycle 0)
  have hfund := W.fundamentalCycle_of_isIntegral hfin
  rw [hdim] at hfund
  unfold AlgebraicGeometry.AlgebraicCycle.degree
  rw [finsum_eq_single _ (genericPoint W) (fun x hx => by rw [hfund]; simp [hx]), hfund]
  simp only [if_true, one_mul]
  rw [← AlgebraicGeometry.Scheme.Hom.residueFieldDegree_eq_residueDegree]
  have hcl : IsClosed ({genericPoint W} : Set W) := by
    have huniv : ({genericPoint W} : Set W) = Set.univ :=
      Set.eq_univ_of_forall (fun y => Set.mem_singleton_iff.mpr (Subsingleton.elim y _))
    rw [huniv]
    exact isClosed_univ
  unfold AlgebraicGeometry.Intersection.residueFieldDegree
  letI : Algebra K (W.residueField (genericPoint W)) :=
    (AlgebraicGeometry.Intersection.pointBaseMap (W ↘ AlgebraicGeometry.Spec (CommRingCat.of K))
      (genericPoint W)).hom.toAlgebra
  haveI : Module.Finite K (W.residueField (genericPoint W)) :=
    AlgebraicGeometry.Intersection.pointBaseMap_finite (W ↘ AlgebraicGeometry.Spec (CommRingCat.of K))
      (genericPoint W) hcl
  exact_mod_cast Module.finrank_pos

end MiyaokaMori.AmpleTopSelfIntersection

end
