import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ChowDegreeRatPushforward
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleTrivialOfDiscrete
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.AmpleTopSelfIntersectionPositive
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.FiberedTwistCapDegreeLeaves
import MiyaokaMori.AlgebraicGeometry.Morphisms.CurveInFiberFactors
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.CurveToCurveSurjectiveOrConstant
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.ZeroSchemeOfCurveSectionDiscrete
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.PointDivisor
import MiyaokaMori.AlgebraicGeometry.Chow.Cycles.PointClosurePushforwardSingle
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierDivisorLocalData
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.FiberDivisorPullback
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.SmoothProjectiveCurveIntegral
import MiyaokaMori.AlgebraicGeometry.Divisors.Cartier.CartierLocalDataPullback
import MiyaokaMori.AlgebraicGeometry.Divisors.LineBundle.DivisorLineBundleIsSheaf
import MiyaokaMori.AlgebraicGeometry.Divisors.LineBundle.DivisorLineBundleGenericSection
import MiyaokaMori.Paper.S3PositiveLine.NegativeCurve.NegativeCurveViaFibrationBigSectionLeaves
import MiyaokaMori.AlgebraicGeometry.Modules.Ample.IsAmpleOfIso
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorPowCanonicalIso
import MiyaokaMori.AlgebraicGeometry.Modules.Stacks0892_TensorPowIsos

/-! # A negative curve via the fibration, without nef / Kleiman / Nakai

**What this replaces.** The proof of Lemma 2.5 of the paper needs one thing: on `Y = YGG f κ`,
from the negativity of the top self-intersection of the line bundle `M = shiftedBundle f κ m p₀ a b`, produce an
integral curve `Γ ⊂ Y` with `deg(M|_Γ) < 0`. The standard route goes through Kleiman's theorem and the
characterization of big line bundles (Lazarsfeld, *Positivity in Algebraic Geometry I*, Thm 1.4.9 and Thm 1.2.23).

This file gives another route that **only uses the structure of the fibration `π : Y → C`**: nef classes,
Kleiman's theorem and the Nakai–Moishezon criterion never appear; the only positivity facts used are

* Serre vanishing;
* an ample bundle stays ample when restricted to a closed subscheme;
* an ample line bundle has positive top self-intersection on a positive-dimensional integral closed subscheme
  (the "only if" direction of the Nakai criterion);
* the Snapper polynomial;
* the cycle-theoretic representation of an effective divisor (Fulton, *Intersection Theory*, §2.3).

**The general lemma (Lemma K′).** `k` algebraically closed, `C` a smooth projective curve, `p₀ ∈ C` a closed point,
`F := π^*O_C(p₀)`. `V` is an integral proper scheme over `k`, `π : V → C` a `k`-morphism, `B` a line bundle on `V`.
Take moreover **an ample line bundle `A` on `C` with a nonzero global section `s_A`**, and assume `A₀ := B ⊗ π^*A`
ample (on `YGG` this is provided by Stacks 0892(1)). Put `M := B^{⊗e_B} ⊗ F^{⊗e_F}` (`e_B > 0`, `e_F ≥ 0`). If
`(M^{dim V}) < 0`, there is an integral curve `Γ ⊂ V` with `deg(M|_Γ) < 0`.

**Why the auxiliary bundle is `A` rather than `O_C(p₀)`**: the shape of `M` is fixed by the paper and must use
`O_C(p₀)`; but the **auxiliary** ample bundle, and the divisor used in the step "big ⇒ has a section", need not be
`O_C(p₀)`. Taking an ample `A` directly from the projectivity of `C` (`isProjectiveOver_iff_isProper_and_isAmple`)
avoids the fact "`O_C(p₀)` is ample" entirely — that fact would require Riemann–Roch and Serre duality on curves.
The price is that the "fiber restriction sequence" of step 4 becomes the restriction to the zero scheme
`Z := Z(π^*s_A)` (`= π^{-1}(Z(s_A))`, where `Z(s_A) ⊂ C` is a finite closed subscheme, possibly with several points
and non-reduced), so one new fact is needed: **a line bundle restricted to the zero scheme of one of its own
sections is trivial** (the zero scheme is a finite scheme, and invertible modules over local rings are free). The
intersection-number step is unaffected: in step 5 of `exists_negative_component_of_fibered` the quantity
`w' := (B^{r−1}·π^*A)` cancels completely from the nonemptiness condition of the interval, exactly as with a single
fiber.

**Proof (strong induction on `r = dim V`, see `exists_integralCurve_degree_neg_of_fibered`).**
* `r = 0`: the degree of an integral zero-dimensional proper scheme is `[κ(V):k] > 0`, contradicting `(M^0) < 0`.
* `r = 1`: `V` itself is an integral curve (`ι = 𝟙`) and `deg(M|_V) = (M^1) < 0`.
* `r ≥ 2`: if `π(V)` is a point, then `F|_V` and `(π^*A)|_V` are trivial, `M|_V ≅ (A₀|_V)^{⊗e_B}`, and the top
  self-intersection is `e_B^r·(A₀^r) > 0`, a contradiction; so `π` is surjective. Then
  (`exists_negative_component_of_fibered`) an intersection-number computation produces a "big" line bundle
  `L := B^{⊗b} ⊗ (π^*A)^{⊗a}` with `(L^r) > 0` and `(M^{r−1}·L) < 0`; the restriction sequence along `Z` and Serre
  vanishing show that some positive power of `L` has a nonzero global section `σ`; the zero divisor
  `Z(σ) = Σ m_i[V_i]` (`m_i > 0`, `V_i` integral of dimension `r−1`) satisfies `deg(c₁(M)^{r−1} ∩ [Z(σ)]) < 0`, so
  some `V_i` has `((M|_{V_i})^{r−1}) < 0`; apply the induction hypothesis to `V_i`.

**Sources**: step 4 (a big line bundle has a section) follows Lazarsfeld, Thm 1.2.23, Step 1 (pp. 34–35); steps 3
and 5 are the standard operations of Fulton §2.3–2.5.

Since `e_F ≥ 0` and `(M^r) < 0` give `Λ := −(B^r) > 0` at once, the left end of the interval in step 5 is positive,
so **`a` can be taken to be a positive natural number**; hence only `tensorPow` (natural powers) is used, and no
isomorphism between `L ^ (p : ℤ)` and `tensorPow` is needed.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace MiyaokaMori.FiberedNegativeCurve

open AlgebraicGeometry

attribute [local instance] AlgebraicGeometry.Scheme.isLocallyNoetherian_pointClosure

/-! ## Notation -/

/-- `O_C(p₀)` (the paper's `F_C`). An `abbrev`, so that the spellings of `shiftedBundle` and `fiberedTwist` are
definitionally interchangeable. -/
noncomputable abbrev pointBundle {K : Type u} [Field K] {C : SmoothProjectiveCurve K}
    (p₀ : C.toScheme) : C.toScheme.Modules :=
  (Divisor.ofPoint p₀).lineBundle.toModules

/-- The line bundle `B^{⊗eB} ⊗ (π^*N)^{⊗eN}` in the fibration setting (`N` a line bundle on the base curve `C`).

`shiftedBundle f κ m p₀ a b` is by definition
`fiberedTwist (YGG.proj f κ) (polarization f κ m) (pointBundle p₀) b (m * a)`. -/
noncomputable def fiberedTwist {K : Type u} [Field K] {C : SmoothProjectiveCurve K}
    {V : AlgebraicGeometry.Scheme.{u}} (π : V ⟶ C.toScheme) (B : V.Modules)
    (N : C.toScheme.Modules) (eB eN : ℕ) : V.Modules :=
  AlgebraicGeometry.Scheme.Modules.tensor
    (AlgebraicGeometry.Scheme.Modules.tensorPow B eB)
    (AlgebraicGeometry.Scheme.Modules.tensorPow
      ((AlgebraicGeometry.Scheme.Modules.pullback π).obj N) eN)

instance fiberedTwist_isLineBundle {K : Type u} [Field K] {C : SmoothProjectiveCurve K}
    {V : AlgebraicGeometry.Scheme.{u}} (π : V ⟶ C.toScheme) (B : V.Modules) [B.IsLineBundle]
    (N : C.toScheme.Modules) [N.IsLineBundle] (eB eN : ℕ) :
    (fiberedTwist π B N eB eN).IsLineBundle := by
  change (AlgebraicGeometry.Scheme.Modules.tensor
    (AlgebraicGeometry.Scheme.Modules.tensorPow B eB)
    (AlgebraicGeometry.Scheme.Modules.tensorPow
      ((AlgebraicGeometry.Scheme.Modules.pullback π).obj N) eN)).IsLineBundle
  infer_instance

/-- The mixed intersection number `deg(c₁(M)^e ∩ α)`: apply `e` times the `c₁(M)`-cap to the `e`-dimensional Chow
class `α`, then take the degree of the zero-dimensional class. For `e = X.dimension` and `α = [X]` this is by
definition `AlgebraicGeometry.topSelfIntersection X hX M`. -/
noncomputable def capDegree {K : Type u} [Field K] (X : AlgebraicGeometry.Scheme.{u})
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of K))] (hX : IsProperOver K X)
    (M : X.Modules) [M.IsLineBundle] (e : ℕ) (α : AlgebraicGeometry.ChowGroup X e) : ℤ :=
  AlgebraicGeometry.ChowGroup.degreeOver K X hX
    (AlgebraicGeometry.firstChernClass.capPow M e 0
      (cast (congrArg (AlgebraicGeometry.ChowGroup X) (zero_add e).symm) α))

/-! ## Dependence on the isomorphism class only (private copies, to keep the imports of this file small) -/

private theorem capPow_congr {X : AlgebraicGeometry.Scheme.{u}}
    (L L' : X.Modules) [L.IsLineBundle] [L'.IsLineBundle] (e : L ≅ L') :
    ∀ (n d : ℕ), AlgebraicGeometry.firstChernClass.capPow L n d =
      AlgebraicGeometry.firstChernClass.capPow L' n d
  | 0, _ => rfl
  | n + 1, d => by
    show (AlgebraicGeometry.firstChernClass.capPow L n d).comp
        (AlgebraicGeometry.firstChernClass L (d + n + 1)) =
      (AlgebraicGeometry.firstChernClass.capPow L' n d).comp
        (AlgebraicGeometry.firstChernClass L' (d + n + 1))
    rw [capPow_congr L L' e n d, AlgebraicGeometry.firstChernClass_congr L L' e (d + n)]

/-- The top self-intersection depends only on the isomorphism class of the line bundle. -/
theorem topSelfIntersection_congr {K : Type u} [Field K]
    (X : AlgebraicGeometry.Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (CommRingCat.of K))]
    (hX : IsProperOver K X) (L L' : X.Modules) [L.IsLineBundle] [L'.IsLineBundle] (e : L ≅ L') :
    AlgebraicGeometry.topSelfIntersection X hX L =
      AlgebraicGeometry.topSelfIntersection X hX L' := by
  unfold AlgebraicGeometry.topSelfIntersection
  rw [capPow_congr L L' e]

/-- Proper over a field ⇒ locally Noetherian (the same route as in the body of `topSelfIntersection`). -/
theorem isLocallyNoetherian_of_isProperOver {K : Type u} [Field K]
    (X : AlgebraicGeometry.Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (CommRingCat.of K))]
    (hX : IsProperOver K X) : AlgebraicGeometry.IsLocallyNoetherian X := by
  haveI : AlgebraicGeometry.IsProper (X ↘ AlgebraicGeometry.Spec (CommRingCat.of K)) := hX
  exact AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian
    (X ↘ AlgebraicGeometry.Spec (CommRingCat.of K))

/-- Pullback along a composite of closed immersions: `(ι' ≫ ι)^*L` and `ι'^*(ι^*L)` have the same top self-intersection (`Modules.pullbackComp`). -/
theorem topSelfIntersection_pullback_comp {K : Type u} [Field K]
    {V W : AlgebraicGeometry.Scheme.{u}} (Z : AlgebraicGeometry.Scheme.{u})
    [Z.Over (AlgebraicGeometry.Spec (CommRingCat.of K))] (hZ : IsProperOver K Z)
    (ι' : Z ⟶ W) (ι : W ⟶ V) (L : V.Modules) [L.IsLineBundle] :
    AlgebraicGeometry.topSelfIntersection Z hZ
        ((AlgebraicGeometry.Scheme.Modules.pullback (ι' ≫ ι)).obj L) =
      AlgebraicGeometry.topSelfIntersection Z hZ
        ((AlgebraicGeometry.Scheme.Modules.pullback ι').obj
          ((AlgebraicGeometry.Scheme.Modules.pullback ι).obj L)) := by
  have e : (AlgebraicGeometry.Scheme.Modules.pullback ι').obj
      ((AlgebraicGeometry.Scheme.Modules.pullback ι).obj L) ≅
      (AlgebraicGeometry.Scheme.Modules.pullback (ι' ≫ ι)).obj L :=
    (AlgebraicGeometry.Scheme.Modules.pullbackComp ι' ι).app L
  exact (topSelfIntersection_congr Z hZ _ _ e).symm

/-! ## General lemmas: additivity of `capDegree`, homogeneity in tensor powers, triviality inside a fiber -/

/-- `cast` along `ChowGroup X m = ChowGroup X n` preserves addition. -/
private theorem cast_chow_add {X : AlgebraicGeometry.Scheme.{u}} {m n : ℕ} (h : m = n)
    (α β : AlgebraicGeometry.ChowGroup X m) :
    cast (congrArg (AlgebraicGeometry.ChowGroup X) h) (α + β) =
      cast (congrArg (AlgebraicGeometry.ChowGroup X) h) α +
        cast (congrArg (AlgebraicGeometry.ChowGroup X) h) β := by
  subst h; rfl

private theorem cast_chow_zero {X : AlgebraicGeometry.Scheme.{u}} {m n : ℕ} (h : m = n) :
    cast (congrArg (AlgebraicGeometry.ChowGroup X) h) (0 : AlgebraicGeometry.ChowGroup X m) = 0 := by
  subst h; rfl

/-- `capDegree X hX M e` is additive in the Chow class. -/
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

/-- `cast` along `ChowGroup X m = ChowGroup X n`, as an additive homomorphism. -/
private def castChowHom {X : AlgebraicGeometry.Scheme.{u}} {m n : ℕ} (h : m = n) :
    AlgebraicGeometry.ChowGroup X m →+ AlgebraicGeometry.ChowGroup X n :=
  AddMonoidHom.mk' (cast (congrArg (AlgebraicGeometry.ChowGroup X) h)) (cast_chow_add h)

/-- `capDegree X hX M e` as an additive homomorphism `ChowGroup X e →+ ℤ`. -/
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

/-- `cast` commutes with proper pushforward (both sides are transported along the same `m = n`). -/
private theorem cast_chowPushforward {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y)
    [AlgebraicGeometry.IsProper f] {m n : ℕ} (h : m = n) (α : AlgebraicGeometry.ChowGroup X m) :
    cast (congrArg (AlgebraicGeometry.ChowGroup Y) h) (AlgebraicGeometry.chowPushforward f m α) =
      AlgebraicGeometry.chowPushforward f n (cast (congrArg (AlgebraicGeometry.ChowGroup X) h) α) := by
  subst h; rfl

/-- **Mixed intersection number of the fundamental class of a closed subscheme = top self-intersection of the
restricted bundle**: for `ι' : Z' → Z` proper, `Z'` proper over `K` and `dim Z' = d`,
`deg(c₁(M)^d ∩ ι'_*[Z']) = ((ι'^*M)^d)`.

**Source**: the projection formula for closed immersions (`chowPushforward_firstChernClass_pullback`, iterated `d`
times in `chowPushforward_capPow_of_pullbackIso`) and invariance of the degree under proper pushforward
(`degreeOver_chowPushforward`). -/
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

/-- `c₁(N^{⊗n}) = n · c₁(N)` (induction on `tensorPow` with `firstChernClass_tensor`; `n = 0` uses `firstChernClass_one`). -/
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

/-- `c₁(L) = m·c₁(L')` (in every dimension) ⇒ `capPow L n d = m^n • capPow L' n d`
(a private copy of `WeightedProjOneTwistTopDegree.capPow_nsmul_of_firstChernClass_nsmul`, to keep the imports of
this file small). -/
private theorem capPow_nsmul_of_c1_nsmul {X : AlgebraicGeometry.Scheme.{u}}
    (L L' : X.Modules) [L.IsLineBundle] [L'.IsLineBundle] (m : ℕ)
    (h : ∀ d : ℕ, AlgebraicGeometry.firstChernClass L (d + 1) =
      m • AlgebraicGeometry.firstChernClass L' (d + 1)) :
    ∀ (n d : ℕ), AlgebraicGeometry.firstChernClass.capPow L n d =
      m ^ n • AlgebraicGeometry.firstChernClass.capPow L' n d
  | 0, _ => by simp [AlgebraicGeometry.firstChernClass.capPow]
  | n + 1, d => by
    show (AlgebraicGeometry.firstChernClass.capPow L n d).comp
        (AlgebraicGeometry.firstChernClass L (d + n + 1)) =
      m ^ (n + 1) • (AlgebraicGeometry.firstChernClass.capPow L' n d).comp
        (AlgebraicGeometry.firstChernClass L' (d + n + 1))
    rw [capPow_nsmul_of_c1_nsmul L L' m h n d, h (d + n)]
    ext x
    simp only [AddMonoidHom.comp_apply, AddMonoidHom.nsmul_apply, map_nsmul, pow_succ, mul_nsmul]

/-- Homogeneity of the top self-intersection in tensor powers: `((L^{⊗m})^r) = m^r · (L^r)`, `r = dim X`. -/
theorem topSelfIntersection_tensorPow {K : Type u} [Field K] (X : AlgebraicGeometry.Scheme.{u})
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of K))] (hX : IsProperOver K X)
    (L : X.Modules) [L.IsLineBundle] (m : ℕ) :
    AlgebraicGeometry.topSelfIntersection X hX (AlgebraicGeometry.Scheme.Modules.tensorPow L m) =
      (m : ℤ) ^ X.dimension * AlgebraicGeometry.topSelfIntersection X hX L := by
  unfold AlgebraicGeometry.topSelfIntersection
  rw [capPow_nsmul_of_c1_nsmul _ L m (fun d => firstChernClass_tensorPow_eq_nsmul X hX L d m),
    AddMonoidHom.nsmul_apply, map_nsmul]
  simp

/-- If `ι^*(π^*N)` is trivial, then `ι^*(fiberedTwist π B N eB eN) ≅ (ι^*B)^{⊗eB}`
(pullback commutes with `tensor`/`tensorPow`: Stacks 01CD; `O^{⊗eN} ≅ O`; right unitor). -/
noncomputable def pullbackFiberedTwistIsoOfTrivial {K : Type u} [Field K] {C : SmoothProjectiveCurve K}
    {V W : AlgebraicGeometry.Scheme.{u}} (π : V ⟶ C.toScheme) (B : V.Modules)
    (N : C.toScheme.Modules) (eB eN : ℕ) (ι : W ⟶ V)
    (eN' : (AlgebraicGeometry.Scheme.Modules.pullback ι).obj
        ((AlgebraicGeometry.Scheme.Modules.pullback π).obj N) ≅
      SheafOfModules.unit W.ringCatSheaf) :
    (AlgebraicGeometry.Scheme.Modules.pullback ι).obj (fiberedTwist π B N eB eN) ≅
      AlgebraicGeometry.Scheme.Modules.tensorPow
        ((AlgebraicGeometry.Scheme.Modules.pullback ι).obj B) eB :=
  (show (AlgebraicGeometry.Scheme.Modules.pullback ι).obj (fiberedTwist π B N eB eN) ≅
      (AlgebraicGeometry.Scheme.Modules.pullback ι).obj
        (AlgebraicGeometry.Scheme.Modules.tensor
          (AlgebraicGeometry.Scheme.Modules.tensorPow B eB)
          (AlgebraicGeometry.Scheme.Modules.tensorPow
            ((AlgebraicGeometry.Scheme.Modules.pullback π).obj N) eN)) from Iso.refl _) ≪≫
  AlgebraicGeometry.Scheme.Modules.pullbackTensorIso ι _ _ ≪≫
  AlgebraicGeometry.Scheme.Modules.tensorCongrLeftIso
    (AlgebraicGeometry.Scheme.Modules.pullbackTensorPowIso ι B eB) _ ≪≫
  AlgebraicGeometry.Scheme.Modules.tensorCongrRightIso _
    (AlgebraicGeometry.Scheme.Modules.pullbackTensorPowIso ι
        ((AlgebraicGeometry.Scheme.Modules.pullback π).obj N) eN ≪≫
      AlgebraicGeometry.Scheme.Modules.tensorPowMapIso eN' eN ≪≫
      AlgebraicGeometry.Scheme.Modules.unitTensorPowIso W eN) ≪≫
  AlgebraicGeometry.Scheme.Modules.tensorUnitIso _

/-- On a subscheme `ι : W → V` lying in a fiber `π^{-1}(c)` (i.e. the image of `ι ≫ π` is contained in the closed
point `{c}`), every line bundle pulled back from `C` is trivial. -/
theorem pullback_pullback_iso_unit_of_range_subset {K : Type u} [Field K]
    {C : SmoothProjectiveCurve K} {V W : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsReduced W] (π : V ⟶ C.toScheme) (ι : W ⟶ V)
    [AlgebraicGeometry.IsClosedImmersion ι] (c : C.toScheme)
    (hc : IsClosed ({c} : Set C.toScheme)) (hrange : Set.range (ι ≫ π).base ⊆ {c})
    (N : C.toScheme.Modules) [N.IsLineBundle] :
    Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback ι).obj
        ((AlgebraicGeometry.Scheme.Modules.pullback π).obj N) ≅
      SheafOfModules.unit W.ringCatSheaf) := by
  obtain ⟨j, hj, hjι⟩ :=
    AlgebraicGeometry.exists_closedImmersion_to_fiber_of_range_subset ι π c hc hrange
  obtain ⟨e⟩ := AlgebraicGeometry.pullback_fiberι_pullback_iso_unit π N c
  exact ⟨(AlgebraicGeometry.Scheme.Modules.pullbackCongr hjι.symm).app _ ≪≫
    ((AlgebraicGeometry.Scheme.Modules.pullbackComp j (π.fiberι c)).app _).symm ≪≫
    (AlgebraicGeometry.Scheme.Modules.pullback j).mapIso e ≪≫
    AlgebraicGeometry.Scheme.Modules.pullbackUnitIso j⟩

/-! ## The ingredients -/

/-- **D0, the zero-dimensional case**: on an integral, proper, zero-dimensional scheme over `K`, the top
self-intersection of any line bundle is positive.

**Source**: Fulton §1.4.

**Proof**: for `W.dimension = 0`, `topSelfIntersection W hW L` is by definition `capPow L 0 0` applied to `[W]_0`
followed by the degree, and `capPow L 0 0 = AddMonoidHom.id`, so it is `deg [W]_0`. `W` is integral and
zero-dimensional, so its fundamental cycle is the cycle with value `1` at the unique point (both generic and closed),
and `AlgebraicCycle.degree` at this point is `[κ(W) : K]`; `κ(W)` is a finite extension of `K` (`W` proper and
zero-dimensional over `K` ⇒ `W = Spec κ(W)` with `κ(W)/K` finite), so `deg [W] = [κ(W):K] ≥ 1 > 0`. (For `K`
algebraically closed this is `1`; algebraic closedness is not needed.)

**Edge cases**: `W` is nonempty by `IsIntegral`; `L` is arbitrary, since `capPow L 0 0` does not depend on `L`. -/
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
  -- top self-intersection = deg [W]_0
  rw [MiyaokaMori.TopSelfIntersectionCurve.topSelfIntersection_eq_of_dimension hW L hdim]
  change 0 < AlgebraicGeometry.AlgebraicCycle.degree (k := K) (W.fundamentalCycle 0)
  have hfund := W.fundamentalCycle_of_isIntegral hfin
  rw [hdim] at hfund
  unfold AlgebraicGeometry.AlgebraicCycle.degree
  rw [finsum_eq_single _ (genericPoint W) (fun x hx => by rw [hfund]; simp [hx]), hfund]
  simp only [if_true, one_mul]
  -- the residue degree [κ(W) : K] at the generic (unique) point is finite and positive
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

/-- **D1, the one-dimensional case**: a one-dimensional integral closed subscheme `ι : W ↪ V` of `V` is itself an
integral curve in `V`, and its degree `Γ.degree L` is the top self-intersection `((ι^*L)^1)` on `W`.

**Source**: the structure `IntegralCurve`, `TopSelfIntersectionCurve.hasCurveModuleDegree_topSelfIntersection` and
`IntegralCurve.degree_eq_of_hasCurveModuleDegree`.

**Proof**:
1. Take `Γ : IntegralCurve K V` to be `⟨W, ι⟩`: `isClosedImmersion` and `isIntegral` are hypotheses; `isProper` asks
   for `IsProper (ι ≫ (V ↘ Spec K))`, which by `ι.IsOver (Spec K)` equals `W ↘ Spec K`, i.e. `hW`; `dim_eq_one` asks
   for `topologicalKrullDim W = 1`, obtained from `hdim : W.dimension = 1` and
   `AlgebraicGeometry.Scheme.dimension_spec` (`W` nonempty and of finite type over a field ⇒ the dimension is neither
   `⊥` nor `⊤`; `⊥` is excluded by the nonemptiness from `IsIntegral`, `⊤` by proper ⇒ finite type ⇒ finite dimension).
2. `Γ.degree L` is by definition `topSelfIntersection W _ (ι^*L)`, with the `k`-structure written as
   `ι ≫ (V ↘ Spec K)`; `ι` is a `K`-morphism (`hcomp`), so this is the given `k`-structure
   (`topSelfIntersection_congr_over`) — the two `SchemeOver` data are definitionally equal under `ι.IsOver`
   (the structure morphism of `closedCurveOver` is `ι ≫ (V ↘ Spec K)`, which is also `W ↘ Spec K`). If needed, rewrite
   with `Scheme.Hom.IsOver.comp_over`.

**Edge cases**: `W` may be singular and need not be projective (proper suffices); `V` need not be integral. -/
theorem exists_integralCurve_of_dimension_one {K : Type u} [Field K]
    {V : AlgebraicGeometry.Scheme.{u}} [V.Over (AlgebraicGeometry.Spec (CommRingCat.of K))]
    (W : AlgebraicGeometry.Scheme.{u}) [W.Over (AlgebraicGeometry.Spec (CommRingCat.of K))]
    [AlgebraicGeometry.IsIntegral W] (ι : W ⟶ V) [AlgebraicGeometry.IsClosedImmersion ι]
    [ι.IsOver (AlgebraicGeometry.Spec (CommRingCat.of K))]
    (hW : IsProperOver K W) (hdim : W.dimension = 1)
    (L : V.Modules) [L.IsLineBundle] :
    ∃ Γ : IntegralCurve K V,
      Γ.degree L = AlgebraicGeometry.topSelfIntersection W hW
        ((AlgebraicGeometry.Scheme.Modules.pullback ι).obj L) := by
  haveI hprop : AlgebraicGeometry.IsProper (W ↘ AlgebraicGeometry.Spec (CommRingCat.of K)) := hW
  have hcomp : ι ≫ (V ↘ AlgebraicGeometry.Spec (CommRingCat.of K)) =
      W ↘ AlgebraicGeometry.Spec (CommRingCat.of K) :=
    comp_over ι (AlgebraicGeometry.Spec (CommRingCat.of K))
  have hkd : SchemeIsOneDimensional W := by
    show topologicalKrullDim W = 1
    rw [W.dimension_spec MiyaokaMori.TopSelfIntersectionCurve.topologicalKrullDim_ne_bot
      (MiyaokaMori.TopSelfIntersectionCurve.topologicalKrullDim_ne_top_of_dimension Nat.one_pos hdim),
      hdim]
    rfl
  haveI : AlgebraicGeometry.IsProper (ι ≫ (V ↘ AlgebraicGeometry.Spec (CommRingCat.of K))) := by
    rw [hcomp]; exact hprop
  refine ⟨{ carrier := W, ι := ι, dim_eq_one := hkd }, ?_⟩
  -- `Γ.degree L` is `topSelfIntersection` of `ι^*L` on `W` for the k-structure `ι ≫ (V ↘ Spec K)`,
  -- which is the given one by `hcomp`
  exact AlgebraicGeometry.topSelfIntersection_congr_over
    (IntegralCurve.over { carrier := W, ι := ι, dim_eq_one := hkd }) inferInstance hcomp
    (IntegralCurve.isProperOver _) hW ((AlgebraicGeometry.Scheme.Modules.pullback ι).obj L)

/-- **F0, a subscheme inside a fiber**: on an integral closed subscheme lying in a single fiber, the top
self-intersection of `M = B^{⊗eB} ⊗ F^{⊗eF}` is **positive**.

This is the step of the induction that excludes "`π` contracts `W` to a point".

**Source**: line bundles pulled back from `C` are trivial on a subscheme inside a fiber; an ample line bundle has
positive top self-intersection on a positive-dimensional integral closed subscheme.

**Proof**:
1. `hrange` says that the image of `ι ≫ π` is contained in the single point `{c}`; the image is nonempty (`W` is
   integral, hence nonempty), so it equals `{c}`, and since `W` is proper over `K` the image is closed, so `c` is a
   closed point. `W` is reduced, so `ι ≫ π` factors through the scheme-theoretic fiber `π.fiberι c`.
2. Hence **every line bundle pulled back from `C`** is trivial on `W` (it is the pullback of a one-dimensional vector
   space on `Spec κ(c)`). Apply this to `N = pointBundle p₀` and to `N = A`:
   `ι^*(π^*(pointBundle p₀)) ≅ O_W` and `ι^*(π^*A) ≅ O_W`.
3. So `ι^*M ≅ (ι^*B)^{⊗eB}`, and `ι^*B ≅ ι^*(B ⊗ π^*A) = ι^*A₀` (second isomorphism of step 2).
4. `A₀ = fiberedTwist π B A 1 1` is ample (`hA`); the positivity of the top self-intersection of an ample bundle on
   an integral proper positive-dimensional closed subscheme gives `0 < ((ι^*A₀)^r)`, `r = dim W ≥ 1`.
5. `c₁((ι^*A₀)^{⊗eB}) = eB · c₁(ι^*A₀)` (induction on `tensorPow`), so
   `(((ι^*A₀)^{⊗eB})^r) = eB^r · ((ι^*A₀)^r) > 0` (`eB > 0`). Together with the isomorphism of step 3 and
   `topSelfIntersection_congr` this is the claim.

**Edge cases**: `eF = 0` (`F^{⊗0} = O`, step 2 is trivially true); `eB > 0` is necessary (for `eB = 0`,
`M|_W ≅ O_W` has top self-intersection `0`, not positive); `dim W = 0` is excluded by `hpos` (the zero-dimensional
case is D0); the section of `A` is not used in this step. -/
theorem topSelfIntersection_pos_of_range_singleton {K : Type u} [Field K] [IsAlgClosed K]
    {C : SmoothProjectiveCurve K} (p₀ : C.toScheme)
    {V : AlgebraicGeometry.Scheme.{u}} [V.Over (AlgebraicGeometry.Spec (CommRingCat.of K))]
    (π : V ⟶ C.toScheme) [π.IsOver (AlgebraicGeometry.Spec (CommRingCat.of K))]
    (B : V.Modules) [B.IsLineBundle] (A : C.toScheme.Modules) [A.IsLineBundle]
    (hA : AlgebraicGeometry.IsAmple (fiberedTwist π B A 1 1))
    (W : AlgebraicGeometry.Scheme.{u}) [W.Over (AlgebraicGeometry.Spec (CommRingCat.of K))]
    [AlgebraicGeometry.IsIntegral W] (ι : W ⟶ V) [AlgebraicGeometry.IsClosedImmersion ι]
    [ι.IsOver (AlgebraicGeometry.Spec (CommRingCat.of K))]
    (hW : IsProperOver K W) (hpos : 0 < W.dimension)
    (hrange : ∃ c : C.toScheme, Set.range (ι ≫ π).base ⊆ {c})
    (eB eF : ℕ) (heB : 0 < eB) :
    0 < AlgebraicGeometry.topSelfIntersection W hW
      ((AlgebraicGeometry.Scheme.Modules.pullback ι).obj
        (fiberedTwist π B (pointBundle p₀) eB eF)) := by
  obtain ⟨c, hc⟩ := hrange
  -- 1. `c` is a closed point: the dichotomy `range_closedPoint_or_surjective`; the surjective branch contradicts `dim C = 1`
  have hcl : IsClosed ({c} : Set C.toScheme) := by
    rcases range_closedPoint_or_surjective W hW (ι ≫ π) with ⟨c', hc', hr'⟩ | hs
    · obtain ⟨w⟩ := (AlgebraicGeometry.irreducibleSpace_of_isIntegral W).toNonempty
      have h1 : (ι ≫ π).base w = c := Set.mem_singleton_iff.mp (hc ⟨w, rfl⟩)
      have h2 : (ι ≫ π).base w = c' := Set.mem_singleton_iff.mp (hr' ⟨w, rfl⟩)
      rwa [h2.symm.trans h1] at hc'
    · exfalso
      haveI hsub : Subsingleton C.toScheme := ⟨fun x y => by
        obtain ⟨x', hx'⟩ := hs x
        obtain ⟨y', hy'⟩ := hs y
        have hx : x = c := Set.mem_singleton_iff.mp (hc ⟨x', hx'⟩)
        have hy : y = c := Set.mem_singleton_iff.mp (hc ⟨y', hy'⟩)
        exact hx.trans hy.symm⟩
      have hle : topologicalKrullDim C.toScheme ≤ 0 :=
        topologicalKrullDim_zero_of_discreteTopology C.toScheme
      have h1 : topologicalKrullDim C.toScheme = 1 := C.dim_one
      rw [h1] at hle
      norm_num at hle
  -- 2. line bundles pulled back from C are trivial on W
  obtain ⟨tF⟩ := pullback_pullback_iso_unit_of_range_subset π ι c hcl hc (pointBundle p₀)
  obtain ⟨tA⟩ := pullback_pullback_iso_unit_of_range_subset π ι c hcl hc A
  -- 3. `ι^*B ≅ ι^*A₀`, hence `ι^*M ≅ (ι^*A₀)^{⊗eB}`
  have eBA : (AlgebraicGeometry.Scheme.Modules.pullback ι).obj B ≅
      (AlgebraicGeometry.Scheme.Modules.pullback ι).obj (fiberedTwist π B A 1 1) :=
    (show (AlgebraicGeometry.Scheme.Modules.pullback ι).obj B ≅
        AlgebraicGeometry.Scheme.Modules.tensorPow
          ((AlgebraicGeometry.Scheme.Modules.pullback ι).obj B) 1 from
      (AlgebraicGeometry.Scheme.Modules.unitTensorIso _).symm) ≪≫
    (pullbackFiberedTwistIsoOfTrivial π B A 1 1 ι tA).symm
  have eM : (AlgebraicGeometry.Scheme.Modules.pullback ι).obj
      (fiberedTwist π B (pointBundle p₀) eB eF) ≅
      AlgebraicGeometry.Scheme.Modules.tensorPow
        ((AlgebraicGeometry.Scheme.Modules.pullback ι).obj (fiberedTwist π B A 1 1)) eB :=
    pullbackFiberedTwistIsoOfTrivial π B (pointBundle p₀) eB eF ι tF ≪≫
      AlgebraicGeometry.Scheme.Modules.tensorPowMapIso eBA eB
  -- 4–5. ampleness ⇒ `((ι^*A₀)^r) > 0`; homogeneity gives `eB^r · ((ι^*A₀)^r) > 0`
  rw [topSelfIntersection_congr W hW _ _ eM, topSelfIntersection_tensorPow W hW _ eB]
  exact mul_pos (pow_pos (by exact_mod_cast heB) _)
    (AlgebraicGeometry.topSelfIntersection_pos_of_isAmple V (fiberedTwist π B A 1 1) hA W ι hW hpos)

/-- On a smooth projective curve, the line bundle `O_C(D) ⊆ 𝒦_C` of an **effective** Cartier divisor `D` (in the
subsheaf form `lineBundleSections` of Hartshorne II.6.13) contains the constant rational function `1`.

**Proof**: take local data `(U_i, g_i)` of `D` (`cartierDivisor_exists_localData`). For every point `x` choose
`x ∈ U_i`; `ofLocalData` has a local equation `t` on `U_i` whose value at the generic point is `g_i`
(`IsLocalData.exists_isLocalEquation_ofLocalData`). `D` effective ⇒ `g_i` is regular at `x`: `g_i = a` with
`a ∈ O_{C,x}` (`SmoothProjectiveCurve.localData_mem_range_of_effective`), and `a` is the germ of some `b ∈ O(V)`
(`x ∈ V`). On `W := V ⊓ U_i`, `b|_W` and `t|_W` both have value `g_i` at the generic point, and `𝒦(W) → K(C)` is
injective (Stacks 01X5), so `1 · t|_W = b|_W ∈ O(W)`, which is exactly the condition for `1 ∈ O_C(D)(⊤)` near `x`. -/
theorem lineBundleSections_one_mem_top_of_effective {K : Type u} [Field K]
    {C : SmoothProjectiveCurve K} {D : CartierDivisor C.toVariety}
    (hD : CartierDivisor.Effective D) :
    (1 : C.toScheme.rationalFunctionsSheaf.val.obj (Opposite.op (⊤ : C.toScheme.Opens))) ∈
      CartierDivisor.lineBundleSections D ⊤ := by
  letI : AlgebraicGeometry.IsIntegral C.toScheme :=
    SmoothProjectiveCurve.isIntegral_of_smooth_connected C
  obtain ⟨ι, U, g, hUg, hDg⟩ := cartierDivisor_exists_localData C.toVariety D
  intro x _
  have hx : x ∈ (⨆ i, U i) := by rw [hUg.1]; trivial
  obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp hx
  haveI : Nonempty (U i) := ⟨⟨x, hxi⟩⟩
  obtain ⟨t, ht, hloc⟩ := hUg.exists_isLocalEquation_ofLocalData i
  rw [← hDg] at hloc
  obtain ⟨a, ha⟩ :=
    SmoothProjectiveCurve.localData_mem_range_of_effective hD U g hUg hDg i x hxi
  obtain ⟨V, hxV, b, hb⟩ := TopCat.Presheaf.exists_germ_eq C.toScheme.presheaf a
  let W : C.toScheme.Opens := V ⊓ U i
  have hxW : x ∈ W := ⟨hxV, hxi⟩
  haveI : Nonempty W := ⟨⟨x, hxW⟩⟩
  have hWV : W ≤ V := inf_le_left
  have hWU : W ≤ U i := inf_le_right
  let b' : Γ(C.toScheme, W) := (C.toScheme.presheaf.map (homOfLE hWV).op).hom b
  have hgerm : C.toScheme.presheaf.germ W x hxW b' = a := by
    rw [← hb]
    exact C.toScheme.presheaf.germ_res_apply (homOfLE hWV) x hxW b
  have h1 : (C.toScheme.germToFunctionField W).hom b' = (g i : C.toScheme.functionField) := by
    have h := AlgebraicGeometry.Scheme.algebraMap_germ_eq_germToFunctionField C.toScheme hxW b'
    rw [hgerm, ha] at h
    exact h.symm
  have h2 : (C.toScheme.rationalSectionToFunctionField W).hom
      (CartierDivisor.unitVal (X := C.toVariety)
        (C.toScheme.rationalFunctionsUnitsSheaf.val.map (homOfLE hWU).op t)) =
      (g i : C.toScheme.functionField) := by
    have h := congrArg Units.val
      (C.toScheme.rationalUnitsSectionToFunctionField_res (U i) W hWU t)
    rw [ht] at h
    exact h
  have hmem : (C.toScheme.toRationalFunctionsSheaf.hom.app (Opposite.op W)).hom b' =
      CartierDivisor.unitVal (X := C.toVariety)
        (C.toScheme.rationalFunctionsUnitsSheaf.val.map (homOfLE hWU).op t) := by
    apply C.toScheme.rationalSectionToFunctionField_injective W
    exact ((CartierDivisor.rationalSectionToFunctionField_toRat (X := C.toVariety) W b').trans
      h1).trans h2.symm
  refine ⟨W, hxW, le_top,
    C.toScheme.rationalFunctionsUnitsSheaf.val.map (homOfLE hWU).op t, hloc.restrict hWU, ?_⟩
  rw [map_one, one_mul]
  exact ⟨b', hmem⟩

/-- On a smooth projective curve, the line bundle `O_C(D)` of an effective Cartier divisor `D` has a nonzero global
section: the constant function `1` (`one_mem_lineBundleSections_top_of_effective`) transported to `Γ(O_C(D), ⊤)` by
`lineBundleSectionEquiv` (sheafification of modules does not change sections); `1 ≠ 0` because `𝒦(⊤) → K(C)` is
injective and `K(C)` is a field. -/
theorem exists_lineBundle_section_ne_zero_of_effective {K : Type u} [Field K]
    {C : SmoothProjectiveCurve K} {D : CartierDivisor C.toVariety}
    (hD : CartierDivisor.Effective D) :
    ∃ s : Γ(CartierDivisor.lineBundleModules D, ⊤), s ≠ 0 := by
  letI : AlgebraicGeometry.IsIntegral C.toScheme :=
    SmoothProjectiveCurve.isIntegral_of_smooth_connected C
  haveI : Nonempty ((⊤ : C.toScheme.Opens) : Type u) :=
    ⟨⟨genericPoint C.toScheme, trivial⟩⟩
  refine ⟨CartierDivisor.lineBundleSectionEquiv D ⊤
    ⟨1, lineBundleSections_one_mem_top_of_effective hD⟩, fun h0 => ?_⟩
  have h1 : (⟨1, lineBundleSections_one_mem_top_of_effective hD⟩ :
      CartierDivisor.lineBundleSections D ⊤) = 0 :=
    (CartierDivisor.lineBundleSectionEquiv D ⊤).injective (h0.trans (map_zero _).symm)
  have h2 : (1 : C.toScheme.rationalFunctionsSheaf.val.obj (Opposite.op (⊤ : C.toScheme.Opens)))
      = 0 := congrArg Subtype.val h1
  have h3 := congrArg (C.toScheme.rationalSectionToFunctionField ⊤).hom h2
  rw [map_one, map_zero] at h3
  exact one_ne_zero h3

/-- **The point bundle `O_C(p₀)` has a nonzero global section** (`p₀` a closed point).

**Source**: Hartshorne II.6 (an effective divisor `D ≥ 0` has `1 ∈ Γ(X, O_X(D))`); `Divisor.ofPoint_effective` (the
Weil coefficients of `[p₀]` are nonnegative); cf. `EffectiveCartierDivisor.canonicalSection_ne_zero`.

**Proof**: `Divisor.ofPoint p₀` is given by local equations `g_i ∈ κ(C)^×` (a local parameter of `p₀` at `p₀`, `1` on
`{p₀}ᶜ`), and its line bundle `O_C([p₀])` is the subsheaf of the constant sheaf `κ(C)` locally generated by
`g_i^{-1}`. `[p₀]` is effective (`Divisor.ofPoint_effective`) ⇒ every `g_i` is a regular function, so the constant
`1 = g_i · g_i^{-1}` lies in `O(U_i)·g_i^{-1}` on every `U_i`, i.e. `1` is a global section of `O_C([p₀])`; `C` is
nonempty and integral, so `1 ≠ 0`. (Equivalently: `[p₀]` is an effective Cartier divisor and the canonical section
`1_D` of `O([p₀]) = I^∨` is nonzero.)

**Edge cases**: only the closedness of `p₀` (`hp₀`) is used; `K` need not be algebraically closed. -/
theorem pointBundle_exists_section_ne_zero {K : Type u} [Field K] {C : SmoothProjectiveCurve K}
    (p₀ : C.toScheme) (hp₀ : IsClosed ({p₀} : Set C.toScheme)) :
    ∃ s : Γ(pointBundle p₀, ⊤), s ≠ 0 :=
  exists_lineBundle_section_ne_zero_of_effective (Divisor.ofPoint_effective p₀)

/-- **N, the intersection-number computation**: if `π|_W` is nonconstant, there are positive `a, b` such that
`L := B^{⊗b} ⊗ (π^*A)^{⊗a}` satisfies `(L^r) > 0` while the mixed intersection number `(M^{r−1}·L) < 0`
(`r = dim W = d+2 ≥ 2`).

**Source**: the standard operations of Fulton §2.3–2.5; the product of **two** classes pulled back from the curve
has intersection number zero with any two-dimensional class (stated for two possibly different line bundles, so
all three mixed terms `F·F`, `F·π^*A`, `π^*A·π^*A` are killed).

**Proof** (write `β = c₁(ι^*B)`, `φ = c₁(ι^*π^*O_C(p₀))`, `φ' = c₁(ι^*π^*A)`, `r = d + 2`):
1. **All quadratic terms vanish**: `φ² = φφ' = φ'² = 0` (for any proper `W → C` and any two line bundles on `C`).
   So only the linear terms in `φ`, `φ'` survive in the binomial expansions.
2. **Write `Λ := −(B^r)`, `w := (B^{r−1}·F)`, `w' := (B^{r−1}·π^*A)`.** Then
   `(M^r) = eB^{r−1}(−eB·Λ + r·eF·w)`,
   `(L^r) = b^{r−1}(−b·Λ + r·a·w')`,
   `(M^{r−1}·L) = eB^{r−2}[eB(−b·Λ + a·w') + (r−1)·eF·b·w]`.
   (In the third formula `φφ' = 0` kills the cross term, so `w` and `w'` each appear once.)
3. **`w > 0` and `w' > 0`**: `π|_W` nonconstant ⇒ its image is a closed irreducible subset of `C` which is not a
   point ⇒ the image is `C` ⇒ `π|_W` is surjective.
   * `w`: the canonical section of `O_C(p₀)` pulls back to a nonzero section on `W` (`W` integral, `π|_W` dominant)
     whose zero scheme is `(π|_W)^{-1}(p₀)`, an effective Cartier divisor; by the cycle representation of an
     effective divisor, `φ ∩ [W] = Σ m_i[W_i]` with `m_i > 0`, `W_i` integral of dimension `r−1` and `π(W_i) = {p₀}`.
   * `w'`: replace the canonical section of `O_C(p₀)` by `s_A`; the zero scheme is `(π|_W)^{-1}(Z(s_A))`, where
     `Z(s_A) ⊂ C` is a **finite** closed subscheme (possibly several points, possibly non-reduced), and each component
     `W'_j` is again integral of dimension `r−1` with `π(W'_j)` a point.
   In both cases: a component maps to a point ⇒ `(π^*A)|_{W_i}` is trivial ⇒ `B|_{W_i} ≅ A₀|_{W_i}` is ample ⇒
   `((B|_{W_i})^{r−1}) > 0` (`dim W_i = r−1 ≥ 1`). Summing with the projection formula for closed immersions gives
   `w > 0` and `w' > 0`.
4. **`Λ > 0`**: by `hneg` and step 2, `−eB·Λ + r·eF·w < 0`, i.e. `eB·Λ > r·eF·w ≥ 0` (`eF ≥ 0`, `w > 0`), so `Λ > 0`.
   **This guarantees that the `a` chosen below is positive.**
5. **Choice of `a, b`**: `(L^r) > 0 ⟺ a/b > Λ/(r·w')`; `(M^{r−1}·L) < 0 ⟺ a/b < Λ/w' − (r−1)·eF·w/(eB·w')`.
   The interval is nonempty ⟺ `Λ(r−1)/(r·w') > (r−1)·eF·w/(eB·w') ⟺ eB·Λ > r·eF·w`: **`w'` cancels completely**, the
   condition is verbatim the one with a single fiber, and it is the inequality of step 4 (`r−1 > 0` for `r ≥ 2`).
   Take the midpoint of the interval; explicitly `b := 2·r·w'·eB`, `a := Λ·eB·(r+1) − r·(r−1)·eF·w` (integers, and
   `a > 0`).

**Edge cases**: `r = d + 2 ≥ 2` makes `eB^{r−2}` meaningful and the interval nonempty; `eF = 0` is allowed; `Z(s_A)`
may consist of several points and be non-reduced (step 3 only uses multiplicities `> 0` and that each component maps
to **some** point); `W` may be singular.

**Assembly of the formal proof**:
* steps 1–2 (the expansions): `CapDegreeExpansion` — `capDeg_expand` (the binomial expansion of `c₁(M) = x·β + y·φ`
  with `φ² ≡ 0`, entirely in the `ℤ`-Chow group), `degreeOver_pullback_pullback_eq_zero`, `capDeg_sq_zero`;
* step 3 (positivity): `FiberedTwistCapDegreeLeaves.capDeg_pullback_section_nonneg` (`w ≥ 0`) and
  `capDeg_pullback_section_pos` (`w' > 0`, needs `Z(s_A) ≠ ∅`), together with `pointBundle_exists_section_ne_zero`
  (a nonzero section of `O_C(p₀)`). The case `Z(s_A) = ∅` is handled separately: then `A` is trivial
  (`nonempty_iso_unit_of_support_eq_empty`) ⇒ `ι^*B ≅ ι^*A₀` is ample ⇒ `T > 0`, contradicting step 4.
  **Only `w ≥ 0` is used (not `w > 0`).**
* steps 4–5 (`Λ > 0` and the choice): `FiberedTwistCapDegreeLeaves.exists_ab` (explicitly `b = 2(d+2)w'eB`,
  `a = (d+3)eBΛ − (d+1)(d+2)eF w`). -/
theorem exists_positive_twist_of_not_range_singleton {K : Type u} [Field K] [IsAlgClosed K]
    {C : SmoothProjectiveCurve K} (p₀ : C.toScheme) (hp₀ : IsClosed ({p₀} : Set C.toScheme))
    {V : AlgebraicGeometry.Scheme.{u}} [V.Over (AlgebraicGeometry.Spec (CommRingCat.of K))]
    (π : V ⟶ C.toScheme) [π.IsOver (AlgebraicGeometry.Spec (CommRingCat.of K))]
    (B : V.Modules) [B.IsLineBundle] (A : C.toScheme.Modules) [A.IsLineBundle]
    (sA : Γ(A, ⊤)) (hsA : sA ≠ 0)
    (hA : AlgebraicGeometry.IsAmple (fiberedTwist π B A 1 1))
    (W : AlgebraicGeometry.Scheme.{u}) [W.Over (AlgebraicGeometry.Spec (CommRingCat.of K))]
    [AlgebraicGeometry.IsIntegral W] [AlgebraicGeometry.IsLocallyNoetherian W]
    (ι : W ⟶ V) [AlgebraicGeometry.IsClosedImmersion ι]
    [ι.IsOver (AlgebraicGeometry.Spec (CommRingCat.of K))]
    (hW : IsProperOver K W) (d : ℕ) (hdim : W.dimension = d + 2)
    (hns : ¬ ∃ c : C.toScheme, Set.range (ι ≫ π).base ⊆ {c})
    (eB eF : ℕ) (heB : 0 < eB)
    (hneg : AlgebraicGeometry.topSelfIntersection W hW
      ((AlgebraicGeometry.Scheme.Modules.pullback ι).obj
        (fiberedTwist π B (pointBundle p₀) eB eF)) < 0) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧
      0 < AlgebraicGeometry.topSelfIntersection W hW
        ((AlgebraicGeometry.Scheme.Modules.pullback ι).obj (fiberedTwist π B A b a)) ∧
      capDegree W hW
          ((AlgebraicGeometry.Scheme.Modules.pullback ι).obj
            (fiberedTwist π B (pointBundle p₀) eB eF)) (d + 1)
          (AlgebraicGeometry.firstChernClass
            ((AlgebraicGeometry.Scheme.Modules.pullback ι).obj (fiberedTwist π B A b a)) (d + 2)
            (W.fundamentalChowClass (d + 2))) < 0 := by
  classical
  open MiyaokaMori.CapDegreeExpansion MiyaokaMori.FiberedTwistCapDegreeLeaves in
  haveI hprop : AlgebraicGeometry.IsProper (W ↘ AlgebraicGeometry.Spec (CommRingCat.of K)) := hW
  haveI hCprop : AlgebraicGeometry.IsProper
    (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of K)) := C.isProper
  -- 0. `ρ := ι ≫ π` is proper (`W` proper, `C` separated)
  haveI hρ : AlgebraicGeometry.IsProper (ι ≫ π) := by
    haveI : AlgebraicGeometry.IsProper
        ((ι ≫ π) ≫ (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of K))) := by
      have heq : (ι ≫ π) ≫ (C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of K)) =
          W ↘ AlgebraicGeometry.Spec (CommRingCat.of K) := by simp
      rw [heq]; exact hprop
    exact AlgebraicGeometry.IsProper.of_comp (f := ι ≫ π)
      (g := C.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of K))
  -- notation
  set Bh : W.Modules := (AlgebraicGeometry.Scheme.Modules.pullback ι).obj B with hBh
  set Ω : AlgebraicGeometry.ChowGroup W (d + 2) := W.fundamentalChowClass (d + 2) with hΩ
  -- 1. the product of two classes pulled back from `C` kills everything
  have hc1 : ∀ (N : C.toScheme.Modules) [N.IsLineBundle] (k : ℕ),
      AlgebraicGeometry.firstChernClass ((AlgebraicGeometry.Scheme.Modules.pullback ι).obj
        ((AlgebraicGeometry.Scheme.Modules.pullback π).obj N)) (k + 1) =
      AlgebraicGeometry.firstChernClass
        ((AlgebraicGeometry.Scheme.Modules.pullback (ι ≫ π)).obj N) (k + 1) :=
    fun N _ k => AlgebraicGeometry.firstChernClass_congr
      ((AlgebraicGeometry.Scheme.Modules.pullback ι).obj
        ((AlgebraicGeometry.Scheme.Modules.pullback π).obj N))
      ((AlgebraicGeometry.Scheme.Modules.pullback (ι ≫ π)).obj N)
      ((AlgebraicGeometry.Scheme.Modules.pullbackComp ι π).app N) k
  have hsq : ∀ (N N' : C.toScheme.Modules) [N.IsLineBundle] [N'.IsLineBundle] (k : ℕ)
      (γ : AlgebraicGeometry.ChowGroup W (k + 2)),
      capDeg W hW Bh k (AlgebraicGeometry.firstChernClass
        ((AlgebraicGeometry.Scheme.Modules.pullback ι).obj
          ((AlgebraicGeometry.Scheme.Modules.pullback π).obj N)) (k + 1)
        (AlgebraicGeometry.firstChernClass
          ((AlgebraicGeometry.Scheme.Modules.pullback ι).obj
            ((AlgebraicGeometry.Scheme.Modules.pullback π).obj N')) (k + 2) γ)) = 0 := by
    intro N N' _ _
    refine capDeg_sq_zero W hW Bh _ _ (fun γ => ?_)
    rw [hc1 N 0, hc1 N' 1]
    exact degreeOver_pullback_pullback_eq_zero W hW (ι ≫ π) N N' γ
  -- 2. `c₁(ι^*(B^x ⊗ (π^*N)^y)) = x·c₁(ι^*B) + y·c₁(ι^*π^*N)`
  have hM : ∀ (N : C.toScheme.Modules) [N.IsLineBundle] (x y k : ℕ)
      (z : AlgebraicGeometry.ChowGroup W (k + 1)),
      AlgebraicGeometry.firstChernClass
          ((AlgebraicGeometry.Scheme.Modules.pullback ι).obj (fiberedTwist π B N x y)) (k + 1) z =
        x • AlgebraicGeometry.firstChernClass Bh (k + 1) z +
          y • AlgebraicGeometry.firstChernClass
            ((AlgebraicGeometry.Scheme.Modules.pullback ι).obj
              ((AlgebraicGeometry.Scheme.Modules.pullback π).obj N)) (k + 1) z := by
    intro N _ x y k z
    have e : (AlgebraicGeometry.Scheme.Modules.pullback ι).obj (fiberedTwist π B N x y) ≅
        AlgebraicGeometry.Scheme.Modules.tensor
          (AlgebraicGeometry.Scheme.Modules.tensorPow Bh x)
          (AlgebraicGeometry.Scheme.Modules.tensorPow
            ((AlgebraicGeometry.Scheme.Modules.pullback ι).obj
              ((AlgebraicGeometry.Scheme.Modules.pullback π).obj N)) y) :=
      AlgebraicGeometry.Scheme.Modules.pullbackTensorIso ι _ _ ≪≫
      AlgebraicGeometry.Scheme.Modules.tensorCongrLeftIso
        (AlgebraicGeometry.Scheme.Modules.pullbackTensorPowIso ι B x) _ ≪≫
      AlgebraicGeometry.Scheme.Modules.tensorCongrRightIso _
        (AlgebraicGeometry.Scheme.Modules.pullbackTensorPowIso ι _ y)
    rw [AlgebraicGeometry.firstChernClass_congr _ _ e k,
      AlgebraicGeometry.firstChernClass_tensor (k := K) _ _ (k + 1),
      firstChernClass_tensorPow_eq_nsmul W hW Bh k x, firstChernClass_tensorPow_eq_nsmul W hW _ k y]
    rfl
  -- 3. top self-intersection = `capDeg`
  have htop : ∀ (L : W.Modules) [L.IsLineBundle],
      AlgebraicGeometry.topSelfIntersection W hW L = capDeg W hW L (d + 2) Ω :=
    fun L _ => MiyaokaMori.TopSelfIntersectionCurve.topSelfIntersection_eq_of_dimension hW L hdim
  -- 4. `(M^r) = eB^r·T + r·eB^{r−1}·eF·w`
  have hMexp := capDeg_expand W hW _ Bh _ eB eF (hM (pointBundle p₀) eB eF)
    (hsq (pointBundle p₀) (pointBundle p₀)) (d + 1) Ω
  have hneg'' : (eB : ℤ) ^ (d + 2) * capDeg W hW Bh (d + 2) Ω +
      ((d : ℤ) + 2) * (eB : ℤ) ^ (d + 1) * (eF : ℤ) *
        capDeg W hW Bh (d + 1) (AlgebraicGeometry.firstChernClass
          ((AlgebraicGeometry.Scheme.Modules.pullback ι).obj
            ((AlgebraicGeometry.Scheme.Modules.pullback π).obj (pointBundle p₀))) (d + 2) Ω) < 0 := by
    have h := hneg
    rw [htop, hMexp] at h
    push_cast at h
    linarith
  -- 5. `w ≥ 0` (N-P0 plus the nonzero section of the point bundle)
  obtain ⟨sF, hsF⟩ := pointBundle_exists_section_ne_zero p₀ hp₀
  have hw : 0 ≤ capDeg W hW Bh (d + 1) (AlgebraicGeometry.firstChernClass
      ((AlgebraicGeometry.Scheme.Modules.pullback ι).obj
        ((AlgebraicGeometry.Scheme.Modules.pullback π).obj (pointBundle p₀))) (d + 2) Ω) :=
    capDeg_pullback_section_nonneg π B A hA W ι hW d hdim hns (pointBundle p₀) sF hsF
  -- 6. `w' > 0` (N-P1; if `Z(s_A) = ∅` then `A` is trivial, `ι^*B` ample, `T > 0`, contradicting step 4)
  have hw' : 0 < capDeg W hW Bh (d + 1) (AlgebraicGeometry.firstChernClass
      ((AlgebraicGeometry.Scheme.Modules.pullback ι).obj
        ((AlgebraicGeometry.Scheme.Modules.pullback π).obj A)) (d + 2) Ω) := by
    by_cases hsupp : (SetLike.coe (AlgebraicGeometry.Scheme.idealSheafOfSection A sA).support).Nonempty
    · exact capDeg_pullback_section_pos π B A hA W ι hW d hdim hns A sA hsA hsupp
    · exfalso
      have hempty : SetLike.coe (AlgebraicGeometry.Scheme.idealSheafOfSection A sA).support = ∅ :=
        Set.not_nonempty_iff_eq_empty.mp hsupp
      obtain ⟨eA⟩ := nonempty_iso_unit_of_support_eq_empty A sA hempty
      have eΦ' : (AlgebraicGeometry.Scheme.Modules.pullback ι).obj
          ((AlgebraicGeometry.Scheme.Modules.pullback π).obj A) ≅
          SheafOfModules.unit W.ringCatSheaf :=
        (AlgebraicGeometry.Scheme.Modules.pullback ι).mapIso
          ((AlgebraicGeometry.Scheme.Modules.pullback π).mapIso eA ≪≫
            AlgebraicGeometry.Scheme.Modules.pullbackUnitIso π) ≪≫
          AlgebraicGeometry.Scheme.Modules.pullbackUnitIso ι
      have eB1 : (AlgebraicGeometry.Scheme.Modules.pullback ι).obj (fiberedTwist π B A 1 1) ≅ Bh :=
        pullbackFiberedTwistIsoOfTrivial π B A 1 1 ι eΦ' ≪≫
          (AlgebraicGeometry.Scheme.Modules.unitTensorIso Bh :
            AlgebraicGeometry.Scheme.Modules.tensor
              (AlgebraicGeometry.Scheme.Modules.tensorPow Bh 0) Bh ≅ Bh)
      have hT : 0 < capDeg W hW Bh (d + 2) Ω := by
        rw [← htop Bh, ← topSelfIntersection_congr W hW _ _ eB1]
        exact AlgebraicGeometry.topSelfIntersection_pos_of_isAmple V (fiberedTwist π B A 1 1) hA W ι
          hW (by omega)
      have h1 : 0 < (eB : ℤ) ^ (d + 2) * capDeg W hW Bh (d + 2) Ω :=
        mul_pos (pow_pos (by exact_mod_cast heB) _) hT
      have h2 : 0 ≤ ((d : ℤ) + 2) * (eB : ℤ) ^ (d + 1) * (eF : ℤ) *
          capDeg W hW Bh (d + 1) (AlgebraicGeometry.firstChernClass
            ((AlgebraicGeometry.Scheme.Modules.pullback ι).obj
              ((AlgebraicGeometry.Scheme.Modules.pullback π).obj (pointBundle p₀))) (d + 2) Ω) :=
        mul_nonneg (by positivity) hw
      linarith
  -- 7. choose `a, b`
  obtain ⟨a, b, ha, hb, h1, h2⟩ := exists_ab d eB eF _ _ _ heB hw hw' hneg''
  refine ⟨a, b, ha, hb, ?_, ?_⟩
  · -- `(L^r) = b^r·T + r·b^{r−1}·a·w' > 0`
    have hLexp := capDeg_expand W hW _ Bh _ b a (hM A b a) (hsq A A) (d + 1) Ω
    rw [htop, hLexp]
    push_cast
    linarith
  · -- `(M^{r−1}·L) = eB^{r−1}(bT + a w') + (r−1)eB^{r−2}eF·b·w < 0`
    show capDeg W hW ((AlgebraicGeometry.Scheme.Modules.pullback ι).obj
      (fiberedTwist π B (pointBundle p₀) eB eF)) (d + 1)
      (AlgebraicGeometry.firstChernClass
        ((AlgebraicGeometry.Scheme.Modules.pullback ι).obj (fiberedTwist π B A b a)) (d + 2) Ω) < 0
    rw [capDeg_expand W hW _ Bh _ eB eF (hM (pointBundle p₀) eB eF)
      (hsq (pointBundle p₀) (pointBundle p₀)) d _]
    rw [hM A b a (d + 1) Ω, capDeg_add, capDeg_nsmul, capDeg_nsmul, map_add, map_nsmul, map_nsmul,
      capDeg_add, capDeg_nsmul, capDeg_nsmul, ← capDeg_succ W hW Bh (d + 1) Ω,
      firstChernClass_comm_apply W hW _ Bh d Ω, ← capDeg_succ W hW Bh d, hsq (pointBundle p₀) A d Ω]
    push_cast
    linarith

/-- **Z: a line bundle restricted to the zero scheme of one of its nonzero sections is trivial** (the base being a
smooth projective curve).

This is the **only new** fact needed once "restriction to a single fiber" is replaced by "restriction to the
preimage of `Z(s_A)`", and it is what makes the ampleness of `O_C(p₀)` (hence Riemann–Roch / Serre duality on
curves) unnecessary.

**Source**: elementary commutative algebra (invertible modules over a local ring are free); Stacks 0BCH (effective
Cartier divisors), Stacks 00J7 (an Artinian ring is a finite product of local rings); `IsLineBundle.locally_trivial`.

**Proof**:
1. `C` integral and `s ≠ 0` ⇒ `s` is regular, and the zero scheme `Z := Z(s)` is an effective Cartier divisor on `C`,
   in particular a **closed subscheme different from `C`** (otherwise `s` would vanish at the generic point).
2. `C` is a one-dimensional integral scheme, so every point of `Z` has coheight `1`, i.e. the underlying space of `Z`
   is a **finite** set of closed points of `C`; closed points of a curve are isolated ⇒ the underlying space of `Z` is
   **finite and discrete**.
3. A finite discrete underlying space ⇒ `Z` is a finite disjoint union of clopen subschemes each with a single point,
   i.e. each is a **local scheme** (`Spec` of a local ring).
4. A line bundle on a local scheme is trivial: `IsLineBundle.locally_trivial` gives a trivializing neighbourhood `U`
   of the **closed point**; in a local scheme the only open containing the closed point is the whole space (a basic
   open `D(f)` containing the closed point needs `f ∉ 𝔪`, i.e. `f` invertible, so `D(f)` is everything), so `U` is the
   whole piece and the trivialization is global.
5. Glue the trivializations of the pieces (on a finite disjoint union a module sheaf is determined by the pieces) to get
   `A|_Z ≅ O_Z`.

**Edge cases**: `Z` may be non-reduced (steps 3–4 do not need reducedness) and may have several points (step 3);
`Z` empty would also be fine (every line bundle on the empty scheme is trivial); `s ≠ 0` is necessary (for `s = 0`,
`Z = C` and the claim fails for `A` with `deg A ≠ 0`).

**Formal proof** (in the "local" form above):
* `Z` is discrete: `ZeroSchemeOfCurveSectionDiscrete` (`discreteTopology_zeroScheme`: `η ∉ supp Z(s)`; on `C`,
  `height + coheight = 1` (Stacks 0A21) makes every non-generic point minimal; a closed immersion reflects
  specialization, so all points of `Z` are minimal ⇒ `topologicalKrullDim Z ≤ 0` ⇒ locally Artinian ⇒ discrete, by
  Mathlib's `IsLocallyArtinian.of_topologicalKrullDim_le_zero` / `IsLocallyArtinian.discreteTopology`).
* A line bundle on a discrete scheme is trivial: `LineBundleTrivialOfDiscrete`
  (`nonempty_iso_unit_of_discreteTopology`: the frames on the open points glue along the disjoint open cover to a
  global frame, `IsFrame.of_sSup`). -/
theorem lineBundle_trivial_on_zeroScheme {K : Type u} [Field K]
    (C : SmoothProjectiveCurve K) (A : C.toScheme.Modules) [A.IsLineBundle]
    (sA : Γ(A, ⊤)) (hsA : sA ≠ 0) :
    Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Scheme.idealSheafOfSection A sA).subschemeι).obj A ≅
      SheafOfModules.unit
        (AlgebraicGeometry.Scheme.idealSheafOfSection A sA).subscheme.ringCatSheaf) := by
  haveI := MiyaokaMori.ZeroSchemeOfCurveSectionDiscrete.discreteTopology_zeroScheme C A sA hsA
  exact MiyaokaMori.LineBundleTrivialOfDiscrete.nonempty_iso_unit_of_discreteTopology _

/-- **S, "big on a fibration ⇒ has a section"**: if the top self-intersection of `L = B^{⊗b} ⊗ (π^*A)^{⊗a}` on `W`
is positive, some positive power of `L` has a nonzero global section.

This is the one hard step of the route. It does not need the hypothesis "`L` is ample on every proper closed
subscheme"; only the structure of the fibration.

**Source**: after Lazarsfeld, Thm 1.2.23, Step 1 (pp. 34–35), with the two short exact sequences for `L = A − B`
replaced by the **restriction sequence along `π^*s_A`**; uses Serre vanishing, the `K`-linear long exact sequence of
sheaf cohomology, the Snapper polynomial, and `H⁰ = Γ`.

**Proof** (write `A₀ = B ⊗ π^*A`, ample, `F' = π^*A`, `r = dim W`):
1. **The restriction divisor**: `π|_W` is surjective (from `hns`, as in step 3 of N), `s_A` pulls back to a nonzero
   section of `F'` on `W`; `W` integral ⇒ the section is regular, and its zero scheme `Z := Z(π^*s_A) = (π|_W)^{-1}(Z(s_A))`
   is an effective Cartier divisor with `O_W(Z) ≅ F'`. So for every line bundle `G` there is a short exact sequence
   `0 → G ⊗ F'^{-1} → G → G ⊗ O_Z → 0`.
2. **`F'|_Z` is trivial**: `Z = W ×_C Z(s_A)`, `F'|_Z = (π|_Z)^*(A|_{Z(s_A)})`, and `A|_{Z(s_A)} ≅ O_{Z(s_A)}` (Z), so
   `F' ⊗ O_Z ≅ O_Z`, hence for all `j, t`: `O_Z ⊗ A₀^{⊗j} ≅ O_Z ⊗ B^{⊗j} ⊗ F'^{⊗t}`.
   **This is the only step that differs substantially from restricting to a single fiber**: there `Z` is the fiber
   over `Spec κ(p₀)` and triviality is "a line bundle over a field is trivial"; here `Z(s_A)` is a finite scheme and
   triviality is "invertible modules over local rings are free".
3. **Serre vanishing twice**:
   (i) for the coherent sheaf `i_*O_Z` and the ample `A₀`: there is `j₀` such that `H^i(W, O_Z ⊗ A₀^{⊗j}) = 0` for
   `j ≥ j₀`, `i ≥ 1`; by step 2 the same holds for `O_Z ⊗ B^{⊗j} ⊗ F'^{⊗t}` (any `t ≥ 0`);
   (ii) for `O_W` and `A₀`: there is `n₀` such that `H^i(W, A₀^{⊗j}) = H^i(W, B^{⊗j} ⊗ F'^{⊗j}) = 0` for `j ≥ n₀`, `i ≥ 1`.
4. **Higher cohomology is independent of `t`**: apply the sequence of step 1 to `G = B^{⊗j} ⊗ F'^{⊗t}`; in the long
   exact sequence `H^{i−1}(G ⊗ O_Z) → H^i(G ⊗ F'^{-1}) → H^i(G) → H^i(G ⊗ O_Z)` both ends vanish for `i ≥ 2`, `j ≥ j₀`
   (step 3(i)), so `H^i(B^{⊗j} F'^{⊗(t−1)}) ≅ H^i(B^{⊗j} F'^{⊗t})`. Inducting over `0 ≤ t ≤ j` (with the anchor `t = j`
   from step 3(ii)) gives: for `j ≥ max(j₀, n₀)`, `H^i(W, B^{⊗j} ⊗ F'^{⊗t}) = 0` **for all `t ≥ 0`** (`i ≥ 2`).
5. **Snapper**: `χ(W, L^{⊗n}) = P(n)` with `deg P ≤ r` and `r!·[n^r]P = (L^r) > 0`, so `P(n) → +∞`.
   `L^{⊗n} ≅ B^{⊗(n b)} ⊗ F'^{⊗(n a)}`; take `n` large with `n b ≥ max(j₀, n₀)`; step 4 gives `h^i(L^{⊗n}) = 0`
   (`i ≥ 2`), so `χ(L^{⊗n}) = h⁰ − h¹ ≤ h⁰(L^{⊗n})`, and `h⁰(L^{⊗n}) > 0` for `n ≫ 0`.
6. **`H⁰ = Γ`**: identify `Sheaf.H M 0` with `Γ(M, ⊤)` and extract a nonzero section.

**Edge cases**: `a = 0` is allowed but the caller has `a > 0`; `Z` may be non-reduced, reducible, and dominate several
closed points — steps 1–4 only use that it is an effective Cartier divisor together with the triviality of step 2;
`Z` is nonempty since `π|_W` is surjective and `s_A ≠ 0`; for `r = 0` the claim is trivial (`L^{⊗0} = O` has the
section `1`), though the caller has `r ≥ 2`.

**Assembly of the formal proof** (from the three ingredients in `NegativeCurveViaFibrationBigSectionLeaves`):
* steps 1–2 (geometric input): `exists_effectiveCartierDivisor_pullback_pullback_trivial` — the effective Cartier
  divisor `D` on `F' := ι^*π^*A` pulled back from `s_A`, `O_W(D) ≅ F'`, `F'|_D ≅ O_D`;
* steps 3–4 (cohomological core): `subsingleton_sheafCohomology_tensor_tensorPow_of_trivial_on_divisor` —
  `∃ j₀, ∀ j ≥ j₀, ∀ t, ∀ p ≥ 2, H^p(W, B'^{⊗j} ⊗ F'^{⊗t}) = 0`;
* steps 5–6 (Snapper): `exists_pos_tensorPow_section_ne_zero_of_eventually_subsingleton`;
* glue (this proof body): `ι^*A₀ ≅ B' ⊗ F'` is ample (Stacks 01PU and `IsAmple.of_iso`) ⇒ `W` is projective
  (`isProjectiveOver_iff_isProper_and_isAmple`); `L^{⊗n} ≅ B'^{⊗(bn)} ⊗ F'^{⊗(an)}`
  (`pullbackTensorIso`, `pullbackTensorPowIso`, `tensorPowTensorIso`, `tensorPowMulIso`); `b ≥ 1` makes `bn ≥ n ≥ j₀`.
  The hypothesis `hb : 0 < b` is harmless: the only caller `exists_negative_component_of_fibered` has `0 < b`, and for
  `b = 0`, `dim W ≥ 2` and `(L^r) > 0` would be contradictory anyway. -/
theorem exists_pos_section_of_topSelfIntersection_pos {K : Type u} [Field K] [IsAlgClosed K]
    {C : SmoothProjectiveCurve K}
    {V : AlgebraicGeometry.Scheme.{u}} [V.Over (AlgebraicGeometry.Spec (CommRingCat.of K))]
    (π : V ⟶ C.toScheme) [π.IsOver (AlgebraicGeometry.Spec (CommRingCat.of K))]
    (B : V.Modules) [B.IsLineBundle] (A : C.toScheme.Modules) [A.IsLineBundle]
    (sA : Γ(A, ⊤)) (hsA : sA ≠ 0)
    (hA : AlgebraicGeometry.IsAmple (fiberedTwist π B A 1 1))
    (W : AlgebraicGeometry.Scheme.{u}) [W.Over (AlgebraicGeometry.Spec (CommRingCat.of K))]
    [AlgebraicGeometry.IsIntegral W] (ι : W ⟶ V) [AlgebraicGeometry.IsClosedImmersion ι]
    [ι.IsOver (AlgebraicGeometry.Spec (CommRingCat.of K))]
    (hW : IsProperOver K W)
    (hns : ¬ ∃ c : C.toScheme, Set.range (ι ≫ π).base ⊆ {c})
    (a b : ℕ) (hb : 0 < b)
    (hpos : 0 < AlgebraicGeometry.topSelfIntersection W hW
      ((AlgebraicGeometry.Scheme.Modules.pullback ι).obj (fiberedTwist π B A b a))) :
    ∃ n : ℕ, 0 < n ∧
      ∃ σ : Γ(AlgebraicGeometry.Scheme.Modules.tensorPow
        ((AlgebraicGeometry.Scheme.Modules.pullback ι).obj (fiberedTwist π B A b a)) n, ⊤),
        σ ≠ 0 := by
  haveI : AlgebraicGeometry.IsLocallyNoetherian W := isLocallyNoetherian_of_isProperOver W hW
  -- notation: `B' := ι^*B`, `F' := ι^*π^*A`
  set B' : W.Modules := (AlgebraicGeometry.Scheme.Modules.pullback ι).obj B with hB'
  set F' : W.Modules := (AlgebraicGeometry.Scheme.Modules.pullback ι).obj
    ((AlgebraicGeometry.Scheme.Modules.pullback π).obj A) with hF'
  -- 1. `ι^*A₀ ≅ B' ⊗ F'` is ample (Stacks 01PU + invariance under isomorphism)
  have e11 : (AlgebraicGeometry.Scheme.Modules.pullback ι).obj (fiberedTwist π B A 1 1) ≅
      AlgebraicGeometry.Scheme.Modules.tensor B' F' :=
    AlgebraicGeometry.Scheme.Modules.pullbackTensorIso ι
        (AlgebraicGeometry.Scheme.Modules.tensorPow B 1)
        (AlgebraicGeometry.Scheme.Modules.tensorPow
          ((AlgebraicGeometry.Scheme.Modules.pullback π).obj A) 1) ≪≫
      AlgebraicGeometry.Scheme.Modules.tensorIsoLeft
        (AlgebraicGeometry.Scheme.Modules.pullbackTensorPowIso ι B 1 ≪≫
          AlgebraicGeometry.Scheme.Modules.unitTensorIso B') _ ≪≫
      AlgebraicGeometry.Scheme.Modules.tensorIsoRight _
        (AlgebraicGeometry.Scheme.Modules.pullbackTensorPowIso ι
            ((AlgebraicGeometry.Scheme.Modules.pullback π).obj A) 1 ≪≫
          AlgebraicGeometry.Scheme.Modules.unitTensorIso F')
  have hA' : AlgebraicGeometry.IsAmple (AlgebraicGeometry.Scheme.Modules.tensor B' F') :=
    AlgebraicGeometry.IsAmple.of_iso e11
      (AlgebraicGeometry.IsAmple.pullback_of_isClosedImmersion ι (fiberedTwist π B A 1 1) hA)
  -- 2. `W` is projective (proper + an ample bundle)
  have hproj : IsProjectiveOver K W :=
    (isProjectiveOver_iff_isProper_and_isAmple K W).mpr ⟨hW, _, inferInstance, hA'⟩
  -- 3. S3: the effective divisor `D`, `O(D) ≅ F'`, `F'|_D` trivial
  obtain ⟨D, eD, htriv⟩ :=
    MiyaokaMori.FiberedBigHasSection.exists_effectiveCartierDivisor_pullback_pullback_trivial
      π A sA hsA W ι hW hns
  -- 4. S1: for `j ≥ j₀`, `H^{≥2}(B'^{⊗j} ⊗ F'^{⊗t}) = 0` (all `t`)
  obtain ⟨j₀, hj₀⟩ :=
    MiyaokaMori.FiberedBigHasSection.subsingleton_sheafCohomology_tensor_tensorPow_of_trivial_on_divisor
      W hW B' F' hA' D eD htriv
  -- 5. `L^{⊗n} ≅ B'^{⊗(b n)} ⊗ F'^{⊗(a n)}`
  have eL : (AlgebraicGeometry.Scheme.Modules.pullback ι).obj (fiberedTwist π B A b a) ≅
      AlgebraicGeometry.Scheme.Modules.tensor
        (AlgebraicGeometry.Scheme.Modules.tensorPow B' b)
        (AlgebraicGeometry.Scheme.Modules.tensorPow F' a) :=
    AlgebraicGeometry.Scheme.Modules.pullbackTensorIso ι
        (AlgebraicGeometry.Scheme.Modules.tensorPow B b)
        (AlgebraicGeometry.Scheme.Modules.tensorPow
          ((AlgebraicGeometry.Scheme.Modules.pullback π).obj A) a) ≪≫
      AlgebraicGeometry.Scheme.Modules.tensorIsoLeft
        (AlgebraicGeometry.Scheme.Modules.pullbackTensorPowIso ι B b) _ ≪≫
      AlgebraicGeometry.Scheme.Modules.tensorIsoRight _
        (AlgebraicGeometry.Scheme.Modules.pullbackTensorPowIso ι
          ((AlgebraicGeometry.Scheme.Modules.pullback π).obj A) a)
  have eLn : ∀ n : ℕ, AlgebraicGeometry.Scheme.Modules.tensorPow
      ((AlgebraicGeometry.Scheme.Modules.pullback ι).obj (fiberedTwist π B A b a)) n ≅
      AlgebraicGeometry.Scheme.Modules.tensor
        (AlgebraicGeometry.Scheme.Modules.tensorPow B' (b * n))
        (AlgebraicGeometry.Scheme.Modules.tensorPow F' (a * n)) := fun n =>
    AlgebraicGeometry.Scheme.Modules.tensorPowMapIso eL n ≪≫
      AlgebraicGeometry.Scheme.Modules.tensorPowTensorIso _ _ n ≪≫
      AlgebraicGeometry.Scheme.Modules.tensorIsoLeft
        (AlgebraicGeometry.Scheme.Modules.tensorPowMulIso B' b n) _ ≪≫
      AlgebraicGeometry.Scheme.Modules.tensorIsoRight _
        (AlgebraicGeometry.Scheme.Modules.tensorPowMulIso F' a n)
  -- 6. S2: Snapper ⇒ a section
  refine MiyaokaMori.FiberedBigHasSection.exists_pos_tensorPow_section_ne_zero_of_eventually_subsingleton
    W hW hproj _ hpos ⟨j₀, fun n hn p hp => ?_⟩
  haveI := hj₀ (b * n) (le_trans hn (Nat.le_mul_of_pos_left n hb)) (a * n) p hp
  exact AlgebraicGeometry.sheafCohomology.subsingleton_of_iso (eLn n) p

/-- **P, homogeneity of the mixed intersection number in tensor powers**:
`deg(c₁(M)^d ∩ (c₁(N^{⊗n}) ∩ α)) = n · deg(c₁(M)^d ∩ (c₁(N) ∩ α))`.

**Source**: Fulton 2.5(e): `c₁(L ⊗ L') = c₁(L) + c₁(L')`; `c₁(O) = 0`.

**Proof**: induction on `n`. For `n = 0`, `N^{⊗0} = O_X` and `c₁(O_X) = 0` (`firstChernClass_one`), so both sides are
`0`. For `n + 1`, `N^{⊗(n+1)} = N^{⊗n} ⊗ N`, and by `firstChernClass_tensor`
`c₁(N^{⊗(n+1)}) = c₁(N^{⊗n}) + c₁(N)` (as addition in `ChowGroup X (d+1) →+ ChowGroup X d`); `capDegree X hX M d` and
evaluation of an `AddMonoidHom` are additive, so both sides gain one summand and the induction closes.
`X` must be locally of finite type over `K` (hypothesis of `firstChernClass_tensor`), which follows from `hX`. -/
theorem capDegree_firstChernClass_tensorPow {K : Type u} [Field K]
    (X : AlgebraicGeometry.Scheme.{u}) [X.Over (AlgebraicGeometry.Spec (CommRingCat.of K))]
    (hX : IsProperOver K X) (M N : X.Modules) [M.IsLineBundle] [N.IsLineBundle]
    (d n : ℕ) (α : AlgebraicGeometry.ChowGroup X (d + 1)) :
    capDegree X hX M d
        (AlgebraicGeometry.firstChernClass
          (AlgebraicGeometry.Scheme.Modules.tensorPow N n) (d + 1) α)
      = (n : ℤ) * capDegree X hX M d (AlgebraicGeometry.firstChernClass N (d + 1) α) := by
  rw [firstChernClass_tensorPow_eq_nsmul X hX N d n, AddMonoidHom.nsmul_apply, capDegree_nsmul,
    nsmul_eq_mul]

/-- **C3: the `d`-dimensional cycle class of a closed subscheme is a positive integer combination of the
fundamental classes of its `d`-dimensional irreducible components**: for `Z` proper over `K` and locally Noetherian,
`I` a (quasi-coherent) ideal sheaf on `Z`, and `[Z(I)]_d := I.cycle d` in `Z_d(Z)`, there are a finite set of points
`s ⊂ Z` and positive integers `m_x` (`x ∈ s`) with `height x = d` such that in `A_d(Z)`,
`[Z(I)]_d = Σ_{x ∈ s} m_x · ι_{x*}[W_x]`, where `W_x := Z.pointClosure x` is the reduced induced closed subscheme of
`x` (integral) and `ι_x := Z.pointClosureι x` the closed immersion.

**Source**: Fulton §1.3 / Stacks 02QU (`[Z]_d = Σ m_i [Z_i]`, `m_i = length O_{Z,Z_i}`); the definition of
pushforward in Stacks 02QW; `IdealSheafData.cycle`.

**Proof**:
1. **Finite support**: `Z` proper over `K` ⇒ the underlying space is compact ⇒ every cycle has finite support
   (`AlgebraicGeometry.Intersection.properCycle_finiteSupport`). Put `s := (support (I.cycle d)).toFinset` and
   `m_x := (I.cycle d x).toNat`.
2. **Dimension**: `I.cycle d ∈ cycleSubgroup Z d` means by `mem_cycleSubgroup_iff_isDimensionCycle` that every point
   `x` with nonzero coefficient has `pointClosureDimension Z x = d`, and `AlgebraicGeometry.Intersection.pointClosureDimension_eq_height`
   gives `height x = d`.
3. **Positive coefficients**: `I.cycle d` is the pushforward along the closed immersion `I.subschemeι` of the
   `d`-dimensional fundamental cycle of `I.subscheme`, with unchanged coefficients at image points
   (`IdealSheafData.cycle_apply_subschemeι`), and the coefficients of the fundamental cycle are
   `integralFundamentalMultiplicity` (`= length`, nonnegative: `integralFundamentalMultiplicity_nonneg`) or `0`; on the
   support they are nonzero, hence `> 0`, so `(m_x : ℤ) = I.cycle d x`.
4. **Decomposition at the level of cycles**: `I.cycle d = Σ_{x ∈ s} (I.cycle d x) • single x` (a finitely supported
   function is the sum of its point values). For each `x`: `W_x` is integral with
   `topologicalKrullDim W_x = height x = d ≠ ⊤` (`topologicalKrullDim_pointClosure`), so `fundamentalCycle_of_isIntegral`
   gives `[W_x]_d = single (genericPoint W_x) 1`; pushing a point cycle forward along a closed immersion gives
   `ι_{x*}[W_x]_d = single (ι_x (genericPoint W_x)) 1 = single x 1`
   (`AlgebraicCycle.properPushforward_single`, `mapCoeff = 1` for a closed immersion:
   `properPushforward_closedImmersion_apply`; `pointClosureι_genericPoint`).
5. **Passage to the Chow group**: when `PushforwardDescends` holds (`AlgebraicCycle.properPushforward_rationallyEquivalent`,
   proper over a field), `chowPushforward ι_x d` is by definition the `QuotientAddGroup.map` of the cycle pushforward
   (`unfold chowPushforward; exact dif_pos _`, as in `chowPushforward_fundamentalChowClass_of_iso`), so
   `chowPushforward ι_x d [W_x] = ChowGroup.mk ⟨ι_{x*}[W_x]_d, _⟩`; `ChowGroup.mk` is additive, and transporting the
   finite sum of step 4 into `A_d(Z)` gives the claim.

**Edge cases**: if `I.cycle d = 0` (e.g. `Z(I) = ∅` or no `d`-dimensional component) then `s = ∅` and the claim is
`0 = 0`; `d = 0` is allowed (`W_x` is the reduced structure `Spec κ(x)` of a closed point); `Z(I)` may be
non-reduced or reducible (the multiplicities `m_x` only need to be `> 0`).

**Formal proof**: the cycle-level mechanics of steps 4–5 are in `PointClosurePushforwardSingle`
(`chowPushforward_pointClosureι_fundamentalChowClass`: `ι_{x*}[W_x] = ChowGroup.mk [x]`;
`AlgebraicCycle.eq_sum_single_of_finite_support`: a finitely supported cycle is the sum of its point cycles); step 3
uses `IdealSheafData.cycle_apply_subschemeι` / `cycle_apply_of_notMem_support` (`IdealSheafCycleApply`). -/
theorem cycle_class_eq_sum_pointClosure_components {K : Type u} [Field K]
    (Z : AlgebraicGeometry.Scheme.{u}) [Z.Over (AlgebraicGeometry.Spec (CommRingCat.of K))]
    (hZ : IsProperOver K Z) [AlgebraicGeometry.IsLocallyNoetherian Z]
    (I : Z.IdealSheafData) (d : ℕ) (h : I.cycle d ∈ AlgebraicGeometry.cycleSubgroup Z d) :
    ∃ (s : Finset Z) (m : Z → ℕ), (∀ x ∈ s, 0 < m x) ∧ (∀ x ∈ s, Order.height x = (d : ℕ∞)) ∧
      AlgebraicGeometry.ChowGroup.mk ⟨I.cycle d, h⟩ =
        ∑ x ∈ s, m x • AlgebraicGeometry.chowPushforward (Z.pointClosureι x) d
          ((Z.pointClosure x).fundamentalChowClass d) := by
  classical
  haveI hprop : AlgebraicGeometry.IsProper (Z ↘ AlgebraicGeometry.Spec (CommRingCat.of K)) := hZ
  haveI : AlgebraicGeometry.IsLocallyNoetherian I.subscheme :=
    AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian I.subschemeι
  -- 1. finite support
  have hfin : (Function.support (I.cycle d)).Finite :=
    AlgebraicGeometry.Intersection.properCycle_finiteSupport
      (Z ↘ AlgebraicGeometry.Spec (CommRingCat.of K)) (I.cycle d)
  -- 3. nonnegative coefficients (at image points = coefficient of the fundamental cycle = length ≥ 0; outside the support = 0)
  have hnonneg : ∀ x : Z, 0 ≤ I.cycle d x := by
    intro x
    by_cases hx : x ∈ I.support
    · obtain ⟨z', rfl⟩ : x ∈ Set.range I.subschemeι.base := by rwa [I.range_subschemeι]
      rw [I.cycle_apply_subschemeι d z']
      change 0 ≤ (if AlgebraicGeometry.Intersection.pointClosureDimension I.subscheme z' = d
        then AlgebraicGeometry.Intersection.integralFundamentalMultiplicity I.subscheme z' else 0)
      split_ifs
      · exact AlgebraicGeometry.Intersection.integralFundamentalMultiplicity_nonneg _ _
      · exact le_rfl
    · rw [I.cycle_apply_of_notMem_support d hx]
  -- 2. dimension: points of the support have height d
  have hht : ∀ x ∈ hfin.toFinset, Order.height x = (d : ℕ∞) := by
    intro x hx
    have hne : I.cycle d x ≠ 0 := by simpa using hx
    exact h x hne
  refine ⟨hfin.toFinset, fun x => (I.cycle d x).toNat, ?_, hht, ?_⟩
  · intro x hx
    have hne : I.cycle d x ≠ 0 := by simpa using hx
    have := hnonneg x
    show 0 < (I.cycle d x).toNat
    omega
  -- 4–5. transport the cycle-level decomposition into the Chow group
  · -- the point cycle `[x]` (defaults to 0 when the height is ≠ d; only used on the support)
    let sx : Z → ↥(AlgebraicGeometry.cycleSubgroup Z d) := fun x =>
      if hx : Order.height x = (d : ℕ∞) then
        ⟨Function.locallyFinsuppWithin.single x (1 : ℤ),
          MiyaokaMori.PointClosurePushforwardSingle.single_mem_cycleSubgroup x hx⟩
      else 0
    have hsx : ∀ x ∈ hfin.toFinset, ((sx x : ↥(AlgebraicGeometry.cycleSubgroup Z d)) :
        AlgebraicGeometry.AlgebraicCycle Z ℤ) = Function.locallyFinsuppWithin.single x (1 : ℤ) := by
      intro x hx
      simp only [sx, dif_pos (hht x hx)]
    have hsingle : ∀ x ∈ hfin.toFinset,
        AlgebraicGeometry.chowPushforward (Z.pointClosureι x) d
            ((Z.pointClosure x).fundamentalChowClass d) =
          AlgebraicGeometry.ChowGroup.mk (sx x) := by
      intro x hx
      rw [MiyaokaMori.PointClosurePushforwardSingle.chowPushforward_pointClosureι_fundamentalChowClass
        (K := K) x (hht x hx)]
      congr 1
      exact Subtype.ext (hsx x hx).symm
    rw [Finset.sum_congr rfl fun x hx => by rw [hsingle x hx]]
    have hdecomp : (⟨I.cycle d, h⟩ : ↥(AlgebraicGeometry.cycleSubgroup Z d)) =
        ∑ x ∈ hfin.toFinset, (I.cycle d x).toNat • sx x := by
      apply Subtype.ext
      rw [AddSubgroup.val_finsetSum]
      simp only [AddSubgroup.coe_nsmul]
      change I.cycle d = _
      refine (AlgebraicGeometry.AlgebraicCycle.eq_sum_single_of_finite_support (I.cycle d) hfin).trans ?_
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [hsx x hx, ← Int.toNat_of_nonneg (hnonneg x)]
      simp only [Int.toNat_natCast, natCast_zsmul]
    rw [hdecomp, map_sum]
    simp only [map_nsmul]

/-- **C, a negative component of an effective divisor**: `Z` integral and proper with `dim Z = d + 1`, `N` with a
nonzero global section `σ`; if `deg(c₁(M)^d ∩ (c₁(N) ∩ [Z])) < 0`, then `Z` has a `d`-dimensional integral closed
subscheme `Z'` with `((M|_{Z'})^d) < 0`.

This step **does not involve the fibration**; it is a general fact about Chow groups.

**Source**: Fulton §2.3 / Stacks 02SJ (the cap of an effective divisor is the divisor cycle); a nonzero section on
an integral scheme is regular; an effective Cartier divisor has pure codimension `1`; the projection formula for
closed immersions and the invariance of the degree under proper pushforward.

**Proof**:
1. `Z` integral and `σ ≠ 0` ⇒ `σ` is regular, and the zero scheme `Z(σ)` is an effective Cartier divisor. By the cycle
   representation of an effective divisor (`Z` integral, locally Noetherian and locally of finite type over a field,
   all from properness), `c₁(N) ∩ [Z] = [Z(σ)]_d`, which is by definition `Σ_i m_i [Z_i]`, `Z_i` running over the
   `d`-dimensional irreducible components of `Z(σ)` (every component has codimension exactly `1`, i.e. dimension
   exactly `d`), `m_i = length O_{Z(σ), ξ_i} > 0`.
2. `capDegree Z hZ M d` is an additive homomorphism `ChowGroup Z d → ℤ` (both `capPow` and `degreeOver` are), so
   `0 > capDegree ... (c₁(N) ∩ [Z]) = Σ_i m_i · capDegree Z hZ M d [Z_i]`. A negative finite sum with all `m_i > 0`
   forces `capDegree Z hZ M d [Z_i] < 0` for some `i` (otherwise every term is `≥ 0`).
3. Let `Z'` be the reduced induced closed subscheme of that `Z_i` (integral, `d`-dimensional, closed immersion
   `ι' : Z' ↪ Z`, proper over `K` since a closed immersion is finite, finite ⇒ proper, and proper is stable under
   composition). The projection formula for closed immersions gives
   `capDegree Z hZ M d [Z_i] = topSelfIntersection Z' hZ' (ι'^*M)`
   (`c₁(M)^d ∩ ι'_*[Z'] = ι'_*(c₁(ι'^*M)^d ∩ [Z'])`, then take degrees; the degree is invariant under proper pushforward).

**Edge cases**: `Z(σ)` may be reducible or non-reduced (only `m_i > 0` is used; the multiplicities only appear as
positive coefficients in step 2 and do not affect "some component is negative"); `Z(σ)` cannot be empty — then
`c₁(N) ∩ [Z] = 0` and the mixed intersection number would be `0`, contradicting `hneg`, so the sum in step 2 is
nonempty; `d = 0` is allowed (`Z'` is a zero-dimensional integral closed subscheme, and `topSelfIntersection` is the
degree). -/
theorem exists_negative_component_of_section {K : Type u} [Field K]
    (Z : AlgebraicGeometry.Scheme.{u}) [Z.Over (AlgebraicGeometry.Spec (CommRingCat.of K))]
    [AlgebraicGeometry.IsIntegral Z] [AlgebraicGeometry.IsLocallyNoetherian Z]
    (hZ : IsProperOver K Z) (d : ℕ) (hdim : Z.dimension = d + 1)
    (M N : Z.Modules) [M.IsLineBundle] [N.IsLineBundle]
    (σ : Γ(N, ⊤)) (hσ : σ ≠ 0)
    (hneg : capDegree Z hZ M d
      (AlgebraicGeometry.firstChernClass N (d + 1) (Z.fundamentalChowClass (d + 1))) < 0) :
    ∃ (Z' : AlgebraicGeometry.Scheme.{u}) (_ : Z'.Over (AlgebraicGeometry.Spec (CommRingCat.of K)))
      (_ : AlgebraicGeometry.IsIntegral Z') (ι' : Z' ⟶ Z)
      (_ : AlgebraicGeometry.IsClosedImmersion ι')
      (_ : ι'.IsOver (AlgebraicGeometry.Spec (CommRingCat.of K)))
      (hZ' : IsProperOver K Z'),
      Z'.dimension = d ∧
        AlgebraicGeometry.topSelfIntersection Z' hZ'
          ((AlgebraicGeometry.Scheme.Modules.pullback ι').obj M) < 0 := by
  haveI hprop : AlgebraicGeometry.IsProper (Z ↘ AlgebraicGeometry.Spec (CommRingCat.of K)) := hZ
  -- 1. c₁(N) ∩ [Z] = [Z(σ)]_d
  obtain ⟨hmem, hcap⟩ :=
    AlgebraicGeometry.firstChernClass_cap_fundamentalClass_of_regular_section (k := K) N σ hσ d hdim
  rw [hcap] at hneg
  -- 2. [Z(σ)]_d = Σ m_i · ι_{i*}[Z_i], m_i > 0, dim Z_i = d
  obtain ⟨s, m, hmpos, hht, hsum⟩ :=
    cycle_class_eq_sum_pointClosure_components Z hZ
      (AlgebraicGeometry.Scheme.idealSheafOfSection N σ) d hmem
  rw [hsum, capDegree_finset_sum] at hneg
  simp only [capDegree_nsmul, nsmul_eq_mul] at hneg
  -- 3. a negative finite sum has a negative term
  have hex : ∃ x ∈ s, (m x : ℤ) * capDegree Z hZ M d
      (AlgebraicGeometry.chowPushforward (Z.pointClosureι x) d
        ((Z.pointClosure x).fundamentalChowClass d)) < 0 := by
    by_contra hall
    push Not at hall
    exact absurd hneg (not_lt.2 (Finset.sum_nonneg hall))
  obtain ⟨x, hxs, hxneg⟩ := hex
  -- 4. move to Z_x: projection formula + invariance of the degree under pushforward
  letI : (Z.pointClosure x).Over (AlgebraicGeometry.Spec (CommRingCat.of K)) :=
    ⟨Z.pointClosureι x ≫ (Z ↘ AlgebraicGeometry.Spec (CommRingCat.of K))⟩
  haveI : (Z.pointClosureι x).IsOver (AlgebraicGeometry.Spec (CommRingCat.of K)) := ⟨rfl⟩
  have hZ' : IsProperOver K (Z.pointClosure x) :=
    inferInstanceAs (AlgebraicGeometry.IsProper
      (Z.pointClosureι x ≫ (Z ↘ AlgebraicGeometry.Spec (CommRingCat.of K))))
  have hdimZ' : (Z.pointClosure x).dimension = d :=
    AlgebraicGeometry.Scheme.dimension_pointClosure x (hht x hxs)
  refine ⟨Z.pointClosure x, inferInstance, inferInstance, Z.pointClosureι x, inferInstance,
    inferInstance, hZ', hdimZ', ?_⟩
  rw [← capDegree_chowPushforward_fundamentalChowClass Z hZ M d (Z.pointClosure x) hZ'
    (Z.pointClosureι x) hdimZ']
  by_contra hc
  push Not at hc
  exact absurd hxneg (not_lt.2 (mul_nonneg (by exact_mod_cast (hmpos x hxs).le) hc))

/-! ## Assembly: one step down in dimension -/

/-- One step of the induction: `W ⊂ V` integral and proper with `dim W = d + 2` and `(M|_W)^{d+2} < 0` ⇒ there is a
`(d+1)`-dimensional integral closed subscheme `Z'` of `W` with `(M|_{Z'})^{d+1} < 0`.

The proof assembles N, S, P and C. -/
theorem exists_negative_component_of_fibered {K : Type u} [Field K] [IsAlgClosed K]
    {C : SmoothProjectiveCurve K} (p₀ : C.toScheme) (hp₀ : IsClosed ({p₀} : Set C.toScheme))
    {V : AlgebraicGeometry.Scheme.{u}} [V.Over (AlgebraicGeometry.Spec (CommRingCat.of K))]
    (π : V ⟶ C.toScheme) [π.IsOver (AlgebraicGeometry.Spec (CommRingCat.of K))]
    (B : V.Modules) [B.IsLineBundle] (A : C.toScheme.Modules) [A.IsLineBundle]
    (sA : Γ(A, ⊤)) (hsA : sA ≠ 0)
    (hA : AlgebraicGeometry.IsAmple (fiberedTwist π B A 1 1))
    (W : AlgebraicGeometry.Scheme.{u}) [W.Over (AlgebraicGeometry.Spec (CommRingCat.of K))]
    [AlgebraicGeometry.IsIntegral W] (ι : W ⟶ V) [AlgebraicGeometry.IsClosedImmersion ι]
    [ι.IsOver (AlgebraicGeometry.Spec (CommRingCat.of K))]
    (hW : IsProperOver K W) (d : ℕ) (hdim : W.dimension = d + 2)
    (hns : ¬ ∃ c : C.toScheme, Set.range (ι ≫ π).base ⊆ {c})
    (eB eF : ℕ) (heB : 0 < eB)
    (hneg : AlgebraicGeometry.topSelfIntersection W hW
      ((AlgebraicGeometry.Scheme.Modules.pullback ι).obj
        (fiberedTwist π B (pointBundle p₀) eB eF)) < 0) :
    ∃ (Z' : AlgebraicGeometry.Scheme.{u}) (_ : Z'.Over (AlgebraicGeometry.Spec (CommRingCat.of K)))
      (_ : AlgebraicGeometry.IsIntegral Z') (ι' : Z' ⟶ W)
      (_ : AlgebraicGeometry.IsClosedImmersion ι')
      (_ : ι'.IsOver (AlgebraicGeometry.Spec (CommRingCat.of K)))
      (hZ' : IsProperOver K Z'),
      Z'.dimension = d + 1 ∧
        AlgebraicGeometry.topSelfIntersection Z' hZ'
          ((AlgebraicGeometry.Scheme.Modules.pullback ι').obj
            ((AlgebraicGeometry.Scheme.Modules.pullback ι).obj
              (fiberedTwist π B (pointBundle p₀) eB eF))) < 0 := by
  haveI : AlgebraicGeometry.IsLocallyNoetherian W := isLocallyNoetherian_of_isProperOver W hW
  obtain ⟨a, b, ha, hb, hLpos, hmix⟩ :=
    exists_positive_twist_of_not_range_singleton p₀ hp₀ π B A sA hsA hA W ι hW d hdim hns eB eF heB
      hneg
  obtain ⟨n, hn, σ, hσ⟩ :=
    exists_pos_section_of_topSelfIntersection_pos π B A sA hsA hA W ι hW hns a b hb hLpos
  have hscale := capDegree_firstChernClass_tensorPow (K := K) W hW
    ((AlgebraicGeometry.Scheme.Modules.pullback ι).obj (fiberedTwist π B (pointBundle p₀) eB eF))
    ((AlgebraicGeometry.Scheme.Modules.pullback ι).obj (fiberedTwist π B A b a))
    (d + 1) n (W.fundamentalChowClass (d + 2))
  have hneg' : capDegree W hW
      ((AlgebraicGeometry.Scheme.Modules.pullback ι).obj
        (fiberedTwist π B (pointBundle p₀) eB eF)) (d + 1)
      (AlgebraicGeometry.firstChernClass
        (AlgebraicGeometry.Scheme.Modules.tensorPow
          ((AlgebraicGeometry.Scheme.Modules.pullback ι).obj (fiberedTwist π B A b a)) n)
        (d + 2) (W.fundamentalChowClass (d + 2))) < 0 := by
    rw [hscale]
    exact mul_neg_of_pos_of_neg (by exact_mod_cast hn) hmix
  exact exists_negative_component_of_section W hW (d + 1) hdim
    ((AlgebraicGeometry.Scheme.Modules.pullback ι).obj (fiberedTwist π B (pointBundle p₀) eB eF))
    (AlgebraicGeometry.Scheme.Modules.tensorPow
      ((AlgebraicGeometry.Scheme.Modules.pullback ι).obj (fiberedTwist π B A b a)) n)
    σ hσ hneg'

/-! ## Top level: Lemma K′ -/

/-- **Lemma K′**: in the fibration setting, a line bundle `M = B^{⊗eB} ⊗ (π^*O_C(p₀))^{⊗eF}` with negative top
self-intersection has negative degree on some integral curve.

The auxiliary data are an ample line bundle `A` on `C`, a nonzero global section `s_A` of it, and the ampleness of
`A₀ = B ⊗ π^*A`. **The ampleness of `O_C(p₀)` is not needed** (it would require Riemann–Roch and Serre duality on
curves).

The proof is a strong induction on `dim`, assembled from D0, D1, F0 and `exists_negative_component_of_fibered`. -/
theorem exists_integralCurve_degree_neg_of_fibered {K : Type u} [Field K] [IsAlgClosed K]
    {C : SmoothProjectiveCurve K} (p₀ : C.toScheme) (hp₀ : IsClosed ({p₀} : Set C.toScheme))
    (V : AlgebraicGeometry.Scheme.{u}) [V.Over (AlgebraicGeometry.Spec (CommRingCat.of K))]
    [AlgebraicGeometry.IsIntegral V] (hV : IsProperOver K V)
    (π : V ⟶ C.toScheme) [π.IsOver (AlgebraicGeometry.Spec (CommRingCat.of K))]
    (B : V.Modules) [B.IsLineBundle] (A : C.toScheme.Modules) [A.IsLineBundle]
    (sA : Γ(A, ⊤)) (hsA : sA ≠ 0)
    (hA : AlgebraicGeometry.IsAmple (fiberedTwist π B A 1 1))
    (eB eF : ℕ) (heB : 0 < eB)
    (hneg : AlgebraicGeometry.topSelfIntersection V hV
      (fiberedTwist π B (pointBundle p₀) eB eF) < 0) :
    ∃ Γ : IntegralCurve K V, Γ.degree (fiberedTwist π B (pointBundle p₀) eB eF) < 0 := by
  have key : ∀ r : ℕ, ∀ (W : AlgebraicGeometry.Scheme.{u})
      [W.Over (AlgebraicGeometry.Spec (CommRingCat.of K))] [AlgebraicGeometry.IsIntegral W]
      (ι : W ⟶ V) [AlgebraicGeometry.IsClosedImmersion ι]
      [ι.IsOver (AlgebraicGeometry.Spec (CommRingCat.of K))]
      (hW : IsProperOver K W), W.dimension = r →
      AlgebraicGeometry.topSelfIntersection W hW
        ((AlgebraicGeometry.Scheme.Modules.pullback ι).obj
          (fiberedTwist π B (pointBundle p₀) eB eF)) < 0 →
      ∃ Γ : IntegralCurve K V, Γ.degree (fiberedTwist π B (pointBundle p₀) eB eF) < 0 := by
    intro r
    induction r using Nat.strong_induction_on with
    | _ r ih =>
      intro W _ _ ι _ _ hW hdim hlt
      match r, hdim with
      | 0, hdim =>
        exact absurd hlt
          (not_lt.2 (le_of_lt (topSelfIntersection_pos_of_dimension_zero W hW hdim _)))
      | 1, hdim =>
        obtain ⟨Γ, hΓ⟩ := exists_integralCurve_of_dimension_one W ι hW hdim
          (fiberedTwist π B (pointBundle p₀) eB eF)
        exact ⟨Γ, by rw [hΓ]; exact hlt⟩
      | (d + 2), hdim =>
        by_cases hc : ∃ c : C.toScheme, Set.range (ι ≫ π).base ⊆ {c}
        · exact absurd hlt (not_lt.2 (le_of_lt
            (topSelfIntersection_pos_of_range_singleton p₀ π B A hA W ι hW
              (by omega) hc eB eF heB)))
        · obtain ⟨Z', oZ', iZ', ι', ciZ', ioZ', hZ', hdimZ', hnegZ'⟩ :=
            exists_negative_component_of_fibered p₀ hp₀ π B A sA hsA hA W ι hW d hdim hc eB eF heB
              hlt
          refine ih (d + 1) (by omega) Z' (ι' ≫ ι) hZ' hdimZ' ?_
          rw [topSelfIntersection_pullback_comp Z' hZ' ι' ι]
          exact hnegZ'
  haveI : AlgebraicGeometry.Scheme.Hom.IsOver (𝟙 V)
      (AlgebraicGeometry.Spec (CommRingCat.of K)) := ⟨by simp⟩
  refine key V.dimension V (𝟙 V) hV rfl ?_
  rw [topSelfIntersection_congr V hV _ (fiberedTwist π B (pointBundle p₀) eB eF)
    ((AlgebraicGeometry.Scheme.Modules.pullbackId V).app
      (fiberedTwist π B (pointBundle p₀) eB eF))]
  exact hneg

end MiyaokaMori.FiberedNegativeCurve

end
