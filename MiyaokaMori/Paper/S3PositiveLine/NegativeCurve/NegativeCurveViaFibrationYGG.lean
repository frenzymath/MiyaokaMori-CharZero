import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.RationalTopSelfIntersection
import MiyaokaMori.AlgebraicGeometry.Chow.DivisorOperator.RatCapPowBinomial
import MiyaokaMori.Paper.S3PositiveLine.NegativeCurve.NegativeCurveViaFibration
import MiyaokaMori.Paper.S3PositiveLine.NegativeCurve.ShiftedClassLineBundle
import MiyaokaMori.Paper.S3PositiveLine.NegativeCurve.YggGeometry

/-! # The negative curve via the fibration, instantiated on `Y_κ^GG`

The statement needed in the proof of Lemma 2.5 of the paper:

> there is `Γ : IntegralCurve K (YGG f κ)` with `Γ.degree (shiftedBundle f κ m p₀ a b) < 0`.

This file instantiates `MiyaokaMori.FiberedNegativeCurve.exists_integralCurve_degree_neg_of_fibered` (Lemma K′)
at `V := YGG f κ`, `π := YGG.proj f κ`, `B := polarization f κ m`, `eB := b`, `eF := m * a`, so that
`fiberedTwist (YGG.proj f κ) (polarization f κ m) (pointBundle p₀) b (m * a)` **is** by definition
`shiftedBundle f κ m p₀ a b`.

The auxiliary data of Lemma K′ (an ample bundle `A` on `C` with a nonzero section such that `B ⊗ π^*A` is ample)
are provided by `exists_ampleCurveBundle_with_section`. Ampleness of `O_C(p₀)` is **not** needed here (that would
require Riemann–Roch and Serre duality on curves).

Source: §2.4 of the paper; for the route see the header of `NegativeCurveViaFibration`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace MiyaokaMori.FiberedNegativeCurve

open AlgebraicGeometry

/-- **`B_κ = O(m)` is ample relative to `π_κ : Y_κ^GG → C`** (in the form of Stacks 01VJ(3): `B_κ` is ample on the
preimage of every affine open `V` of `C`).

**Proof**: `S := jetAlgebra f κ` is locally a weighted polynomial algebra (`YGG.jetAlgebra_isLocallyWeightedPolynomial`);
`m` sufficiently divisible (`Fact`) gives `m > 0` and that `S^{(m)}` is generated in degree one; `S_m = (S^{(m)})_1`
is of finite type (`locallyWeighted_part_isFiniteType`). `Proj S ≅ Proj S^{(m)}` over `C` (`veroneseIso`, whose
inverse component `i` is a closed immersion), and `O_{Proj S}(m) ≅ i^* O_{Proj S^{(m)}}(1)`
(`veronese_twist_pullback_iso`). For an affine open `V ⊆ C`, `O_{Proj S^{(m)}}(1)` is ample on `π'^{-1}V` (the core
of Stacks 07RL: `isAmple_twist_one_pullback_preimage_ι`), stays ample after pullback along the closed immersion
`i|_{π^{-1}V}` (Stacks 01PU), is rewritten as `(π^{-1}V).ι^* (i^* O(1))` via `pullbackComp` / `pullbackCongr`, and
finally transported to `(π^{-1}V).ι^* B_κ` by `IsAmple.of_iso`. This is the argument of
`IsProjectiveMorphism.isQuasiProjective_isProper` with the bundle fixed to `B_κ`.
The case `κ = 0` also holds (`locallyWeighted_part_isFiniteType` applies for empty `σ`; `Nonempty σ` is not needed). -/
theorem polarization_isAmple_pullback_preimage_ι {K : Type u} [Field K]
    {X : SmoothProjectiveVariety K} {C : SmoothProjectiveCurve K}
    (f : C.toScheme ⟶ X.toScheme) [MMSetup f] (κ m : ℕ)
    [Fact ((jetAlgebra f κ).SufficientlyDivisible m)] (V : C.toScheme.affineOpens) :
    AlgebraicGeometry.IsAmple
      ((AlgebraicGeometry.Scheme.Modules.pullback (YGG.proj f κ ⁻¹ᵁ V.1).ι).obj
        (polarization f κ m)) := by
  have hSD : (jetAlgebra f κ).SufficientlyDivisible m := Fact.out
  have hmpos : 0 < m := hSD.1
  have hgen : ((jetAlgebra f κ).veronese m).GeneratedInDegreeOne := hSD.2
  have hloc := YGG.jetAlgebra_isLocallyWeightedPolynomial f rfl κ
  have hft1 : ((jetAlgebra f κ).part (1 * m)).IsFiniteType := by
    rw [Nat.one_mul]
    exact locallyWeighted_part_isFiniteType (jetAlgebra f κ) _ (fun _ => Nat.succ_pos _) hloc m
  have hft : (((jetAlgebra f κ).veronese m).part 1).IsFiniteType := hft1
  -- data of relative very ampleness: the closed immersion `i : Proj S → Proj S^{(m)}` over `C`, `O(m) ≅ i^* O(1)`.
  -- First abstract `i` as a free variable (if the component of `veroneseIso` stays a `let`, later unifications unfold it, which is very slow).
  obtain ⟨i, hi, hover, ⟨φ⟩⟩ : ∃ i : YGG f κ ⟶
        (AlgebraicGeometry.Scheme.relativeProj ((jetAlgebra f κ).veronese m)).left,
      AlgebraicGeometry.IsClosedImmersion i ∧
      i ≫ (AlgebraicGeometry.Scheme.relativeProj ((jetAlgebra f κ).veronese m)).hom = YGG.proj f κ ∧
      Nonempty (polarization f κ m ≅ (AlgebraicGeometry.Scheme.Modules.pullback i).obj
        (AlgebraicGeometry.Scheme.relativeProj.twist ((jetAlgebra f κ).veronese m) 1)) := by
    let e := AlgebraicGeometry.Scheme.relativeProj.veroneseIso (jetAlgebra f κ) m hmpos
    refine ⟨e.inv.left, ?_, CategoryTheory.Over.w e.inv,
      AlgebraicGeometry.Scheme.relativeProj.veronese_twist_pullback_iso (jetAlgebra f κ) m hmpos⟩
    have hleft : e.inv.left ≫ e.hom.left = 𝟙 _ :=
      congrArg CategoryTheory.Over.Hom.left e.inv_hom_id
    have hcomp : AlgebraicGeometry.IsClosedImmersion (e.inv.left ≫ e.hom.left) := by
      rw [hleft]
      infer_instance
    exact AlgebraicGeometry.IsClosedImmersion.of_comp e.inv.left e.hom.left
  have hL1 : (AlgebraicGeometry.Scheme.relativeProj.twist ((jetAlgebra f κ).veronese m) 1).IsLineBundle :=
    (AlgebraicGeometry.Scheme.relativeProj.twist_one_universalQuotient _ hgen).1 1
  -- general form (for any `g` equal to `i ≫ π'`), so that we can `subst`; this is the argument of
  -- `IsProjectiveMorphism.isQuasiProjective_isProper`.
  have key : ∀ (g : YGG f κ ⟶ C.toScheme),
      g = i ≫ (AlgebraicGeometry.Scheme.relativeProj ((jetAlgebra f κ).veronese m)).hom →
      AlgebraicGeometry.IsAmple
        ((AlgebraicGeometry.Scheme.Modules.pullback (g ⁻¹ᵁ V.1).ι).obj
          ((AlgebraicGeometry.Scheme.Modules.pullback i).obj
            (AlgebraicGeometry.Scheme.relativeProj.twist ((jetAlgebra f κ).veronese m) 1))) := by
    rintro g rfl
    have hamp := AlgebraicGeometry.Scheme.relativeProj.isAmple_twist_one_pullback_preimage_ι
      ((jetAlgebra f κ).veronese m) hgen hft V
    have hL2 : ((AlgebraicGeometry.Scheme.Modules.pullback
        (i ∣_ ((AlgebraicGeometry.Scheme.relativeProj ((jetAlgebra f κ).veronese m)).hom ⁻¹ᵁ V.1))).obj
          ((AlgebraicGeometry.Scheme.Modules.pullback
            ((AlgebraicGeometry.Scheme.relativeProj ((jetAlgebra f κ).veronese m)).hom ⁻¹ᵁ V.1).ι).obj
            (AlgebraicGeometry.Scheme.relativeProj.twist ((jetAlgebra f κ).veronese m) 1))).IsLineBundle :=
      AlgebraicGeometry.Scheme.Modules.IsLineBundle.pullback _ _
    have hamp' := AlgebraicGeometry.IsAmple.pullback_of_isClosedImmersion
      (i ∣_ ((AlgebraicGeometry.Scheme.relativeProj ((jetAlgebra f κ).veronese m)).hom ⁻¹ᵁ V.1)) _ hamp
    have hL3 : ((AlgebraicGeometry.Scheme.Modules.pullback
        ((i ≫ (AlgebraicGeometry.Scheme.relativeProj ((jetAlgebra f κ).veronese m)).hom) ⁻¹ᵁ V.1).ι).obj
          ((AlgebraicGeometry.Scheme.Modules.pullback i).obj
            (AlgebraicGeometry.Scheme.relativeProj.twist ((jetAlgebra f κ).veronese m) 1))).IsLineBundle :=
      AlgebraicGeometry.Scheme.Modules.IsLineBundle.pullback _ _
    have e' : (AlgebraicGeometry.Scheme.Modules.pullback
          (i ∣_ ((AlgebraicGeometry.Scheme.relativeProj ((jetAlgebra f κ).veronese m)).hom ⁻¹ᵁ V.1))).obj
          ((AlgebraicGeometry.Scheme.Modules.pullback
            ((AlgebraicGeometry.Scheme.relativeProj ((jetAlgebra f κ).veronese m)).hom ⁻¹ᵁ V.1).ι).obj
            (AlgebraicGeometry.Scheme.relativeProj.twist ((jetAlgebra f κ).veronese m) 1)) ≅
        (AlgebraicGeometry.Scheme.Modules.pullback
          ((i ≫ (AlgebraicGeometry.Scheme.relativeProj ((jetAlgebra f κ).veronese m)).hom) ⁻¹ᵁ V.1).ι).obj
          ((AlgebraicGeometry.Scheme.Modules.pullback i).obj
            (AlgebraicGeometry.Scheme.relativeProj.twist ((jetAlgebra f κ).veronese m) 1)) :=
      ((AlgebraicGeometry.Scheme.Modules.pullbackComp
          (i ∣_ ((AlgebraicGeometry.Scheme.relativeProj ((jetAlgebra f κ).veronese m)).hom ⁻¹ᵁ V.1))
          ((AlgebraicGeometry.Scheme.relativeProj ((jetAlgebra f κ).veronese m)).hom ⁻¹ᵁ V.1).ι).app
          (AlgebraicGeometry.Scheme.relativeProj.twist ((jetAlgebra f κ).veronese m) 1)) ≪≫
      ((AlgebraicGeometry.Scheme.Modules.pullbackCongr
          (AlgebraicGeometry.morphismRestrict_ι i
            ((AlgebraicGeometry.Scheme.relativeProj ((jetAlgebra f κ).veronese m)).hom ⁻¹ᵁ V.1))).app
          (AlgebraicGeometry.Scheme.relativeProj.twist ((jetAlgebra f κ).veronese m) 1)) ≪≫
      ((AlgebraicGeometry.Scheme.Modules.pullbackComp
          (i ⁻¹ᵁ ((AlgebraicGeometry.Scheme.relativeProj ((jetAlgebra f κ).veronese m)).hom ⁻¹ᵁ V.1)).ι i).app
          (AlgebraicGeometry.Scheme.relativeProj.twist ((jetAlgebra f κ).veronese m) 1)).symm
    exact @AlgebraicGeometry.IsAmple.of_iso _ _ _ hL2 hL3 e' hamp'
  have h1 := key (YGG.proj f κ) hover.symm
  have hLi : ((AlgebraicGeometry.Scheme.Modules.pullback i).obj
      (AlgebraicGeometry.Scheme.relativeProj.twist ((jetAlgebra f κ).veronese m) 1)).IsLineBundle :=
    AlgebraicGeometry.Scheme.Modules.IsLineBundle.pullback _ _
  have hL4 : ((AlgebraicGeometry.Scheme.Modules.pullback (YGG.proj f κ ⁻¹ᵁ V.1).ι).obj
        ((AlgebraicGeometry.Scheme.Modules.pullback i).obj
          (AlgebraicGeometry.Scheme.relativeProj.twist ((jetAlgebra f κ).veronese m) 1))).IsLineBundle :=
    AlgebraicGeometry.Scheme.Modules.IsLineBundle.pullback _ _
  exact @AlgebraicGeometry.IsAmple.of_iso _ _ _ hL4 inferInstance
    ((AlgebraicGeometry.Scheme.Modules.pullback (YGG.proj f κ ⁻¹ᵁ V.1).ι).mapIso φ.symm) h1

/-- On the fibration `Y_κ^GG → C`, the auxiliary data required by Lemma K′ exist: a line bundle `A` on `C` with a
nonzero global section `s_A` such that `B_κ ⊗ π_κ^*A` is ample.

**Key point**: only the projectivity of `C` is used to get an ample bundle, not the ampleness of `O_C(p₀)`, so
Riemann–Roch / Serre duality on curves are not needed.

**Source**: `isProjectiveOver_iff_isProper_and_isAmple` (`ProjectiveOverField`), the definition of `IsAmple`,
Stacks 0892(1) (`exists_isAmple_tensor_pullback_tensorPow`), the relative ampleness of `B_κ = O(m)`
(`polarization_isAmple_pullback_preimage_ι`), and tensor powers of sections (`s^{⊗e} ∈ Γ(M^{⊗e})`).

**Proof**:
1. `C` is projective over `K` (`SmoothProjectiveCurve.projective`); `isProjectiveOver_iff_isProper_and_isAmple` gives
   an ample line bundle `A₁` on `C`.
2. Pick any `x : C`; the definition of `IsAmple A₁` directly gives `m₁ > 0` and `s ∈ Γ(A₁^{⊗m₁}, ⊤)` such that `x` lies
   in the nonvanishing locus of `s`; in particular **`s ≠ 0`**. (This is "some power of an ample bundle has a
   nonzero section", without Riemann–Roch.)
3. `YGG.proj f κ` is quasi-compact and `polarization f κ m` is relatively ample over `C` (relative very ampleness of
   the Veronese polarization, then Stacks 01VJ(3): ample on the preimage of every affine open;
   `[Fact (SufficientlyDivisible m)]` guarantees that `O(m)` is invertible). `exists_isAmple_tensor_pullback_tensorPow`
   (Stacks 0892(1), `M := A₁`) gives `N₀` such that `polarization f κ m ⊗ (YGG.proj f κ)^*(A₁^{⊗a})` is ample for
   `a ≥ N₀`.
4. Take `e := m₁ * (N₀ + 1)` (`≥ N₀` and `≥ 1`), `A := A₁^{⊗e}`, `s_A := s^{⊗(N₀+1)}` (`sectionPow`; `s_A` is nonvanishing
   at `x`, hence `≠ 0`). Note that `π^*A = π^*(A₁^{⊗e})` is the bundle of step 3.
5. Rewrite the bundle `B ⊗ π^*(A₁^{⊗e})` of step 3 as `fiberedTwist π B A 1 1 = B^{⊗1} ⊗ (π^*A)^{⊗1}`: the difference
   is `tensorPow L 1 ≅ L` twice.

**Edge cases**: for `N₀ = 0`, `e = m₁ ≥ 1` and `A` is still a nontrivial power; `m₁ ≥ 1` is guaranteed by the definition
of `IsAmple`. Whether the zero scheme of `s_A` is empty is irrelevant here — inside Lemma K′ it is shown to be nonempty
(if it were empty, `π^*A|_W` would be trivial, `B|_W` ample and `Λ < 0`, contradicting `Λ > 0` there).

In the proof below, the relative ampleness of `B_κ` in step 3 is `polarization_isAmple_pullback_preimage_ι` (via the
Veronese closed immersion and the core of Stacks 07RL, `isAmple_twist_one_pullback_preimage_ι`); quasi-compactness
of `π_κ` follows from `YGG.proj_isProper` and Mathlib's `UniversallyClosed → QuasiCompact`; the existence of `x : C`
uses `C.connected` (`ConnectedSpace → Nonempty`). Neither `[IsAlgClosed K]`, nor `κ ≥ 1`, nor `CharZero` is needed. -/
theorem exists_ampleCurveBundle_with_section {K : Type u} [Field K] [IsAlgClosed K]
    {X : SmoothProjectiveVariety K} {C : SmoothProjectiveCurve K}
    (f : C.toScheme ⟶ X.toScheme) [MMSetup f] (κ m : ℕ)
    [Fact ((jetAlgebra f κ).SufficientlyDivisible m)] :
    ∃ (A : C.toScheme.Modules) (instA : A.IsLineBundle),
      letI : A.IsLineBundle := instA
      ∃ sA : Γ(A, ⊤), sA ≠ 0 ∧
        AlgebraicGeometry.IsAmple
          (fiberedTwist (YGG.proj f κ) (polarization f κ m) A 1 1) := by
  -- step 1: `C` projective ⇒ there is an ample line bundle `A₁`
  obtain ⟨_, A₁, instA₁, hA₁⟩ :=
    (isProjectiveOver_iff_isProper_and_isAmple K C.toScheme).mp C.projective
  have : A₁.IsLineBundle := instA₁
  -- step 2: pick any `x : C`; `IsAmple A₁` gives `m₁ > 0` and `s ∈ Γ(A₁^{⊗m₁})` nonvanishing at `x`
  have : ConnectedSpace C.toScheme := C.connected
  obtain ⟨x⟩ := (inferInstance : Nonempty C.toScheme)
  obtain ⟨m₁, hm₁, s, hxs, -⟩ := hA₁.2 x
  -- step 3: `π_κ` quasi-compact, `B_κ` relatively ample; Stacks 0892(1) gives `N₀`
  have : AlgebraicGeometry.IsProper (YGG.proj f κ) := YGG.proj_isProper f rfl κ
  have : AlgebraicGeometry.QuasiCompact (YGG.proj f κ) := inferInstance
  obtain ⟨N₀, hN₀⟩ := AlgebraicGeometry.exists_isAmple_tensor_pullback_tensorPow (YGG.proj f κ)
    (polarization f κ m) A₁ (polarization_isAmple_pullback_preimage_ι f κ m) hA₁
  -- step 4: `A := A₁^{⊗(m₁ (N₀+1))}`, `s_A := s^{⊗(N₀+1)}` via `(A₁^{⊗m₁})^{⊗(N₀+1)} ≅ A₁^{⊗(m₁(N₀+1))}`
  let A : C.toScheme.Modules := AlgebraicGeometry.Scheme.Modules.tensorPow A₁ (m₁ * (N₀ + 1))
  let Ψ := AlgebraicGeometry.Scheme.Modules.tensorPowMulIso A₁ m₁ (N₀ + 1)
  let sA : Γ(A, ⊤) := Ψ.hom.app ⊤ (AlgebraicGeometry.Scheme.Modules.tensorPowSection s (N₀ + 1))
  have hxA : x ∈ A.nonvanishingLocus sA := by
    refine (AlgebraicGeometry.Scheme.Modules.mem_nonvanishingLocus_iso Ψ
      (AlgebraicGeometry.Scheme.Modules.tensorPowSection s (N₀ + 1)) x).mpr ?_
    rw [AlgebraicGeometry.Scheme.Modules.nonvanishingLocus_tensorPowSection _ s (Nat.succ_pos N₀)]
    exact hxs
  refine ⟨A, inferInstance, sA, ?_, ?_⟩
  · -- `s_A ≠ 0`: the zero section vanishes everywhere
    intro h0
    rw [AlgebraicGeometry.Scheme.Modules.mem_nonvanishingLocus] at hxA
    apply hxA
    rw [h0]
    change (TopCat.Presheaf.germ A.presheaf ⊤ x trivial).hom 0 ∈ _
    rw [map_zero]
    exact Submodule.zero_mem _
  · -- step 5: `B ⊗ π^*A` is ample; rewrite as `fiberedTwist π B A 1 1 = B^{⊗1} ⊗ (π^*A)^{⊗1}`
    have hamp := hN₀ (m₁ * (N₀ + 1)) (by nlinarith)
    let P : (YGG f κ).Modules := (AlgebraicGeometry.Scheme.Modules.pullback (YGG.proj f κ)).obj A
    have : P.IsLineBundle := AlgebraicGeometry.Scheme.Modules.IsLineBundle.pullback _ _
    have e1 : AlgebraicGeometry.Scheme.Modules.tensor (polarization f κ m) P ≅
        AlgebraicGeometry.Scheme.Modules.tensor
          (AlgebraicGeometry.Scheme.Modules.tensorPow (polarization f κ m) 1)
          (AlgebraicGeometry.Scheme.Modules.tensorPow P 1) :=
      AlgebraicGeometry.Scheme.Modules.tensorCongrLeftIso
        (AlgebraicGeometry.Scheme.Modules.unitTensorIso (polarization f κ m)).symm P ≪≫
      AlgebraicGeometry.Scheme.Modules.tensorCongrRightIso _
        (AlgebraicGeometry.Scheme.Modules.unitTensorIso P).symm
    change AlgebraicGeometry.IsAmple (AlgebraicGeometry.Scheme.Modules.tensor
      (AlgebraicGeometry.Scheme.Modules.tensorPow (polarization f κ m) 1)
      (AlgebraicGeometry.Scheme.Modules.tensorPow P 1))
    exact AlgebraicGeometry.IsAmple.of_iso e1 hamp

/-- If the top self-intersection of a `ℚ`-divisor operator is negative, so is the (integer) top self-intersection of
a line bundle representing it.

If `(N:ℚ) • D = c₁(M)` then `(N•D)^s = N^s·(D^s)`, and `RatDivisorOp.topSelfIntersection` on a line bundle equals the
`ℚ`-image of `topSelfIntersection`. -/
theorem topSelfIntersection_neg_of_ratDivisorOp_neg {K : Type u} [Field K]
    (Y : AlgebraicGeometry.Scheme.{u}) [Y.Over (AlgebraicGeometry.Spec (CommRingCat.of K))]
    [AlgebraicGeometry.IsIntegral Y]
    (hY : IsProperOver K Y) (D : AlgebraicGeometry.RatDivisorOp Y) (N : ℕ) (hN : 0 < N)
    (M : Y.Modules) [M.IsLineBundle]
    (hDL : (N : ℚ) • D = AlgebraicGeometry.ratDivisorOpOfLineBundle M)
    (s : ℕ) (hs : Y.dimension = s)
    (hD : AlgebraicGeometry.RatDivisorOp.topSelfIntersection Y hY D s hs < 0) :
    AlgebraicGeometry.topSelfIntersection Y hY M < 0 := by
  have hscale : AlgebraicGeometry.RatDivisorOp.topSelfIntersection Y hY ((N : ℚ) • D) s hs =
      ((N : ℚ)) ^ s *
        AlgebraicGeometry.RatDivisorOp.topSelfIntersection Y hY D s hs := by
    unfold AlgebraicGeometry.RatDivisorOp.topSelfIntersection
    rw [AlgebraicGeometry.RatDivisorOp.capPow_smul]
    exact (AlgebraicGeometry.ChowGroupRat.degree Y hY).map_smul _ _
  rw [hDL, AlgebraicGeometry.RatDivisorOp.topSelfIntersection_lineBundle Y hY M s hs] at hscale
  have hNpos : (0 : ℚ) < ((N : ℚ)) ^ s := by
    have : (0 : ℚ) < (N : ℚ) := by exact_mod_cast hN
    positivity
  have : ((AlgebraicGeometry.topSelfIntersection Y hY M : ℤ) : ℚ) < 0 := by
    rw [hscale]
    exact mul_neg_of_pos_of_neg hNpos hD
  exact_mod_cast this

/-- **The statement needed for Lemma 2.5** (the conclusion of `exists_integralCurve_inter_neg`,
with the fibration data among the hypotheses instead of `hproj`): if the top self-intersection of `H'_κ` is negative,
there is an integral curve `Γ ⊂ Y_κ^GG` with `Γ.degree M < 0`, `M = shiftedBundle f κ m p₀ a b`.

The proof assembles `exists_ampleCurveBundle_with_section`, `topSelfIntersection_neg_of_ratDivisorOp_neg` and
Lemma K′. -/
theorem exists_integralCurve_shiftedBundle_degree_neg {K : Type u} [Field K] [IsAlgClosed K]
    {X : SmoothProjectiveVariety K} {C : SmoothProjectiveCurve K}
    (f : C.toScheme ⟶ X.toScheme) [MMSetup f] (κ m : ℕ)
    [Fact ((jetAlgebra f κ).SufficientlyDivisible m)]
    [AlgebraicGeometry.IsIntegral (YGG f κ)]
    (hY : IsProperOver K (YGG f κ))
    (p₀ : C.toScheme) (hp₀ : IsClosed ({p₀} : Set C.toScheme))
    (a b : ℕ) (hb : 0 < b)
    (D : AlgebraicGeometry.RatDivisorOp (YGG f κ)) (N : ℕ) (hN : 0 < N)
    (hDL : (N : ℚ) • D =
      AlgebraicGeometry.ratDivisorOpOfLineBundle (shiftedBundle f κ m p₀ a b))
    (s : ℕ) (hs : (YGG f κ).dimension = s)
    (hD : AlgebraicGeometry.RatDivisorOp.topSelfIntersection (YGG f κ) hY D s hs < 0) :
    ∃ Γ : IntegralCurve K (YGG f κ), Γ.degree (shiftedBundle f κ m p₀ a b) < 0 := by
  have : AlgebraicGeometry.Scheme.Hom.IsOver (YGG.proj f κ)
      (AlgebraicGeometry.Spec (CommRingCat.of K)) := ⟨rfl⟩
  obtain ⟨A, instA, sA, hsA, hA⟩ := exists_ampleCurveBundle_with_section f κ m
  have : A.IsLineBundle := instA
  -- `fiberedTwist (YGG.proj f κ) (polarization f κ m) (pointBundle p₀) b (m * a)` and
  -- `shiftedBundle f κ m p₀ a b` are definitionally equal (the two `IsLineBundle` instances are proofs of a `Prop`).
  have hM : fiberedTwist (YGG.proj f κ) (polarization f κ m) (pointBundle p₀) b (m * a) =
      shiftedBundle f κ m p₀ a b := rfl
  have hneg : AlgebraicGeometry.topSelfIntersection (YGG f κ) hY
      (fiberedTwist (YGG.proj f κ) (polarization f κ m) (pointBundle p₀) b (m * a)) < 0 :=
    topSelfIntersection_neg_of_ratDivisorOp_neg (YGG f κ) hY D N hN
      (shiftedBundle f κ m p₀ a b) hDL s hs hD
  obtain ⟨Γ, hΓ⟩ := exists_integralCurve_degree_neg_of_fibered p₀ hp₀ (YGG f κ) hY
    (YGG.proj f κ) (polarization f κ m) A sA hsA hA b (m * a) hb hneg
  exact ⟨Γ, hΓ⟩

end MiyaokaMori.FiberedNegativeCurve

end
