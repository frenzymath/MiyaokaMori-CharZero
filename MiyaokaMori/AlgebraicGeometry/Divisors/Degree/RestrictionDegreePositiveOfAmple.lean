import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Ample.AmpleLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.SectionIsZeroAt
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.SectionPullbackAlong
import MiyaokaMori.AlgebraicGeometry.Chow.IntersectionNumber.IntegralCurveDegree
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.IntegralCurveDegreeTensor
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.SectionPullbackNotZeroAt
import MiyaokaMori.AlgebraicGeometry.Varieties.Curves.IntegralCurve
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.RationalSectionDegree
import MiyaokaMori.AlgebraicGeometry.Chow.ChernClass.RationalSectionDivisorTensor
import MiyaokaMori.AlgebraicGeometry.Divisors.RationalSections.RationalSectionOrdGenerator
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModulePullbackStalkTensor
import MiyaokaMori.AlgebraicGeometry.Chow.Degree.ZeroCycleDegreePositivity
import MiyaokaMori.AlgebraicGeometry.Divisors.Degree.LineSectionCartierNonnegative

/-! # Positivity of the degree of an ample line bundle on a curve

The restriction of an ample line bundle to any integral curve has positive degree (used in the
proof of Lemma 5.1 of the paper, and for the positive anticanonical degree in
the proof of Theorem 1.3). The proof follows Stacks 0BEV (case `d = 1`) with the degree
relation `AlgebraicGeometry.Intersection.HasCurveModuleDegree`, which is the definition of `IntegralCurve.degree`.

Route (all steps formalized below; no Chow classes, no projection formula):
1. `IsAmple L` gives `m > 0` and `s ∈ Γ(X, L^{⊗m})` with `ι(η) ∈ X_s` and `X_s` affine (`η` the
   generic point of `Γ`).  Let `t := ι^*s ∈ Γ(Γ, ι^*L^{⊗m})`.
2. `t` is nonzero at `η` (`not_isZeroAt_sectionPullbackAlong`), so its generic germ `t_η ≠ 0`.
3. `t` vanishes at some point `x₀`: otherwise `ι⁻¹(X_s) = Γ` (a section vanishing at `ι x` pulls back
   to one vanishing at `x`), which is affine since `ι` is a closed immersion; but an integral curve
   proper over `k` is not affine (`IntegralCurve.not_isAffine`: proper + affine ⇒ finite ⇒ `Γ(Γ, 𝒪)`
   is a finite `k`-algebra ⇒ Artinian ⇒ `Γ` discrete ⇒ `dim Γ = 0 ≠ 1`).
4. `x₀ ≠ η` has coheight one, and `ord_{x₀}(t_η) > 0`
   (`rationalSectionOrd_pos_of_isZeroAt`: `t_{x₀} = a • e` with `e` a generator, `a ∈ 𝔪_{x₀}`,
   `ord(a) = length(𝒪/(a)) ≥ 1`).
5. Any Cartier presentation `Q` of `(ι^*L^{⊗m}, t_η)` has nonnegative coefficients
   (`coefficient_nonneg`) and coefficient `ord_{x₀}(t_η) > 0` at `x₀`, so its zero cycle has positive
   degree (`rawZeroCycleDegree_pos_of_nonneg`); by uniqueness of the degree relation this is
   `Γ.degree (L^{⊗m})`.
6. `Γ.degree (L^{⊗m}) = m · Γ.degree L` (`degree_tensorPow_of_field`), hence `Γ.degree L > 0`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-! ### Step A: degree is additive in tensor products over an arbitrary field

`IntegralCurve.degree_tensor` / `degree_tensorPow` in `IntegralCurveDegreeTensor.lean` carry a
superfluous `[IsAlgClosed K]`; the two statements are re-proved here for an arbitrary field. -/

private lemma degree_add_cycle' {K : Type u} [Field K]
    {W : AlgebraicGeometry.Scheme.{u}}
    [W.Over (AlgebraicGeometry.Spec (CommRingCat.of K))]
    (hW : IsProperOver K W)
    (A B : AlgebraicGeometry.AlgebraicCycle W ℤ) :
    AlgebraicGeometry.AlgebraicCycle.degree (k := K) (A + B) =
      AlgebraicGeometry.AlgebraicCycle.degree (k := K) A +
        AlgebraicGeometry.AlgebraicCycle.degree (k := K) B := by
  let : AlgebraicGeometry.IsProper
      (W ↘ AlgebraicGeometry.Spec (CommRingCat.of K)) := hW
  have hA' : (Function.support A).Finite :=
    AlgebraicGeometry.Intersection.properCycle_finiteSupport
      (W ↘ AlgebraicGeometry.Spec (CommRingCat.of K)) A
  have hB' : (Function.support B).Finite :=
    AlgebraicGeometry.Intersection.properCycle_finiteSupport
      (W ↘ AlgebraicGeometry.Spec (CommRingCat.of K)) B
  have hAdeg : Function.HasFiniteSupport
      (fun x : W => A x *
        ((W ↘ AlgebraicGeometry.Spec (CommRingCat.of K)).residueDegree x : ℤ)) :=
    Function.HasFiniteSupport.mul_left hA' _
  have hBdeg : Function.HasFiniteSupport
      (fun x : W => B x *
        ((W ↘ AlgebraicGeometry.Spec (CommRingCat.of K)).residueDegree x : ℤ)) :=
    Function.HasFiniteSupport.mul_left hB' _
  unfold AlgebraicGeometry.AlgebraicCycle.degree
  change (∑ᶠ x : W, (A x + B x) *
    ((W ↘ AlgebraicGeometry.Spec (CommRingCat.of K)).residueDegree x : ℤ)) = _
  rw [show (fun x : W => (A x + B x) *
      ((W ↘ AlgebraicGeometry.Spec (CommRingCat.of K)).residueDegree x : ℤ)) =
        (fun x : W => A x *
          ((W ↘ AlgebraicGeometry.Spec (CommRingCat.of K)).residueDegree x : ℤ) +
        B x * ((W ↘ AlgebraicGeometry.Spec (CommRingCat.of K)).residueDegree x : ℤ)) by
    funext x
    ring]
  exact finsum_add_distrib hAdeg hBdeg

/-- `IntegralCurve.degree_tensor` without the unused `[IsAlgClosed K]` (Stacks 02SL). -/
theorem IntegralCurve.degree_tensor_of_field {K : Type u} [Field K]
    {Y : AlgebraicGeometry.Scheme.{u}}
    [Y.Over (AlgebraicGeometry.Spec (CommRingCat.of K))]
    (Γ : IntegralCurve K Y)
    (A B : Y.Modules) [A.IsLineBundle] [B.IsLineBundle]
    [(AlgebraicGeometry.Scheme.Modules.tensor A B).IsLineBundle] :
    Γ.degree (AlgebraicGeometry.Scheme.Modules.tensor A B) =
      Γ.degree A + Γ.degree B := by
  let AΓ := (AlgebraicGeometry.Scheme.Modules.pullback Γ.ι).obj A
  let BΓ := (AlgebraicGeometry.Scheme.Modules.pullback Γ.ι).obj B
  let TΓ := (AlgebraicGeometry.Scheme.Modules.pullback Γ.ι).obj
    (AlgebraicGeometry.Scheme.Modules.tensor A B)
  let : AΓ.IsLineBundle :=
    AlgebraicGeometry.Scheme.Modules.IsLineBundle.pullback Γ.ι A
  let : BΓ.IsLineBundle :=
    AlgebraicGeometry.Scheme.Modules.IsLineBundle.pullback Γ.ι B
  let : TΓ.IsLineBundle :=
    AlgebraicGeometry.Scheme.Modules.IsLineBundle.pullback Γ.ι _
  have hdim : topologicalKrullDim Γ.carrier ≤ 1 := by
    rw [Γ.dim_eq_one]
  have hproper : IsProperOver K Γ.carrier := Γ.isProperOver
  let : AlgebraicGeometry.IsNoetherian Γ.carrier :=
    AlgebraicGeometry.Intersection.properFieldScheme_isNoetherian
      (Γ.ι ≫ (Y ↘ AlgebraicGeometry.Spec (CommRingCat.of K)))
  obtain ⟨s, hs⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_stalk_genericPoint_ne_zero AΓ
  obtain ⟨t, ht⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_stalk_genericPoint_ne_zero BΓ
  have hAeq : AlgebraicGeometry.AlgebraicCycle.degree (k := K)
      (AΓ.rationalSectionDivisor s) = Γ.degree A :=
    (Γ.degree_eq_degree_rationalSectionDivisor A s hs).symm
  have hBeq : AlgebraicGeometry.AlgebraicCycle.degree (k := K)
      (BΓ.rationalSectionDivisor t) = Γ.degree B :=
    (Γ.degree_eq_degree_rationalSectionDivisor B t ht).symm
  obtain ⟨v, hv, hdiv⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_rationalSectionDivisor_tensor
      AΓ BΓ s t hs ht
  have hiso := (AlgebraicGeometry.Scheme.Modules.pullbackTensorIso Γ.ι A B).symm
  have hTeq : AlgebraicGeometry.AlgebraicCycle.degree (k := K)
      ((AΓ.tensor BΓ).rationalSectionDivisor v) =
        Γ.degree (AlgebraicGeometry.Scheme.Modules.tensor A B) := by
    rw [Γ.degree_eq_topSelfIntersection,
      ← AlgebraicGeometry.topSelfIntersection_congr Γ.carrier Γ.isProperOver _ _ hiso,
      MiyaokaMori.TopSelfIntersectionCurve.topSelfIntersection_eq_degree_rationalSectionDivisor
        Γ.isProperOver Γ.carrier_dimension (AΓ.tensor BΓ) v hv]
  have hsum := degree_add_cycle' hproper
    (AΓ.rationalSectionDivisor s) (BΓ.rationalSectionDivisor t)
  calc
    Γ.degree (AlgebraicGeometry.Scheme.Modules.tensor A B) =
        AlgebraicGeometry.AlgebraicCycle.degree (k := K)
          ((AΓ.tensor BΓ).rationalSectionDivisor v) := hTeq.symm
    _ = AlgebraicGeometry.AlgebraicCycle.degree (k := K)
          (AΓ.rationalSectionDivisor s + BΓ.rationalSectionDivisor t) := by rw [hdiv]
    _ = _ := by rw [hsum, hAeq, hBeq]

/-- `IntegralCurve.degree_tensorPow` without the unused `[IsAlgClosed K]`. -/
theorem IntegralCurve.degree_tensorPow_of_field {K : Type u} [Field K]
    {Y : AlgebraicGeometry.Scheme.{u}}
    [Y.Over (AlgebraicGeometry.Spec (CommRingCat.of K))]
    (Γ : IntegralCurve K Y) (A : Y.Modules) [A.IsLineBundle] (q : ℕ) :
    Γ.degree (AlgebraicGeometry.Scheme.Modules.tensorPow A q) =
      (q : ℤ) * Γ.degree A := by
  induction q with
  | zero =>
      change Γ.degree (SheafOfModules.unit Y.ringCatSheaf) = _
      rw [IntegralCurve.degree_unit]
      simp
  | succ q ih =>
      change Γ.degree (AlgebraicGeometry.Scheme.Modules.tensor
        (AlgebraicGeometry.Scheme.Modules.tensorPow A q) A) = _
      rw [IntegralCurve.degree_tensor_of_field, ih]
      push_cast
      ring

/-! ### Step B: an integral curve is never affine

Stacks 0BEV (proof, "X is not affine"): an affine scheme proper over `k` is finite over `k`
(Mathlib `IsFinite.iff_isProper_and_isAffineHom`), so `Γ(C, 𝒪)` is a finite `k`-algebra, hence
Artinian, so `C ≅ Spec Γ(C, 𝒪)` is discrete and has Krull dimension `≤ 0`, contradicting `dim C = 1`. -/

theorem IntegralCurve.not_isAffine {k : Type u} [Field k] {X : AlgebraicGeometry.Scheme.{u}}
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (Γ : IntegralCurve k X) :
    ¬ AlgebraicGeometry.IsAffine Γ.carrier := by
  intro hC
  let p : Γ.carrier ⟶ AlgebraicGeometry.Spec (CommRingCat.of k) :=
    Γ.ι ≫ (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
  have : AlgebraicGeometry.IsProper p := Γ.isProper
  have : AlgebraicGeometry.IsFinite p :=
    AlgebraicGeometry.IsFinite.iff_isProper_and_isAffineHom.mpr ⟨inferInstance, inferInstance⟩
  have hfin : p.appTop.hom.Finite := p.finite_appTop
  let : Algebra Γ(AlgebraicGeometry.Spec (CommRingCat.of k), ⊤) Γ(Γ.carrier, ⊤) :=
    p.appTop.hom.toAlgebra
  have : Module.Finite Γ(AlgebraicGeometry.Spec (CommRingCat.of k), ⊤) Γ(Γ.carrier, ⊤) := hfin
  have : IsArtinianRing Γ(AlgebraicGeometry.Spec (CommRingCat.of k), ⊤) :=
    (AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv.symm.isArtinianRing
  have : IsArtinianRing Γ(Γ.carrier, ⊤) :=
    IsArtinianRing.of_finite Γ(AlgebraicGeometry.Spec (CommRingCat.of k), ⊤) Γ(Γ.carrier, ⊤)
  have : AlgebraicGeometry.IsLocallyArtinian (AlgebraicGeometry.Spec Γ(Γ.carrier, ⊤)) :=
    AlgebraicGeometry.Scheme.isLocallyArtinianScheme_Spec.mpr inferInstance
  have : AlgebraicGeometry.IsLocallyArtinian Γ.carrier :=
    AlgebraicGeometry.IsLocallyArtinian.of_isImmersion Γ.carrier.isoSpec.hom
  have h0 := topologicalKrullDim_zero_of_discreteTopology Γ.carrier
  rw [Γ.dim_eq_one] at h0
  exact absurd h0 (by decide)

/-! ### Step C: a point of a one-dimensional integral scheme other than the generic point has
coheight one (the generic point is the top of the specialization order; a non-generic point is not
maximal, so its coheight is `≥ 1`, and `≤ dim = 1`). -/

theorem AlgebraicGeometry.Scheme.coheight_eq_one_of_ne_genericPoint
    {C : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsIntegral C]
    (hC : topologicalKrullDim C = 1) {x : C} (hx : x ≠ genericPoint C) :
    Order.coheight x = 1 := by
  have hdim : Order.krullDim C = 1 := by
    calc
      Order.krullDim C = topologicalKrullDim C :=
        (Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := C))).symm
      _ = 1 := hC
  have hu : Order.coheight x ≤ 1 := by
    exact_mod_cast (Order.coheight_le_krullDim x).trans_eq hdim
  have hn : Order.coheight x ≠ 0 := by
    intro h0
    have hm : IsMax x := Order.coheight_eq_zero.mp h0
    apply hx
    have h1 : (⊤ : C) ≤ x := hm le_top
    have h2 : x ≤ (⊤ : C) := le_top
    exact ((AlgebraicGeometry.Scheme.le_iff_specializes.mp h1).antisymm
      (AlgebraicGeometry.Scheme.le_iff_specializes.mp h2)).eq
  exact le_antisymm hu (Order.one_le_iff_ne_zero.mpr hn)

/-! ### Step D: at a zero of a global section of a line bundle the order of vanishing is positive

Stacks 02SE / 02QU: write `t_x = a • e` with `e` a generator of `M_x`; `t_x ∈ 𝔪_x M_x` forces
`a ∈ 𝔪_x` (Nakayama for the rank-one stalk), and `ord_x(a) = length(𝒪_x/(a)) ≥ 1`. -/

theorem AlgebraicGeometry.Scheme.Modules.rationalSectionOrd_pos_of_isZeroAt
    {C : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsIntegral C]
    [AlgebraicGeometry.IsLocallyNoetherian C] (M : C.Modules) [M.IsLineBundle]
    (t : Γ(M, ⊤)) {x : C} (hx : Order.coheight x = 1) (hzero : IsZeroAt t x)
    (hη : M.presheaf.germ ⊤ (genericPoint C) trivial t ≠ 0) :
    0 < M.rationalSectionOrd (M.presheaf.germ ⊤ (genericPoint C) trivial t) x := by
  classical
  obtain ⟨e, he⟩ := AlgebraicGeometry.Scheme.Modules.exists_stalk_generator M x
  set tx : M.presheaf.stalk x := M.presheaf.germ ⊤ x trivial t with htx
  have hmem : tx ∈ Submodule.span (C.presheaf.stalk x) {e} := by rw [he]; trivial
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hmem
  set j := AlgebraicGeometry.Scheme.Modules.moduleStalkToGenericFiber C M x with hj
  have hjt : j tx = M.presheaf.germ ⊤ (genericPoint C) trivial t :=
    AlgebraicGeometry.Scheme.Modules.moduleStalkToGenericFiber_germ C M x ⊤ trivial t
  have hje : j (a • e) = algebraMap (C.presheaf.stalk x) C.functionField a • j e :=
    LinearMap.map_smulₛₗ j a e
  have hg : algebraMap (C.presheaf.stalk x) C.functionField a • j e =
      M.presheaf.germ ⊤ (genericPoint C) trivial t := by
    rw [← hje, ha, hjt]
  have ha0 : a ≠ 0 := by
    rintro rfl
    apply hη
    rw [← hg, map_zero, zero_smul]
  have hnu : ¬ IsUnit a := by
    intro hu
    have hze : tx ∈ (IsLocalRing.maximalIdeal (C.presheaf.stalk x)) •
        (⊤ : Submodule (C.presheaf.stalk x) (M.stalk x)) := hzero
    have he_mem : e ∈ (IsLocalRing.maximalIdeal (C.presheaf.stalk x)) •
        Submodule.span (C.presheaf.stalk x) {e} := by
      rw [he]
      obtain ⟨u, rfl⟩ := hu
      have : e = ((u⁻¹ : (C.presheaf.stalk x)ˣ) : C.presheaf.stalk x) • tx := by
        rw [← ha, smul_smul, Units.inv_mul, one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ hze
    obtain ⟨c, hc, hce⟩ := Submodule.mem_smul_span_singleton.mp he_mem
    have hunit : IsUnit (1 - c) :=
      IsLocalRing.isUnit_one_sub_self_of_mem_nonunits c ((IsLocalRing.mem_maximalIdeal c).mp hc)
    have hz : (1 - c) • e = 0 := by rw [sub_smul, one_smul, hce, sub_self]
    have he0 : e = 0 := by
      obtain ⟨v, hv⟩ := hunit
      have h2 : ((v⁻¹ : (C.presheaf.stalk x)ˣ) : C.presheaf.stalk x) • ((1 - c) • e) = 0 := by
        rw [hz, smul_zero]
      rwa [smul_smul, ← hv, Units.inv_mul, one_smul] at h2
    apply hη
    rw [← hg, he0, map_zero, smul_zero]
  have hmax : a ∈ IsLocalRing.maximalIdeal (C.presheaf.stalk x) :=
    (IsLocalRing.mem_maximalIdeal a).mpr hnu
  rw [AlgebraicGeometry.Scheme.Modules.rationalSectionOrd_eq_ord_of_generator M x e he _ _ hη hg]
  have : Ring.KrullDimLE 1 (C.presheaf.stalk x) := AlgebraicGeometry.krullDimLE_of_coheight_le hx.le
  have hg0 : algebraMap (C.presheaf.stalk x) C.functionField a ≠ 0 := by
    intro h0
    apply ha0
    exact IsFractionRing.injective (C.presheaf.stalk x) C.functionField (h0.trans (map_zero _).symm)
  have h1 : (1 : ℤ) ≤ C.ord (algebraMap (C.presheaf.stalk x) C.functionField a) x := by
    apply (AlgebraicGeometry.Scheme.le_ord_iff hx hg0).2
    change Multiplicative.ofAdd (1 : ℤ) ≤
      Ring.ordFrac (C.presheaf.stalk x) (algebraMap (C.presheaf.stalk x) C.functionField a)
    rw [Ring.ordFrac_eq_ord _ ha0]
    have hnz : a ∈ nonZeroDivisors (C.presheaf.stalk x) := mem_nonZeroDivisors_of_ne_zero ha0
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (Ring.ord_ne_top hnz)
    rw [Ring.ordMonoidWithZeroHom_eq_coe _ hnz hn.symm]
    have hpos : 0 < Ring.ord (C.presheaf.stalk x) a := by
      have : Nontrivial ((C.presheaf.stalk x) ⧸ Ideal.span {a}) :=
        Ideal.Quotient.nontrivial_iff.mpr (by rwa [Ne, Ideal.span_singleton_eq_top])
      exact Module.length_pos
    rw [← hn] at hpos
    have h1n : 1 ≤ n := by exact_mod_cast hpos
    exact WithZero.coe_le_coe.mpr (Multiplicative.ofAdd_le.mpr (by exact_mod_cast h1n))
  omega

/-! ### Step D0: a section vanishing at `g x` pulls back to a section vanishing at `x`

(Copy of `isZeroAt_sectionPullbackAlong_of_isZeroAt` from `SeedSectionInPunctured.lean`, whose import
closure is far heavier than needed here.)  The germ of the pulled-back section is the adjunction unit
applied to the original germ; the unit is semilinear over the local homomorphism `g^♯_x`, which maps
`𝔪_{g x}` into `𝔪_x`. -/

private theorem isZeroAt_sectionPullbackAlong_of_isZeroAt'
    {X Y : AlgebraicGeometry.Scheme.{u}} (g : X ⟶ Y)
    (M : Y.Modules) (s : (M.val.obj (Opposite.op ⊤) : Type u)) (x : X)
    (h : IsZeroAt s (g.base x)) : IsZeroAt (sectionPullbackAlong g s) x := by
  have hgerm :
      (((AlgebraicGeometry.Scheme.Modules.pullback g).obj M).presheaf.germ ⊤ x trivial).hom
          (sectionPullbackAlong g s) =
        AlgebraicGeometry.Scheme.Modules.modulePullbackStalkUnit g M x
          ((M.presheaf.germ ⊤ (g.base x) trivial).hom s) :=
    (AlgebraicGeometry.Scheme.Modules.modulePullbackStalkUnitAddHom_germ g M x ⊤ trivial s).symm
  have h' : (M.presheaf.germ ⊤ (g.base x) trivial).hom s ∈
      (IsLocalRing.maximalIdeal (Y.presheaf.stalk (g.base x))) •
        (⊤ : Submodule (Y.presheaf.stalk (g.base x)) (M.presheaf.stalk (g.base x))) := h
  have hle : (IsLocalRing.maximalIdeal (Y.presheaf.stalk (g.base x))) •
        (⊤ : Submodule (Y.presheaf.stalk (g.base x)) (M.presheaf.stalk (g.base x))) ≤
      Submodule.comap (AlgebraicGeometry.Scheme.Modules.modulePullbackStalkUnit g M x)
        ((IsLocalRing.maximalIdeal (X.presheaf.stalk x)) •
          (⊤ : Submodule (X.presheaf.stalk x) (AlgebraicGeometry.Scheme.Modules.modulePullbackStalk g M x))) := by
    refine Submodule.smul_le.2 (fun r hr n _ => ?_)
    rw [Submodule.mem_comap, LinearMap.map_smulₛₗ]
    exact Submodule.smul_mem_smul (map_nonunit _ r hr) Submodule.mem_top
  have hfin :
      (((AlgebraicGeometry.Scheme.Modules.pullback g).obj M).presheaf.germ ⊤ x trivial).hom
          (sectionPullbackAlong g s) ∈
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) •
          (⊤ : Submodule (X.presheaf.stalk x) (AlgebraicGeometry.Scheme.Modules.modulePullbackStalk g M x)) := by
    rw [hgerm]
    exact hle h'
  exact hfin

/-! ### Step E: the theorem -/

theorem degree_restrict_pos_of_ample {k : Type u} [Field k] {X : AlgebraicGeometry.Scheme.{u}}
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    {L : X.Modules} [L.IsLineBundle] (hL : AlgebraicGeometry.IsAmple L)
    (Γ : IntegralCurve k X) :
    0 < Γ.degree L := by
  classical
  obtain ⟨m, hm, s, hηs, hXs⟩ := hL.2 (Γ.ι.base (genericPoint Γ.carrier))
  let N : X.Modules := AlgebraicGeometry.Scheme.Modules.tensorPow L m
  let M : Γ.carrier.Modules := (AlgebraicGeometry.Scheme.Modules.pullback Γ.ι).obj N
  have : N.IsLineBundle := SheafOfModules.IsLineBundle.tensorPow L m
  have : M.IsLineBundle := AlgebraicGeometry.Scheme.Modules.IsLineBundle.pullback Γ.ι N
  let t : Γ(M, ⊤) := sectionPullbackAlong Γ.ι s
  have : AlgebraicGeometry.IsNoetherian Γ.carrier :=
    AlgebraicGeometry.Intersection.properFieldScheme_isNoetherian
      (Γ.ι ≫ (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))
  -- (a) the pulled-back section is nonzero at the generic point
  have hsη : ¬ IsZeroAt s (Γ.ι.base (genericPoint Γ.carrier)) := hηs
  have htη : ¬ IsZeroAt t (genericPoint Γ.carrier) :=
    not_isZeroAt_sectionPullbackAlong Γ.ι N s _ hsη
  have htη0 : M.presheaf.germ ⊤ (genericPoint Γ.carrier) trivial t ≠ 0 := by
    intro h0
    apply htη
    show M.presheaf.germ ⊤ (genericPoint Γ.carrier) trivial t ∈ _
    rw [h0]
    exact Submodule.zero_mem _
  -- (b) it vanishes somewhere, since otherwise Γ = ι⁻¹(X_s) would be affine
  have hex : ∃ x : Γ.carrier, IsZeroAt t x := by
    by_contra hno
    push Not at hno
    apply Γ.not_isAffine
    have htop : Γ.ι ⁻¹ᵁ (N.nonvanishingLocus s) = ⊤ := by
      apply top_le_iff.mp
      intro x _
      show Γ.ι.base x ∈ N.nonvanishingLocus s
      rw [AlgebraicGeometry.Scheme.Modules.mem_nonvanishingLocus]
      intro hz
      exact hno x (isZeroAt_sectionPullbackAlong_of_isZeroAt' Γ.ι N s x hz)
    have haff : AlgebraicGeometry.IsAffineOpen (Γ.ι ⁻¹ᵁ (N.nonvanishingLocus s)) :=
      hXs.preimage Γ.ι
    rw [htop] at haff
    exact (AlgebraicGeometry.IsAffine.iff_of_isIso (AlgebraicGeometry.Scheme.topIso Γ.carrier).hom).mp haff
  obtain ⟨x₀, hx₀⟩ := hex
  have hx₀η : x₀ ≠ genericPoint Γ.carrier := fun h => htη (h ▸ hx₀)
  have hcoh : Order.coheight x₀ = 1 :=
    AlgebraicGeometry.Scheme.coheight_eq_one_of_ne_genericPoint Γ.dim_eq_one hx₀η
  have hord : 0 < M.rationalSectionOrd (M.presheaf.germ ⊤ (genericPoint Γ.carrier) trivial t) x₀ :=
    AlgebraicGeometry.Scheme.Modules.rationalSectionOrd_pos_of_isZeroAt M t hcoh hx₀ htη0
  -- (c) hence deg(L^{⊗m}|_Γ) > 0
  have hN : 0 < Γ.degree N := by
    have : AlgebraicGeometry.IsProper (Γ.carrier ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      Γ.isProperOver
    have hdim : topologicalKrullDim Γ.carrier ≤ 1 := by
      rw [Γ.dim_eq_one]
    have hrank : AlgebraicGeometry.Scheme.Modules.IsLocallyFreeRank
        (⟨Γ.carrier, Γ.carrier ↘ AlgebraicGeometry.Spec (CommRingCat.of k)⟩ : AlgebraicGeometry.Proj.SchemeOver k)
        M 1 :=
      MiyaokaMori.RationalSectionDegree.isLocallyFreeRank_one_of_isLineBundle
        (⟨Γ.carrier, Γ.carrier ↘ AlgebraicGeometry.Spec (CommRingCat.of k)⟩ : AlgebraicGeometry.Proj.SchemeOver k) M
    obtain ⟨Q⟩ := AlgebraicGeometry.Divisors.LineCartierPresentationExistence.exists_lineCartierPresentation
      (⟨Γ.carrier, Γ.carrier ↘ AlgebraicGeometry.Spec (CommRingCat.of k)⟩ : AlgebraicGeometry.Proj.SchemeOver k)
      M hrank (M.presheaf.germ ⊤ (genericPoint Γ.carrier) trivial t) htη0
    have hQ := AlgebraicGeometry.Intersection.hasCurveModuleDegree_of_presentation
      (⟨Γ.carrier, Γ.carrier ↘ AlgebraicGeometry.Spec (CommRingCat.of k)⟩ : AlgebraicGeometry.Proj.SchemeOver k)
      M hdim (M.presheaf.germ ⊤ (genericPoint Γ.carrier) trivial t) Q
    have hd : Γ.degree N =
        AlgebraicGeometry.Intersection.rawZeroCycleDegree
          (Γ.carrier ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) (Q.cartier.zeroCycle hdim) :=
      Γ.degree_eq_of_hasCurveModuleDegree N hQ
    have hα : ∀ x : Γ.carrier, 0 ≤ (Q.cartier.zeroCycle hdim).1 x := fun x => by
      show 0 ≤ Q.cartier.coefficient x
      exact AlgebraicGeometry.Divisors.LineSectionCartierNonnegative.coefficient_nonneg
        (X := (⟨Γ.carrier, Γ.carrier ↘ AlgebraicGeometry.Spec (CommRingCat.of k)⟩ :
          AlgebraicGeometry.Proj.SchemeOver k)) t Q x
    have hα_ne : ∃ x : Γ.carrier, (Q.cartier.zeroCycle hdim).1 x ≠ 0 := by
      refine ⟨x₀, ?_⟩
      have hc := MiyaokaMori.RationalSectionDegree.coefficient_eq_rationalSectionOrd
        (⟨Γ.carrier, Γ.carrier ↘ AlgebraicGeometry.Spec (CommRingCat.of k)⟩ : AlgebraicGeometry.Proj.SchemeOver k)
        M (M.presheaf.germ ⊤ (genericPoint Γ.carrier) trivial t) Q x₀
      show Q.cartier.coefficient x₀ ≠ 0
      rw [hc]
      exact hord.ne'
    have hpos := AlgebraicGeometry.Intersection.rawZeroCycleDegree_pos_of_nonneg
      (Γ.carrier ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) (Q.cartier.zeroCycle hdim) hα hα_ne
    exact lt_of_lt_of_eq hpos hd.symm
  -- (d) deg(L^{⊗m}|_Γ) = m · deg(L|_Γ)
  have hmul : Γ.degree N = (m : ℤ) * Γ.degree L := Γ.degree_tensorPow_of_field L m
  rw [hmul] at hN
  exact pos_of_mul_pos_right hN (by exact_mod_cast hm.le)

end
