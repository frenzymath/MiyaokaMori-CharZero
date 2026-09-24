import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModuleLocalIso
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPullbackMonoidal
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorMonoidalIso
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.OfGradedQCAlgebra
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.GradedQuasicoherentAlgebra
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorPower
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjQC
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.RelativeProjTwistQC
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.SufficientlyDivisible
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.TwistMultiplication
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.TwistPowerIsoProjTwistZero
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.TwistPowerIsoUnitRestrictEval
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.TwistPowerIsoSectionsGeneration
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.RelativeProjEvaluation
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.Stacks01ms
import MiyaokaMori.AlgebraicGeometry.Modules.Glue.ModulesHomGlue

/-! # The tensor powers of the twisting sheaf: `O(m)^{⊗ℓ} ≅ O(ℓm)`

For a graded quasi-coherent algebra `S` over `X` and `m` sufficiently divisible, the multiplication maps
of the twisting sheaves on `Proj_X S` assemble to an isomorphism `O(m)^{⊗ℓ} ≅ O(ℓm)`. This is the reason
why the rational tautological class `H_k = c₁(O(m))/m` does not depend on the sufficiently divisible `m`
(Lemma 2.2 of the paper).

The isomorphism obligation `twistPowHom_isIso` is proved by induction on `ℓ`: every factor of the recursive
definition is an isomorphism. The key factor `twistMul S (ℓm) m` is an isomorphism because being an
isomorphism is local (`moduleHom_isIso_of_locally_isIso`), the glued morphism restricts on each chart to the
local piece (`restrictFunctor_map_glueHom`), the local piece is a pullback of `Proj.twistMul`
(`twistMulLocal_isIso`), and on the absolute Proj the local isomorphism of Stacks 01MS on `D₊(f)` with
`f ∈ 𝒜_m` together with the covering by these `D₊(f)` (`exists_basicOpen_mem_of_generatedInDegree`) finishes
the argument. Sufficient divisibility is transported from the sheaf level to the section rings by
`SufficientlyDivisible.toGradedAffineAlgebra` (`TwistPowerIsoSectionsGeneration`), and the unit
`O → O(0)` is an isomorphism by `TwistPowerIsoProjTwistZero` and `TwistPowerIsoUnitRestrictEval`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/- Construction: the multiplication map `Ψ_ℓ : O(m)^{⊗ℓ} → O(ℓm)`, following the recursion of `tensorPow`
   (with `τ := Modules.tensorIsoTensorObj` to pass to the monoidal `⊗` and take `tensorHom`):
   `ℓ = 0`: `O = π^*O → π^*S_0 → O(0)` (`S.one` pulled back, followed by the evaluation `relativeProj.evaluation S 0`,
   i.e. `1 ↦ 1`);
   `ℓ + 1`: `O(m)^{⊗ℓ} ⊗ O(m) → O(ℓm) ⊗ O(m) → O(ℓm + m)` (`relativeProj.twistMul`), with `eqToHom` moving the index.
   When `S` is sufficiently divisible at `m`, `Ψ_ℓ` is an isomorphism (checked locally by 01MS/01NR); this is the
   proof obligation, and the inverse is taken with `asIso`.

   The two branches of the recursion are the named definitions `twistPowHomZero` / `twistPowHomStep`, so that the
   unfolding lemmas `twistPowHom_zero` / `twistPowHom_succ` are `rfl` on small terms. Restating the recursive body
   verbatim and closing with `rfl`/`show`/`rw [twistPowHom]` made the kernel compare two spellings of the same
   recursive body, 30–60 s each. -/

/-- The `ℓ = 0` branch: `O ≅ π^*O → π^*S_0 → O(0)`, followed by moving the index `0` to `0 · m`. -/
noncomputable def AlgebraicGeometry.Scheme.relativeProj.twistPowHomZero {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) (m : ℕ) :
    AlgebraicGeometry.Scheme.Modules.tensorPow (AlgebraicGeometry.Scheme.relativeProj.twist S (m : ℤ)) 0 ⟶
      AlgebraicGeometry.Scheme.relativeProj.twist S ((0 * m : ℕ) : ℤ) :=
  (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso (AlgebraicGeometry.Scheme.relativeProj S).hom).inv ≫
    (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).map S.one ≫
    AlgebraicGeometry.Scheme.relativeProj.evaluation S 0 ≫
    CategoryTheory.eqToHom (congrArg (AlgebraicGeometry.Scheme.relativeProj.twist S) (by simp))

/-- The `ℓ + 1` branch: given `Ψ : O(m)^{⊗ℓ} → O(ℓm)`, form
`O(m)^{⊗ℓ} ⊗ O(m) → O(ℓm) ⊗ O(m) → O(ℓm + m) = O((ℓ+1)m)`. -/
noncomputable def AlgebraicGeometry.Scheme.relativeProj.twistPowHomStep {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) (m ℓ : ℕ)
    (Ψ : AlgebraicGeometry.Scheme.Modules.tensorPow (AlgebraicGeometry.Scheme.relativeProj.twist S (m : ℤ)) ℓ ⟶
      AlgebraicGeometry.Scheme.relativeProj.twist S ((ℓ * m : ℕ) : ℤ)) :
    AlgebraicGeometry.Scheme.Modules.tensorPow (AlgebraicGeometry.Scheme.relativeProj.twist S (m : ℤ)) (ℓ + 1) ⟶
      AlgebraicGeometry.Scheme.relativeProj.twist S (((ℓ + 1) * m : ℕ) : ℤ) :=
  (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _).hom ≫
    CategoryTheory.MonoidalCategoryStruct.tensorHom Ψ (CategoryTheory.CategoryStruct.id _) ≫
    (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _).inv ≫
    AlgebraicGeometry.Scheme.relativeProj.twistMul S _ _ ≫
    CategoryTheory.eqToHom (congrArg (AlgebraicGeometry.Scheme.relativeProj.twist S) (by push_cast; ring))

noncomputable def AlgebraicGeometry.Scheme.relativeProj.twistPowHom {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) (m : ℕ) : (ℓ : ℕ) →
    (AlgebraicGeometry.Scheme.Modules.tensorPow (AlgebraicGeometry.Scheme.relativeProj.twist S (m : ℤ)) ℓ ⟶
      AlgebraicGeometry.Scheme.relativeProj.twist S ((ℓ * m : ℕ) : ℤ))
  | 0 => AlgebraicGeometry.Scheme.relativeProj.twistPowHomZero S m
  | ℓ + 1 => AlgebraicGeometry.Scheme.relativeProj.twistPowHomStep S m ℓ
      (AlgebraicGeometry.Scheme.relativeProj.twistPowHom S m ℓ)

theorem AlgebraicGeometry.Scheme.relativeProj.twistPowHom_zero {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) (m : ℕ) :
    AlgebraicGeometry.Scheme.relativeProj.twistPowHom S m 0 =
      AlgebraicGeometry.Scheme.relativeProj.twistPowHomZero S m := rfl

theorem AlgebraicGeometry.Scheme.relativeProj.twistPowHom_succ {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) (m ℓ : ℕ) :
    AlgebraicGeometry.Scheme.relativeProj.twistPowHom S m (ℓ + 1) =
      AlgebraicGeometry.Scheme.relativeProj.twistPowHomStep S m ℓ
        (AlgebraicGeometry.Scheme.relativeProj.twistPowHom S m ℓ) := rfl

/-! ## The isomorphism obligation `twistPowHom_isIso`

`twistPowHom S m ℓ` is an isomorphism because every factor is: the `ℓ = 0` layer is
`O ≅ π^*O → π^*S_0 → O(0)` (`isIso_pullback_one_evaluation_zero`, which does not need `hm`); the `ℓ + 1` layer is
`tensorHom (twistPowHom ℓ) id` (induction hypothesis and Mathlib's `tensor_isIso`) followed by `twistMul S (ℓm) m`
(`twistMul_isIso_of_dvd`: for `m` sufficiently divisible and `m ∣ a`, `O(a) ⊗ O(b) → O(a+b)` is an isomorphism).
The latter is reduced as follows: being an isomorphism is local (`moduleHom_isIso_of_locally_isIso`); the glued
morphism restricts on a chart to the local piece (`restrictFunctor_map_glueHom`); the local piece is the pullback of
`Proj.twistMul` on `Proj A(U)` (`twistMulLocal_isIso`); on the absolute Proj, `Proj.twistMul 𝒜 a b` with `m ∣ a` is
an isomorphism on `D₊(f)` for `f ∈ 𝒜_m` (Stacks 01MS) and these `D₊(f)` cover
(`exists_basicOpen_mem_of_generatedInDegree`); sufficient divisibility passes from the sheaf to the section rings
(`SufficientlyDivisible.toGradedAffineAlgebra`). -/

set_option linter.style.haveILetI false in
/-- The canonical map `π^*O → π^*S_0 → O(0)` from the structure sheaf to `O(0)` is an isomorphism (no sufficient
divisibility needed). Source: Stacks 01MN/01MS (`O_{Proj A}(0) = O_{Proj A}`) and 01NR (on `π⁻¹U ≅ Proj A(U)` the
sheaf `O(n)` of the relative Proj is the `O(n)` of `Proj A(U)`).
Proof: being an isomorphism is local (`moduleHom_isIso_of_locally_isIso`), so check on `π⁻¹V` for affine `V`;
by `unitRestrictIso_hom_comp_restrict_eval` the restriction to `π⁻¹V`, up to isomorphisms at both ends, is the
pullback along `e` of `κ : 𝟙 → O(0)` on the absolute `Proj A(V)`, which is an isomorphism
(`Proj.isIso_unitToTwistZero`); functors preserve isomorphisms, and `IsIso.of_isIso_fac_left` /
`IsIso.of_isIso_comp_right` remove the isomorphisms at both ends. -/
theorem AlgebraicGeometry.Scheme.relativeProj.isIso_pullback_one_evaluation_zero
    {X : AlgebraicGeometry.Scheme.{u}} (S : X.GradedQCAlgebra) :
    CategoryTheory.IsIso
      ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).map S.one ≫
        AlgebraicGeometry.Scheme.relativeProj.evaluation S 0) := by
  apply AlgebraicGeometry.Scheme.Modules.moduleHom_isIso_of_locally_isIso
  intro x
  obtain ⟨V, hxV⟩ : ∃ V : X.affineOpens,
      (AlgebraicGeometry.Scheme.relativeProj S).hom.base x ∈ V.1 := by
    have hx : (AlgebraicGeometry.Scheme.relativeProj S).hom.base x ∈
        (⨆ U : X.affineOpens, (U : X.Opens)) := by
      rw [AlgebraicGeometry.iSup_affineOpens_eq_top]; trivial
    exact TopologicalSpace.Opens.mem_iSup.mp hx
  refine ⟨(AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ V.1, hxV, ?_⟩
  haveI hκ : CategoryTheory.IsIso (AlgebraicGeometry.Proj.unitToTwistZero (S.sectionsGrading V.1)) :=
    AlgebraicGeometry.Proj.isIso_unitToTwistZero (S.sectionsGrading V.1)
  haveI h1 : CategoryTheory.IsIso
      ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj.affineIso S V).hom).map
        (AlgebraicGeometry.Proj.unitToTwistZero (S.sectionsGrading V.1))) :=
    CategoryTheory.Functor.map_isIso _ _
  haveI h2 := CategoryTheory.IsIso.of_isIso_fac_left
    (AlgebraicGeometry.Scheme.relativeProj.unitRestrictIso_hom_comp_restrict_eval S V)
  exact CategoryTheory.IsIso.of_isIso_comp_right _
    (AlgebraicGeometry.Scheme.relativeProj.twistAffineIso S V 0).hom

/-- The subring closure `Subring.closure (𝒜 0 ∪ 𝒜 m)` is contained in `𝒜 0 + Ideal.span 𝒜 m` (the right-hand side
is a subring containing `𝒜 0 ∪ 𝒜 m`: `𝒜 0 · 𝒜 0 ⊆ 𝒜 0` and `span 𝒜 m` is an ideal; by `Subring.closure_induction`). -/
theorem AlgebraicGeometry.Proj.exists_mem_zero_sub_mem_span_of_mem_closure {σ A : Type u} [CommRing A]
    [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] (m : ℕ) {z : A}
    (hz : z ∈ Subring.closure ((𝒜 0 : Set A) ∪ (𝒜 m : Set A))) :
    ∃ a₀ ∈ 𝒜 0, z - a₀ ∈ Ideal.span (𝒜 m : Set A) := by
  induction hz using Subring.closure_induction with
  | mem y hy =>
    rcases hy with hy | hy
    · exact ⟨y, hy, by simp⟩
    · exact ⟨0, zero_mem _, by simpa using Ideal.subset_span hy⟩
  | zero => exact ⟨0, zero_mem _, by simp⟩
  | one => exact ⟨1, SetLike.one_mem_graded 𝒜, by simp⟩
  | add y w _ _ hy hw =>
    obtain ⟨a, ha, hya⟩ := hy
    obtain ⟨b, hb, hwb⟩ := hw
    refine ⟨a + b, add_mem ha hb, ?_⟩
    have : y + w - (a + b) = (y - a) + (w - b) := by ring
    rw [this]; exact Ideal.add_mem _ hya hwb
  | neg y _ hy =>
    obtain ⟨a, ha, hya⟩ := hy
    refine ⟨-a, neg_mem ha, ?_⟩
    have : -y - -a = -(y - a) := by ring
    rw [this]; exact neg_mem hya
  | mul y w _ _ hy hw =>
    obtain ⟨a, ha, hya⟩ := hy
    obtain ⟨b, hb, hwb⟩ := hw
    refine ⟨a * b, by simpa using SetLike.mul_mem_graded ha hb, ?_⟩
    have : y * w - a * b = (y - a) * w + a * (w - b) := by ring
    rw [this]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ hya) (Ideal.mul_mem_left _ _ hwb)

/-- A point `x` of `Proj 𝒜` (relevant homogeneous prime `p`) has a homogeneous element of positive degree outside
`p`: `p` does not contain the irrelevant ideal `𝒜₊`, so take `y ∈ 𝒜₊ \ p`; its degree-`0` component vanishes and `y`
is the sum of its positive-degree components, hence some component `g ∉ p`. -/
theorem AlgebraicGeometry.Proj.exists_homogeneous_pos_not_mem {σ A : Type u} [CommRing A]
    [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
    (x : AlgebraicGeometry.Proj 𝒜) :
    ∃ (i : ℕ) (g : A), 0 < i ∧ g ∈ 𝒜 i ∧ g ∉ x.asHomogeneousIdeal := by
  classical
  have hx := x.not_irrelevant_le
  rw [SetLike.not_le_iff_exists] at hx
  obtain ⟨y, hy, hyp⟩ := hx
  rw [HomogeneousIdeal.mem_irrelevant_iff] at hy
  by_contra h
  push Not at h
  apply hyp
  rw [← DirectSum.sum_support_decompose 𝒜 y]
  refine Ideal.sum_mem _ (fun i hi => ?_)
  by_cases hi0 : i = 0
  · subst hi0
    rw [← GradedRing.proj_apply, hy]
    exact Ideal.zero_mem _
  · exact h i _ (Nat.pos_of_ne_zero hi0) (DirectSum.decompose 𝒜 y i).2

/-- Covering of the absolute Proj: if the Veronese subalgebra `𝒜^{(m)}` is generated over `𝒜_0` by `𝒜_m` (`m > 0`),
then the `D₊(f)` with `f ∈ 𝒜_m` cover `Proj 𝒜`.
Source: the proof of Stacks 01MU (Proj is covered by the `D₊(f)`, `f` homogeneous of positive degree) and 01N0.
Proof: `x` corresponds to a relevant homogeneous prime `p`. Take a homogeneous `g ∈ 𝒜_e`, `e > 0`, `g ∉ p`
(`exists_homogeneous_pos_not_mem`). Then `g^m ∈ 𝒜_{m·e}` lies in `Subring.closure (𝒜_0 ∪ 𝒜_m) ⊆ 𝒜_0 + Ideal.span 𝒜_m`
(`exists_mem_zero_sub_mem_span_of_mem_closure`): `g^m = a_0 + y`. Since `span 𝒜_m` is a homogeneous ideal
(`Ideal.homogeneous_span`), take the degree-`m·e` component: the component of `a_0` is `0` (`m·e ≠ 0`), the
component of `y` is still in the span, and the component of `g^m` is `g^m` itself, so `g^m ∈ span 𝒜_m`.
If every `f ∈ 𝒜_m` lay in `p`, then `span 𝒜_m ≤ p`, so `g^m ∈ p` and, `p` being prime, `g ∈ p`, a contradiction. -/
theorem AlgebraicGeometry.Proj.exists_basicOpen_mem_of_generatedInDegree {σ A : Type u} [CommRing A]
    [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] (m : ℕ) (hm : 0 < m)
    (hgen : ∀ (k : ℕ) (a : A), a ∈ 𝒜 (m * k) → a ∈ Subring.closure ((𝒜 0 : Set A) ∪ (𝒜 m : Set A)))
    (x : AlgebraicGeometry.Proj 𝒜) :
    ∃ f ∈ 𝒜 m, x ∈ AlgebraicGeometry.Proj.basicOpen 𝒜 f := by
  classical
  obtain ⟨i, g, hi, hg, hgp⟩ := AlgebraicGeometry.Proj.exists_homogeneous_pos_not_mem 𝒜 x
  have hpow : g ^ m ∈ 𝒜 (m * i) := by
    have := SetLike.pow_mem_graded m hg
    simpa [smul_eq_mul] using this
  obtain ⟨a₀, ha₀, hI⟩ :=
    AlgebraicGeometry.Proj.exists_mem_zero_sub_mem_span_of_mem_closure 𝒜 m (hgen i (g ^ m) hpow)
  have hhom : (Ideal.span (𝒜 m : Set A)).IsHomogeneous 𝒜 :=
    Ideal.homogeneous_span 𝒜 _ (fun f hf => ⟨m, hf⟩)
  have hmi : m * i ≠ 0 := Nat.mul_ne_zero hm.ne' hi.ne'
  have hgI : g ^ m ∈ Ideal.span (𝒜 m : Set A) := by
    have h1 := hhom (m * i) hI
    rw [DirectSum.decompose_sub, DirectSum.sub_apply, AddSubgroupClass.coe_sub,
      DirectSum.decompose_of_mem_same 𝒜 hpow,
      DirectSum.decompose_of_mem_ne 𝒜 ha₀ (Ne.symm hmi), sub_zero] at h1
    exact h1
  by_contra hcon
  push Not at hcon
  have hle : Ideal.span (𝒜 m : Set A) ≤ x.asHomogeneousIdeal.toIdeal := by
    rw [Ideal.span_le]
    intro f hf
    have := hcon f hf
    rw [AlgebraicGeometry.Proj.mem_basicOpen] at this
    exact not_not.mp this
  exact hgp (x.isPrime.mem_of_pow_mem m (hle hgI))

/-- On the absolute Proj: if `𝒜^{(m)}` is generated over `𝒜_0` by `𝒜_m` (`m > 0`) and `m ∣ a`, then the
multiplication `Proj.twistMul 𝒜 a b : O(a) ⊗ O(b) → O(a + b)` is an isomorphism.
Source: Stacks 01MS (with `d = m`, `n = a/m`: on `D₊(f)`, `f ∈ 𝒜_m`, the map `O(nm) ⊗ O(b) → O(nm + b)` is an
isomorphism).
Proof: being an isomorphism is checked on an open cover (`moduleHom_isIso_of_locally_isIso`); every point `x` lies in
some `D₊(f)`, `f ∈ 𝒜_m` (`exists_basicOpen_mem_of_generatedInDegree`); on `D₊(f)` the second part of
`Proj.twist_mul_isIso_on_basicOpen` (01MS) gives the isomorphism. -/
theorem AlgebraicGeometry.Proj.twistMul_isIso_of_generatedInDegree {σ A : Type u} [CommRing A]
    [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜] (m : ℕ) (hm : 0 < m)
    (hgen : ∀ (k : ℕ) (a : A), a ∈ 𝒜 (m * k) → a ∈ Subring.closure ((𝒜 0 : Set A) ∪ (𝒜 m : Set A)))
    (a b : ℤ) (ha : (m : ℤ) ∣ a) :
    CategoryTheory.IsIso (AlgebraicGeometry.Proj.twistMul 𝒜 a b) := by
  apply AlgebraicGeometry.Scheme.Modules.moduleHom_isIso_of_locally_isIso
  intro x
  obtain ⟨f, hf, hx⟩ := AlgebraicGeometry.Proj.exists_basicOpen_mem_of_generatedInDegree 𝒜 m hm hgen x
  refine ⟨AlgebraicGeometry.Proj.basicOpen 𝒜 f, hx, ?_⟩
  obtain ⟨n, rfl⟩ := ha
  have h := (AlgebraicGeometry.Proj.twist_mul_isIso_on_basicOpen 𝒜 f hf hm n b).2
  rw [mul_comm n (m : ℤ)] at h
  exact h

/-- A morphism of sheaves of modules `glueHom` glued along an open cover restricts on the `i`-th piece of the cover
to the local morphism `f i`. Source: Mathlib's `TopCat.Sheaf.extend_hom_app` (a morphism extended from a basis is
the given component on basis elements), i.e. `glueHom_app`.
Proof: `restrict_map_eq_of_app_eq_sectionMap` (if every section map of `g` equals the `sectionMapOfRestrictHom` of
`φ`, then `g|_W = φ`) combined with `glueHom_app` (`restrictSectionMap` and `sectionMapOfRestrictHom` agree by
definition). -/
theorem AlgebraicGeometry.Scheme.Modules.restrictFunctor_map_glueHom {X : AlgebraicGeometry.Scheme.{u}}
    {ι : Type u} (U : ι → X.Opens) (hU : ⨆ i, U i = ⊤) (M N : X.Modules)
    (f : ∀ i, M.restrict (U i).ι ⟶ N.restrict (U i).ι)
    (hf : ∀ i j (V : X.Opens) (hi : V ≤ U i) (hj : V ≤ U j),
      AlgebraicGeometry.Scheme.Modules.restrictSectionMap (f i) V hi
        = AlgebraicGeometry.Scheme.Modules.restrictSectionMap (f j) V hj) (i : ι) :
    (AlgebraicGeometry.Scheme.Modules.restrictFunctor (U i).ι).map
        (AlgebraicGeometry.Scheme.Modules.glueHom U hU M N f hf) = f i :=
  AlgebraicGeometry.Scheme.Modules.restrict_map_eq_of_app_eq_sectionMap _ (f i)
    (fun V hV => AlgebraicGeometry.Scheme.Modules.glueHom_app U hU M N f hf i V hV)

/-- The local multiplication `twistMulLocal S a b U` is an isomorphism as soon as `Proj.twistMul (S(U)) a b` is:
the body of `twistMulLocal` is a composite of isomorphisms with `(pullback φ).map (Proj.twistMul …)`, and functors
preserve isomorphisms. -/
theorem AlgebraicGeometry.Scheme.relativeProj.twistMulLocal_isIso {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) (a b : ℤ) (U : X.affineOpens)
    [CategoryTheory.IsIso (AlgebraicGeometry.Proj.twistMul (S.sectionsGrading U.1) a b)] :
    CategoryTheory.IsIso (AlgebraicGeometry.Scheme.relativeProj.twistMulLocal S a b U) := by
  unfold AlgebraicGeometry.Scheme.relativeProj.twistMulLocal
  infer_instance

set_option linter.style.haveILetI false in
/-- For `m` sufficiently divisible and `m ∣ a`, the multiplication `twistMul S a b : O(a) ⊗ O(b) → O(a + b)` of the
relative Proj is an isomorphism.
Source: Stacks 01MS (an isomorphism on `D₊(f)`, `f ∈ A(U)_m`) and 01NR (the multiplication of the relative Proj is
chartwise the multiplication of `Proj A(U)`).
Proof: being an isomorphism is checked on the open cover `{π⁻¹U : U affine}` (`moduleHom_isIso_of_locally_isIso`;
the covering property is as in the body of `twistMul`); `twistMul` is a `glueHom`, whose restriction to `π⁻¹U` is
`twistMulLocal S a b U` (`restrictFunctor_map_glueHom`); the latter is an isomorphism as soon as
`Proj.twistMul (S(U)) a b` is (`twistMulLocal_isIso`), which follows from `A(U)` being generated in degree `m`
in the Veronese sense (`SufficientlyDivisible.toGradedAffineAlgebra` gives `GeneratedInDegree m`, i.e. every
`A(U)_{mk} ⊆ closure(A(U)_0 ∪ A(U)_m)`) and 01MS (`twistMul_isIso_of_generatedInDegree`). -/
theorem AlgebraicGeometry.Scheme.relativeProj.twistMul_isIso_of_dvd {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) (m : ℕ) (hm : S.SufficientlyDivisible m) (a b : ℤ) (ha : (m : ℤ) ∣ a) :
    CategoryTheory.IsIso (AlgebraicGeometry.Scheme.relativeProj.twistMul S a b) := by
  apply AlgebraicGeometry.Scheme.Modules.moduleHom_isIso_of_locally_isIso
  intro x
  obtain ⟨U, hxU⟩ : ∃ U : X.affineOpens,
      (AlgebraicGeometry.Scheme.relativeProj S).hom.base x ∈ U.1 := by
    have hx : (AlgebraicGeometry.Scheme.relativeProj S).hom.base x ∈
        (⨆ U : X.affineOpens, (U : X.Opens)) := by
      rw [AlgebraicGeometry.iSup_affineOpens_eq_top]; trivial
    exact TopologicalSpace.Opens.mem_iSup.mp hx
  refine ⟨(AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1, hxU, ?_⟩
  have hgen := hm.toGradedAffineAlgebra.2
  have hgen' : ∀ (k : ℕ) (a : S.sectionsRing U.1), a ∈ S.sectionsGrading U.1 (m * k) →
      a ∈ Subring.closure ((S.sectionsGrading U.1 0 : Set (S.sectionsRing U.1)) ∪
        (S.sectionsGrading U.1 m : Set (S.sectionsRing U.1))) :=
    fun k a ha => hgen (AlgebraicGeometry.Scheme.affineSite U) k a ha
  haveI : CategoryTheory.IsIso (AlgebraicGeometry.Proj.twistMul (S.sectionsGrading U.1) a b) :=
    AlgebraicGeometry.Proj.twistMul_isIso_of_generatedInDegree (S.sectionsGrading U.1) m hm.1 hgen' a b ha
  have key := AlgebraicGeometry.Scheme.relativeProj.twistMulLocal_isIso S a b U
  unfold AlgebraicGeometry.Scheme.relativeProj.twistMul
  dsimp only
  rw [AlgebraicGeometry.Scheme.Modules.restrictFunctor_map_glueHom
    (fun U : X.affineOpens => (AlgebraicGeometry.Scheme.relativeProj S).hom ⁻¹ᵁ U.1) _ _ _
    (AlgebraicGeometry.Scheme.relativeProj.twistMulLocal S a b) _ U]
  exact key

/-- `eqToHom` is an isomorphism, with the category instance as a variable (for `exact … _` on goals whose instance
is spelled differently: the `≫` in the bodies of `twistPowHomZero` / `twistPowHomStep` carries
`SheafOfModules.instCategory`, while the `IsIso` of the statement carries `Scheme.Modules.instCategory`, and
instance search does not connect them at reducible transparency). -/
theorem AlgebraicGeometry.Scheme.relativeProj.isIso_eqToHom_of_eq {C : Type*} [CategoryTheory.Category C]
    {X Y : C} (p : X = Y) : CategoryTheory.IsIso (CategoryTheory.eqToHom p) :=
  inferInstance

set_option linter.style.haveILetI false in
/-- The `ℓ = 0` branch is an isomorphism: `pullbackUnitIso.inv` and `eqToHom` are isomorphisms, and the middle
`π^*O → π^*S_0 → O(0)` is one by `isIso_pullback_one_evaluation_zero`. -/
theorem AlgebraicGeometry.Scheme.relativeProj.twistPowHomZero_isIso {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) (m : ℕ) :
    CategoryTheory.IsIso (AlgebraicGeometry.Scheme.relativeProj.twistPowHomZero S m) := by
  unfold AlgebraicGeometry.Scheme.relativeProj.twistPowHomZero
  rw [← CategoryTheory.Category.assoc
    ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).map S.one)
    (AlgebraicGeometry.Scheme.relativeProj.evaluation S 0)]
  refine @CategoryTheory.IsIso.comp_isIso _ _ _ _ _ _ _ (CategoryTheory.Iso.isIso_inv _) ?_
  refine @CategoryTheory.IsIso.comp_isIso _ _ _ _ _ _ _
    (AlgebraicGeometry.Scheme.relativeProj.isIso_pullback_one_evaluation_zero S) ?_
  exact AlgebraicGeometry.Scheme.relativeProj.isIso_eqToHom_of_eq _

/-- The `ℓ + 1` branch is an isomorphism as soon as `Ψ` and `twistMul S (ℓm) m` are: both ends of
`tensorIsoTensorObj`, `tensorHom Ψ (𝟙 _)` (Mathlib's `tensor_isIso`) and `eqToHom` are isomorphisms. -/
theorem AlgebraicGeometry.Scheme.relativeProj.twistPowHomStep_isIso {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) (m ℓ : ℕ)
    (Ψ : AlgebraicGeometry.Scheme.Modules.tensorPow (AlgebraicGeometry.Scheme.relativeProj.twist S (m : ℤ)) ℓ ⟶
      AlgebraicGeometry.Scheme.relativeProj.twist S ((ℓ * m : ℕ) : ℤ))
    [CategoryTheory.IsIso Ψ]
    [CategoryTheory.IsIso (AlgebraicGeometry.Scheme.relativeProj.twistMul S ((ℓ * m : ℕ) : ℤ) (m : ℤ))] :
    CategoryTheory.IsIso (AlgebraicGeometry.Scheme.relativeProj.twistPowHomStep S m ℓ Ψ) := by
  unfold AlgebraicGeometry.Scheme.relativeProj.twistPowHomStep
  refine @CategoryTheory.IsIso.comp_isIso _ _ _ _ _ _ _ (CategoryTheory.Iso.isIso_hom _) ?_
  refine @CategoryTheory.IsIso.comp_isIso _ _ _ _ _ _ _
    (CategoryTheory.MonoidalCategory.tensor_isIso Ψ (CategoryTheory.CategoryStruct.id _)) ?_
  refine @CategoryTheory.IsIso.comp_isIso _ _ _ _ _ _ _ (CategoryTheory.Iso.isIso_inv _) ?_
  refine @CategoryTheory.IsIso.comp_isIso _ _ _ _ _ _ _ inferInstance ?_
  exact AlgebraicGeometry.Scheme.relativeProj.isIso_eqToHom_of_eq _

set_option linter.style.haveILetI false in
/-- For `m` sufficiently divisible, `O(m)^{⊗ℓ} → O(ℓm)` is an isomorphism: `O(m)` is then a line bundle, on a standard
chart `D₊(f)` (`deg f ∣ m`) both sides are free of rank `1`, and the multiplication map sends the generator
`f^{m/d} ⊗ ⋯ ⊗ f^{m/d}` to `f^{ℓm/d}`. (The inverse of `twistPowIso` is obtained from this statement by `asIso`;
the inverse of an isomorphism is unique, so no choice is involved.)
Proof: induction on `ℓ`; every factor is an isomorphism (`isIso_pullback_one_evaluation_zero`, Mathlib's
`tensor_isIso`, `twistMul_isIso_of_dvd`), hence so is the composite. -/
theorem AlgebraicGeometry.Scheme.relativeProj.twistPowHom_isIso {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) (m ℓ : ℕ) (hm : S.SufficientlyDivisible m) :
    CategoryTheory.IsIso (AlgebraicGeometry.Scheme.relativeProj.twistPowHom S m ℓ) := by
  induction ℓ with
  | zero =>
    rw [AlgebraicGeometry.Scheme.relativeProj.twistPowHom_zero]
    exact AlgebraicGeometry.Scheme.relativeProj.twistPowHomZero_isIso S m
  | succ ℓ ih =>
    rw [AlgebraicGeometry.Scheme.relativeProj.twistPowHom_succ]
    haveI := AlgebraicGeometry.Scheme.relativeProj.twistMul_isIso_of_dvd S m hm
      ((ℓ * m : ℕ) : ℤ) (m : ℤ) ⟨(ℓ : ℤ), by push_cast; ring⟩
    exact AlgebraicGeometry.Scheme.relativeProj.twistPowHomStep_isIso S m ℓ _

/-- The isomorphism `O(m)^{⊗ℓ} ≅ O(ℓm)` for `m` sufficiently divisible, with underlying morphism `twistPowHom`. -/
noncomputable def AlgebraicGeometry.Scheme.relativeProj.twistPowIso {X : AlgebraicGeometry.Scheme.{u}}
    (S : X.GradedQCAlgebra) (m ℓ : ℕ) (hm : S.SufficientlyDivisible m) :
    AlgebraicGeometry.Scheme.Modules.tensorPow (AlgebraicGeometry.Scheme.relativeProj.twist S (m : ℤ)) ℓ ≅
      AlgebraicGeometry.Scheme.relativeProj.twist S ((ℓ * m : ℕ) : ℤ) :=
  haveI : CategoryTheory.IsIso (AlgebraicGeometry.Scheme.relativeProj.twistPowHom S m ℓ) :=
    AlgebraicGeometry.Scheme.relativeProj.twistPowHom_isIso S m ℓ hm
  CategoryTheory.asIso (AlgebraicGeometry.Scheme.relativeProj.twistPowHom S m ℓ)

end
