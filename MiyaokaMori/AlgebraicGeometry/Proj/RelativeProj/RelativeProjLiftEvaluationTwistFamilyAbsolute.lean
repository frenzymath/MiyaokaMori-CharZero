import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.ProjTwistingSheaf
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.Stacks01mw
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPullbackMonoidal
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorMonoidalIso
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjLiftEvaluationTwistFamilyAbsolutePullbackMul
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjLiftEvaluationTwistFamilyAbsoluteLocalGeneration
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.RelativeProjLiftEvaluationTwistFamilyAbsoluteChartFractions
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjLiftEvaluationTwistFamilyAbsoluteThetaHom

/-! # Twist families for `Proj.fromOfGlobalSections` (Stacks 01O4 (2), absolute Proj)

Setting: `𝒜` a graded ring, `Y` a scheme, `Φ : A →+* Γ(Y, O)` a ring homomorphism whose image of the irrelevant
ideal generates the unit ideal, `φ := Proj.fromOfGlobalSections 𝒜 Φ hΦ : Y ⟶ Proj 𝒜` (Mathlib), and
`O(n) := Proj.twist 𝒜 n` (Stacks 01MN).

Stacks 01O4 (2) says that `φ^*O(n) ≅ O_Y` compatibly with the multiplication maps `O(a) ⊗ O(b) → O(a+b)` and
with the given sections: the global section `a/1 = Proj.twistSection 𝒜 a` (`a ∈ 𝒜_n`) pulls back to `Φ(a)`.
We package the conclusion as a **twist family**: maps `χ_n : φ^*O(n) ⟶ O_Y`, `n : ℕ`, with
* (F') `χ_n(φ^*(a/1)) = Φ(a)` for `a ∈ 𝒜_n` (on every open `B`, after restriction), and
* (M') `χ_{a+b}(μ(x ⊗ y)) = χ_a(x) · χ_b(y)` for `μ := δ⁻¹ ≫ φ^*(twistMul)` (`mulHom`).

Two main results:
* `exists_homFamily` — existence. `χ_n` is the adjoint transpose of `θ_n : O(n) ⟶ φ_*O_Y`, whose section maps are
  `a/d ↦ Φ(a)Φ(d)⁻¹` on `φ⁻¹D₊(d)`; they are defined by a germ predicate and sheaf gluing
  (`…AbsoluteFracGerm.lean`, `…AbsoluteTheta.lean`, `…AbsoluteThetaHom.lean`), (F') is `θ_n(a/1) = Φ(a)` and (M') is
  the morphism identity `(δ⁻¹ ≫ φ^*twistMul) ≫ χ_{a+b} = (χ_a ⊗ χ_b) ≫ λ`, checked on pure tensors after transposing;
* `IsSectionFamily.eq` — uniqueness of the section maps (01O4 "up to strict equivalence"):
  the comparison principle `Modules.SectionMapPair.eq` (`…AbsoluteLocalGeneration.lean`: sections of a pullback are
  locally `O`-combinations of pulled-back sections, via the stalk formula `(φ^*O(n))_t = O_t ⊗ O(n)_{φ t}`) reduces
  everything to the pulled-back fractions `η(a/d)`, `d` of positive degree (`…AbsoluteChartFractions.lean`), where the
  key identity `c n (η(a/d)) · Φ(d) = Φ(a)` (`IsSectionFamily.mul_res_eq`: one application of (M') and two of (F'),
  through `(a/d)(d/1) = a/1` and `pullbackMulHom_app_tensorSections`, `…AbsolutePullbackMul.lean`) pins the value.

Everything here is about the absolute `Proj 𝒜`; no relative Proj appears. The relative statements
`LiftData.exists_twistFamily_of_piece` / `LiftData.twistFamily_sectionMap_unique`
(`RelativeProjLiftEvaluationTwistFamily.lean`) are obtained from these two by transport
(`RelativeProjLiftEvaluationTwistFamilyTransport.lean`). The special case `𝒜 = Sym` closes
`projBundle.lift_twist` (`ProjectiveBundleUniversalProperty.lean`) as well. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open scoped CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.Proj.TwistFamily

variable {A σ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A] (𝒜 : ℕ → σ) [GradedRing 𝒜]
  {Y : AlgebraicGeometry.Scheme.{u}} (Φ : A →+* Γ(Y, ⊤))
  (hΦ : (HomogeneousIdeal.irrelevant 𝒜).toIdeal.map Φ = ⊤)

/-- Every open of `Y` lies in `φ⁻¹ᵁ ⊤`. -/
theorem le_preimage_top (B : Y.Opens) :
    B ≤ AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ ⁻¹ᵁ ⊤ :=
  fun _ _ => trivial

/-- The pullback of the global section `a/1 = twistSection 𝒜 a` (`a ∈ 𝒜_n`) to `φ^*O(n)`, restricted to an open
`B ⊆ Y`: the adjunction unit `Γ(O(n), ⊤) → Γ(φ^*O(n), φ⁻¹⊤)` followed by restriction. -/
def pullSection {n : ℕ} (a : A) (ha : a ∈ 𝒜 n) (B : Y.Opens) : Γ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ)).obj (AlgebraicGeometry.Proj.twist 𝒜 (n : ℤ)), B) :=
  ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ)).obj (AlgebraicGeometry.Proj.twist 𝒜 (n : ℤ))).presheaf.map (homOfLE (le_preimage_top 𝒜 Φ hΦ B)).op
    (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction
        (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ)).unit.app
        (AlgebraicGeometry.Proj.twist 𝒜 (n : ℤ))).app ⊤
      (AlgebraicGeometry.Proj.twistSection 𝒜 a ha))

/-- `μ_{a b} : φ^*O(a) ⊗ φ^*O(b) ⟶ φ^*O(a+b)`: the inverse of the comparison map `δ` of the strong monoidal
pullback, followed by `φ^*` of the twist multiplication `Proj.twistMul 𝒜 a b` (Stacks 01MO), with the index
identity `(a : ℤ) + b = ((a + b : ℕ) : ℤ)` transported by `eqToHom`. This is the absolute counterpart of
`relativeProj.LiftData.twistMulHom` (same shape, `τ` replaced by `φ`, `relativeProj.twist S` by `Proj.twist 𝒜`). -/
def mulHom (a b : ℕ) : (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ)).obj (AlgebraicGeometry.Proj.twist 𝒜 (a : ℤ)) ⊗ (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ)).obj (AlgebraicGeometry.Proj.twist 𝒜 (b : ℤ)) ⟶ (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ)).obj (AlgebraicGeometry.Proj.twist 𝒜 ((a + b : ℕ) : ℤ)) :=
  CategoryTheory.inv (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom
      (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ)
      (AlgebraicGeometry.Proj.twist 𝒜 (a : ℤ)) (AlgebraicGeometry.Proj.twist 𝒜 (b : ℤ))) ≫
    (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ)).map
      ((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj
          (AlgebraicGeometry.Proj.twist 𝒜 (a : ℤ)) (AlgebraicGeometry.Proj.twist 𝒜 (b : ℤ))).inv ≫
        AlgebraicGeometry.Proj.twistMul 𝒜 (a : ℤ) (b : ℤ) ≫
        CategoryTheory.eqToHom (congrArg (AlgebraicGeometry.Proj.twist 𝒜) (Nat.cast_add a b).symm))

/-- **Twist section family.** A family of maps `c n B : Γ(φ^*O(n), B) → Γ(Y, B)` (all `n : ℕ`, all opens `B`)
which is additive, `Γ(Y, B)`-linear, compatible with restriction, and satisfies
* (F') `c n B (φ^*(a/1)|_B) = Φ(a)|_B` for `a ∈ 𝒜_n`;
* (M') `c (a+b) B (μ(x ⊗ y)) = c a B x * c b B y`.
The section maps of a twist family of morphisms (`IsHomFamily`) form such a family; conversely two such families
coincide (`IsSectionFamily.eq`). -/
structure IsSectionFamily (c : ∀ (n : ℕ) (B : Y.Opens), Γ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ)).obj (AlgebraicGeometry.Proj.twist 𝒜 (n : ℤ)), B) → Γ(Y, B)) : Prop where
  map_add : ∀ (n : ℕ) (B : Y.Opens) (x y : Γ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ)).obj (AlgebraicGeometry.Proj.twist 𝒜 (n : ℤ)), B)), c n B (x + y) = c n B x + c n B y
  map_smul : ∀ (n : ℕ) (B : Y.Opens) (r : Γ(Y, B)) (x : Γ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ)).obj (AlgebraicGeometry.Proj.twist 𝒜 (n : ℤ)), B)),
    c n B (r • x) = r * c n B x
  map_res : ∀ (n : ℕ) {B B' : Y.Opens} (h : B' ≤ B) (x : Γ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ)).obj (AlgebraicGeometry.Proj.twist 𝒜 (n : ℤ)), B)),
    c n B' (((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ)).obj (AlgebraicGeometry.Proj.twist 𝒜 (n : ℤ))).presheaf.map (homOfLE h).op x) = Y.presheaf.map (homOfLE h).op (c n B x)
  eval : ∀ (n : ℕ) (a : A) (ha : a ∈ 𝒜 n) (B : Y.Opens),
    c n B (pullSection 𝒜 Φ hΦ a ha B) = Y.presheaf.map (homOfLE le_top).op (Φ a)
  mul : ∀ (a b : ℕ) (B : Y.Opens) (x : Γ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ)).obj (AlgebraicGeometry.Proj.twist 𝒜 (a : ℤ)), B)) (y : Γ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ)).obj (AlgebraicGeometry.Proj.twist 𝒜 (b : ℤ)), B)),
    c (a + b) B ((mulHom 𝒜 Φ hΦ a b).app B (AlgebraicGeometry.Scheme.Modules.tensorSections _ _ B x y)) =
      c a B x * c b B y

/-- The section maps of a family of morphisms `χ n : φ^*O(n) ⟶ O_Y`. -/
def sectionMaps (χ : ∀ n : ℕ, (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ)).obj (AlgebraicGeometry.Proj.twist 𝒜 (n : ℤ)) ⟶ SheafOfModules.unit Y.ringCatSheaf) (n : ℕ)
    (B : Y.Opens) (x : Γ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ)).obj (AlgebraicGeometry.Proj.twist 𝒜 (n : ℤ)), B)) : Γ(Y, B) :=
  (χ n).app B x

/-- **Twist family of morphisms**: `χ n : φ^*O(n) ⟶ O_Y` whose section maps form a twist section family. -/
def IsHomFamily (χ : ∀ n : ℕ, (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ)).obj (AlgebraicGeometry.Proj.twist 𝒜 (n : ℤ)) ⟶ SheafOfModules.unit Y.ringCatSheaf) : Prop :=
  IsSectionFamily 𝒜 Φ hΦ (sectionMaps 𝒜 Φ hΦ χ)

/-- **Existence of a twist family (Stacks 01O4 (2), absolute form).** For `φ = fromOfGlobalSections 𝒜 Φ hΦ` there
are `χ_n : φ^*O(n) ⟶ O_Y` (`n : ℕ`) with `χ_n(φ^*(a/1)) = Φ(a)` (`a ∈ 𝒜_n`) and
`χ_{a+b}(μ(x ⊗ y)) = χ_a(x)χ_b(y)`.

**Natural-language proof (the formalized route; Stacks 01O4 (2), 01MN, 01MO).**
1. *The section maps `θ_n` (`…AbsoluteTheta.lean`).* For `g ∈ Γ(U, O(n))` define `θ_n g ∈ Γ(φ⁻¹U, O_Y)` as the
   unique section such that, whenever `g` is the fraction `a/d` on an open `W ∋ φ(t)` (`a ∈ 𝒜_p`, `d ∈ 𝒜_q`,
   `p = q + n`, `q > 0`, `W ≤ D₊(d)`), `germ_t(θ_n g)·Φ(d) = Φ(a)` in `O_{Y,t}` (`ThetaPred`).
   *Uniqueness*: `Φ(d)` is a unit at `t ∈ φ⁻¹D₊(d) = Y.basicOpen (Φ d)` (Mathlib
   `fromOfGlobalSections_preimage_basicOpen`), every section is locally such a fraction (01MN,
   `exists_res_eq_res_fracSection`: `0 = 0/s` for a chart element `s`, `exists_mem_basicOpen_of_irrelevant`), and
   sections of `O_Y` are determined by their germs. *Existence*: glue the local sections `Φ(a)Φ(d)⁻¹` on `φ⁻¹W`;
   two representations `a/d = a'/d'` near `φ(t)` mean `u(ad' − a'd) = 0` for some `u ∉ φ(t)`; a homogeneous component
   `u_i ∉ φ(t)` still kills `ad' − a'd`, and `v := u_i s` has positive degree with `t ∈ Y.basicOpen (Φ v)`, so
   `Φ(v)` is a unit at `t` and `germ_t Φ(ad' − a'd) = 0`, i.e. `Φ(a)Φ(d') = Φ(a')Φ(d)` at `t`
   (`germ_mul_eq_of_res_fracSection_eq`, `…AbsoluteFracGerm.lean`). The same identity shows that `θ_n` is additive,
   natural in `U`, multiplicative for the pointwise product of fractions (`(a/d)(a'/d') = aa'/(dd')`, 01MO) and
   `φ^♯`-linear: for `r = c/e` a degree-zero fraction near `φ(t)` (`c, e ∈ 𝒜_k`; multiply by `s` to get `k > 0`),
   `germ_t(φ^♯ r)·Φ(e) = Φ(c)` by the chart formula for `φ` (`fromOfGlobalSections_appLE_awayToSection_mk_mul`,
   `Stacks07rm_LiftSymImmersionOfCharts_ProjChart.lean`; `germ_app_mul_eq_of_res_eq_mk`).
2. *The morphisms (`…AbsoluteThetaHom.lean`).* `θ_n : O(n) ⟶ φ_*O_Y` is the morphism of `O_{Proj}`-modules with
   these section maps (`PresheafOfModules.homMk`), and `χ_n := θ_n^♭ : φ^*O(n) ⟶ O_Y` its adjoint transpose, so
   `χ_n(η g) = θ_n g` (`chi_app_pullbackUnitHom`, `Adjunction.homEquiv_unit`).
3. *(F').* `θ_n(a/1) = Φ(a)`, since `a/1 = a/1` with denominator `1` and `Φ(1) = 1` (`thetaSection_twistSection`);
   `pullSection a ha B` is `η(a/1)` restricted to `B`, and `χ_n` commutes with restriction.
4. *(M').* As morphisms `φ^*O(a) ⊗ φ^*O(b) ⟶ O_Y`: `μ ≫ χ_{a+b} = (χ_a ⊗ χ_b) ≫ λ` (`λ : O_Y ⊗ O_Y ≅ O_Y` is
   multiplication, `leftUnitor_app_tensorSections`). Cancel the isomorphism `δ` in `μ = δ⁻¹ ≫ φ^*(twistMul)`, transpose
   along `φ^* ⊣ φ_*` and compare on pure tensors `g ⊗ h` (`tensorObj_hom_ext`): the left side gives
   `θ_{a+b}(g·h)` and the right side `θ_a(g)·θ_b(h)` (`δ(η(g ⊗ h)) = η g ⊗ η h`,
   `pullbackTensorObjHom_app_unit_tensorSections`; `tensorHom_tensorSections`), equal by step 1
   (`mulHom_comp_chi`). Evaluating on `x ⊗ y` gives (M'). Additivity, linearity and naturality of the section maps
   of `χ_n` are those of a morphism of modules.

**Edge cases.** `n = 0`: `χ_0` is `φ^♯` on `O(0)` (same construction). `Y = ∅`: everything is `0`. `A` the zero ring:
`hΦ` forces `Γ(Y,⊤) = 0`, `Y = ∅`. `𝒜` not generated in degree 1: no assumption is used (weighted case included);
no quasi-coherence of `O(n)` is used. -/
theorem exists_homFamily :
    ∃ χ : ∀ n : ℕ, (AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ)).obj (AlgebraicGeometry.Proj.twist 𝒜 (n : ℤ)) ⟶ SheafOfModules.unit Y.ringCatSheaf, IsHomFamily 𝒜 Φ hΦ χ := by
  refine ⟨fun n => chi 𝒜 Φ hΦ n, ?_, ?_, ?_, ?_, ?_⟩
  · intro n B x y
    exact map_add ((chi 𝒜 Φ hΦ n).app B).hom x y
  · intro n B r x
    exact (chi 𝒜 Φ hΦ n).app_smul r x
  · intro n B B' h x
    exact AlgebraicGeometry.Scheme.Modules.hom_app_res_tfa (chi 𝒜 Φ hΦ n) h x
  · intro n a ha B
    refine (AlgebraicGeometry.Scheme.Modules.hom_app_res_tfa (chi 𝒜 Φ hΦ n) (le_preimage_top 𝒜 Φ hΦ B)
      (AlgebraicGeometry.Scheme.Modules.pullbackUnitHom (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ)
        (AlgebraicGeometry.Proj.twist 𝒜 (n : ℤ)) ⊤ (AlgebraicGeometry.Proj.twistSection 𝒜 a ha))).trans ?_
    have e := congrArg (fun z => Y.presheaf.map (homOfLE (le_preimage_top 𝒜 Φ hΦ B)).op z)
      (chi_app_pullbackUnitHom_twistSection 𝒜 Φ hΦ n a ha)
    exact e.trans (ring_res_res le_top (le_preimage_top 𝒜 Φ hΦ B) (Φ a))
  · intro a b B x y
    have e := congrArg (fun k => k.app B (AlgebraicGeometry.Scheme.Modules.tensorSections _ _ B x y))
      (mulHom_comp_chi 𝒜 Φ hΦ a b)
    refine Eq.trans ?_ (e.trans ?_)
    · rfl
    · refine (AlgebraicGeometry.Scheme.Modules.comp_app_apply' _ _ _ _).trans ?_
      have e2 := congrArg (fun z => (λ_ (𝟙_ Y.Modules)).hom.app B z)
        (AlgebraicGeometry.Scheme.Modules.tensorHom_tensorSections (chi 𝒜 Φ hΦ a) (chi 𝒜 Φ hΦ b) B x y)
      exact e2.trans (AlgebraicGeometry.Scheme.Modules.leftUnitor_app_tensorSections (𝟙_ Y.Modules) B _ _)

/-! ## Uniqueness: chart computations -/

section Unique


variable {𝒜 Φ hΦ}

/-- `pullSection a ha B` is the pulled-back section `η((a/1)|_V)|_B` for every `V` with `B ≤ φ⁻¹V`. -/
theorem pullSection_eq_pullbackSectionsOn {n : ℕ} (a : A) (ha : a ∈ 𝒜 n) (V : (AlgebraicGeometry.Proj 𝒜).Opens)
    (B : Y.Opens) (h : B ≤ AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ ⁻¹ᵁ V) :
    pullSection 𝒜 Φ hΦ a ha B =
      AlgebraicGeometry.Scheme.Modules.pullbackSectionsOn (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ)
        (AlgebraicGeometry.Proj.twist 𝒜 (n : ℤ)) V B h
        (MiyaokaMori.WeightedJets.ProjTwisting.homogeneousSection 𝒜 n a ha V) := by
  show ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ)).obj
      (AlgebraicGeometry.Proj.twist 𝒜 (n : ℤ))).presheaf.map (homOfLE (le_preimage_top 𝒜 Φ hΦ B)).op
      (AlgebraicGeometry.Scheme.Modules.pullbackUnitHom (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ)
        (AlgebraicGeometry.Proj.twist 𝒜 (n : ℤ)) ⊤ (AlgebraicGeometry.Proj.twistSection 𝒜 a ha)) =
    ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ)).obj
      (AlgebraicGeometry.Proj.twist 𝒜 (n : ℤ))).presheaf.map (homOfLE h).op
      (AlgebraicGeometry.Scheme.Modules.pullbackUnitHom (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ)
        (AlgebraicGeometry.Proj.twist 𝒜 (n : ℤ)) V
        ((AlgebraicGeometry.Proj.twist 𝒜 (n : ℤ)).presheaf.map (homOfLE le_top).op
          (AlgebraicGeometry.Proj.twistSection 𝒜 a ha)))
  exact ((congrArg (fun z => ((AlgebraicGeometry.Scheme.Modules.pullback
        (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ)).obj
        (AlgebraicGeometry.Proj.twist 𝒜 (n : ℤ))).presheaf.map (homOfLE h).op z)
      (AlgebraicGeometry.Scheme.Modules.pullbackUnitHom_restrict (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ)
        (AlgebraicGeometry.Proj.twist 𝒜 (n : ℤ)) le_top (AlgebraicGeometry.Proj.twistSection 𝒜 a ha))).trans
    (AlgebraicGeometry.Scheme.Modules.famRes_comp' _ _ _ _)).symm

/-- Restriction of a structure-sheaf section in two steps. -/
theorem ring_res_res_top {B B' : Y.Opens} (h : B' ≤ B) (r : Γ(Y, ⊤)) :
    Y.presheaf.map (homOfLE h).op (Y.presheaf.map (homOfLE le_top).op r) =
      Y.presheaf.map (homOfLE le_top).op r := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

/-- `Φ(d)` restricted to any open `B ≤ Y.basicOpen (Φ d)` is a unit (`RingedSpace.isUnit_res_basicOpen`). -/
theorem isUnit_res_of_le_basicOpen (d : A) {B : Y.Opens} (hB : B ≤ Y.basicOpen (Φ d)) :
    IsUnit (Y.presheaf.map (homOfLE le_top).op (Φ d) : Γ(Y, B)) := by
  have hu : IsUnit (Y.presheaf.map (homOfLE (Y.basicOpen_le (Φ d))).op (Φ d)) :=
    AlgebraicGeometry.RingedSpace.isUnit_res_basicOpen (X := Y.toLocallyRingedSpace.toRingedSpace) (Φ d)
  have h2 := ring_res_res_top hB (Φ d)
  have := hu.map (Y.presheaf.map (homOfLE hB).op).hom
  change IsUnit (Y.presheaf.map (homOfLE hB).op (Y.presheaf.map (homOfLE le_top).op (Φ d))) at this
  rw [h2] at this
  exact this

variable {c : ∀ (n : ℕ) (B : Y.Opens), Γ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ)).obj (AlgebraicGeometry.Proj.twist 𝒜 (n : ℤ)), B) → Γ(Y, B)}

theorem IsSectionFamily.map_zero (hc : IsSectionFamily 𝒜 Φ hΦ c) (n : ℕ) (B : Y.Opens) : c n B 0 = 0 := by
  have h := hc.map_add n B 0 0
  rw [add_zero] at h
  exact (add_left_cancel (a := c n B 0) (by rw [add_zero]; exact h)).symm

/-- **The key identity** (Stacks 01MN/01MO): for `d ∈ 𝒜 q`, `a ∈ 𝒜 p`, `p = q + n` and `B ≤ φ⁻¹D₊(d)`, a twist
section family satisfies `c n B (η(a/d)|_B) · Φ(d)|_B = Φ(a)|_B`. Proof: `(a/d)(d/1) = a/1` in `Γ(D₊(d), O(n+q))`
(`twistSectionMul_fracSection_homogeneousSection`), transported by `mulHom` (`pullbackMulHom_app_tensorSections`),
then (M') once and (F') twice. -/
theorem IsSectionFamily.mul_res_eq (hc : IsSectionFamily 𝒜 Φ hΦ c) (n : ℕ) {p q : ℕ} (a d : A) (ha : a ∈ 𝒜 p)
    (hd : d ∈ 𝒜 q) (hpq : (p : ℤ) = q + n) (B : Y.Opens)
    (h : B ≤ AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 d) :
    c n B (AlgebraicGeometry.Scheme.Modules.pullbackSectionsOn (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ)
          (AlgebraicGeometry.Proj.twist 𝒜 (n : ℤ)) (AlgebraicGeometry.Proj.basicOpen 𝒜 d) B h
          (AlgebraicGeometry.Proj.fracSection 𝒜 (n : ℤ) a d ha hd hpq)) *
        Y.presheaf.map (homOfLE le_top).op (Φ d) =
      Y.presheaf.map (homOfLE le_top).op (Φ a) := by
  have ha' : a ∈ 𝒜 (n + q) := by
    have hp : p = n + q := by omega
    exact hp ▸ ha
  set X := AlgebraicGeometry.Scheme.Modules.pullbackSectionsOn (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ)
    (AlgebraicGeometry.Proj.twist 𝒜 (n : ℤ)) (AlgebraicGeometry.Proj.basicOpen 𝒜 d) B h
    (AlgebraicGeometry.Proj.fracSection 𝒜 (n : ℤ) a d ha hd hpq) with hX
  set Yd := AlgebraicGeometry.Scheme.Modules.pullbackSectionsOn (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ)
    (AlgebraicGeometry.Proj.twist 𝒜 (q : ℤ)) (AlgebraicGeometry.Proj.basicOpen 𝒜 d) B h
    (MiyaokaMori.WeightedJets.ProjTwisting.homogeneousSection 𝒜 q d hd (AlgebraicGeometry.Proj.basicOpen 𝒜 d)) with hYd
  have hy : Yd = pullSection 𝒜 Φ hΦ d hd B := (pullSection_eq_pullbackSectionsOn d hd _ B h).symm
  have e1 := hc.mul n q B X Yd
  have hprod : (AlgebraicGeometry.Proj.twistMul 𝒜 (n : ℤ) (q : ℤ) ≫
      CategoryTheory.eqToHom (congrArg (AlgebraicGeometry.Proj.twist 𝒜) (Nat.cast_add n q).symm)).app
        (AlgebraicGeometry.Proj.basicOpen 𝒜 d)
        (AlgebraicGeometry.Scheme.Modules.moduleTensorSection (AlgebraicGeometry.Proj.fracSection 𝒜 (n : ℤ) a d ha hd hpq)
          (MiyaokaMori.WeightedJets.ProjTwisting.homogeneousSection 𝒜 q d hd (AlgebraicGeometry.Proj.basicOpen 𝒜 d))) =
      MiyaokaMori.WeightedJets.ProjTwisting.homogeneousSection 𝒜 (n + q) a ha' (AlgebraicGeometry.Proj.basicOpen 𝒜 d) :=
    (AlgebraicGeometry.Scheme.Modules.comp_app_apply' _ _ _ _).trans
      ((congrArg (fun z => (CategoryTheory.eqToHom
          (congrArg (AlgebraicGeometry.Proj.twist 𝒜) (Nat.cast_add n q).symm)).app
          (AlgebraicGeometry.Proj.basicOpen 𝒜 d) z)
        (AlgebraicGeometry.Proj.twistMul_app_moduleTensorSection_tfa 𝒜 (n : ℤ) (q : ℤ) _ _ _)).trans
        (congrArg (fun z => (CategoryTheory.eqToHom
          (congrArg (AlgebraicGeometry.Proj.twist 𝒜) (Nat.cast_add n q).symm)).app
          (AlgebraicGeometry.Proj.basicOpen 𝒜 d) z)
        (AlgebraicGeometry.Proj.twistSectionMul_fracSection_homogeneousSection 𝒜 n a d ha hd hpq ha')))
  have e2 : (mulHom 𝒜 Φ hΦ n q).app B (AlgebraicGeometry.Scheme.Modules.tensorSections _ _ B X Yd) =
      pullSection 𝒜 Φ hΦ a ha' B :=
    (AlgebraicGeometry.Scheme.Modules.pullbackMulHom_app_tensorSections
        (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ) (AlgebraicGeometry.Proj.twist 𝒜 (n : ℤ))
        (AlgebraicGeometry.Proj.twist 𝒜 (q : ℤ)) (AlgebraicGeometry.Proj.twist 𝒜 ((n + q : ℕ) : ℤ))
        (AlgebraicGeometry.Proj.twistMul 𝒜 (n : ℤ) (q : ℤ) ≫
          CategoryTheory.eqToHom (congrArg (AlgebraicGeometry.Proj.twist 𝒜) (Nat.cast_add n q).symm))
        (AlgebraicGeometry.Proj.basicOpen 𝒜 d) B h _ _).trans
      ((congrArg (fun z => AlgebraicGeometry.Scheme.Modules.pullbackSectionsOn
          (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ) (AlgebraicGeometry.Proj.twist 𝒜 ((n + q : ℕ) : ℤ))
          (AlgebraicGeometry.Proj.basicOpen 𝒜 d) B h z) hprod).trans
        (pullSection_eq_pullbackSectionsOn a ha' _ B h).symm)
  have e3 : c q B Yd = Y.presheaf.map (homOfLE le_top).op (Φ d) :=
    (congrArg (c q B) hy).trans (hc.eval q d hd B)
  have e4 : c (n + q) B (pullSection 𝒜 Φ hΦ a ha' B) = Y.presheaf.map (homOfLE le_top).op (Φ a) :=
    hc.eval (n + q) a ha' B
  calc c n B X * Y.presheaf.map (homOfLE le_top).op (Φ d) = c n B X * c q B Yd := by rw [e3]
    _ = c (n + q) B ((mulHom 𝒜 Φ hΦ n q).app B (AlgebraicGeometry.Scheme.Modules.tensorSections _ _ B X Yd)) :=
        e1.symm
    _ = c (n + q) B (pullSection 𝒜 Φ hΦ a ha' B) := congrArg (c (n + q) B) e2
    _ = Y.presheaf.map (homOfLE le_top).op (Φ a) := e4

variable {c' : ∀ (n : ℕ) (B : Y.Opens), Γ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ)).obj (AlgebraicGeometry.Proj.twist 𝒜 (n : ℤ)), B) → Γ(Y, B)}

/-- Two twist section families agree, near every point, on every pulled-back section `η(g)|_{B'}`: reduce to a
fraction `a/d` on a chart `D₊(d)` (`exists_res_eq_fracSection`), apply the key identity to both families and cancel
the unit `Φ(d)`. -/
theorem IsSectionFamily.exists_nhds_eq_on_pullback (hc : IsSectionFamily 𝒜 Φ hΦ c) (hc' : IsSectionFamily 𝒜 Φ hΦ c')
    (n : ℕ) (V : (AlgebraicGeometry.Proj 𝒜).Opens) (g : Γ(AlgebraicGeometry.Proj.twist 𝒜 (n : ℤ), V)) (B : Y.Opens)
    (h : B ≤ AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ ⁻¹ᵁ V) (t : Y) (ht : t ∈ B) :
    ∃ (B' : Y.Opens) (_ : t ∈ B') (h' : B' ≤ B),
      c n B' (AlgebraicGeometry.Scheme.Modules.pullbackSectionsOn (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ)
          (AlgebraicGeometry.Proj.twist 𝒜 (n : ℤ)) V B' (h'.trans h) g) =
        c' n B' (AlgebraicGeometry.Scheme.Modules.pullbackSectionsOn (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ)
          (AlgebraicGeometry.Proj.twist 𝒜 (n : ℤ)) V B' (h'.trans h) g) := by
  obtain ⟨e, s, he, hs, hts⟩ := exists_mem_basicOpen_of_irrelevant' 𝒜 Φ hΦ t
  have hφs : (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ).base t ∈ AlgebraicGeometry.Proj.basicOpen 𝒜 s := by
    have : t ∈ AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 s := by
      rw [AlgebraicGeometry.Proj.fromOfGlobalSections_preimage_basicOpen 𝒜 Φ hΦ he hs]
      exact hts
    exact this
  obtain ⟨W, hxW, hWV, hcase⟩ := AlgebraicGeometry.Proj.exists_res_eq_fracSection 𝒜 (n : ℤ) g (h ht) hs hφs
  have htB' : t ∈ B ⊓ AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ ⁻¹ᵁ W := ⟨ht, hxW⟩
  refine ⟨B ⊓ AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ ⁻¹ᵁ W, htB', inf_le_left, ?_⟩
  have h₂ : B ⊓ AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ ⁻¹ᵁ W ≤
      AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ ⁻¹ᵁ W := inf_le_right
  rw [AlgebraicGeometry.Scheme.Modules.pullbackSectionsOn_res_source _ _ hWV (inf_le_left.trans h) h₂ g]
  rcases hcase with h0 | ⟨p, q, a, d, ha, hd, hpq, heq, hW, hfrac⟩
  · rw [h0, AlgebraicGeometry.Scheme.Modules.pullbackSectionsOn_zero, hc.map_zero, hc'.map_zero]
  · have hq : 0 < q := lt_of_lt_of_le he heq
    have hBd : B ⊓ AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ ⁻¹ᵁ W ≤
        AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 d :=
      fun x hx => hW (h₂ hx)
    have hBd' : B ⊓ AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ ⁻¹ᵁ W ≤ Y.basicOpen (Φ d) := by
      rw [← AlgebraicGeometry.Proj.fromOfGlobalSections_preimage_basicOpen 𝒜 Φ hΦ hq hd]
      exact hBd
    rw [hfrac, ← AlgebraicGeometry.Scheme.Modules.pullbackSectionsOn_res_source _ _ hW hBd h₂
      (AlgebraicGeometry.Proj.fracSection 𝒜 (n : ℤ) a d ha hd hpq)]
    exact (isUnit_res_of_le_basicOpen d hBd').mul_left_injective
      ((hc.mul_res_eq n a d ha hd hpq _ hBd).trans (hc'.mul_res_eq n a d ha hd hpq _ hBd).symm)

/-- The comparison data of `Modules.SectionMapPair` for two twist section families in degree `n`. -/
theorem IsSectionFamily.sectionMapPair (hc : IsSectionFamily 𝒜 Φ hΦ c) (hc' : IsSectionFamily 𝒜 Φ hΦ c') (n : ℕ) :
    AlgebraicGeometry.Scheme.Modules.SectionMapPair (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ)
      (AlgebraicGeometry.Proj.twist 𝒜 (n : ℤ)) (c n) (c' n) where
  add := hc.map_add n
  add' := hc'.map_add n
  smul := hc.map_smul n
  smul' := hc'.map_smul n
  res := fun h x => hc.map_res n h x
  res' := fun h x => hc'.map_res n h x
  gen := fun V g B h t ht => hc.exists_nhds_eq_on_pullback hc' n V g B h t ht

end Unique

/-- **Uniqueness of twist section families (Stacks 01O4, "up to strict equivalence"; 01MN for the generators).**
Two twist section families for the same `(𝒜, Φ)` are equal.

**Natural-language proof (the formalized route).** Fix `n`, an open `B` and `x ∈ Γ(φ^*O(n), B)`; we show
`c n B x = c' n B x`. Since `O_Y` is a sheaf it suffices to do so after restriction to a neighbourhood of each
`t ∈ B` (both families commute with restriction, `map_res`).
1. *Local generators.* The stalk `(φ^*O(n))_t ≅ O_{Y,t} ⊗_{O_{Proj,φ t}} O(n)_{φ t}`
   (`modulePullbackStalkTensorMap_bijective`), and the pure tensor
   `r ⊗ germ g` is `r • germ(η g)`. Hence near `t` the section `x` is a finite sum `Σ r_i · η(g_i)|_{B'}` with
   `g_i ∈ Γ(V_i, O(n))`, `V_i ∋ φ t` (`η` the adjunction unit). By additivity and linearity of both families it
   suffices to compare them, near `t`, on each `η(g)|_{B'}` (`Modules.SectionMapPair.eq`,
   `RelativeProjLiftEvaluationTwistFamilyAbsoluteLocalGeneration.lean`). No quasi-coherence of `O(n)` is used.
2. *Chart and fraction (01MN).* Pick `s ∈ 𝒜_e`, `e > 0`, with `t ∈ Y_s := Y.basicOpen (Φ s)` (the `Y_s` cover `Y`
   because `hΦ`: Mathlib `openCoverOfMapIrrelevantEqTop`); `φ⁻¹D₊(s) = Y_s` (`fromOfGlobalSections_preimage_basicOpen`),
   so `φ t ∈ D₊(s)`. Near `φ t` the section `g` is `0` or a fraction `a/b`; multiplying numerator and denominator by
   `s` we may take the denominator `d := bs` of positive degree `q`, and then `g|_W = (a/d)|_W` with `a/d` the section
   `fracSection` of `O(n)` over `D₊(d)` (`exists_res_eq_fracSection`, `…AbsoluteChartFractions.lean`). In the zero
   case both families give `0`. Otherwise `η(g)|_{B'} = η(a/d)|_{B'}` for `B' := B ∩ φ⁻¹W ⊆ φ⁻¹D₊(d) = Y_d`.
3. *The key identity.* In `Γ(D₊(d), O(n + q))`: `(a/d) · (d/1) = a/1` (pointwise multiplication of fractions,
   `twistSectionMul_fracSection_homogeneousSection`). Pulling back (`η` commutes with `twistMul` and `δ`:
   `pullbackMulHom_app_tensorSections`, `…AbsolutePullbackMul.lean`): `μ(η(a/d) ⊗ η(d/1)) = η(a/1)`. Apply (M') once
   and (F') twice: `c n B' (η(a/d)) · Φ(d)|_{B'} = c (n+q) B' (η(a/1)) = Φ(a)|_{B'}` (`IsSectionFamily.mul_res_eq`),
   and the same for `c'`.
4. *Cancel.* `Φ(d)` is a unit on `B' ⊆ Y_d` (`RingedSpace.isUnit_res_basicOpen`), so
   `c n B' (η(a/d)) = c' n B' (η(a/d))` (`IsSectionFamily.exists_nhds_eq_on_pullback`). ∎

**Edge cases.** `B = ∅`, `Y = ∅`: trivial. `A` the zero ring: `Y = ∅`. The families need not come from morphisms
(they are only section maps): this is the form used for the relative uniqueness, where the two families live on
different opens `V₁, V₂ ⊇ V`. Compared with the earlier plan (`a/s^k` and `k` applications of (M')), the fraction
`a/d` with `d = bs` needs a single application of (M'). -/
theorem IsSectionFamily.eq {c c' : ∀ (n : ℕ) (B : Y.Opens), Γ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Proj.fromOfGlobalSections 𝒜 Φ hΦ)).obj (AlgebraicGeometry.Proj.twist 𝒜 (n : ℤ)), B) → Γ(Y, B)}
    (hc : IsSectionFamily 𝒜 Φ hΦ c) (hc' : IsSectionFamily 𝒜 Φ hΦ c') : c = c' :=
  funext fun n => funext fun B => funext fun x => (hc.sectionMapPair hc' n).eq B x

end AlgebraicGeometry.Proj.TwistFamily

end
