import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveLineStandardChart
import MiyaokaMori.AlgebraicGeometry.Morphisms.AffineLineOverCanonicallyOver
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.Stacks01ne
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModuleChartPullback
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ProjectiveSpaceOverChartRatio
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.PullbackUnit

/-! # Trivialization of `O(1)` along the standard chart of the projective line

Statement: the standard chart `stdChart : A¹ → P¹`, `t ↦ [1 : t]`, is a `k`-morphism, factors through
`D₊(x₀)` via a chart map `stdChartToBasicOpen : A¹ → D₊(x₀)` with `(x_i/x₀) ↦ (![1, t]) i`; hence for every
open `O ⊆ A¹` the pullback `(O.ι ≫ stdChart)^* 𝒪(1)` is trivialized by a canonical iso
`stdChartPullbackTwistIso O : (O.ι ≫ stdChart)^* 𝒪(1) ≅ 𝒪_O` sending `x₀ ↦ 1`, `x₁ ↦ t := polynomialSection O X`.
Also: `polynomialSection O p = p(t)` (`polynomialSection_eq_eval₂`), and bookkeeping for the structure sheaf as a
line bundle: a global function `a` with `a • s_ℓ` nowhere simultaneously vanishing is a unit
(`isUnit_of_forall_exists_not_isZeroAt_smul`), and multiplication by a unit is an automorphism `unitMulIso` of `𝒪`.

Generic tool (variable schemes, cheap for the kernel): `pullbackIsoUnitOfChart`: if `f = g ≫ W.ι` factors through an
open `W ⊆ Y` and `e : M|_W ≅ 𝒪_W`, then `f^*M ≅ 𝒪_X` with `f^*s ↦ g^♯(e(s|_W))` (`pullbackIsoUnitOfChart_section`,
bridge form `_of_eq` for concrete instantiation).

Proof: `stdChart = SpecIso.hom ≫ Spec(ψ) ≫ awayι` with `ψ = stdChartRingHom : k[x₀,x₁]_(x₀) → k[t]`, `a/x₀ⁿ ↦ a(1,t)`
(`stdChartRingHom_mk`); `awayι = basicOpenIsoSpec.inv ≫ D₊(x₀).ι` (Mathlib, `rfl`); the ratio `x_i/x₀` is
`ratioSection`, transported through `Γ–Spec` naturality (`ΓSpecIso_inv_naturality`). The `k`-structure is
compared through `awayι_toSpecZero` and `AffineSpace.SpecIso_inv_over` (`stdChartRingHom_comp_fromZero`: constants go to
constants). The trivialization is `pullbackIsoUnitOfChart` applied to the frame `targetFrameIso 0` of
`𝒪(1)|_{D₊(x₀)}` (`targetFrameIso_coordinate : x_l ↦ x_l/x₀`).

Source: Stacks 01NE (morphisms to Proj from sections), 01CD (pullback of invertible sheaves), 01M3/01MD (charts of Proj);
Hartshorne II.7.1; §4 of the paper (the chart `t ↦ [1:t]` of the fibre `P¹` in Theorem 4.2). Used by `ProjectiveLine.morphismOfForms_stdChart_polynomialSection_homog`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (W : Y.Opens) (g : X ⟶ W.toScheme)
  (hg : g ≫ W.ι = f) (M : Y.Modules)

/-- **Pullback along a morphism into a trivialized chart is trivial** (Stacks 01CD/01CR,
`lemma-pullback-invertible`): if `f = g ≫ W.ι` factors through the open `W ⊆ Y` and
`e : M|_W ≅ 𝒪_W` trivializes `M` on `W`, then `f^*M ≅ 𝒪_X` canonically
(`pullbackCongr` ∘ `pullbackComp⁻¹` ∘ `g^*(restrict ≅ pullback)⁻¹` ∘ `g^*e` ∘ `pullbackUnitIso`).
Unlike `AlgebraicGeometry.Scheme.Modules.HomogeneousTupleTwistPullback.pullbackFrameIso` this is a global iso on `X`
(no `restrict ⊤.ι`), which is what `projectiveSpace_hom_ext_of_sections` consumes. -/
def pullbackIsoUnitOfChart
    (e : M.restrict W.ι ≅ SheafOfModules.unit W.toScheme.ringCatSheaf) :
    (AlgebraicGeometry.Scheme.Modules.pullback f).obj M ≅ SheafOfModules.unit X.ringCatSheaf :=
  (AlgebraicGeometry.Scheme.Modules.pullbackCongr hg.symm).app M ≪≫
    ((AlgebraicGeometry.Scheme.Modules.pullbackComp g W.ι).app M).symm ≪≫
    (AlgebraicGeometry.Scheme.Modules.pullback g).mapIso
      ((AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback W.ι).app M).symm ≪≫
    (AlgebraicGeometry.Scheme.Modules.pullback g).mapIso e ≪≫
    AlgebraicGeometry.Scheme.Modules.pullbackUnitIso g

set_option backward.isDefEq.respectTransparency false in
/-- Section formula: `f^*s ↦ g^♯(e(s|_W))`. -/
theorem pullbackIsoUnitOfChart_section
    (e : M.restrict W.ι ≅ SheafOfModules.unit W.toScheme.ringCatSheaf) (s : Γ(M, ⊤)) :
    (pullbackIsoUnitOfChart f W g hg M e).hom.app ⊤ (AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback f s) =
      g.appTop (e.hom.app ⊤
        (AlgebraicGeometry.Scheme.Modules.HomogeneousTupleTwistPullback.restrictedGlobalSection M W s)) := by
  unfold pullbackIsoUnitOfChart AlgebraicGeometry.Scheme.Modules.HomogeneousTupleTwistPullback.restrictedGlobalSection
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, AlgebraicGeometry.Scheme.Modules.pullbackUnitIso_hom,
    AlgebraicGeometry.Scheme.Modules.Hom.comp_app, CategoryTheory.comp_apply]
  rw [AlgebraicGeometry.Scheme.Modules.ModuleSections.pullbackCongr_apply, AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback_comp_inv]
  erw [AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback_naturality (g := g)
    ((AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback W.ι).app M).inv
    (AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback W.ι s)]
  rw [AlgebraicGeometry.Scheme.Modules.HomogeneousTupleTwistPullback.restrictIso_inv_pullback,
    AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback_naturality]
  exact AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback_unit g _

/-- Bridge form of `pullbackIsoUnitOfChart_section` for instantiation at **concrete** schemes: the
concrete module `P`, iso `τ` and section `t` enter as variables tied to the generic ones by equations
discharged by `rfl` at top level, which keeps the kernel cost of the instantiation low
(compare `AlgebraicGeometry.Scheme.Modules.HomogeneousTupleTwistPullback.pullbackFrameIso_section_of_eq`). -/
theorem pullbackIsoUnitOfChart_section_of_eq
    (e : M.restrict W.ι ≅ SheafOfModules.unit W.toScheme.ringCatSheaf)
    {P : Y.Modules} (hP : M = P)
    (τ : (AlgebraicGeometry.Scheme.Modules.pullback f).obj P ≅ SheafOfModules.unit X.ringCatSheaf)
    (hτ : τ = hP ▸ pullbackIsoUnitOfChart f W g hg M e)
    (s : Γ(M, ⊤)) (t : Γ(P, ⊤)) (ht : t = hP ▸ s) :
    τ.hom.app ⊤ (AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback f t) =
      g.appTop (e.hom.app ⊤
        (AlgebraicGeometry.Scheme.Modules.HomogeneousTupleTwistPullback.restrictedGlobalSection M W s)) := by
  subst hP
  have hτ' : τ = pullbackIsoUnitOfChart f W g hg M e := hτ
  have ht' : t = s := ht
  subst hτ'; subst ht'
  exact pullbackIsoUnitOfChart_section f W g hg M e _

end AlgebraicGeometry.Scheme.Modules

namespace ProjectiveLine

variable (k : Type u) [Field k]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The standard chart `A¹ → P¹`, `t ↦ [1 : t]`, factored through its image `D₊(x₀)`:
`A¹ ≅ Spec k[t] → Spec k[x₀,x₁]_(x₀) ≅ D₊(x₀)`. -/
def stdChartToBasicOpen :
    AlgebraicGeometry.Scheme.affineLineOver (AlgebraicGeometry.Spec (CommRingCat.of k)) ⟶
      (Stacks01ne.coordBasicOpen k 1 0).toScheme :=
  (AlgebraicGeometry.AffineSpace.SpecIso (ULift.{u} (Fin 1)) (CommRingCat.of k)).hom ≫
    AlgebraicGeometry.Spec.map (CommRingCat.ofHom (ProjectiveLine.stdChartRingHom k)) ≫
    (Stacks01ne.coordBasicOpenIsoSpec k 1 0).inv

/-- `stdChartToBasicOpen ≫ D₊(x₀).ι = stdChart` (definitional: `awayι = basicOpenIsoSpec.inv ≫ ι`). -/
theorem stdChartToBasicOpen_comp_ι :
    stdChartToBasicOpen k ≫ (Stacks01ne.coordBasicOpen k 1 0).ι = ProjectiveLine.stdChart k := by
  unfold stdChartToBasicOpen ProjectiveLine.stdChart
  simp only [Category.assoc]
  rfl

theorem stdChartToBasicOpen_comp_isoSpec :
    stdChartToBasicOpen k ≫ (Stacks01ne.coordBasicOpenIsoSpec k 1 0).hom =
      (AlgebraicGeometry.AffineSpace.SpecIso (ULift.{u} (Fin 1)) (CommRingCat.of k)).hom ≫
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom (ProjectiveLine.stdChartRingHom k)) := by
  unfold stdChartToBasicOpen
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The chart map pulls the coordinate ratio `x_i/x₀` back to `(![1, t]) i`
(`stdChartRingHom_mk`: `a/x₀ⁿ ↦ a(1, t)`). -/
theorem stdChartToBasicOpen_appTop_ratioSection (i : Fin 2) :
    (stdChartToBasicOpen k).appTop (ProjectiveSpaceOverChart.ratioSection 1 i 0) =
      (AlgebraicGeometry.AffineSpace.SpecIso (ULift.{u} (Fin 1)) (CommRingCat.of k)).hom.appTop
        ((AlgebraicGeometry.Scheme.ΓSpecIso
            (CommRingCat.of (MvPolynomial (ULift.{u} (Fin 1)) k))).inv
          (MvPolynomial.aeval (R := k) ![1, (MvPolynomial.X ⟨0⟩ : MvPolynomial (ULift.{u} (Fin 1)) k)]
            (MvPolynomial.X i : MvPolynomial (Fin (1 + 1)) k))) := by
  unfold ProjectiveSpaceOverChart.ratioSection
  rw [← CommRingCat.comp_apply, ← AlgebraicGeometry.Scheme.Hom.comp_appTop,
    stdChartToBasicOpen_comp_isoSpec, AlgebraicGeometry.Scheme.Hom.comp_appTop,
    CommRingCat.comp_apply]
  congr 1
  have h4 := AlgebraicGeometry.Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (ProjectiveLine.stdChartRingHom k))
  have h5 : ∀ z, (AlgebraicGeometry.Scheme.ΓSpecIso
      (CommRingCat.of (MvPolynomial (ULift.{u} (Fin 1)) k))).inv (ProjectiveLine.stdChartRingHom k z) =
      (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (ProjectiveLine.stdChartRingHom k))).appTop
        ((AlgebraicGeometry.Scheme.ΓSpecIso _).inv z) :=
    fun z => congrArg (fun f => f z) h4
  rw [← h5]
  congr 1
  exact ProjectiveLine.stdChartRingHom_mk k 1 (MvPolynomial.X i) _

theorem stdChartToBasicOpen_appTop_ratioSection_zero :
    (stdChartToBasicOpen k).appTop (ProjectiveSpaceOverChart.ratioSection 1 0 0) = 1 := by
  rw [stdChartToBasicOpen_appTop_ratioSection]
  simp

theorem stdChartToBasicOpen_appTop_ratioSection_one :
    (stdChartToBasicOpen k).appTop (ProjectiveSpaceOverChart.ratioSection 1 1 0) =
      (AlgebraicGeometry.AffineSpace.SpecIso (ULift.{u} (Fin 1)) (CommRingCat.of k)).hom.appTop
        ((AlgebraicGeometry.Scheme.ΓSpecIso
            (CommRingCat.of (MvPolynomial (ULift.{u} (Fin 1)) k))).inv
          (MvPolynomial.X ⟨0⟩)) := by
  rw [stdChartToBasicOpen_appTop_ratioSection]
  simp

/-- The structure morphism of `A¹_k = 𝔸(1; Spec k)` through `Spec k[t]`. -/
theorem affineLineOver_over_eq :
    (AlgebraicGeometry.Scheme.affineLineOver (AlgebraicGeometry.Spec (CommRingCat.of k)) ↘
        AlgebraicGeometry.Spec (CommRingCat.of k)) =
      (AlgebraicGeometry.AffineSpace.SpecIso (ULift.{u} (Fin 1)) (CommRingCat.of k)).hom ≫
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom MvPolynomial.C) := by
  change (AlgebraicGeometry.AffineSpace (ULift.{u} (Fin 1)) (AlgebraicGeometry.Spec (CommRingCat.of k)) ↘
    AlgebraicGeometry.Spec (CommRingCat.of k)) = _
  exact (Iso.inv_comp_eq _).mp (AlgebraicGeometry.AffineSpace.SpecIso_inv_over _)

/-- `D₊(x₀).ι ≫ (P¹ ↘ Spec k) = (D₊(x₀) ≅ Spec A⁰) ≫ Spec (k → 𝒜₀ → A⁰)`. -/
theorem coordBasicOpen_ι_comp_over :
    (Stacks01ne.coordBasicOpen k 1 0).ι ≫
        (ProjectiveLine k ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      (Stacks01ne.coordBasicOpenIsoSpec k 1 0).hom ≫ AlgebraicGeometry.Spec.map (CommRingCat.ofHom
        ((HomogeneousLocalization.fromZeroRingHom (AlgebraicGeometry.Proj.projectiveGrading k 1)
          (Submonoid.powers (MvPolynomial.X 0))).comp
            (algebraMap k ((AlgebraicGeometry.Proj.projectiveGrading k 1) 0)))) := by
  change (Stacks01ne.coordBasicOpen k 1 0).ι ≫
      (AlgebraicGeometry.Proj.toSpecZero (AlgebraicGeometry.Proj.projectiveGrading k 1) ≫
        AlgebraicGeometry.Spec.map (CommRingCat.ofHom
          (algebraMap k ((AlgebraicGeometry.Proj.projectiveGrading k 1) 0)))) = _
  have h1 : (Stacks01ne.coordBasicOpen k 1 0).ι = (Stacks01ne.coordBasicOpenIsoSpec k 1 0).hom ≫
      AlgebraicGeometry.Proj.awayι (AlgebraicGeometry.Proj.projectiveGrading k 1) (MvPolynomial.X 0)
        ((MvPolynomial.mem_homogeneousSubmodule _ _).mpr (MvPolynomial.isHomogeneous_X k 0))
        Nat.one_pos := by
    rw [← AlgebraicGeometry.Proj.basicOpenIsoSpec_inv_ι, Iso.hom_inv_id_assoc]
  rw [h1, Category.assoc]
  rw [AlgebraicGeometry.Proj.awayι_toSpecZero_assoc]
  rw [← AlgebraicGeometry.Spec.map_comp, ← CommRingCat.ofHom_comp]

/-- `stdChartRingHom ∘ (k → 𝒜₀ → k[x₀,x₁]_(x₀)) = C`: constants go to constants. -/
theorem stdChartRingHom_comp_fromZero :
    (ProjectiveLine.stdChartRingHom k).comp
        ((HomogeneousLocalization.fromZeroRingHom (AlgebraicGeometry.Proj.projectiveGrading k 1)
          (Submonoid.powers (MvPolynomial.X 0))).comp
            (algebraMap k ((AlgebraicGeometry.Proj.projectiveGrading k 1) 0))) =
      MvPolynomial.C := by
  refine RingHom.ext fun c => ?_
  rw [RingHom.comp_apply, RingHom.comp_apply]
  unfold ProjectiveLine.stdChartRingHom
  rw [RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply]
  set a : (AlgebraicGeometry.Proj.projectiveGrading k 1) 0 := algebraMap k ((AlgebraicGeometry.Proj.projectiveGrading k 1) 0) c
    with ha
  have hcoe : (a : MvPolynomial (Fin (1 + 1)) k) = MvPolynomial.C c := by
    rw [ha, SetLike.GradeZero.coe_algebraMap]
    rfl
  have hval : (HomogeneousLocalization.fromZeroRingHom (AlgebraicGeometry.Proj.projectiveGrading k 1)
      (Submonoid.powers (MvPolynomial.X 0 : MvPolynomial (Fin (1 + 1)) k)) a).val =
      algebraMap (MvPolynomial (Fin (1 + 1)) k)
        (Localization (Submonoid.powers (MvPolynomial.X 0 : MvPolynomial (Fin (1 + 1)) k)))
        (MvPolynomial.C c) := by
    rw [← hcoe, ← Localization.mk_one_eq_algebraMap]
    rfl
  rw [hval, IsLocalization.Away.lift_eq]
  simp

/-- **`stdChart` is a `k`-morphism**: `stdChart ≫ (P¹ ↘ Spec k) = A¹ ↘ Spec k`. -/
theorem stdChart_comp_over :
    ProjectiveLine.stdChart k ≫ (ProjectiveLine k ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      AlgebraicGeometry.Scheme.affineLineOver (AlgebraicGeometry.Spec (CommRingCat.of k)) ↘
        AlgebraicGeometry.Spec (CommRingCat.of k) := by
  rw [← stdChartToBasicOpen_comp_ι, Category.assoc, coordBasicOpen_ι_comp_over,
    ← Category.assoc, stdChartToBasicOpen_comp_isoSpec, Category.assoc,
    ← AlgebraicGeometry.Spec.map_comp, ← CommRingCat.ofHom_comp, stdChartRingHom_comp_fromZero,
    affineLineOver_over_eq]

theorem stdChart_isOver :
    (ProjectiveLine.stdChart k).IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
  ⟨stdChart_comp_over k⟩

end ProjectiveLine

namespace ProjectiveLine

variable {k : Type u} [Field k]

/-- The structure map `k → Γ(A¹, 𝒪)` through `A¹ ≅ Spec k[t]` sends `c` to the constant `C c`. -/
theorem affineLineOver_appTop_ΓSpecIso_inv (c : k) :
    (AlgebraicGeometry.Scheme.affineLineOver (AlgebraicGeometry.Spec (CommRingCat.of k)) ↘
        AlgebraicGeometry.Spec (CommRingCat.of k)).appTop
        ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv c) =
      (AlgebraicGeometry.AffineSpace.SpecIso (ULift.{u} (Fin 1)) (CommRingCat.of k)).hom.appTop
        ((AlgebraicGeometry.Scheme.ΓSpecIso
            (CommRingCat.of (MvPolynomial (ULift.{u} (Fin 1)) k))).inv (MvPolynomial.C c)) := by
  rw [affineLineOver_over_eq k, AlgebraicGeometry.Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
  congr 1
  have h4 := AlgebraicGeometry.Scheme.ΓSpecIso_inv_naturality
    (CommRingCat.ofHom (MvPolynomial.C : k →+* MvPolynomial (ULift.{u} (Fin 1)) k))
  exact (congrArg (fun f => f c) h4).symm

/-- **`polynomialSection O` is polynomial evaluation**: `p ↦ p(t)` with `t := polynomialSection O X`
and coefficients through the structure map `k → Γ(O, 𝒪)`. Both sides are ring homomorphisms in
`p` agreeing on `C c` (`affineLineOver_appTop_ΓSpecIso_inv`) and on `X` (by definition). -/
theorem polynomialSection_eq_eval₂
    (O : (AlgebraicGeometry.Scheme.affineLineOver (AlgebraicGeometry.Spec (CommRingCat.of k))).Opens)
    (p : Polynomial k) :
    polynomialSection O p =
      Polynomial.eval₂ ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
          (O.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)).appTop).hom
        (show Γ(O.toScheme, ⊤) from polynomialSection O Polynomial.X) p := by
  let ρ : MvPolynomial (ULift.{u} (Fin 1)) k →+* Γ(O.toScheme, ⊤) :=
    ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (ULift.{u} (Fin 1)) k))).inv ≫
      (AlgebraicGeometry.AffineSpace.SpecIso (ULift.{u} (Fin 1)) (CommRingCat.of k)).hom.appTop ≫
      O.ι.appTop).hom
  have key : ρ.comp (Polynomial.aeval (MvPolynomial.X ⟨0⟩ : MvPolynomial (ULift.{u} (Fin 1)) k)).toRingHom =
      Polynomial.eval₂RingHom ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫
          (O.toScheme ↘ AlgebraicGeometry.Spec (CommRingCat.of k)).appTop).hom
        (show Γ(O.toScheme, ⊤) from polynomialSection O Polynomial.X) := by
    apply Polynomial.ringHom_ext
    · intro c
      rw [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C]
      change O.ι.appTop ((AlgebraicGeometry.AffineSpace.SpecIso (ULift.{u} (Fin 1)) (CommRingCat.of k)).hom.appTop
        ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (ULift.{u} (Fin 1)) k))).inv
          (Polynomial.aeval (MvPolynomial.X ⟨0⟩ : MvPolynomial (ULift.{u} (Fin 1)) k) (Polynomial.C c)))) =
        (O.ι ≫ (AlgebraicGeometry.Scheme.affineLineOver (AlgebraicGeometry.Spec (CommRingCat.of k)) ↘
          AlgebraicGeometry.Spec (CommRingCat.of k))).appTop
          ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv c)
      rw [AlgebraicGeometry.Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
        affineLineOver_appTop_ΓSpecIso_inv, Polynomial.aeval_C]
      rfl
    · rw [RingHom.comp_apply, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
      rfl
  exact congrArg (fun f : Polynomial k →+* Γ(O.toScheme, ⊤) => f p) key

end ProjectiveLine

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- If the germ of `a` at `x` is not a unit, then `a • s` vanishes at `x` (`germ (a • s) = germ a • germ s ∈ 𝔪ₓ Mₓ`). -/
theorem isZeroAt_smul_of_not_isUnit_germ {M : X.Modules} (a : Γ(X, ⊤)) (s : Γ(M, ⊤)) (x : X)
    (ha : ¬ IsUnit (X.presheaf.germ ⊤ x trivial a)) : IsZeroAt (a • s : Γ(M, ⊤)) x := by
  have hkey : M.presheaf.germ ⊤ x trivial (a • s) =
      X.presheaf.germ ⊤ x trivial a • M.presheaf.germ ⊤ x trivial s :=
    germ_smul' M (V := ⊤) (y := x) trivial a s
  show M.presheaf.germ ⊤ x trivial (a • s) ∈ _
  rw [hkey]
  exact Submodule.smul_mem_smul ((IsLocalRing.mem_maximalIdeal _).mpr ha) Submodule.mem_top

/-- A global function `a` such that at every point some `a • s ℓ` does not vanish is a unit
(`RingedSpace.isUnit_of_isUnit_germ`). -/
theorem isUnit_of_forall_exists_not_isZeroAt_smul {M : X.Modules} (a : Γ(X, ⊤)) {ι : Type*}
    (s : ι → Γ(M, ⊤)) (h : ∀ x : X, ∃ ℓ, ¬ IsZeroAt (a • s ℓ : Γ(M, ⊤)) x) : IsUnit a := by
  apply X.toRingedSpace.isUnit_of_isUnit_germ
  intro x _
  by_contra hx
  obtain ⟨ℓ, hℓ⟩ := h x
  exact hℓ (isZeroAt_smul_of_not_isUnit_germ a (s ℓ) x hx)

set_option backward.isDefEq.respectTransparency false in
/-- A unit `u ∈ Γ(X, 𝒪)` is a frame of the structure sheaf on `⊤`. -/
theorem isFrame_unit_of_isUnit {u : Γ(X, ⊤)} (hu : IsUnit u) :
    IsFrame (SheafOfModules.unit X.ringCatSheaf) ⊤
      (show Γ(SheafOfModules.unit X.ringCatSheaf, ⊤) from u) := by
  intro W' h
  obtain ⟨v, hv⟩ : IsUnit (X.presheaf.map (homOfLE h).op u) := hu.map _
  show Function.Bijective (fun r : Γ(X, W') => r * X.presheaf.map (homOfLE h).op u)
  rw [← hv]
  exact ⟨v.isUnit.mul_left_injective, fun y => ⟨y * ↑v⁻¹, Units.inv_mul_cancel_right y v⟩⟩

/-- Multiplication by a unit `u` as an automorphism of `𝒪_X` (`IsFrame.topTrivialization` of the frame `u`). -/
def unitMulIso {u : Γ(X, ⊤)} (hu : IsUnit u) :
    Iso (C := X.Modules) (SheafOfModules.unit X.ringCatSheaf) (SheafOfModules.unit X.ringCatSheaf) :=
  (isFrame_unit_of_isUnit hu).topTrivialization

set_option backward.isDefEq.respectTransparency false in
theorem unitMulIso_hom_app_top {u : Γ(X, ⊤)} (hu : IsUnit u) (x : Γ(X, ⊤)) :
    (unitMulIso hu).hom.app ⊤ (show Γ(SheafOfModules.unit X.ringCatSheaf, ⊤) from x) =
      (show Γ(SheafOfModules.unit X.ringCatSheaf, ⊤) from u * x) := by
  change (homOfSection (SheafOfModules.unit X.ringCatSheaf) _).val.app (op ⊤) x = _
  rw [homOfSection_app, res_self]
  exact mul_comm x u

end AlgebraicGeometry.Scheme.Modules

namespace ProjectiveLine

variable {k : Type u} [Field k]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The chart map `O → D₊(x₀)` of an open `O ⊆ A¹`. -/
abbrev stdChartToBasicOpenOn
    (O : (AlgebraicGeometry.Scheme.affineLineOver (AlgebraicGeometry.Spec (CommRingCat.of k))).Opens) :
    O.toScheme ⟶ (Stacks01ne.coordBasicOpen k 1 0).toScheme :=
  O.ι ≫ stdChartToBasicOpen k

theorem stdChartToBasicOpenOn_comp_ι
    (O : (AlgebraicGeometry.Scheme.affineLineOver (AlgebraicGeometry.Spec (CommRingCat.of k))).Opens) :
    stdChartToBasicOpenOn O ≫ (Stacks01ne.coordBasicOpen k 1 0).ι = O.ι ≫ ProjectiveLine.stdChart k := by
  rw [Category.assoc, stdChartToBasicOpen_comp_ι]

/-- **Trivialization of `(O.ι ≫ stdChart)^* 𝒪(1)` on `O ⊆ A¹`**: the pullback of the frame `x₀` of
`𝒪(1)|_{D₊(x₀)}` (`targetFrameIso 0`), transported along the chart map `O → D₊(x₀)`. -/
def stdChartPullbackTwistIso
    (O : (AlgebraicGeometry.Scheme.affineLineOver (AlgebraicGeometry.Spec (CommRingCat.of k))).Opens) :
    (AlgebraicGeometry.Scheme.Modules.pullback (O.ι ≫ ProjectiveLine.stdChart k)).obj
        (projectiveSpaceTwist k 1 1) ≅
      SheafOfModules.unit O.toScheme.ringCatSheaf :=
  AlgebraicGeometry.Scheme.Modules.pullbackIsoUnitOfChart (O.ι ≫ ProjectiveLine.stdChart k)
    (Stacks01ne.coordBasicOpen k 1 0) (stdChartToBasicOpenOn O) (stdChartToBasicOpenOn_comp_ι O)
    (projectiveSpaceTwist k 1 1) (ProjectiveSpaceOverChart.targetFrameIso (R := k) 1 0)

set_option backward.isDefEq.respectTransparency false in
/-- `τ((O.ι ≫ stdChart)^* x_l) = (chart map)^♯(x_l / x₀)`. -/
theorem stdChartPullbackTwistIso_coordinate
    (O : (AlgebraicGeometry.Scheme.affineLineOver (AlgebraicGeometry.Spec (CommRingCat.of k))).Opens)
    (l : Fin 2) :
    (stdChartPullbackTwistIso O).hom.app ⊤
        (sectionPullbackAlong (O.ι ≫ ProjectiveLine.stdChart k) (projectiveSpaceCoordinate k 1 l)) =
      (stdChartToBasicOpenOn O).appTop (ProjectiveSpaceOverChart.ratioSection 1 l 0) := by
  rw [← AlgebraicGeometry.Scheme.Modules.HomogeneousTupleTwistPullback.targetFrameIso_coordinate (k := k) (N := 1) 0 l]
  exact AlgebraicGeometry.Scheme.Modules.pullbackIsoUnitOfChart_section_of_eq
    (O.ι ≫ ProjectiveLine.stdChart k) (Stacks01ne.coordBasicOpen k 1 0) (stdChartToBasicOpenOn O)
    (stdChartToBasicOpenOn_comp_ι O)
    (MiyaokaMori.WeightedJets.ProjTwisting.sheaf (AlgebraicGeometry.Proj.projectiveGrading k 1) 1)
    (ProjectiveSpaceOverChart.targetFrameIso (R := k) 1 0)
    (P := projectiveSpaceTwist k 1 1) rfl (stdChartPullbackTwistIso O) rfl
    (projectiveSpaceCoordinate k 1 l) (projectiveSpaceCoordinate k 1 l) rfl

theorem stdChartPullbackTwistIso_coordinate_zero
    (O : (AlgebraicGeometry.Scheme.affineLineOver (AlgebraicGeometry.Spec (CommRingCat.of k))).Opens) :
    (stdChartPullbackTwistIso O).hom.app ⊤
        (sectionPullbackAlong (O.ι ≫ ProjectiveLine.stdChart k) (projectiveSpaceCoordinate k 1 0)) =
      (show Γ(SheafOfModules.unit O.toScheme.ringCatSheaf, ⊤) from (1 : Γ(O.toScheme, ⊤))) := by
  rw [stdChartPullbackTwistIso_coordinate, stdChartToBasicOpenOn,
    AlgebraicGeometry.Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    stdChartToBasicOpen_appTop_ratioSection_zero, map_one]

theorem stdChartPullbackTwistIso_coordinate_one
    (O : (AlgebraicGeometry.Scheme.affineLineOver (AlgebraicGeometry.Spec (CommRingCat.of k))).Opens) :
    (stdChartPullbackTwistIso O).hom.app ⊤
        (sectionPullbackAlong (O.ι ≫ ProjectiveLine.stdChart k) (projectiveSpaceCoordinate k 1 1)) =
      polynomialSection O Polynomial.X := by
  rw [stdChartPullbackTwistIso_coordinate, stdChartToBasicOpenOn,
    AlgebraicGeometry.Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    stdChartToBasicOpen_appTop_ratioSection_one]
  unfold polynomialSection
  rw [Polynomial.aeval_X]

end ProjectiveLine

end
