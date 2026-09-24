import MiyaokaMori.AlgebraicGeometry.Modules.Dual.SheafDualLocallyFree
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.LocallyFreeQuasicoherent
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModulesCoevaluation
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.AlgebraMapToPushforwardMorphismLevel
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedAlgebraTotalComponent
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.ModulesUnitHomTopSection
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.MonoidalPowMulCompat
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveBundle.ProjectiveBundleUniversalProperty
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.RelativeSpecUniversalProperty
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.SectionPullbackAlong
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotalSpaceTriangleTransport
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotalSpaceVectorBundle
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedSymGenerator

/-! # The section–morphism constructions for the total space

Statement: for a locally free module `V` of finite type on a base scheme `X` and an `X`-scheme `T`, a section
`s : Γ(T, g^*V)` gives, through the universal property of the symmetric algebra, an algebra map and a morphism
`T → Tot(V)`; conversely, a morphism gives a section through its degree-one generator part and the canonical
coevaluation section. The two constructions are inverse to each other.

Proof:
1. For a linear form `ψ : g^*(Vᵛ) → O_T`, descend in degree `m` by `symGradedPullbackDesc` to `Sym^m(Vᵛ)` and multiply
   with `unitPowCollapse`; degree `0` gives the unit, and the compatibility of `symPowMul` with the concatenation of
   tensor powers gives multiplicativity, hence `IsAlgebraMapToPushforward`.
2. The universal property of the relative Spec turns this algebra map into `T → Tot(V)`; conversely take the degree-one
   part of the algebra map, obtain `ψ : g^*(Vᵛ) → O_T` by the pullback–pushforward adjunction, and apply it to
   `g^*(coev_V)`.
3. The degree-one generators determine an algebra map out of the symmetric algebra; the two triangle identities for
   `eval`/`coev` give `ofSection (toSection h) = h` and `toSection (ofSection s) = s`.

References: Stacks 01LQ, 01CM, 01CN.

## Structure

* §A. Transport lemmas for `symGradedAlgebra W` in the quasi-coherent case: `symGradedAlgebra W` is a
  `dite` on `W.IsQuasicoherent`; `symGradedPullbackDesc` and `symGen` are defined through that `dite`
  (the former by `unfold; split`, producing an `Eq.mpr` cast). We record the branch as a `HEq`
  (`symGradedPullbackDesc_heq`, `symGen_heq`) and then transport along `symGradedAlgebra W = symGradedAlgebraOfQC W hq`
  by `subst` inside auxiliary lemmas quantified over an abstract `S` (`…_aux`). This avoids all
  `eqToHom` bookkeeping; see the `_aux` lemmas.
  Pitfall: composites such as `(λ_ W).inv ≫ symPowπ W 1` are only well typed up to unfolding
  `monoidalPow W 1 = 𝟙_ ⊗ W`, and objects `SheafOfModules.unit T.ringCatSheaf` are only `T.Modules`
  objects up to unfolding `Scheme.Modules`; `rw`/`simp` then fail to find patterns
  ("target is not type-correct under the implicit transparency level"). Remedy used here:
  `show`/`let` the goal into a uniformly elaborated form first (`let ψ' : _ ⟶ 𝟙_ T.Modules := ψ`), or `erw`.
* §B. `functionalOfSectionCore`, `algebraMapOfFunctionalCore`; unit preservation
  `algebraMapOfFunctionalCore_one`; multiplicativity `algebraMapOfFunctionalCore_mul`, from three helper modules:
  `GradedAlgebraTotalComponent` (component formula of `total.mul` and the joint-epi lemma `tensorObj_sigma_hom_ext`),
  `MonoidalPowMulCompat` (multiplicativity of `pullbackMonoidalPow` / `monoidalPowMap` / `unitPowCollapse` and of the
  symmetric-power descent) and `AlgebraMapToPushforwardMorphismLevel` (section-level ⇄ morphism-level
  `IsAlgebraMapToPushforward`, `pushforwardUnitMul`, adjoint transposition of products). Transport to the `dite`
  branch: `mul_homEquiv_symGradedPullbackDesc_aux`.
  Second pitfall: once a goal mixes `S.total.carrier` / `∐ S.part`, `(symGradedAlgebraOfQC W hq).part m` /
  `symPow W m`, or `SheafOfModules.unit T.ringCatSheaf` / `𝟙_ T.Modules`, `rw`/`simp`/`reassoc` no longer match
  (they work at instance transparency, where these are not unfolded). Remedy used throughout §A/§B/§D: state the
  needed equation in a `have` spelled like the goal and prove it by `exact` (defeq at default transparency), or
  chain `Eq.trans`/`congrArg` in term mode; abstract monoidal steps go into lemmas over an arbitrary category
  (`ext_step_aux`, `MonoidalPowMulCompat.MonoidalPowAux.*`).
* §C. `ofSectionCore`, `functionalOfHomCore`, `sectionOfFunctionalCore`, `toSectionCore`
  (`toSectionCore = sectionOfFunctionalCore ∘ functionalOfHomCore`, `rfl`).
* §D. Degree-one component `symGen_ι_algebraMapOfFunctionalCore`; "an algebra map out of Sym(V^∨)
  is determined by its degree-one part" (`algebraMapToPushforward_ext_of_symGen`,
  via `ι_comp_ext_of_symGen_aux`: induction on the degree, cancelling `symPowπ`, using the component formula and
  morphism-level multiplicativity). The two triangle identities for `coevSection`
  (`functionalOfSectionCore_sectionOfFunctionalCore`, `sectionOfFunctionalCore_functionalOfSectionCore`) are
  `exact` applications of `DualZigzag.triangle1` / `triangle2`
  (`TotalSpaceTriangleTransport`): the `X`-level zigzag identities of `(coevSection, dualEv)` are checked on the
  frames of `locallyFreeData V` (`DualCoevZigzag`), transported along the braided strong monoidal `g^*`
  (`ZigzagBraided`), and converted between sections and morphisms `O_T ⟶ g^*V`.
  `sectionConstructionsCore_inverse` is assembled from them and from `relativeSpecHomEquiv` (Stacks 01LQ).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry CategoryTheory.MonoidalCategory

noncomputable section

/-! ## §A. Transport lemmas for the quasi-coherent branch of `symGradedAlgebra` -/

namespace AlgebraicGeometry.Scheme.Modules

/-- `V` locally free of finite type ⇒ `V^∨` locally free (`isLocallyFree_dual'`) ⇒ quasi-coherent. -/
theorem dual_isQuasicoherent_of_locallyFree {X : AlgebraicGeometry.Scheme.{u}} (V : X.Modules)
    [V.IsLocallyFree] [V.IsFiniteType] : (dual V).IsQuasicoherent :=
  haveI := isLocallyFree_dual' V
  isQuasicoherent_of_isLocallyFree (dual V)

private theorem casesOn_const {P : Prop} {T : Type u} (d : Decidable P) (f : ¬P → T) (g : P → T)
    (hp : P) : Decidable.casesOn (motive := fun _ => T) d f g = g hp := by
  cases d with
  | isFalse h => exact absurd hp h
  | isTrue h => rfl

/-- The quasi-coherent branch of the `dite` defining `symGradedAlgebra`. -/
theorem symGradedAlgebra_of_isQuasicoherent {X : AlgebraicGeometry.Scheme.{u}} (W : X.Modules)
    (hq : W.IsQuasicoherent) : symGradedAlgebra W = symGradedAlgebraOfQC W hq := by
  delta symGradedAlgebra
  exact dif_pos hq

theorem symGradedAlgebra_part_eq_symPow {X : AlgebraicGeometry.Scheme.{u}} (W : X.Modules)
    (hq : W.IsQuasicoherent) (m : ℕ) : (symGradedAlgebra W).part m = symPow W m := by
  rw [symGradedAlgebra_of_isQuasicoherent W hq]; rfl

/-- In the quasi-coherent case `symGen W` is `V ≅ 𝟙_ ⊗ V → V^{⊗1} → Sym^1 V` followed by the
transport `eqToHom` into `(symGradedAlgebra W).part 1`. -/
theorem symGen_eq_of_isQuasicoherent {X : AlgebraicGeometry.Scheme.{u}} (W : X.Modules)
    (hq : W.IsQuasicoherent) :
    symGen W = (λ_ W).inv ≫ symPowπ W 1 ≫ eqToHom (symGradedAlgebra_part_eq_symPow W hq 1).symm := by
  unfold symGen
  rw [dif_pos hq]

theorem symGen_heq {X : AlgebraicGeometry.Scheme.{u}} (W : X.Modules) (hq : W.IsQuasicoherent) :
    HEq (symGen W) ((λ_ W).inv ≫ symPowπ W 1) := by
  rw [symGen_eq_of_isQuasicoherent W hq]
  exact heq_comp rfl rfl (symGradedAlgebra_part_eq_symPow W hq 1) HEq.rfl (comp_eqToHom_heq _ _)

/-- In the quasi-coherent case `symGradedPullbackDesc` is (heterogeneously) `symPowPullbackDesc`. -/
theorem symGradedPullbackDesc_heq {X Y : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) {W : Y.Modules}
    (hq : W.IsQuasicoherent) {M : X.Modules} [M.IsLineBundle] (ψ : (pullback f).obj W ⟶ M) (m : ℕ) :
    HEq (symGradedPullbackDesc f ψ m) (symPowPullbackDesc f ψ m) := by
  unfold symGradedPullbackDesc
  rw [casesOn_const _ _ _ hq]
  exact cast_heq _ _

theorem pullback_map_one_symGradedPullbackDesc_zero_aux {X T : AlgebraicGeometry.Scheme.{u}} (g : T ⟶ X)
    (W : X.Modules) (hq : W.IsQuasicoherent)
    (ψ : (pullback g).obj W ⟶ SheafOfModules.unit T.ringCatSheaf)
    (S : X.GradedQCAlgebra) (hS : S = symGradedAlgebraOfQC W hq)
    (D : (pullback g).obj (S.part 0) ⟶ SheafOfModules.unit T.ringCatSheaf)
    (hD : HEq D (symPowPullbackDesc g ψ 0)) :
    (pullback g).map S.one ≫ D = (pullbackUnitIso g).hom := by
  subst hS
  have hD' : D = symPowPullbackDesc g ψ 0 := eq_of_heq hD
  subst hD'
  show (pullback g).map (symPowπ W 0) ≫ symPowPullbackDesc g ψ 0 = (pullbackUnitIso g).hom
  refine (pullback_map_symPowπ_symPowPullbackDesc g W ψ 0).trans ?_
  show pullbackMonoidalPow g W 0 ≫ 𝟙 _ = _
  rw [Category.comp_id]
  rfl

/-- Degree 0: the unit of `Sym(W)` pulled back and descended along `ψ` is the canonical `g^*O_X ≅ O_T`. -/
theorem pullback_map_one_symGradedPullbackDesc_zero {X T : AlgebraicGeometry.Scheme.{u}} (g : T ⟶ X)
    (W : X.Modules) (hq : W.IsQuasicoherent)
    (ψ : (pullback g).obj W ⟶ SheafOfModules.unit T.ringCatSheaf) :
    (pullback g).map (symGradedAlgebra W).one ≫ symGradedPullbackDesc g ψ 0 =
      (pullbackUnitIso g).hom :=
  pullback_map_one_symGradedPullbackDesc_zero_aux g W hq ψ _ (symGradedAlgebra_of_isQuasicoherent W hq) _
    (symGradedPullbackDesc_heq g hq ψ 0)

/-- The adjoint transpose of `pullbackUnitIso g` is Mathlib's `unitToPushforwardObjUnit` (`g^♯` on sections):
`pullback_η` + `pushforwardLaxMonoidal_ε`. -/
theorem homEquiv_pullbackUnitIso_hom_eq {Y T : AlgebraicGeometry.Scheme.{u}} (g : T ⟶ Y) :
    (pullbackPushforwardAdjunction g).homEquiv _ _ (pullbackUnitIso g).hom =
      SheafOfModules.unitToPushforwardObjUnit g.toRingCatSheafHom := by
  rw [← pullback_η]
  exact (congrArg _ rfl).trans ((Equiv.apply_symm_apply _ _).trans (pushforwardLaxMonoidal_ε g))

theorem homEquiv_pullbackUnitIso_hom_app_one {Y T : AlgebraicGeometry.Scheme.{u}} (g : T ⟶ Y)
    (U : Y.Opens) :
    (show Γ(T, g ⁻¹ᵁ U) from
      ((pullbackPushforwardAdjunction g).homEquiv _ _ (pullbackUnitIso g).hom).app U
        (show Γ(Y, U) from 1)) = 1 := by
  rw [homEquiv_pullbackUnitIso_hom_eq]
  exact map_one (g.app U).hom

theorem pullback_map_symGen_symGradedPullbackDesc_one_aux {X T : AlgebraicGeometry.Scheme.{u}} (g : T ⟶ X)
    (W : X.Modules) (hq : W.IsQuasicoherent)
    (ψ : (pullback g).obj W ⟶ SheafOfModules.unit T.ringCatSheaf)
    (S : X.GradedQCAlgebra) (hS : S = symGradedAlgebraOfQC W hq)
    (G : W ⟶ S.part 1) (hG : HEq G ((λ_ W).inv ≫ symPowπ W 1))
    (D : (pullback g).obj (S.part 1) ⟶ monoidalPow (SheafOfModules.unit T.ringCatSheaf) 1)
    (hD : HEq D (symPowPullbackDesc g ψ 1)) :
    (pullback g).map G ≫ D ≫ unitPowCollapse T 1 = ψ := by
  subst hS
  have hD' : D = symPowPullbackDesc g ψ 1 := eq_of_heq hD
  have hG' : G = (λ_ W).inv ≫ symPowπ W 1 := eq_of_heq hG
  subst hD' hG'
  let ψ' : (pullback g).obj W ⟶ 𝟙_ T.Modules := ψ
  let η' : (pullback g).obj (𝟙_ X.Modules) ⟶ 𝟙_ T.Modules := (pullbackUnitIso g).hom
  have hA : (pullback g).map (λ_ W).inv ≫ pullbackTensorObjHom g (𝟙_ X.Modules) W ≫
      (η' ▷ (pullback g).obj W) = (λ_ ((pullback g).obj W)).inv := by
    show (pullback g).map (λ_ W).inv ≫ pullbackTensorObjHom g (𝟙_ X.Modules) W ≫
      ((pullbackUnitIso g).hom ▷ (pullback g).obj W) = (λ_ ((pullback g).obj W)).inv
    rw [← Iso.hom_comp_eq_id, pullback_left_unitality]
    simp only [Category.assoc]
    rw [← CategoryTheory.Functor.map_comp_assoc, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
      Category.id_comp]
    show _ ≫ (pullbackTensorObjIso g (𝟙_ X.Modules) W).inv ≫
      (pullbackTensorObjIso g (𝟙_ X.Modules) W).hom ≫ _ = _
    erw [Iso.inv_hom_id_assoc, ← MonoidalCategory.comp_whiskerRight, Iso.inv_hom_id,
      MonoidalCategory.id_whiskerRight]
  have key2 : (pullback g).map (λ_ W).inv ≫ (pullbackMonoidalPow g W 1 ≫ monoidalPowMap ψ 1) ≫
      unitPowCollapse T 1 = ψ := by
    show (pullback g).map (λ_ W).inv ≫ ((pullbackTensorObjHom g (𝟙_ X.Modules) W ≫
        (η' ▷ (pullback g).obj W)) ≫ (𝟙 (𝟙_ T.Modules) ⊗ₘ ψ')) ≫
        ((𝟙 (𝟙_ T.Modules) ▷ 𝟙_ T.Modules) ≫ (λ_ (𝟙_ T.Modules)).hom) = ψ'
    rw [MonoidalCategory.id_whiskerRight, Category.id_comp, MonoidalCategory.id_tensorHom,
      ← Category.assoc, ← Category.assoc, hA, Category.assoc, MonoidalCategory.leftUnitor_naturality,
      Iso.inv_hom_id_assoc]
  erw [CategoryTheory.Functor.map_comp, Category.assoc,
    reassoc_of% (pullback_map_symPowπ_symPowPullbackDesc g W ψ 1)]
  exact key2

/-- Degree 1: the generator `symGen W : W → Sym^1 W`, pulled back and descended along `ψ`, then collapsed
`O_T^{⊗1} → O_T`, gives back `ψ`. -/
theorem pullback_map_symGen_symGradedPullbackDesc_one {X T : AlgebraicGeometry.Scheme.{u}} (g : T ⟶ X)
    (W : X.Modules) (hq : W.IsQuasicoherent)
    (ψ : (pullback g).obj W ⟶ SheafOfModules.unit T.ringCatSheaf) :
    (pullback g).map (symGen W) ≫ symGradedPullbackDesc g ψ 1 ≫ unitPowCollapse T 1 = ψ :=
  pullback_map_symGen_symGradedPullbackDesc_one_aux g W hq ψ _ (symGradedAlgebra_of_isQuasicoherent W hq)
    _ (symGen_heq W hq) _ (symGradedPullbackDesc_heq g hq ψ 1)


/-- Transport of `pullback_map_symPowMul_symPowPullbackDesc` (`MonoidalPowMulCompat`) to the `dite`-defined
`symGradedAlgebra`/`symGradedPullbackDesc`, after adjoint transposition: with `Ψ_m := D m ≫ unitPowCollapse T m`
and `φ_m := homEquiv Ψ_m`, `S.mul m n ≫ φ_{m+n} = (φ_m ⊗ₘ φ_n) ≫ pushforwardUnitMul g`. Stated for an abstract
`S = symGradedAlgebraOfQC W hq` and `D m` heterogeneously equal to `symPowPullbackDesc g ψ m`, so that `subst`
does the transport (see the module docstring, §A). -/
theorem mul_homEquiv_symGradedPullbackDesc_aux {X T : AlgebraicGeometry.Scheme.{u}} (g : T ⟶ X)
    (W : X.Modules) (hq : W.IsQuasicoherent)
    (ψ : (pullback g).obj W ⟶ SheafOfModules.unit T.ringCatSheaf)
    (S : X.GradedQCAlgebra) (hS : S = symGradedAlgebraOfQC W hq)
    (D : ∀ m : ℕ, (pullback g).obj (S.part m) ⟶ monoidalPow (SheafOfModules.unit T.ringCatSheaf) m)
    (hD : ∀ m, HEq (D m) (symPowPullbackDesc g ψ m)) (m n : ℕ) :
    S.mul m n ≫ (pullbackPushforwardAdjunction g).homEquiv _ _ (D (m + n) ≫ unitPowCollapse T (m + n)) =
      ((pullbackPushforwardAdjunction g).homEquiv _ _ (D m ≫ unitPowCollapse T m) ⊗ₘ
        (pullbackPushforwardAdjunction g).homEquiv _ _ (D n ≫ unitPowCollapse T n)) ≫
        pushforwardUnitMul g := by
  subst hS
  have hD' : D = fun m => symPowPullbackDesc g ψ m := funext fun m => eq_of_heq (hD m)
  subst hD'
  have hT : ((pullbackPushforwardAdjunction g).homEquiv _ _
        (symPowPullbackDesc g ψ m ≫ unitPowCollapse T m) ⊗ₘ
      (pullbackPushforwardAdjunction g).homEquiv _ _
        (symPowPullbackDesc g ψ n ≫ unitPowCollapse T n)) ≫ pushforwardUnitMul g =
      (pullbackPushforwardAdjunction g).homEquiv _ _
        (pullbackTensorObjHom g (symPow W m) (symPow W n) ≫
          ((symPowPullbackDesc g ψ m ≫ unitPowCollapse T m) ⊗ₘ
            (symPowPullbackDesc g ψ n ≫ unitPowCollapse T n)) ≫ (λ_ (𝟙_ T.Modules)).hom) :=
    tensorHom_homEquiv_pushforwardUnitMul g _ _
  refine Eq.trans ?_ hT.symm
  rw [← Adjunction.homEquiv_naturality_left]
  exact congrArg _ (pullback_map_symPowMul_symPowPullbackDesc g W ψ m n)

section general

open CategoryTheory.MonoidalCategory

variable {C : Type u'} [Category.{v'} C] [MonoidalCategory C]

/-- Abstract induction step for `ι_comp_ext_of_symGen_aux`: if `π' = c ≫ (p₁ ⊗ₘ p₂) ≫ s`, `s ≫ i = (q₁ ⊗ₘ q₂) ≫ μ`
and `μ ≫ φ = (φ ⊗ₘ φ) ≫ ν`, then `π' ≫ i ≫ φ = c ≫ ((p₁ ≫ q₁ ≫ φ) ⊗ₘ (p₂ ≫ q₂ ≫ φ)) ≫ ν`. Stated over abstract
objects so that it can be applied by `exact` (the concrete objects `Sym^m W` / `S.part m` differ in spelling). -/
theorem ext_step_aux {A A₁ A₂ B₁ B₂ B E R : C} (π' : A ⟶ B) (c : A ⟶ A₁ ⊗ A₂) (p₁ : A₁ ⟶ B₁) (p₂ : A₂ ⟶ B₂)
    (s : B₁ ⊗ B₂ ⟶ B) (e : π' = c ≫ (p₁ ⊗ₘ p₂) ≫ s) (i : B ⟶ E) (q₁ : B₁ ⟶ E) (q₂ : B₂ ⟶ E)
    (μ : E ⊗ E ⟶ E) (hc : s ≫ i = (q₁ ⊗ₘ q₂) ≫ μ) (φ : E ⟶ R) (ν : R ⊗ R ⟶ R)
    (hφ : μ ≫ φ = (φ ⊗ₘ φ) ≫ ν) :
    π' ≫ i ≫ φ = c ≫ ((p₁ ≫ q₁ ≫ φ) ⊗ₘ (p₂ ≫ q₂ ≫ φ)) ≫ ν := by
  subst e
  rw [Category.assoc, Category.assoc, ← Category.assoc s, hc, Category.assoc, hφ,
    tensorHom_comp_tensorHom_assoc, tensorHom_comp_tensorHom_assoc]
  simp only [Category.assoc]

end general

/-- **An algebra map out of `Sym(W)` is determined by its degree-one part** (transport version): for
`S = symGradedAlgebraOfQC W hq`, `G` heterogeneously equal to `(λ_ W).inv ≫ symPowπ W 1` (i.e. `symGen W`), and
`φ₁ φ₂ : ∐ S.part ⟶ g_*O_T` multiplicative (morphism level) and agreeing on the unit and on `G ≫ ι_1`, one has
`ι_m ≫ φ₁ = ι_m ≫ φ₂` for every `m`. Induction on `m`, cancelling the epimorphism `symPowπ W m`:
`m = 0` is the unit clause (`S.total.one = symPowπ W 0 ≫ ι_0`); `m + 1` uses
`(π_m ⊗ₘ π_1) ≫ symPowMul W m 1 = cat.hom ≫ π_{m+1}` (`tensorHom_symPowπ_symPowMul`), the component formula
`total_mul_component` and multiplicativity (`ext_step_aux`). All steps are term-mode `exact`s: `rw` cannot see
through `S.part m = Sym^m W` (module docstring, §A). -/
theorem ι_comp_ext_of_symGen_aux {X T : AlgebraicGeometry.Scheme.{u}} (g : T ⟶ X)
    (W : X.Modules) (hq : W.IsQuasicoherent)
    (S : X.GradedQCAlgebra) (hS : S = symGradedAlgebraOfQC W hq)
    (G : W ⟶ S.part 1) (hG : HEq G ((λ_ W).inv ≫ symPowπ W 1))
    (φ₁ φ₂ : S.total.carrier ⟶ (pushforward g).obj (SheafOfModules.unit T.ringCatSheaf))
    (h1 : S.total.mul ≫ φ₁ = (φ₁ ⊗ₘ φ₁) ≫ pushforwardUnitMul g)
    (h2 : S.total.mul ≫ φ₂ = (φ₂ ⊗ₘ φ₂) ≫ pushforwardUnitMul g)
    (u : S.total.one ≫ φ₁ = S.total.one ≫ φ₂)
    (h : G ≫ Sigma.ι S.part 1 ≫ φ₁ = G ≫ Sigma.ι S.part 1 ≫ φ₂) :
    ∀ m : ℕ, Sigma.ι S.part m ≫ φ₁ = Sigma.ι S.part m ≫ φ₂ := by
  subst hS
  have hG' : G = (λ_ W).inv ≫ symPowπ W 1 := eq_of_heq hG
  subst hG'
  have h' : symPowπ W 1 ≫ Sigma.ι (symGradedAlgebraOfQC W hq).part 1 ≫ φ₁ =
      symPowπ W 1 ≫ Sigma.ι (symGradedAlgebraOfQC W hq).part 1 ≫ φ₂ :=
    (Iso.cancel_iso_inv_left (λ_ W) _ _).mp
      ((Category.assoc (λ_ W).inv (symPowπ W 1) _).symm.trans
        (h.trans (Category.assoc (λ_ W).inv (symPowπ W 1) _)))
  intro m
  induction m with
  | zero =>
    refine (cancel_epi (symPowπ W 0)).mp ?_
    exact (Category.assoc (symPowπ W 0) (Sigma.ι (symGradedAlgebraOfQC W hq).part 0) φ₁).symm.trans
      (u.trans (Category.assoc (symPowπ W 0) (Sigma.ι (symGradedAlgebraOfQC W hq).part 0) φ₂))
  | succ m ih =>
    refine (cancel_epi (symPowπ W (m + 1))).mp ?_
    have e : symPowπ W (m + 1) = (monoidalPowCat W m 1).inv ≫
        (symPowπ W m ⊗ₘ symPowπ W 1) ≫ symPowMul W m 1 := by
      rw [tensorHom_symPowπ_symPowMul, Iso.inv_hom_id_assoc]
    have hc : symPowMul W m 1 ≫ Sigma.ι (symGradedAlgebraOfQC W hq).part (m + 1) =
        (Sigma.ι (symGradedAlgebraOfQC W hq).part m ⊗ₘ Sigma.ι (symGradedAlgebraOfQC W hq).part 1) ≫
          (symGradedAlgebraOfQC W hq).total.mul :=
      (GradedQCAlgebra.total_mul_component (symGradedAlgebraOfQC W hq) m 1).symm
    have k₁ := ext_step_aux (symPowπ W (m + 1)) (monoidalPowCat W m 1).inv (symPowπ W m) (symPowπ W 1)
      (symPowMul W m 1) e (Sigma.ι (symGradedAlgebraOfQC W hq).part (m + 1))
      (Sigma.ι (symGradedAlgebraOfQC W hq).part m) (Sigma.ι (symGradedAlgebraOfQC W hq).part 1)
      (symGradedAlgebraOfQC W hq).total.mul hc φ₁ (pushforwardUnitMul g) h1
    have k₂ := ext_step_aux (symPowπ W (m + 1)) (monoidalPowCat W m 1).inv (symPowπ W m) (symPowπ W 1)
      (symPowMul W m 1) e (Sigma.ι (symGradedAlgebraOfQC W hq).part (m + 1))
      (Sigma.ι (symGradedAlgebraOfQC W hq).part m) (Sigma.ι (symGradedAlgebraOfQC W hq).part 1)
      (symGradedAlgebraOfQC W hq).total.mul hc φ₂ (pushforwardUnitMul g) h2
    refine k₁.trans (Eq.trans ?_ k₂.symm)
    exact congrArg (fun z => (monoidalPowCat W m 1).inv ≫ z ≫ pushforwardUnitMul g)
      (congrArg₂ (fun a b => a ⊗ₘ b) (congrArg (fun z => symPowπ W m ≫ z) ih) h')

end AlgebraicGeometry.Scheme.Modules

/-! ## §B. From a section to an algebra map -/

noncomputable def AlgebraicGeometry.Scheme.totalSpace.functionalOfSectionCore
    {X : AlgebraicGeometry.Scheme.{u}} (V : X.Modules) (T : CategoryTheory.Over X)
    (s : (((AlgebraicGeometry.Scheme.Modules.pullback T.hom).obj V).val.obj
      (Opposite.op ⊤) : Type u)) :
    (AlgebraicGeometry.Scheme.Modules.pullback T.hom).obj
        (AlgebraicGeometry.Scheme.Modules.dual V) ⟶
      SheafOfModules.unit T.left.ringCatSheaf :=
  (ρ_ ((AlgebraicGeometry.Scheme.Modules.pullback T.hom).obj
      (AlgebraicGeometry.Scheme.Modules.dual V))).inv ≫
    ((AlgebraicGeometry.Scheme.Modules.pullback T.hom).obj
      (AlgebraicGeometry.Scheme.Modules.dual V) ◁
      AlgebraicGeometry.Scheme.Modules.homOfTopSection _ s) ≫
    (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjIso T.hom
      (AlgebraicGeometry.Scheme.Modules.dual V) V).inv ≫
    (AlgebraicGeometry.Scheme.Modules.pullback T.hom).map
      (AlgebraicGeometry.Scheme.Modules.internalHomEval V
        (SheafOfModules.unit X.ringCatSheaf)) ≫
    (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso T.hom).hom

noncomputable def AlgebraicGeometry.Scheme.totalSpace.algebraMapOfFunctionalCore
    {X : AlgebraicGeometry.Scheme.{u}} (V : X.Modules) (T : CategoryTheory.Over X)
    (ψ : (AlgebraicGeometry.Scheme.Modules.pullback T.hom).obj
        (AlgebraicGeometry.Scheme.Modules.dual V) ⟶
      SheafOfModules.unit T.left.ringCatSheaf) :
    (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
      (AlgebraicGeometry.Scheme.Modules.dual V)).total.carrier ⟶
      (AlgebraicGeometry.Scheme.Modules.pushforward T.hom).obj
        (SheafOfModules.unit T.left.ringCatSheaf) :=
  CategoryTheory.Limits.Sigma.desc fun m ↦
    (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction T.hom).homEquiv _ _
      (AlgebraicGeometry.Scheme.Modules.symGradedPullbackDesc T.hom ψ m ≫
        AlgebraicGeometry.Scheme.Modules.unitPowCollapse T.left m)

/-- **Multiplicativity of `algebraMapOfFunctionalCore`** (first half of `IsAlgebraMapToPushforward`).

References: Stacks 01LQ (maps to a relative Spec are algebra maps), 01M2/01N8 (symmetric algebra maps are
determined degreewise). This is the same statement as
`projBundle.localRingHomComponent_mul` (`ProjectiveBundleUniversalProperty`) with `M = O_T`,
`U = T`, all degrees at once, and phrased on sections of the coproduct `∐ Sym^m`.

## Proof

Write `W := V^∨` (quasi-coherent by `dual_isQuasicoherent_of_locallyFree`, so `symGradedAlgebra W` is
`symGradedAlgebraOfQC W hq`: `part m = Sym^m W`, `mul m n = symPowMul W m n`, `one = symPowπ W 0`),
`g := T.hom`, `C := ∐_m Sym^m W`, `Ψ_m := symGradedPullbackDesc g ψ m ≫ unitPowCollapse T m :
g^*Sym^m W ⟶ O_T`, `φ_m := homEquiv Ψ_m : Sym^m W ⟶ g_*O_T`, `Φ := Sigma.desc φ = algebraMapOfFunctionalCore`.
Let `μ_T := (λ_ O_T).hom : O_T ⊗ O_T ⟶ O_T` and `μ_* := LaxMonoidal.μ (pushforward g) O_T O_T`
(`pushforwardLaxMonoidal`).

**Step 1 (morphism-level statement).** It suffices to prove the equality of morphisms `C ⊗ C ⟶ g_*O_T`
  `S.total.mul ≫ Φ = (Φ ⊗ₘ Φ) ≫ μ_* ≫ (pushforward g).map μ_T`.            (★)
Indeed, evaluating (★) at `U` on `tensorSections C C U a b` and using
`tensorHom_tensorSections`, `pushforwardLaxMonoidal_μ_tensorSections` (`μ_*(a ⊗ b) = a ⊗ b` on `g⁻¹U`) and
`leftUnitor_app_tensorSections` (`(λ_ O).hom (r ⊗ a) = r • a = r * a`) gives exactly the claim.

**Step 2 (reduce to components).** `- ⊗ -` preserves coproducts in each variable
(`tensorLeft_preservesColimitsOfSize`, `tensorRight_preservesColimitsOfSize`), so the family
`Sigma.ι m ⊗ₘ Sigma.ι n : Sym^m ⊗ Sym^n ⟶ C ⊗ C` is jointly epimorphic; it suffices to check (★) after precomposition
with each `ι_m ⊗ₘ ι_n`. The component formula for the total multiplication (unwinding `totalMul`/`totalMulRow`/`totalCurry`,
using `tensorObjHomEquiv_naturality_left` and `Sigma.ι_desc`):
  `(ι_m ⊗ₘ ι_n) ≫ S.total.mul = symPowMul W m n ≫ ι_{m+n}`.
So the left side of (★) on the `(m,n)` component is `symPowMul W m n ≫ φ_{m+n}` and the right side is
`(φ_m ⊗ₘ φ_n) ≫ μ_* ≫ (pushforward g).map μ_T`.

**Step 3 (transpose along `g^* ⊣ g_*`).** Both sides are maps `Sym^m ⊗ Sym^n ⟶ g_*O_T`; apply
`homEquiv.symm`. Left: `g^*(symPowMul m n) ≫ Ψ_{m+n}` (`homEquiv_naturality_left_symm`). Right: by
`homEquiv_pullbackTensorObjHom` (`δ` transposes to `(η ⊗ η) ≫ μ_*`) and naturality,
`(φ_m ⊗ₘ φ_n) ≫ μ_* = homEquiv (δ_{Sym^m, Sym^n} ≫ (Ψ_m ⊗ₘ Ψ_n))`, so the right side transposes to
`δ ≫ (Ψ_m ⊗ₘ Ψ_n) ≫ μ_T` where `δ = pullbackTensorObjHom g (Sym^m W) (Sym^n W)`.
Goal: `g^*(symPowMul W m n) ≫ Ψ_{m+n} = δ ≫ (Ψ_m ⊗ₘ Ψ_n) ≫ (λ_ O_T).hom`.                    (★★)

**Step 4 (kill the symmetric quotient).** Precompose with the epimorphism
`g^*(symPowπ W m ⊗ₘ symPowπ W n)` (`symPowπ_epi`, `tensorLeft/Right_preservesEpimorphisms`, `pullback g`
is a left adjoint hence preserves epis). Using `symPowMul`'s defining property
(`symPowDesc₂`: `(π_m ⊗ₘ π_n) ≫ symPowMul m n = (monoidalPowCat W m n).hom ≫ π_{m+n}`) and
`pullback_map_symPowπ_symPowPullbackDesc`, (★★) becomes
  `g^*((monoidalPowCat W m n).hom) ≫ pullbackMonoidalPow g W (m+n) ≫ monoidalPowMap ψ (m+n) ≫ unitPowCollapse (m+n)`
  `= δ_{W^{⊗m},W^{⊗n}} ≫ ((pullbackMonoidalPow g W m ≫ monoidalPowMap ψ m ≫ unitPowCollapse m) ⊗ₘ (… n …)) ≫ (λ_ O_T).hom`
(the `δ` for `Sym^m ⊗ Sym^n` and for `W^{⊗m} ⊗ W^{⊗n}` are related by `δ_natural`/`pullback_μ_natural_left/right`).

**Step 5 (induction on `n`).** Three compatibilities, each by induction on `n` unwinding the recursive
definitions (`monoidalPowCat`, `pullbackMonoidalPow`, `monoidalPowMap`, `unitPowCollapse`):
 (a) `pullbackMonoidalPow` is multiplicative: `g^*(monoidalPowCat W m n).hom ≫ pullbackMonoidalPow g W (m+n)
     = δ ≫ (pullbackMonoidalPow g W m ⊗ₘ pullbackMonoidalPow g W n) ≫ (monoidalPowCat (g^*W) m n).hom`
     (n = 0: `pullback_right_unitality`; n+1: `pullback_μ_associativity` and `δ_natural_left`).
 (b) `monoidalPowMap ψ` is multiplicative: `(monoidalPowCat (g^*W) m n).hom ≫ monoidalPowMap ψ (m+n)
     = (monoidalPowMap ψ m ⊗ₘ monoidalPowMap ψ n) ≫ (monoidalPowCat O_T m n).hom` (naturality of `ρ_`, `α_`).
 (c) `unitPowCollapse` is multiplicative: `(monoidalPowCat O_T m n).hom ≫ unitPowCollapse (m+n)
     = (unitPowCollapse m ⊗ₘ unitPowCollapse n) ≫ (λ_ O_T).hom` (n = 0: `unitors_equal`; n+1: triangle
     identity `α_ ≫ (𝟙 ◁ λ_) = ρ_ ▷ 𝟙` and `leftUnitor_naturality`).
Chaining (a)(b)(c) gives Step 4. ∎

As formalized: Step 1 = `QCAlgebra.isAlgebraMap_mul_of_mul_comp` (`AlgebraMapToPushforwardMorphismLevel`); Step 2 =
`tensorObj_sigma_hom_ext` + `GradedQCAlgebra.total_mul_component` (`GradedAlgebraTotalComponent`); Step 3 =
`tensorHom_homEquiv_pushforwardUnitMul`; Steps 4-5 = `pullback_map_symPowMul_symPowPullbackDesc`
(`MonoidalPowMulCompat`, (a) `pullbackMonoidalPow_monoidalPowCat`, (b) `monoidalPowCat_monoidalPowMap` from
`SymPowMap`, (c) `unitPowCollapse_monoidalPowCat`). Transport to the `dite`-defined `symGradedAlgebra`:
`mul_homEquiv_symGradedPullbackDesc_aux` (§A). -/
theorem AlgebraicGeometry.Scheme.totalSpace.algebraMapOfFunctionalCore_mul
    {X : AlgebraicGeometry.Scheme.{u}} (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType]
    (T : CategoryTheory.Over X)
    (ψ : (AlgebraicGeometry.Scheme.Modules.pullback T.hom).obj
        (AlgebraicGeometry.Scheme.Modules.dual V) ⟶
      SheafOfModules.unit T.left.ringCatSheaf) :
    ∀ (U : X.Opens)
      (a b : (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
        (AlgebraicGeometry.Scheme.Modules.dual V)).total.carrier.val.obj (Opposite.op U)),
      (show Γ(T.left, T.hom ⁻¹ᵁ U) from
        (AlgebraicGeometry.Scheme.totalSpace.algebraMapOfFunctionalCore V T ψ).app U
          ((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
            (AlgebraicGeometry.Scheme.Modules.dual V)).total.mul.app U
              (AlgebraicGeometry.Scheme.Modules.tensorSections _ _ U a b))) =
        (show Γ(T.left, T.hom ⁻¹ᵁ U) from
          (AlgebraicGeometry.Scheme.totalSpace.algebraMapOfFunctionalCore V T ψ).app U a) *
        (show Γ(T.left, T.hom ⁻¹ᵁ U) from
          (AlgebraicGeometry.Scheme.totalSpace.algebraMapOfFunctionalCore V T ψ).app U b) := by
  have hq := AlgebraicGeometry.Scheme.Modules.dual_isQuasicoherent_of_locallyFree V
  apply AlgebraicGeometry.Scheme.QCAlgebra.isAlgebraMap_mul_of_mul_comp
  apply AlgebraicGeometry.Scheme.Modules.tensorObj_sigma_hom_ext
  intro m n
  -- all steps are term-mode: `rw` cannot see through `S.total.carrier = ∐ S.part` (module docstring, §A)
  have e1 : (CategoryTheory.Limits.Sigma.ι (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
        (AlgebraicGeometry.Scheme.Modules.dual V)).part m ⊗ₘ
        CategoryTheory.Limits.Sigma.ι (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
          (AlgebraicGeometry.Scheme.Modules.dual V)).part n) ≫
        (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
          (AlgebraicGeometry.Scheme.Modules.dual V)).total.mul ≫
        AlgebraicGeometry.Scheme.totalSpace.algebraMapOfFunctionalCore V T ψ =
      (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
          (AlgebraicGeometry.Scheme.Modules.dual V)).mul m n ≫
        CategoryTheory.Limits.Sigma.ι (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
          (AlgebraicGeometry.Scheme.Modules.dual V)).part (m + n) ≫
        AlgebraicGeometry.Scheme.totalSpace.algebraMapOfFunctionalCore V T ψ :=
    (Category.assoc _ _ _).symm.trans
      ((congrArg (fun z => z ≫ AlgebraicGeometry.Scheme.totalSpace.algebraMapOfFunctionalCore V T ψ)
        (AlgebraicGeometry.Scheme.GradedQCAlgebra.total_mul_component _ m n)).trans
        (Category.assoc _ _ _))
  have hd : ∀ k : ℕ, CategoryTheory.Limits.Sigma.ι (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
        (AlgebraicGeometry.Scheme.Modules.dual V)).part k ≫
        AlgebraicGeometry.Scheme.totalSpace.algebraMapOfFunctionalCore V T ψ =
      (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction T.hom).homEquiv _ _
        (AlgebraicGeometry.Scheme.Modules.symGradedPullbackDesc T.hom ψ k ≫
          AlgebraicGeometry.Scheme.Modules.unitPowCollapse T.left k) :=
    fun k => CategoryTheory.Limits.Sigma.ι_desc _ _
  refine e1.trans (Eq.trans ?_ (MonoidalCategory.tensorHom_comp_tensorHom_assoc _ _ _ _ _).symm)
  refine (congrArg (fun z => (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
      (AlgebraicGeometry.Scheme.Modules.dual V)).mul m n ≫ z) (hd (m + n))).trans
    (Eq.trans ?_ (congrArg (fun z => z ≫ AlgebraicGeometry.Scheme.Modules.pushforwardUnitMul T.hom)
      (congrArg₂ (fun a b => a ⊗ₘ b) (hd m) (hd n))).symm)
  exact AlgebraicGeometry.Scheme.Modules.mul_homEquiv_symGradedPullbackDesc_aux T.hom
    (AlgebraicGeometry.Scheme.Modules.dual V) hq ψ _
    (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra_of_isQuasicoherent _ hq) _
    (fun m => AlgebraicGeometry.Scheme.Modules.symGradedPullbackDesc_heq T.hom hq ψ m) m n

/-- **Unit preservation of `algebraMapOfFunctionalCore`**: `total.one = one ≫ ι_0`, `ι_0 ≫ Sigma.desc = φ_0`,
`one ≫ φ_0 = homEquiv (g^*one ≫ Ψ_0) = homEquiv (pullbackUnitIso g).hom`
(`pullback_map_one_symGradedPullbackDesc_zero`) `= unitToPushforwardObjUnit g^♯`
(`homEquiv_pullbackUnitIso_hom_eq`), which is the ring map `g^♯` on sections, so `1 ↦ 1`. -/
theorem AlgebraicGeometry.Scheme.totalSpace.algebraMapOfFunctionalCore_one
    {X : AlgebraicGeometry.Scheme.{u}} (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType]
    (T : CategoryTheory.Over X)
    (ψ : (AlgebraicGeometry.Scheme.Modules.pullback T.hom).obj
        (AlgebraicGeometry.Scheme.Modules.dual V) ⟶
      SheafOfModules.unit T.left.ringCatSheaf) :
    ∀ U : X.Opens,
      (show Γ(T.left, T.hom ⁻¹ᵁ U) from
        (AlgebraicGeometry.Scheme.totalSpace.algebraMapOfFunctionalCore V T ψ).app U
          ((AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
            (AlgebraicGeometry.Scheme.Modules.dual V)).total.one.app U
              (show Γ(X, U) from 1))) = 1 := by
  intro U
  have hq := AlgebraicGeometry.Scheme.Modules.dual_isQuasicoherent_of_locallyFree V
  let S := AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
    (AlgebraicGeometry.Scheme.Modules.dual V)
  let f : ∀ m, S.part m ⟶
      (AlgebraicGeometry.Scheme.Modules.pushforward T.hom).obj
        (SheafOfModules.unit T.left.ringCatSheaf) := fun m ↦
    (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction T.hom).homEquiv _ _
      (AlgebraicGeometry.Scheme.Modules.symGradedPullbackDesc T.hom ψ m ≫
        AlgebraicGeometry.Scheme.Modules.unitPowCollapse T.left m)
  have hcomp : S.total.one ≫ CategoryTheory.Limits.Sigma.desc f = S.one ≫ f 0 := by
    change (S.one ≫ CategoryTheory.Limits.Sigma.ι S.part 0) ≫
      CategoryTheory.Limits.Sigma.desc f = S.one ≫ f 0
    rw [Category.assoc, CategoryTheory.Limits.Sigma.ι_desc]
  have h2 : S.one ≫ f 0 =
      (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction T.hom).homEquiv _ _
        (AlgebraicGeometry.Scheme.Modules.pullbackUnitIso T.hom).hom := by
    show S.one ≫ (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction T.hom).homEquiv _ _
      (AlgebraicGeometry.Scheme.Modules.symGradedPullbackDesc T.hom ψ 0 ≫
        AlgebraicGeometry.Scheme.Modules.unitPowCollapse T.left 0) = _
    rw [← Adjunction.homEquiv_naturality_left]
    congr 1
    show (AlgebraicGeometry.Scheme.Modules.pullback T.hom).map S.one ≫
      AlgebraicGeometry.Scheme.Modules.symGradedPullbackDesc T.hom ψ 0 ≫ 𝟙 _ = _
    rw [Category.comp_id]
    exact AlgebraicGeometry.Scheme.Modules.pullback_map_one_symGradedPullbackDesc_zero T.hom
      (AlgebraicGeometry.Scheme.Modules.dual V) hq ψ
  change (show Γ(T.left, T.hom ⁻¹ᵁ U) from
    ((S.total.one ≫ CategoryTheory.Limits.Sigma.desc f).app U)
      (show Γ(X, U) from 1)) = 1
  rw [hcomp, h2]
  exact AlgebraicGeometry.Scheme.Modules.homEquiv_pullbackUnitIso_hom_app_one T.hom U

theorem AlgebraicGeometry.Scheme.totalSpace.algebraMapOfFunctionalCore_preservesOperations
    {X : AlgebraicGeometry.Scheme.{u}} (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType]
    (T : CategoryTheory.Over X)
    (ψ : (AlgebraicGeometry.Scheme.Modules.pullback T.hom).obj
        (AlgebraicGeometry.Scheme.Modules.dual V) ⟶
      SheafOfModules.unit T.left.ringCatSheaf) :
    (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
      (AlgebraicGeometry.Scheme.Modules.dual V)).total.IsAlgebraMapToPushforward T.hom
        (AlgebraicGeometry.Scheme.totalSpace.algebraMapOfFunctionalCore V T ψ) := by
  exact ⟨AlgebraicGeometry.Scheme.totalSpace.algebraMapOfFunctionalCore_mul V T ψ,
    AlgebraicGeometry.Scheme.totalSpace.algebraMapOfFunctionalCore_one V T ψ⟩

/-! ## §C. The two constructions -/

noncomputable def AlgebraicGeometry.Scheme.totalSpace.ofSectionCore
    {X : AlgebraicGeometry.Scheme.{u}} (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType]
    (T : CategoryTheory.Over X)
    (s : (((AlgebraicGeometry.Scheme.Modules.pullback T.hom).obj V).val.obj
      (Opposite.op ⊤) : Type u)) :
    T ⟶ AlgebraicGeometry.Scheme.totalSpace V :=
  AlgebraicGeometry.Scheme.relativeSpec.ofAlgebraMap
    (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
      (AlgebraicGeometry.Scheme.Modules.dual V)).total T
    (AlgebraicGeometry.Scheme.totalSpace.algebraMapOfFunctionalCore V T
      (AlgebraicGeometry.Scheme.totalSpace.functionalOfSectionCore V T s))
    (AlgebraicGeometry.Scheme.totalSpace.algebraMapOfFunctionalCore_preservesOperations V T
      (AlgebraicGeometry.Scheme.totalSpace.functionalOfSectionCore V T s))

/-- The linear functional `g^*(V^∨) → O_T` attached to an `X`-morphism `h : T → Tot(V)`: the degree-one
part `V^∨ → Sym^1 → Sym → g_*O_T` of the algebra map `relativeSpec.toAlgebraMap … h`, transposed along
`g^* ⊣ g_*`. -/
noncomputable def AlgebraicGeometry.Scheme.totalSpace.functionalOfHomCore
    {X : AlgebraicGeometry.Scheme.{u}} (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType]
    (T : CategoryTheory.Over X) (h : T ⟶ AlgebraicGeometry.Scheme.totalSpace V) :
    (AlgebraicGeometry.Scheme.Modules.pullback T.hom).obj
        (AlgebraicGeometry.Scheme.Modules.dual V) ⟶ 𝟙_ T.left.Modules :=
  ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction T.hom).homEquiv _ _).symm
    (AlgebraicGeometry.Scheme.Modules.symGen (AlgebraicGeometry.Scheme.Modules.dual V) ≫
      CategoryTheory.Limits.Sigma.ι (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
        (AlgebraicGeometry.Scheme.Modules.dual V)).part 1 ≫
      AlgebraicGeometry.Scheme.relativeSpec.toAlgebraMap
        (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
          (AlgebraicGeometry.Scheme.Modules.dual V)).total T h)

/-- The section `(ψ ⊗ id)(g^* coev_V) ∈ Γ(T, g^*V)` attached to a functional `ψ : g^*(V^∨) → O_T`. -/
noncomputable def AlgebraicGeometry.Scheme.totalSpace.sectionOfFunctionalCore
    {X : AlgebraicGeometry.Scheme.{u}} (V : X.Modules) [V.IsLocallyFree]
    (T : CategoryTheory.Over X)
    (ψ : (AlgebraicGeometry.Scheme.Modules.pullback T.hom).obj
        (AlgebraicGeometry.Scheme.Modules.dual V) ⟶ 𝟙_ T.left.Modules) :
    (((AlgebraicGeometry.Scheme.Modules.pullback T.hom).obj V).val.obj
      (Opposite.op ⊤) : Type u) :=
  let Ψ : (AlgebraicGeometry.Scheme.Modules.pullback T.hom).obj
        (AlgebraicGeometry.Scheme.Modules.tensor
          (AlgebraicGeometry.Scheme.Modules.dual V) V) ⟶
      (AlgebraicGeometry.Scheme.Modules.pullback T.hom).obj V :=
    (AlgebraicGeometry.Scheme.Modules.pullback T.hom).map
        (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj
          (AlgebraicGeometry.Scheme.Modules.dual V) V).hom ≫
      AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom T.hom
        (AlgebraicGeometry.Scheme.Modules.dual V) V ≫
      (ψ ▷ (AlgebraicGeometry.Scheme.Modules.pullback T.hom).obj V) ≫
      (λ_ ((AlgebraicGeometry.Scheme.Modules.pullback T.hom).obj V)).hom
  Ψ.app ⊤ (sectionPullbackAlong T.hom
    (AlgebraicGeometry.Scheme.Modules.coevSection V))

noncomputable def AlgebraicGeometry.Scheme.totalSpace.toSectionCore
    {X : AlgebraicGeometry.Scheme.{u}} (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType]
    (T : CategoryTheory.Over X) (h : T ⟶ AlgebraicGeometry.Scheme.totalSpace V) :
    (((AlgebraicGeometry.Scheme.Modules.pullback T.hom).obj V).val.obj
      (Opposite.op ⊤) : Type u) :=
  let S := AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
    (AlgebraicGeometry.Scheme.Modules.dual V)
  let φ := AlgebraicGeometry.Scheme.relativeSpec.toAlgebraMap S.total T h
  let ψ : (AlgebraicGeometry.Scheme.Modules.pullback T.hom).obj
        (AlgebraicGeometry.Scheme.Modules.dual V) ⟶ 𝟙_ T.left.Modules :=
    ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction T.hom).homEquiv _ _).symm
      (AlgebraicGeometry.Scheme.Modules.symGen
          (AlgebraicGeometry.Scheme.Modules.dual V) ≫
        CategoryTheory.Limits.Sigma.ι S.part 1 ≫ φ)
  let Ψ : (AlgebraicGeometry.Scheme.Modules.pullback T.hom).obj
        (AlgebraicGeometry.Scheme.Modules.tensor
          (AlgebraicGeometry.Scheme.Modules.dual V) V) ⟶
      (AlgebraicGeometry.Scheme.Modules.pullback T.hom).obj V :=
    (AlgebraicGeometry.Scheme.Modules.pullback T.hom).map
        (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj
          (AlgebraicGeometry.Scheme.Modules.dual V) V).hom ≫
      AlgebraicGeometry.Scheme.Modules.pullbackTensorObjHom T.hom
        (AlgebraicGeometry.Scheme.Modules.dual V) V ≫
      (ψ ▷ (AlgebraicGeometry.Scheme.Modules.pullback T.hom).obj V) ≫
      (λ_ ((AlgebraicGeometry.Scheme.Modules.pullback T.hom).obj V)).hom
  Ψ.app ⊤ (sectionPullbackAlong T.hom
    (AlgebraicGeometry.Scheme.Modules.coevSection V))

theorem AlgebraicGeometry.Scheme.totalSpace.toSectionCore_eq
    {X : AlgebraicGeometry.Scheme.{u}} (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType]
    (T : CategoryTheory.Over X) (h : T ⟶ AlgebraicGeometry.Scheme.totalSpace V) :
    AlgebraicGeometry.Scheme.totalSpace.toSectionCore V T h =
      AlgebraicGeometry.Scheme.totalSpace.sectionOfFunctionalCore V T
        (AlgebraicGeometry.Scheme.totalSpace.functionalOfHomCore V T h) := rfl

/-! ## §D. The inverse laws -/

/-- **Degree-one component of `algebraMapOfFunctionalCore`**: `symGen ≫ ι_1 ≫ Φ_ψ = homEquiv ψ`
(`Sigma.ι_desc`, `homEquiv_naturality_left`, `pullback_map_symGen_symGradedPullbackDesc_one`). -/
theorem AlgebraicGeometry.Scheme.totalSpace.symGen_ι_algebraMapOfFunctionalCore
    {X : AlgebraicGeometry.Scheme.{u}} (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType]
    (T : CategoryTheory.Over X)
    (ψ : (AlgebraicGeometry.Scheme.Modules.pullback T.hom).obj
        (AlgebraicGeometry.Scheme.Modules.dual V) ⟶
      SheafOfModules.unit T.left.ringCatSheaf) :
    AlgebraicGeometry.Scheme.Modules.symGen (AlgebraicGeometry.Scheme.Modules.dual V) ≫
        CategoryTheory.Limits.Sigma.ι (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
          (AlgebraicGeometry.Scheme.Modules.dual V)).part 1 ≫
        AlgebraicGeometry.Scheme.totalSpace.algebraMapOfFunctionalCore V T ψ =
      (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction T.hom).homEquiv _ _ ψ := by
  have hq := AlgebraicGeometry.Scheme.Modules.dual_isQuasicoherent_of_locallyFree V
  unfold AlgebraicGeometry.Scheme.totalSpace.algebraMapOfFunctionalCore
  rw [CategoryTheory.Limits.Sigma.ι_desc]
  refine (Adjunction.homEquiv_naturality_left
    (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction T.hom) _ _).symm.trans ?_
  exact congrArg _ (AlgebraicGeometry.Scheme.Modules.pullback_map_symGen_symGradedPullbackDesc_one T.hom
    (AlgebraicGeometry.Scheme.Modules.dual V) hq ψ)

/-- **Triangle identity (coev then ev)**: for `ψ : g^*(V^∨) → O_T`, the functional attached to the section
`(ψ ⊗ id)(g^*coev_V)` is `ψ` again.

References: Stacks 01CM/01CN (dual of a locally free module, `V^∨ ⊗ V ≅ 𝓗om(V,V)`, the evaluation/coevaluation
triangle identities).

Proof sketch. Write `s := sectionOfFunctionalCore V T ψ = (λ_).hom ((ψ ▷ g^*V) (δ (g^*(coev))))`,
where `δ = pullbackTensorObjHom` and `g^*(coev)` is `sectionPullbackAlong T.hom (coevSection V)`.
`functionalOfSectionCore V T s` is, on a section `φ` of `g^*(V^∨)` over `W ⊆ T`,
`η ((g^* ev)(δ⁻¹(φ ⊗ s|_W)))`. Locally, on the pullback of the trivializing cover `U_i` of `locallyFreeData V`,
`coev = Σ_j e_j^∨ ⊗ e_j`, so `s = Σ_j ψ(g^*e_j^∨) · g^*e_j` and, for `φ = Σ_k c_k g^*e_k^∨`,
`⟨φ, s⟩ = Σ_{j,k} c_k ψ(g^*e_j^∨) ⟨g^*e_k^∨, g^*e_j⟩ = Σ_k c_k ψ(g^*e_k^∨) = ψ(φ)`.

As formalized (the standard rigid-category zigzag): the **`X`-level** zigzag identity for the pair
`(ev = internalHomEval V O, c = homOfTopSection coevSection)`,
`(ρ_ V^∨).inv ≫ (V^∨ ◁ (c ≫ tensorIsoTensorObj.hom)) ≫ α⁻¹ ≫ (β_{V^∨,V^∨} ▷ V) ≫ α ≫ (V^∨ ◁ ev) ≫ (ρ_ V^∨).hom = 𝟙`,
is `DualZigzag.zigzag1` (`DualCoevZigzag`), checked on sections `dualUnit ψ` over the opens `W ⊆ U_i` of
`locallyFreeData V` with the restricted frame (`Frame.coevOfData_res`, `Frame.phi_eq_sum`,
`dualEv_app_tensorSections_dualUnit`); `Zigzag.Z1_map` transports it along the braided strong monoidal `g^*`;
`Zigzag.lemmaB` (abstract braided monoidal algebra) turns it into the statement at the morphism level;
`DualZigzag.triangle1` converts sections to morphisms `O_T ⟶ g^*V` (`homOfTopSection_app_top`,
`homOfTopSection_sectionPullbackAlong`). For the rank-0/empty cases the statement is still true (both sides are `0`). -/
theorem AlgebraicGeometry.Scheme.totalSpace.functionalOfSectionCore_sectionOfFunctionalCore
    {X : AlgebraicGeometry.Scheme.{u}} (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType]
    (T : CategoryTheory.Over X)
    (ψ : (AlgebraicGeometry.Scheme.Modules.pullback T.hom).obj
        (AlgebraicGeometry.Scheme.Modules.dual V) ⟶ 𝟙_ T.left.Modules) :
    AlgebraicGeometry.Scheme.totalSpace.functionalOfSectionCore V T
        (AlgebraicGeometry.Scheme.totalSpace.sectionOfFunctionalCore V T ψ) = ψ := by
  exact AlgebraicGeometry.Scheme.Modules.DualZigzag.triangle1 V T ψ

/-- **Triangle identity (ev then coev)**: for `s ∈ Γ(T, g^*V)`, `(ψ_s ⊗ id)(g^*coev_V) = s` where
`ψ_s = functionalOfSectionCore V T s` is `φ ↦ ⟨φ, s⟩`.

References: Stacks 01CM/01CN.

Proof sketch. On the pulled-back trivializing cover `g⁻¹U_i`, `g^*coev = Σ_j g^*e_j^∨ ⊗ g^*e_j`, so
`(ψ_s ⊗ id)(g^*coev) = Σ_j ⟨g^*e_j^∨, s⟩ · g^*e_j`, and writing `s|_{g⁻¹U_i} = Σ_k s_k g^*e_k`,
`⟨g^*e_j^∨, s⟩ = s_j`, so the sum is `s|_{g⁻¹U_i}`.

As formalized: the second `X`-level zigzag identity
`(λ_ V).inv ≫ ((c ≫ tensorIsoTensorObj.hom) ▷ V) ≫ α ≫ (V^∨ ◁ β_{V,V}) ≫ α⁻¹ ≫ (ev ▷ V) ≫ (λ_ V).hom = 𝟙 V`
(elementwise `v ↦ Σ_j ⟨e_j^∨, v⟩ e_j = v`, from `Frame.frameData`) is `DualZigzag.zigzag2` (`DualCoevZigzag`, checked on
the frames of `locallyFreeData V` via `IsFrameData.expand`); `Zigzag.Z2_map` transports it along the strong monoidal
`g^*`; `Zigzag.lemmaA` (abstract) and `DualZigzag.triangle2` (sections ⇄ morphisms `O_T ⟶ g^*V`) conclude, so no
expansion in the pulled-back basis is needed. -/
theorem AlgebraicGeometry.Scheme.totalSpace.sectionOfFunctionalCore_functionalOfSectionCore
    {X : AlgebraicGeometry.Scheme.{u}} (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType]
    (T : CategoryTheory.Over X)
    (s : (((AlgebraicGeometry.Scheme.Modules.pullback T.hom).obj V).val.obj
      (Opposite.op ⊤) : Type u)) :
    AlgebraicGeometry.Scheme.totalSpace.sectionOfFunctionalCore V T
        (AlgebraicGeometry.Scheme.totalSpace.functionalOfSectionCore V T s) = s := by
  exact AlgebraicGeometry.Scheme.Modules.DualZigzag.triangle2 V T s

/-- **`Sym(V^∨)` is generated in degree one**: two `O_X`-algebra maps `∐_m Sym^m(V^∨) → g_*O_T`
(`IsAlgebraMapToPushforward`) that agree on `symGen ≫ ι_1 : V^∨ → Sym^1 → ∐ Sym^m` are equal.

References: Stacks 01M2 (the symmetric algebra is generated by its degree-one part); 01LQ.

Proof. Write `W = V^∨` (quasi-coherent, `dual_isQuasicoherent_of_locallyFree`, so
`part m = Sym^m W`, `one = symPowπ W 0`, `mul = symPowMul`). By `Sigma.hom_ext` it suffices to show
`ι_m ≫ φ₁ = ι_m ≫ φ₂` for every `m`; since `symPowπ W m : W^{⊗m} → Sym^m W` is an epimorphism
(`symPowπ_epi`) it suffices to show `symPowπ W m ≫ ι_m ≫ φ₁ = symPowπ W m ≫ ι_m ≫ φ₂`. Induction on `m`:
* `m = 0`: `symPowπ W 0 ≫ ι_0 = total.one` up to the unitor, and both `φ_i` send `total.one (r) = r • 1` to
  `g^♯(r) · 1` (unit preservation + `O_X`-linearity of `φ_i`), so they agree.
* `m + 1`: `W^{⊗(m+1)} = W^{⊗m} ⊗ W`, and `symPowπ W (m+1) = (symPowπ W m ⊗ symPowπ W 1') ≫ symPowMul W m 1`
  up to `monoidalPowCat`/unitor (defining property of `symPowMul` via `symPowDesc₂`), so
  `ι_{m+1} ∘ symPowπ_{m+1} (x ⊗ w) = total.mul (ι_m π_m x ⊗ ι_1 π_1 w)` (component formula of `total.mul`).
  Multiplicativity of `φ_i` gives `φ_i(…) = φ_i(ι_m π_m x) · φ_i(ι_1 π_1 w)`; the first factors agree by
  induction, the second by the hypothesis (`ι_1 ∘ π_1 ∘ (λ_ W).inv = symGen ≫ ι_1`, `symGen_heq`).
As formalized: `ι_comp_ext_of_symGen_aux` (§A) follows this induction but stays at the morphism level throughout: the
section-level hypotheses are converted once by `QCAlgebra.mul_comp_eq_of_isAlgebraMap_mul` /
`one_comp_eq_of_isAlgebraMap_one` (`AlgebraMapToPushforwardMorphismLevel`), and the component formula is
`GradedQCAlgebra.total_mul_component` (`GradedAlgebraTotalComponent`). -/
theorem AlgebraicGeometry.Scheme.totalSpace.algebraMapToPushforward_ext_of_symGen
    {X : AlgebraicGeometry.Scheme.{u}} (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType]
    (T : CategoryTheory.Over X)
    (φ₁ φ₂ : (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
        (AlgebraicGeometry.Scheme.Modules.dual V)).total.carrier ⟶
      (AlgebraicGeometry.Scheme.Modules.pushforward T.hom).obj
        (SheafOfModules.unit T.left.ringCatSheaf))
    (h₁ : (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
      (AlgebraicGeometry.Scheme.Modules.dual V)).total.IsAlgebraMapToPushforward T.hom φ₁)
    (h₂ : (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
      (AlgebraicGeometry.Scheme.Modules.dual V)).total.IsAlgebraMapToPushforward T.hom φ₂)
    (h : AlgebraicGeometry.Scheme.Modules.symGen (AlgebraicGeometry.Scheme.Modules.dual V) ≫
        CategoryTheory.Limits.Sigma.ι (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
          (AlgebraicGeometry.Scheme.Modules.dual V)).part 1 ≫ φ₁ =
      AlgebraicGeometry.Scheme.Modules.symGen (AlgebraicGeometry.Scheme.Modules.dual V) ≫
        CategoryTheory.Limits.Sigma.ι (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
          (AlgebraicGeometry.Scheme.Modules.dual V)).part 1 ≫ φ₂) :
    φ₁ = φ₂ := by
  have hq := AlgebraicGeometry.Scheme.Modules.dual_isQuasicoherent_of_locallyFree V
  apply CategoryTheory.Limits.Sigma.hom_ext
  exact AlgebraicGeometry.Scheme.Modules.ι_comp_ext_of_symGen_aux T.hom
    (AlgebraicGeometry.Scheme.Modules.dual V) hq _
    (AlgebraicGeometry.Scheme.Modules.symGradedAlgebra_of_isQuasicoherent _ hq) _
    (AlgebraicGeometry.Scheme.Modules.symGen_heq _ hq) φ₁ φ₂
    (AlgebraicGeometry.Scheme.QCAlgebra.mul_comp_eq_of_isAlgebraMap_mul _ _ _ h₁.1)
    (AlgebraicGeometry.Scheme.QCAlgebra.mul_comp_eq_of_isAlgebraMap_mul _ _ _ h₂.1)
    (AlgebraicGeometry.Scheme.QCAlgebra.one_comp_eq_of_isAlgebraMap_one _ _ φ₁ φ₂ h₁.2 h₂.2) h

/-- Both inverse laws, assembled from `relativeSpecHomEquiv` (Stacks 01LQ), the degree-one component
formula `symGen_ι_algebraMapOfFunctionalCore`, `algebraMapToPushforward_ext_of_symGen` and the two
triangle identities. -/
theorem AlgebraicGeometry.Scheme.totalSpace.sectionConstructionsCore_inverse
    {X : AlgebraicGeometry.Scheme.{u}} (V : X.Modules) [V.IsLocallyFree] [V.IsFiniteType]
    (T : CategoryTheory.Over X) :
    Function.LeftInverse
        (AlgebraicGeometry.Scheme.totalSpace.ofSectionCore V T)
        (AlgebraicGeometry.Scheme.totalSpace.toSectionCore V T) ∧
      Function.RightInverse
        (AlgebraicGeometry.Scheme.totalSpace.ofSectionCore V T)
        (AlgebraicGeometry.Scheme.totalSpace.toSectionCore V T) := by
  let S := AlgebraicGeometry.Scheme.Modules.symGradedAlgebra
    (AlgebraicGeometry.Scheme.Modules.dual V)
  constructor
  · intro h
    have e1 : AlgebraicGeometry.Scheme.totalSpace.functionalOfSectionCore V T
          (AlgebraicGeometry.Scheme.totalSpace.toSectionCore V T h) =
        AlgebraicGeometry.Scheme.totalSpace.functionalOfHomCore V T h :=
      AlgebraicGeometry.Scheme.totalSpace.functionalOfSectionCore_sectionOfFunctionalCore V T
        (AlgebraicGeometry.Scheme.totalSpace.functionalOfHomCore V T h)
    have e2 : AlgebraicGeometry.Scheme.totalSpace.algebraMapOfFunctionalCore V T
          (AlgebraicGeometry.Scheme.totalSpace.functionalOfHomCore V T h) =
        AlgebraicGeometry.Scheme.relativeSpec.toAlgebraMap S.total T h := by
      apply AlgebraicGeometry.Scheme.totalSpace.algebraMapToPushforward_ext_of_symGen V T _ _
        (AlgebraicGeometry.Scheme.totalSpace.algebraMapOfFunctionalCore_preservesOperations V T _)
        (AlgebraicGeometry.Scheme.relativeSpecHomEquiv S.total T h).2
      rw [AlgebraicGeometry.Scheme.totalSpace.symGen_ι_algebraMapOfFunctionalCore]
      exact Equiv.apply_symm_apply _ _
    have e4 : (⟨AlgebraicGeometry.Scheme.totalSpace.algebraMapOfFunctionalCore V T
          (AlgebraicGeometry.Scheme.totalSpace.functionalOfSectionCore V T
            (AlgebraicGeometry.Scheme.totalSpace.toSectionCore V T h)),
          AlgebraicGeometry.Scheme.totalSpace.algebraMapOfFunctionalCore_preservesOperations V T _⟩ :
          {φ // S.total.IsAlgebraMapToPushforward T.hom φ}) =
        AlgebraicGeometry.Scheme.relativeSpecHomEquiv S.total T h := by
      apply Subtype.ext
      show AlgebraicGeometry.Scheme.totalSpace.algebraMapOfFunctionalCore V T
          (AlgebraicGeometry.Scheme.totalSpace.functionalOfSectionCore V T
            (AlgebraicGeometry.Scheme.totalSpace.toSectionCore V T h)) =
        AlgebraicGeometry.Scheme.relativeSpec.toAlgebraMap S.total T h
      rw [e1, e2]
    show (AlgebraicGeometry.Scheme.relativeSpecHomEquiv S.total T).symm
      ⟨AlgebraicGeometry.Scheme.totalSpace.algebraMapOfFunctionalCore V T
          (AlgebraicGeometry.Scheme.totalSpace.functionalOfSectionCore V T
            (AlgebraicGeometry.Scheme.totalSpace.toSectionCore V T h)),
        AlgebraicGeometry.Scheme.totalSpace.algebraMapOfFunctionalCore_preservesOperations V T _⟩ = h
    rw [e4]
    exact (AlgebraicGeometry.Scheme.relativeSpecHomEquiv S.total T).symm_apply_apply h
  · intro s
    have e3 : AlgebraicGeometry.Scheme.totalSpace.functionalOfHomCore V T
          (AlgebraicGeometry.Scheme.totalSpace.ofSectionCore V T s) =
        AlgebraicGeometry.Scheme.totalSpace.functionalOfSectionCore V T s := by
      have hr : AlgebraicGeometry.Scheme.relativeSpec.toAlgebraMap S.total T
            (AlgebraicGeometry.Scheme.totalSpace.ofSectionCore V T s) =
          AlgebraicGeometry.Scheme.totalSpace.algebraMapOfFunctionalCore V T
            (AlgebraicGeometry.Scheme.totalSpace.functionalOfSectionCore V T s) :=
        congrArg Subtype.val ((AlgebraicGeometry.Scheme.relativeSpecHomEquiv S.total T).apply_symm_apply
          ⟨AlgebraicGeometry.Scheme.totalSpace.algebraMapOfFunctionalCore V T
            (AlgebraicGeometry.Scheme.totalSpace.functionalOfSectionCore V T s),
           AlgebraicGeometry.Scheme.totalSpace.algebraMapOfFunctionalCore_preservesOperations V T _⟩)
      show ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction T.hom).homEquiv _ _).symm
        (AlgebraicGeometry.Scheme.Modules.symGen (AlgebraicGeometry.Scheme.Modules.dual V) ≫
          CategoryTheory.Limits.Sigma.ι S.part 1 ≫
          AlgebraicGeometry.Scheme.relativeSpec.toAlgebraMap S.total T
            (AlgebraicGeometry.Scheme.totalSpace.ofSectionCore V T s)) = _
      rw [hr, AlgebraicGeometry.Scheme.totalSpace.symGen_ι_algebraMapOfFunctionalCore,
        Equiv.symm_apply_apply]
    rw [AlgebraicGeometry.Scheme.totalSpace.toSectionCore_eq, e3]
    exact AlgebraicGeometry.Scheme.totalSpace.sectionOfFunctionalCore_functionalOfSectionCore V T s

end
