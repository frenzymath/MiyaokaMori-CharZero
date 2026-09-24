import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetGrading
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetRescalingAction
import MiyaokaMori.Paper.S2WeightedJets.Jets.JetRescalingActionAffineLine
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.PushforwardComorphism
import MiyaokaMori.Paper.S2WeightedJets.Jets.RelativeJetFunctor
import MiyaokaMori.Paper.S2WeightedJets.Jets.RelativeJetRepresentableBy

/-! # The degree-zero part of the jet grading is `O_C`

The degree-zero part of the jet grading is `O_C`: the unit map `O_C → S_0` is an isomorphism (a consequence of the
constant term being fixed to `s`; §2 of the paper, `S_0 = O_C`).

## Route

`(jetGradedAlgebra Z s hs r).1.one` is, by definition, the kernel lift
`kernel.lift φ₀ π^♯ _ : O_C ⟶ S_0 = ker φ₀` of the unit `π^♯ : O_C → π_*O_J` into the weight-`0`
kernel of the defect `φ₀ = act^♯ − pr₂^♯` (`GroupSchemeAction.weightOne`).  It is an isomorphism
because `π^♯` has a retraction `c^♯ : π_*O_J → O_C` coming from the *constant-jet section*
`c : C → J` (the based jet `pr ≫ s` over `(C, 𝟙)`), and

* `π^♯ ≫ c^♯ = (c ≫ π)^♯ = 𝟙` (`jetUnit_comp_constantJetRetraction`, proved here), and
* on `S_0`, `c^♯ ≫ π^♯` is the identity: a weight-`0` function on `J` is the pullback of its
  constant term (`weightZero_constantJet`).

The abstract assembly is `CategoryTheory.Limits.isIso_kernel_lift_of_retraction`, a purely categorical argument.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.style.haveILetI false

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open scoped CategoryTheory.MonoidalCategory

/-- Abstract form: a kernel lift `X → ker φ` of `f : X → Y` is an isomorphism when `f` admits a
retraction `ρ` (`f ≫ ρ = 𝟙`) such that `ρ ≫ f` is the identity on `ker φ`
(`kernel.ι φ ≫ ρ ≫ f = kernel.ι φ`).  The inverse is `kernel.ι φ ≫ ρ`. -/
theorem CategoryTheory.Limits.isIso_kernel_lift_of_retraction {A : Type v} [CategoryTheory.Category.{w} A]
    [CategoryTheory.Limits.HasZeroMorphisms A] {X Y W : A} (φ : Y ⟶ W)
    [CategoryTheory.Limits.HasKernel φ] (f : X ⟶ Y) (hf : f ≫ φ = 0) (ρ : Y ⟶ X)
    (h1 : f ≫ ρ = CategoryTheory.CategoryStruct.id X)
    (h2 : CategoryTheory.Limits.kernel.ι φ ≫ ρ ≫ f = CategoryTheory.Limits.kernel.ι φ) :
    CategoryTheory.IsIso (CategoryTheory.Limits.kernel.lift φ f hf) := by
  refine ⟨CategoryTheory.Limits.kernel.ι φ ≫ ρ, ?_, ?_⟩
  · rw [← CategoryTheory.Category.assoc, CategoryTheory.Limits.kernel.lift_ι, h1]
  · apply (CategoryTheory.cancel_mono (CategoryTheory.Limits.kernel.ι φ)).1
    rw [CategoryTheory.Category.id_comp, CategoryTheory.Category.assoc,
      CategoryTheory.Category.assoc, CategoryTheory.Limits.kernel.lift_ι]
    exact h2

section ConstantJet

variable {k : Type u} [Field k] {C : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (Z : CategoryTheory.Over C)
    [AlgebraicGeometry.IsAffineHom Z.hom]
    (s : C ⟶ Z.left) (hs : s ≫ Z.hom = CategoryTheory.CategoryStruct.id C) (r : ℕ)

omit [AlgebraicGeometry.IsAffineHom Z.hom] in
include hs in
/-- The constant jet `pr ≫ s : C ×_k D_r → Z` is a based jet over `W := (C, 𝟙 C)`
(it lies over `C` by `hs`, and its constant term is `s` by `jetConstantTerm_comp_proj`). -/
theorem constantJet_prop :
    let W : CategoryTheory.Over C := CategoryTheory.Over.mk (CategoryTheory.CategoryStruct.id C)
    letI : W.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
      ⟨W.hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
    (jetThickeningProj (k := k) r W.left ≫ s) ≫ Z.hom =
        jetThickeningProj (k := k) r W.left ≫ W.hom ∧
      jetConstantTerm (k := k) r W.left ≫ (jetThickeningProj (k := k) r W.left ≫ s) =
        W.hom ≫ s := by
  intro W
  letI : W.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨W.hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  constructor
  · rw [CategoryTheory.Category.assoc, hs]
    rfl
  · rw [← CategoryTheory.Category.assoc, jetConstantTerm_comp_proj]
    rfl

/-- The constant-jet section `c : C → J_r^s(Z/C)`: under representability
(`relativeJetScheme.representableBy`) it corresponds to the based jet `pr ≫ s` over `(C, 𝟙 C)`
(§2 of the paper: the jet "`s|_W`", i.e. the `C`-point of `J` given by the constant jet). -/
noncomputable def constantJet : C ⟶ (relativeJetScheme (k := k) Z s hs r).left :=
  ((relativeJetScheme.representableBy (k := k) Z s hs r).homEquiv.symm
    ⟨jetThickeningProj (k := k) r C ≫ s, constantJet_prop (k := k) Z s hs r⟩ :
      CategoryTheory.Over.mk (CategoryTheory.CategoryStruct.id C) ⟶
        relativeJetScheme (k := k) Z s hs r).left

/-- `c` is a section of `π : J → C` (`Over.w`). -/
theorem constantJet_comp_hom :
    constantJet (k := k) Z s hs r ≫ (relativeJetScheme (k := k) Z s hs r).hom =
      CategoryTheory.CategoryStruct.id C :=
  CategoryTheory.Over.w _

/-- `act'` at `λ = 0` is the constant jet: `(0, id) ≫ act' = π ≫ c`.
Proof: by naturality of the representing bijection, compare the based jets `z^*(ρ' ≫ x₀')` and
`π^*(pr ≫ s)`: `(z × 𝟙) ≫ ρ' = ρ'_{z ≫ λ'} ≫ (z × 𝟙)` with `z ≫ λ' = (J ↘ k) ≫ 0`, `ρ'_0 = pr ≫ ct`
(`rescaleByA1_zero`), `(z × 𝟙) ≫ (pr₂' × 𝟙) = 𝟙`, and `ct ≫ x₀ = π ≫ s`
(`jetConstantTerm_comp_universalJet`); on the other side `(π × 𝟙) ≫ pr ≫ s = pr ≫ π ≫ s`. -/
theorem affineLineJet.zeroSection_comp_act :
    affineLineJet.zeroSection (k := k) Z s hs r ≫ affineLineRescalingAct (k := k) Z s hs r =
      (relativeJetScheme (k := k) Z s hs r).hom ≫ constantJet (k := k) Z s hs r := by
  let F := relativeJetFunctor (k := k) Z s hs r
  let J := relativeJetScheme (k := k) Z s hs r
  let e := relativeJetScheme.representableBy (k := k) Z s hs r
  let Cid : CategoryTheory.Over C := CategoryTheory.Over.mk (CategoryTheory.CategoryStruct.id C)
  let W' : CategoryTheory.Over C := affineLineJet (k := k) Z s hs r
  letI : Cid.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨Cid.hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  letI : W'.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨W'.hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  letI : J.left.Over (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨J.hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))⟩
  let y : F.obj (Opposite.op Cid) := ⟨jetThickeningProj (k := k) r C ≫ s, constantJet_prop (k := k) Z s hs r⟩
  let z : J.left ⟶ W'.left := affineLineJet.zeroSection (k := k) Z s hs r
  let snd' : W'.left ⟶ J.left := CategoryTheory.Limits.pullback.snd _ _
  let π : J.left ⟶ Cid.left := J.hom
  let zO : J ⟶ W' := CategoryTheory.Over.homMk z
    ((CategoryTheory.Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ J.hom) (affineLineJet.zeroSection_comp_snd (k := k) Z s hs r)).trans
        (CategoryTheory.Category.id_comp _)))
  let πO : J ⟶ Cid := CategoryTheory.Over.homMk π (CategoryTheory.Category.comp_id _)
  haveI hz : z.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) := ⟨CategoryTheory.Over.w_assoc zO _⟩
  haveI hsnd' : snd'.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨CategoryTheory.Over.w_assoc (CategoryTheory.Over.homMk snd' rfl : W' ⟶ J) _⟩
  haveI hπ : π.IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) := ⟨CategoryTheory.Over.w_assoc πO _⟩
  haveI hzsnd : (z ≫ snd').IsOver (AlgebraicGeometry.Spec (CommRingCat.of k)) :=
    ⟨(CategoryTheory.Category.assoc z snd' _).trans ((congrArg (z ≫ ·) hsnd'.comp_over).trans hz.comp_over)⟩
  have hzs : z ≫ snd' = CategoryTheory.CategoryStruct.id _ := affineLineJet.zeroSection_comp_snd (k := k) Z s hs r
  have hlam : (z ≫ affineLineJet.lam (k := k) Z s hs r) ≫
      (AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k)) ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) =
      (J.left ↘ AlgebraicGeometry.Spec (CommRingCat.of k)) := by
    rw [CategoryTheory.Category.assoc, affineLineJet.lam_over]
    exact hz.comp_over
  have hx : F.map zO.op (affineLineJet.basedJet (k := k) Z s hs r) = F.map πO.op y := by
    apply Subtype.ext
    show jetThickeningMap (k := k) r z ≫ (affineLineJet.rescale (k := k) Z s hs r ≫
        (jetThickeningMap (k := k) r snd' ≫ relativeJetScheme.universalJet (k := k) Z s hs r)) =
      jetThickeningMap (k := k) r π ≫ (jetThickeningProj (k := k) r Cid.left ≫ s)
    have hnat := jetThickening.rescaleByA1_naturality (k := k) r J.left z
      (affineLineJet.lam (k := k) Z s hs r) (affineLineJet.lam_over (k := k) Z s hs r) hlam
    have hzero : jetThickening.rescaleByA1 (k := k) r J.left (z ≫ affineLineJet.lam (k := k) Z s hs r) hlam =
        jetThickeningProj (k := k) r J.left ≫ jetConstantTerm (k := k) r J.left :=
      (jetThickening.rescaleByA1_congr (k := k) r J.left _ (affineLineJet.zeroSection_comp_lam (k := k) Z s hs r) hlam
        (by rw [CategoryTheory.Category.assoc, affineLineZero_comp_structure, CategoryTheory.Category.comp_id]; rfl)).trans
      (jetThickening.rescaleByA1_zero (k := k) r J.left _)
    have hmap : jetThickeningMap (k := k) r z ≫ jetThickeningMap (k := k) r snd' =
        CategoryTheory.CategoryStruct.id _ :=
      (jetThickeningMap_comp (k := k) r z snd').symm.trans
        ((jetThickeningMap_congr (k := k) r J.left (V' := J.left) hzs).trans (jetThickeningMap_id (k := k) r))
    have hu := relativeJetScheme.jetConstantTerm_comp_universalJet (k := k) Z s hs r
    have hproj : jetThickeningMap (k := k) r π ≫ jetThickeningProj (k := k) r Cid.left =
        jetThickeningProj (k := k) r J.left ≫ π := jetThickeningMap_proj (k := k) r π
    refine Eq.trans ?_ (((CategoryTheory.Category.assoc _ _ _).symm.trans
      (congrArg (· ≫ s) hproj)).trans (CategoryTheory.Category.assoc _ _ _)).symm
    exact (CategoryTheory.Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ (jetThickeningMap (k := k) r snd' ≫ relativeJetScheme.universalJet (k := k) Z s hs r)) hnat).trans
      ((congrArg (fun m => (m ≫ jetThickeningMap (k := k) r z) ≫
          (jetThickeningMap (k := k) r snd' ≫ relativeJetScheme.universalJet (k := k) Z s hs r)) hzero).trans
      ((CategoryTheory.Category.assoc _ _ _).trans
      ((congrArg ((jetThickeningProj (k := k) r J.left ≫ jetConstantTerm (k := k) r J.left) ≫ ·)
          (CategoryTheory.Category.assoc _ _ _).symm).trans
      ((congrArg (fun m => (jetThickeningProj (k := k) r J.left ≫ jetConstantTerm (k := k) r J.left) ≫
          (m ≫ relativeJetScheme.universalJet (k := k) Z s hs r)) hmap).trans
      ((congrArg ((jetThickeningProj (k := k) r J.left ≫ jetConstantTerm (k := k) r J.left) ≫ ·)
          (CategoryTheory.Category.id_comp _)).trans
      ((CategoryTheory.Category.assoc _ _ _).trans
      (congrArg (jetThickeningProj (k := k) r J.left ≫ ·) hu))))))))
  show (zO ≫ e.homEquiv.symm (affineLineJet.basedJet (k := k) Z s hs r)).left = (πO ≫ e.homEquiv.symm y).left
  rw [e.comp_homEquiv_symm, e.comp_homEquiv_symm, hx]

/-- `π^♯ : O_C → π_*O_J`, the unit of the jet coordinate algebra.  This is the same morphism as
`(pushforwardStructureSheaf π).one` (definitionally), typed against `pushforward`/`unit` directly
so that the `Scheme.Modules.Hom.app` API applies. -/
noncomputable def jetUnit :
    (SheafOfModules.unit C.ringCatSheaf : C.Modules) ⟶
      (AlgebraicGeometry.Scheme.Modules.pushforward (relativeJetScheme (k := k) Z s hs r).hom).obj
        (SheafOfModules.unit (relativeJetScheme (k := k) Z s hs r).left.ringCatSheaf :
          (relativeJetScheme (k := k) Z s hs r).left.Modules) :=
  SheafOfModules.unitToPushforwardObjUnit (relativeJetScheme (k := k) Z s hs r).hom.toRingCatSheafHom

/-- The retraction `c^♯ : π_*O_J → O_C` induced by the constant-jet section `c`:
`pushforward π` of `O_J → c_*O_C`, then `π_*c_* ≅ (c ≫ π)_* = (𝟙 C)_* ≅ 𝟭`.
On sections over `U` it is `a ↦ c.app (π⁻¹U) a` (up to the identification `(𝟙 C)⁻¹U = U`). -/
noncomputable def constantJetRetraction :
    (AlgebraicGeometry.Scheme.Modules.pushforward (relativeJetScheme (k := k) Z s hs r).hom).obj
        (SheafOfModules.unit (relativeJetScheme (k := k) Z s hs r).left.ringCatSheaf :
          (relativeJetScheme (k := k) Z s hs r).left.Modules) ⟶
      (SheafOfModules.unit C.ringCatSheaf : C.Modules) :=
  (AlgebraicGeometry.Scheme.Modules.pushforward (relativeJetScheme (k := k) Z s hs r).hom).map
      (SheafOfModules.unitToPushforwardObjUnit (constantJet (k := k) Z s hs r).toRingCatSheafHom) ≫
    (AlgebraicGeometry.Scheme.Modules.pushforwardComp (constantJet (k := k) Z s hs r)
      (relativeJetScheme (k := k) Z s hs r).hom).hom.app _ ≫
    (AlgebraicGeometry.Scheme.Modules.pushforwardCongr (constantJet_comp_hom (k := k) Z s hs r)).hom.app _ ≫
    (AlgebraicGeometry.Scheme.Modules.pushforwardId C).hom.app _

/-- `π^♯ ≫ c^♯ = (c ≫ π)^♯ = 𝟙`: the unit `O_C → π_*O_J` followed by the retraction is the
identity.  Proof: on sections over `U`, both sides send `x` to `x`; the left side is
`(c ≫ π).app U x` transported along `(𝟙 C)⁻¹U = (c ≫ π)⁻¹U` (`Scheme.Hom.congr_app`). -/
theorem jetUnit_comp_constantJetRetraction :
    jetUnit (k := k) Z s hs r ≫ constantJetRetraction (k := k) Z s hs r =
      CategoryTheory.CategoryStruct.id _ := by
  refine AlgebraicGeometry.Scheme.Modules.hom_ext _ _ fun U => ?_
  ext x
  show C.presheaf.map (CategoryTheory.eqToHom (by rw [constantJet_comp_hom] :
        (CategoryTheory.CategoryStruct.id C) ⁻¹ᵁ U =
          (constantJet (k := k) Z s hs r ≫ (relativeJetScheme (k := k) Z s hs r).hom) ⁻¹ᵁ U)).op
      ((constantJet (k := k) Z s hs r).app ((relativeJetScheme (k := k) Z s hs r).hom ⁻¹ᵁ U)
        ((relativeJetScheme (k := k) Z s hs r).hom.app U x)) = x
  have hcomp : (constantJet (k := k) Z s hs r).app ((relativeJetScheme (k := k) Z s hs r).hom ⁻¹ᵁ U)
        ((relativeJetScheme (k := k) Z s hs r).hom.app U x) =
      (constantJet (k := k) Z s hs r ≫ (relativeJetScheme (k := k) Z s hs r).hom).app U x := rfl
  rw [hcomp, AlgebraicGeometry.Scheme.Hom.congr_app (constantJet_comp_hom (k := k) Z s hs r) U,
    AlgebraicGeometry.Scheme.Hom.id_app]
  erw [CategoryTheory.Category.id_comp, ← CommRingCat.comp_apply,
    ← CategoryTheory.Functor.map_comp, ← CategoryTheory.op_comp, CategoryTheory.eqToHom_trans,
    CategoryTheory.eqToHom_refl, CategoryTheory.op_id, CategoryTheory.Functor.map_id]
  rfl

/-- `unitMul 1 = 𝟙` (local copy; the same statement is `unitMul_one` in
`PushforwardQcAlgebraMap`, not imported here to avoid the duplicate `unitMul`
of `JetGrading.lean`). -/
theorem JetWeightZero.unitMul_one {X : AlgebraicGeometry.Scheme.{u}} :
    AlgebraicGeometry.Scheme.Modules.unitMul (X := X) (1 : Γ(X, ⊤)) = CategoryTheory.CategoryStruct.id _ := by
  unfold AlgebraicGeometry.Scheme.Modules.unitMul
  rw [Equiv.symm_apply_eq]
  ext U
  rw [SheafOfModules.unitHomEquiv_apply_coe]
  show (X.presheaf.map (CategoryTheory.homOfLE (le_top : U.unop ≤ ⊤)).op).hom 1 = 1
  exact map_one _

/-- The weight-`0` defect is the difference of the two comorphisms `act^♯ − pr₂^♯`
(`λ^0 = 1`, `unitMul 1 = 𝟙`). -/
theorem GroupSchemeAction.weightDefect_zero_eq {S : AlgebraicGeometry.Scheme.{u}}
    [S.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {T : CategoryTheory.Over S} (α : GmActionOver k T) :
    GroupSchemeAction.weightDefect α 0 =
      AlgebraicGeometry.Scheme.Modules.pushforwardUnitMap α.act T.hom
          (CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom
            (T.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) ≫ T.hom) α.act_over -
        AlgebraicGeometry.Scheme.Modules.pushforwardUnitMap
          (CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom
            (T.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))) T.hom _ rfl := by
  have hid : (AlgebraicGeometry.Scheme.Modules.pushforward
        (CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom
          (T.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) ≫ T.hom)).map
        (AlgebraicGeometry.Scheme.Modules.unitMul
          ((CategoryTheory.Limits.pullback.fst ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom
            (T.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).appTop.hom
            ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of (LaurentPolynomial k))).inv.hom
              (LaurentPolynomial.T 1)) ^ 0)) =
      (AlgebraicGeometry.Scheme.Modules.pushforwardCongr (rfl :
        CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom
          (T.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) ≫ T.hom = _)).hom.app
        (SheafOfModules.unit (CategoryTheory.Limits.pullback ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom
          (T.hom ≫ (S ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).ringCatSheaf) := by
    rw [pow_zero, JetWeightZero.unitMul_one]
    exact (CategoryTheory.Functor.map_id _ _).trans
      (AlgebraicGeometry.Scheme.Modules.pushforwardCongr_rfl_hom_app' _ _).symm
  unfold GroupSchemeAction.weightDefect
  dsimp only
  rw [hid]
  rfl

/-- `c^♯ ≫ π^♯` is the comorphism of `π ≫ c : J → J` (over `π`). -/
theorem constantJetRetraction_comp_jetUnit :
    constantJetRetraction (k := k) Z s hs r ≫ jetUnit (k := k) Z s hs r =
      AlgebraicGeometry.Scheme.Modules.pushforwardUnitMap (constantJet (k := k) Z s hs r)
          (relativeJetScheme (k := k) Z s hs r).hom (CategoryTheory.CategoryStruct.id C)
          (constantJet_comp_hom (k := k) Z s hs r) ≫
        AlgebraicGeometry.Scheme.Modules.pushforwardUnitMap (relativeJetScheme (k := k) Z s hs r).hom
          (CategoryTheory.CategoryStruct.id C) (relativeJetScheme (k := k) Z s hs r).hom
          (CategoryTheory.Category.comp_id _) := by
  refine AlgebraicGeometry.Scheme.Modules.hom_ext _ _ fun U => ?_
  ext x
  show ((constantJetRetraction (k := k) Z s hs r ≫ jetUnit (k := k) Z s hs r).app U).hom x =
    ((AlgebraicGeometry.Scheme.Modules.pushforwardUnitMap (relativeJetScheme (k := k) Z s hs r).hom
      (CategoryTheory.CategoryStruct.id C) (relativeJetScheme (k := k) Z s hs r).hom
      (CategoryTheory.Category.comp_id _)).app U).hom
      (((AlgebraicGeometry.Scheme.Modules.pushforwardUnitMap (constantJet (k := k) Z s hs r)
        (relativeJetScheme (k := k) Z s hs r).hom (CategoryTheory.CategoryStruct.id C)
        (constantJet_comp_hom (k := k) Z s hs r)).app U).hom x)
  exact (AlgebraicGeometry.Scheme.Modules.pushforwardUnitMap_app_apply_eq _ _ _ _ _ _ _ HEq.rfl).symm

/-- `j ≫ q' = q`: the inclusion `G_m ×_k J → A¹ ×_k J` is over `C`. -/
theorem affineLineJet.fromGm_comp_q :
    affineLineJet.fromGm (k := k) Z s hs r ≫
        (CategoryTheory.Limits.pullback.snd
          (AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k)) ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
          ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) ≫
          (relativeJetScheme (k := k) Z s hs r).hom) =
      CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom
          ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) ≫
        (relativeJetScheme (k := k) Z s hs r).hom :=
  (CategoryTheory.Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ (relativeJetScheme (k := k) Z s hs r).hom) (affineLineJet.fromGm_comp_snd (k := k) Z s hs r))

/-- `z ≫ q' = π`: the zero section is over `C`. -/
theorem affineLineJet.zeroSection_comp_q :
    affineLineJet.zeroSection (k := k) Z s hs r ≫
        (CategoryTheory.Limits.pullback.snd
          (AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k)) ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
          ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) ≫
          (relativeJetScheme (k := k) Z s hs r).hom) =
      (relativeJetScheme (k := k) Z s hs r).hom :=
  (CategoryTheory.Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ (relativeJetScheme (k := k) Z s hs r).hom)
      (affineLineJet.zeroSection_comp_snd (k := k) Z s hs r)).trans (CategoryTheory.Category.id_comp _))

/-- `j^♯` is injective on sections (`affineLine_fromGm_app_injective` transported along the
identification `q⁻¹U = (j ≫ q')⁻¹U`). -/
theorem affineLineJet.pushforwardUnitMap_fromGm_app_injective (U : C.Opens) :
    Function.Injective
      ((AlgebraicGeometry.Scheme.Modules.pushforwardUnitMap (affineLineJet.fromGm (k := k) Z s hs r) _ _
        (affineLineJet.fromGm_comp_q (k := k) Z s hs r)).app U).hom := by
  intro y₁ y₂ hy
  have e : (CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom
        ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) ≫
        (relativeJetScheme (k := k) Z s hs r).hom) ⁻¹ᵁ U =
      (affineLineJet.fromGm (k := k) Z s hs r ≫
        (CategoryTheory.Limits.pullback.snd
          (AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k)) ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
          ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))) ≫
          (relativeJetScheme (k := k) Z s hs r).hom)) ⁻¹ᵁ U := by
    rw [affineLineJet.fromGm_comp_q]
  have hy' : ((CategoryTheory.Limits.pullback ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom
        ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).presheaf.map
        (CategoryTheory.eqToHom e).op).hom
        (((affineLineJet.fromGm (k := k) Z s hs r).app _).hom y₁) =
      ((CategoryTheory.Limits.pullback ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom
        ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).presheaf.map
        (CategoryTheory.eqToHom e).op).hom
        (((affineLineJet.fromGm (k := k) Z s hs r).app _).hom y₂) := hy
  haveI : CategoryTheory.IsIso (CategoryTheory.eqToHom e).op := (CategoryTheory.eqToIso e).op.isIso_hom
  exact affineLine_fromGm_app_injective
    ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))
    ((relativeJetScheme (k := k) Z s hs r).hom ⁻¹ᵁ U)
    ((CategoryTheory.ConcreteCategory.bijective_of_isIso
      ((CategoryTheory.Limits.pullback ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom
        ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).presheaf.map
        (CategoryTheory.eqToHom e).op)).1 hy')

/-- **Weight-`0` sections are constant.** A weight-`0` section
of `π_*O_J` is the pullback of its constant term: on `S_0 = ker φ₀`, `c^♯ ≫ π^♯` is the identity, i.e.
`kernel.ι φ₀ ≫ c^♯ ≫ π^♯ = kernel.ι φ₀`.

Source: §2 of the paper (replacing `t` by `λt` gives the coordinate algebra a nonnegative grading; `S_m` consists
of functions homogeneous of weight `m` under parameter rescaling, and `S_0 = O_C`). The paper states `S_0 = O_C`
without proof; the argument is: extend the `𝔾_m`-action to `𝔸¹`
(`affineLineRescalingAct`, module `JetRescalingActionAffineLine`), a `G_m`-invariant function is then
`A¹`-invariant because `A[λ] ↪ A[λ^{±1}]` (`affineLine_fromGm_app_injective`), and evaluating the
`A¹`-invariance at `λ = 0` (`affineLineJet.zeroSection_comp_act`: `act' ∘ (0, id) = π ≫ c`) gives
`a = π^♯(c^♯ a)`.

Proof (categorical, in `C.Modules`; `g^♯ := pushforwardUnitMap g`):
1. `kernel.condition` and `weightDefect_zero_eq`: `ι ≫ act^♯ = ι ≫ pr₂^♯`.
2. `act = j ≫ act'`, `pr₂ = j ≫ pr₂'` (`affineLineRescalingAct_restrict`, `fromGm_comp_snd`) and
   functoriality (`pushforwardUnitMap_comp`): `ι ≫ act'^♯ ≫ j^♯ = ι ≫ pr₂'^♯ ≫ j^♯`.
3. `j^♯` is injective on sections (`affineLine_fromGm_app_injective`): `ι ≫ act'^♯ = ι ≫ pr₂'^♯`.
4. Compose with `z^♯` for the zero section `z = (0, id)`: `z ≫ act' = π ≫ c`
   (`zeroSection_comp_act`), `z ≫ pr₂' = 𝟙` (`zeroSection_comp_snd`), so
   `ι ≫ (π ≫ c)^♯ = ι`, and `(π ≫ c)^♯ = c^♯ ≫ π^♯ = constantJetRetraction ≫ jetUnit`
   (`constantJetRetraction_comp_jetUnit`).
Edge cases: `r = 0` (`J = C`, `φ₀ = 0`, `c = 𝟙`, statement `𝟙 ≫ 𝟙 = 𝟙`); `U = ∅`, `C = ∅` (zero rings). -/
theorem weightZero_constantJet :
    CategoryTheory.Limits.kernel.ι
        (GroupSchemeAction.weightDefect (jetRescalingAction (k := k) Z s hs r) 0) ≫
      constantJetRetraction (k := k) Z s hs r ≫ jetUnit (k := k) Z s hs r =
    CategoryTheory.Limits.kernel.ι
      (GroupSchemeAction.weightDefect (jetRescalingAction (k := k) Z s hs r) 0) := by
  -- Step 1
  have hker : CategoryTheory.Limits.kernel.ι (GroupSchemeAction.weightDefect (jetRescalingAction (k := k) Z s hs r) 0) ≫
      (AlgebraicGeometry.Scheme.Modules.pushforwardUnitMap (jetRescalingAction (k := k) Z s hs r).act
          (relativeJetScheme (k := k) Z s hs r).hom _ (jetRescalingAction (k := k) Z s hs r).act_over -
        AlgebraicGeometry.Scheme.Modules.pushforwardUnitMap
          (CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom
            ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))))
          (relativeJetScheme (k := k) Z s hs r).hom _ rfl) = 0 := by
    rw [← GroupSchemeAction.weightDefect_zero_eq]
    exact CategoryTheory.Limits.kernel.condition _
  rw [CategoryTheory.Preadditive.comp_sub, sub_eq_zero] at hker
  -- Step 2
  have hact : AlgebraicGeometry.Scheme.Modules.pushforwardUnitMap (jetRescalingAction (k := k) Z s hs r).act
        (relativeJetScheme (k := k) Z s hs r).hom _ (jetRescalingAction (k := k) Z s hs r).act_over =
      AlgebraicGeometry.Scheme.Modules.pushforwardUnitMap (affineLineRescalingAct (k := k) Z s hs r)
          (relativeJetScheme (k := k) Z s hs r).hom _ (affineLineRescalingAct_over (k := k) Z s hs r) ≫
        AlgebraicGeometry.Scheme.Modules.pushforwardUnitMap (affineLineJet.fromGm (k := k) Z s hs r) _ _
          (affineLineJet.fromGm_comp_q (k := k) Z s hs r) :=
    ((AlgebraicGeometry.Scheme.Modules.pushforwardUnitMap_comp _ _ _ _ _ _ _
        (by rw [affineLineRescalingAct_restrict]; exact (jetRescalingAction (k := k) Z s hs r).act_over)).trans
      (AlgebraicGeometry.Scheme.Modules.pushforwardUnitMap_congr
        (affineLineRescalingAct_restrict (k := k) Z s hs r) _ _ _ _)).symm
  have hpr : AlgebraicGeometry.Scheme.Modules.pushforwardUnitMap
        (CategoryTheory.Limits.pullback.snd ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom
          ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))))
        (relativeJetScheme (k := k) Z s hs r).hom _ rfl =
      AlgebraicGeometry.Scheme.Modules.pushforwardUnitMap
          (CategoryTheory.Limits.pullback.snd
            (AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k)) ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
            ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))))
          (relativeJetScheme (k := k) Z s hs r).hom _ rfl ≫
        AlgebraicGeometry.Scheme.Modules.pushforwardUnitMap (affineLineJet.fromGm (k := k) Z s hs r) _ _
          (affineLineJet.fromGm_comp_q (k := k) Z s hs r) :=
    ((AlgebraicGeometry.Scheme.Modules.pushforwardUnitMap_comp _ _ _ _ _ _ _
        (by rw [affineLineJet.fromGm_comp_snd])).trans
      (AlgebraicGeometry.Scheme.Modules.pushforwardUnitMap_congr
        (affineLineJet.fromGm_comp_snd (k := k) Z s hs r) _ _ _ _)).symm
  rw [hact, hpr] at hker
  -- Step 3: cancel `j^♯` on sections
  have h2 : CategoryTheory.Limits.kernel.ι (GroupSchemeAction.weightDefect (jetRescalingAction (k := k) Z s hs r) 0) ≫
        AlgebraicGeometry.Scheme.Modules.pushforwardUnitMap (affineLineRescalingAct (k := k) Z s hs r)
          (relativeJetScheme (k := k) Z s hs r).hom _ (affineLineRescalingAct_over (k := k) Z s hs r) =
      CategoryTheory.Limits.kernel.ι (GroupSchemeAction.weightDefect (jetRescalingAction (k := k) Z s hs r) 0) ≫
        AlgebraicGeometry.Scheme.Modules.pushforwardUnitMap
          (CategoryTheory.Limits.pullback.snd
            (AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k)) ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
            ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))))
          (relativeJetScheme (k := k) Z s hs r).hom _ rfl := by
    refine AlgebraicGeometry.Scheme.Modules.hom_ext _ _ fun U => ?_
    ext x
    have hx := congrArg (fun φ : CategoryTheory.Limits.kernel (GroupSchemeAction.weightDefect (jetRescalingAction (k := k) Z s hs r) 0) ⟶
        (AlgebraicGeometry.Scheme.Modules.pushforward _).obj
          (SheafOfModules.unit (CategoryTheory.Limits.pullback ((Gm k).asOver (AlgebraicGeometry.Spec (CommRingCat.of k))).hom
            ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).ringCatSheaf) =>
        (φ.app U).hom x) hker
    have hx' : ((AlgebraicGeometry.Scheme.Modules.pushforwardUnitMap (affineLineJet.fromGm (k := k) Z s hs r) _ _
          (affineLineJet.fromGm_comp_q (k := k) Z s hs r)).app U).hom
          (((CategoryTheory.Limits.kernel.ι (GroupSchemeAction.weightDefect (jetRescalingAction (k := k) Z s hs r) 0) ≫
            AlgebraicGeometry.Scheme.Modules.pushforwardUnitMap (affineLineRescalingAct (k := k) Z s hs r)
              (relativeJetScheme (k := k) Z s hs r).hom _ (affineLineRescalingAct_over (k := k) Z s hs r)).app U).hom x) =
        ((AlgebraicGeometry.Scheme.Modules.pushforwardUnitMap (affineLineJet.fromGm (k := k) Z s hs r) _ _
          (affineLineJet.fromGm_comp_q (k := k) Z s hs r)).app U).hom
          (((CategoryTheory.Limits.kernel.ι (GroupSchemeAction.weightDefect (jetRescalingAction (k := k) Z s hs r) 0) ≫
            AlgebraicGeometry.Scheme.Modules.pushforwardUnitMap
              (CategoryTheory.Limits.pullback.snd
                (AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k)) ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
                ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))))
              (relativeJetScheme (k := k) Z s hs r).hom _ rfl).app U).hom x) := hx
    exact affineLineJet.pushforwardUnitMap_fromGm_app_injective (k := k) Z s hs r U hx'
  -- Step 4: evaluate at `λ = 0`
  have hc : ((relativeJetScheme (k := k) Z s hs r).hom ≫ constantJet (k := k) Z s hs r) ≫
      (relativeJetScheme (k := k) Z s hs r).hom = (relativeJetScheme (k := k) Z s hs r).hom := by
    rw [CategoryTheory.Category.assoc, constantJet_comp_hom, CategoryTheory.Category.comp_id]
  have h' : (affineLineJet.zeroSection (k := k) Z s hs r ≫ affineLineRescalingAct (k := k) Z s hs r) ≫
      (relativeJetScheme (k := k) Z s hs r).hom = (relativeJetScheme (k := k) Z s hs r).hom := by
    rw [affineLineJet.zeroSection_comp_act]; exact hc
  have h'' : (affineLineJet.zeroSection (k := k) Z s hs r ≫
      CategoryTheory.Limits.pullback.snd
        (AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k)) ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
        ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))) ≫
      (relativeJetScheme (k := k) Z s hs r).hom = (relativeJetScheme (k := k) Z s hs r).hom := by
    rw [affineLineJet.zeroSection_comp_snd, CategoryTheory.Category.id_comp]
  have e1 : AlgebraicGeometry.Scheme.Modules.pushforwardUnitMap (affineLineRescalingAct (k := k) Z s hs r)
        (relativeJetScheme (k := k) Z s hs r).hom _ (affineLineRescalingAct_over (k := k) Z s hs r) ≫
      AlgebraicGeometry.Scheme.Modules.pushforwardUnitMap (affineLineJet.zeroSection (k := k) Z s hs r) _ _
        (affineLineJet.zeroSection_comp_q (k := k) Z s hs r) =
      AlgebraicGeometry.Scheme.Modules.pushforwardUnitMap
        ((relativeJetScheme (k := k) Z s hs r).hom ≫ constantJet (k := k) Z s hs r)
        (relativeJetScheme (k := k) Z s hs r).hom (relativeJetScheme (k := k) Z s hs r).hom hc :=
    (AlgebraicGeometry.Scheme.Modules.pushforwardUnitMap_comp _ _ _ _ _ _ _ h').trans
      (AlgebraicGeometry.Scheme.Modules.pushforwardUnitMap_congr (affineLineJet.zeroSection_comp_act (k := k) Z s hs r) _ _ h' hc)
  have e2 : AlgebraicGeometry.Scheme.Modules.pushforwardUnitMap
        (CategoryTheory.Limits.pullback.snd
          (AlgebraicGeometry.Spec (CommRingCat.of (Polynomial k)) ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
          ((relativeJetScheme (k := k) Z s hs r).hom ≫ (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))))
        (relativeJetScheme (k := k) Z s hs r).hom _ rfl ≫
      AlgebraicGeometry.Scheme.Modules.pushforwardUnitMap (affineLineJet.zeroSection (k := k) Z s hs r) _ _
        (affineLineJet.zeroSection_comp_q (k := k) Z s hs r) = CategoryTheory.CategoryStruct.id _ :=
    (AlgebraicGeometry.Scheme.Modules.pushforwardUnitMap_comp _ _ _ _ _ _ _ h'').trans
      ((AlgebraicGeometry.Scheme.Modules.pushforwardUnitMap_congr (affineLineJet.zeroSection_comp_snd (k := k) Z s hs r) _ _ h''
        (CategoryTheory.Category.id_comp _)).trans
        (AlgebraicGeometry.Scheme.Modules.pushforwardUnitMap_id (relativeJetScheme (k := k) Z s hs r).hom))
  have e3 : AlgebraicGeometry.Scheme.Modules.pushforwardUnitMap
        ((relativeJetScheme (k := k) Z s hs r).hom ≫ constantJet (k := k) Z s hs r)
        (relativeJetScheme (k := k) Z s hs r).hom (relativeJetScheme (k := k) Z s hs r).hom hc =
      constantJetRetraction (k := k) Z s hs r ≫ jetUnit (k := k) Z s hs r :=
    (AlgebraicGeometry.Scheme.Modules.pushforwardUnitMap_comp (relativeJetScheme (k := k) Z s hs r).hom
      (constantJet (k := k) Z s hs r) (relativeJetScheme (k := k) Z s hs r).hom (CategoryTheory.CategoryStruct.id C)
      (constantJet_comp_hom (k := k) Z s hs r) (relativeJetScheme (k := k) Z s hs r).hom
      (CategoryTheory.Category.comp_id _) hc).symm.trans (constantJetRetraction_comp_jetUnit (k := k) Z s hs r).symm
  have h3 := congrArg (· ≫ AlgebraicGeometry.Scheme.Modules.pushforwardUnitMap (affineLineJet.zeroSection (k := k) Z s hs r) _ _
    (affineLineJet.zeroSection_comp_q (k := k) Z s hs r)) h2
  exact (congrArg (CategoryTheory.Limits.kernel.ι (GroupSchemeAction.weightDefect (jetRescalingAction (k := k) Z s hs r) 0) ≫ ·)
      e3.symm).trans
    ((congrArg (CategoryTheory.Limits.kernel.ι (GroupSchemeAction.weightDefect (jetRescalingAction (k := k) Z s hs r) 0) ≫ ·)
      e1.symm).trans
    ((CategoryTheory.Category.assoc _ _ _).symm.trans
    (h3.trans
    ((CategoryTheory.Category.assoc _ _ _).trans
    ((congrArg (CategoryTheory.Limits.kernel.ι (GroupSchemeAction.weightDefect (jetRescalingAction (k := k) Z s hs r) 0) ≫ ·)
      e2).trans
    (CategoryTheory.Category.comp_id _))))))

end ConstantJet

theorem jetGraded_one_isIso {k : Type u} [Field k] {C : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (Z : CategoryTheory.Over C)
    [AlgebraicGeometry.IsAffineHom Z.hom]
    (s : C ⟶ Z.left) (hs : s ≫ Z.hom = CategoryTheory.CategoryStruct.id C) (r : ℕ) :
    CategoryTheory.IsIso (jetGradedAlgebra (k := k) Z s hs r).1.one :=
  CategoryTheory.Limits.isIso_kernel_lift_of_retraction
    (GroupSchemeAction.weightDefect (jetRescalingAction (k := k) Z s hs r) 0)
    (AlgebraicGeometry.Scheme.QCAlgebra.pushforwardStructureSheaf
      (relativeJetScheme (k := k) Z s hs r).hom).one
    (GroupSchemeAction.weightPart_one_condition (jetRescalingAction (k := k) Z s hs r))
    (constantJetRetraction (k := k) Z s hs r)
    (jetUnit_comp_constantJetRetraction (k := k) Z s hs r)
    (weightZero_constantJet (k := k) Z s hs r)

end
