import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.TwistPullbackPowLocal
import MiyaokaMori.AlgebraicGeometry.Proj.Twist.RelativeProjEvaluationEpi
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.DualFrameOldSections
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.DualSheafOld
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.FrameLocus
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.DualCoevZigzag
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.DualEvSections
import MiyaokaMori.AlgebraicGeometry.Modules.NonvanishingLocusTensorSection
import MiyaokaMori.Paper.S3PositiveLine.Realization.ProjectivizationOfNowhereZeroTuple
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.TensorSectionsBilinear
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.Stacks01ct

/-! # Restriction of a split weighted coordinate to a frame open: the variable-level core

**Local form of a "coordinate" `(ev_q ∘ π^*ι ⊗ id)(π^* coev_Q)` on a frame open.** For a graded quasi-coherent
algebra `S` on `X` with relative Proj `π : Proj_X S → X`, a line bundle `Q` on `X`, and any `ι : Q^∨ ⟶ S_q`, the global
section `x := Φ (pullbackTensorIso.hom (π^* coev_Q)) ∈ Γ(Proj_X S, O(q) ⊗ π^*Q)` with `Φ = τ ≫ (φ ▷ π^*Q) ≫ τ⁻¹`,
`φ = π^*ι ≫ ev_q` (exactly the shape of `splitWeightedCoord`) restricts on `π⁻¹V`
(`V` affine, `ε` a frame of `Q` on `V`) to the pure tensor `evaluationLocal S q V (ι ε^∨) ⊗ η(ε)`, where
`ε^∨ = IsFrame.dualFrameSection` is the dual frame and `η = unitSec` the adjunction unit.

The concrete statement for `splitWeightedCoord` (`splitWeightedCoord_res_eq_moduleTensorSection_of_frame`, module
`CoordinatesNotAllVanish_LocalGenerators`) is this lemma instantiated at `ι = splitCoordIncl F i q hq` (`exact`;
`splitCoordIncl` is literally the `let ι` of `splitWeightedCoord`).

**Private copies.** `coev|_V = ε^∨ ⊗ ε` is `IsFrame.res_coevSection` (module
`FrameCoordinateMonomialFrameTautological`, with `IsFrame.localDual`, `dualFrameSection`,
`dualEv_dualFrameSection`, `dualFrameSection_isFrame`) and uses `IsFrame.moduleTensorSection`
(`FrameCoordinateMonomialFrameCoefficient`). Importing either module here would add several hundred modules to the
import closure of the coordinate lemmas (through `IsLineBundleZpow` resp. `JetWeightComponentEqCoefficient` →
`GenericallyScalarOfCoefficientsZero`), so the five declarations are copied
verbatim as `private` declarations (`isFrame_moduleTensorSection_cf`, `localDualCf`, `dualFrameSecCf`,
`dualEv_dualFrameSecCf`, `dualFrameSecCf_isFrame`, `res_coevSection_cf`); `dualFrameSecCf hε` is definitionally
`hε.dualFrameOld` (both are the sheafification unit of the dual presheaf applied to the coordinate functionals
`hε.coordEquiv`), which is why `res_coevSection_cf` can be used with `dualFrameOld` in the statement below.

Route (all steps are library facts): restriction commutes with `Hom.app` (`Hom.app_res`) and with `η` (`unitSec_res`);
`coev_Q|_V = ε^∨ ⊗ ε` (`IsFrame.res_coevSection`, module `…FrameCoordinateMonomialFrameTautological`);
`pullbackTensorIso.hom (η(a ⊗ b)) = η a ⊗ η b` (inverse of `pullbackTensorIso_inv_app_moduleTensorSection_unitSec`);
`Φ` acts on the first factor of a pure tensor (`tensorIsoTensorObj_hom_app_moduleTensorSection_tppl`,
`whiskerRight_app_tensorSections_tppl`, `tensorIsoTensorObj_inv_app_tensorSections`); `π^*ι (η a) = η (ι a)`
(`unitSec_map`) and `ev_q (η b) = evaluationLocal S q V b` (`evaluation_app_unit`).

Source: the proof of Proposition 2.4 of the paper (coordinate-divisor calculation); Stacks 01CD.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
open scoped CategoryTheory.MonoidalCategory

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- **The tensor product of two frames is a frame** (private copy of `IsFrame.moduleTensorSection`, module `…FrameCoordinateMonomialFrameCoefficient`, whose import closure is 300 modules larger): `a ⊗ b` is a frame of `A ⊗ B` on `W`. -/
private theorem isFrame_moduleTensorSection_cf {A B : X.Modules} [A.IsLineBundle] [B.IsLineBundle] {W : X.Opens}
    {a : Γ(A, W)} {b : Γ(B, W)} (ha : IsFrame A W a) (hb : IsFrame B W b) :
    IsFrame (AlgebraicGeometry.Scheme.Modules.tensor A B) W (AlgebraicGeometry.Scheme.Modules.moduleTensorSection a b) := by
  let T : X.Modules := AlgebraicGeometry.Scheme.Modules.tensor A B
  have hT : T.IsLineBundle := SheafOfModules.IsLineBundle.tensor A B
  let s : Γ(T, W) := AlgebraicGeometry.Scheme.Modules.moduleTensorSection a b
  have key : ∀ x : X, x ∈ W → ∃ V : X.Opens, ∃ hVW : V ≤ W, x ∈ V ∧ IsFrame T V (T.res hVW s) := by
    intro x hx
    obtain ⟨W₁, hxW₁, e, hf⟩ := exists_frame T x
    have h₂W : W ⊓ W₁ ≤ W := inf_le_left
    have h₂₁ : W ⊓ W₁ ≤ W₁ := inf_le_right
    have hx₂ : x ∈ W ⊓ W₁ := ⟨hx, hxW₁⟩
    have hf₂ : IsFrame T (W ⊓ W₁) (T.res h₂₁ e) := hf.restrict h₂₁
    let f : Γ(X, W ⊓ W₁) := hf₂.coord le_rfl (T.res h₂W s)
    -- `s|_{W₂} = f • e|_{W₂}`
    have hse : T.res h₂W s = f • T.res h₂₁ e := by
      have := hf₂.coord_smul_frame le_rfl (T.res h₂W s)
      rw [res_self] at this
      exact this.symm
    -- `s|_{W₂}` is the tensor of the restricted frames
    have hs₂ : T.res h₂W s = AlgebraicGeometry.Scheme.Modules.moduleTensorSection (A.res h₂W a) (B.res h₂W b) :=
      AlgebraicGeometry.Scheme.Modules.moduleTensorSection_restrict (homOfLE h₂W) a b
    -- the germ of `f` at `x` is a unit
    have hunit : IsUnit (X.presheaf.germ (W ⊓ W₁) x hx₂ f) := by
      have hΘ := (ha.restrict h₂W).tensorStalkEquivOfFrames_germ_frame (hb.restrict h₂W) hx₂
      have h1 : T.presheaf.germ (W ⊓ W₁) x hx₂
          (AlgebraicGeometry.Scheme.Modules.moduleTensorSection (A.res h₂W a) (B.res h₂W b)) =
          X.presheaf.germ (W ⊓ W₁) x hx₂ f • T.presheaf.germ (W ⊓ W₁) x hx₂ (T.res h₂₁ e) := by
        rw [← hs₂, hse]
        exact germ_smul' T hx₂ f (T.res h₂₁ e)
      rw [h1, LinearEquiv.map_smul, smul_eq_mul] at hΘ
      exact IsUnit.of_mul_eq_one _ hΘ
    have hmem : x ∈ X.basicOpen f := (X.mem_basicOpen f x hx₂).mpr hunit
    have hle : X.basicOpen f ≤ W ⊓ W₁ := X.basicOpen_le f
    refine ⟨X.basicOpen f, hle.trans h₂W, hmem, ?_⟩
    have hcoord : IsFrame.coord (hf₂.restrict hle) le_rfl (T.res (hle.trans h₂W) s) =
        X.presheaf.map (homOfLE hle).op f := by
      refine IsFrame.coord_unique (hf₂.restrict hle) le_rfl _ _ ?_
      have h1 := congrArg (T.res hle) (hf₂.coord_smul_frame le_rfl (T.res h₂W s))
      have h2 : T.res hle (f • T.res le_rfl (T.res h₂₁ e)) =
          X.presheaf.map (homOfLE hle).op f • T.res le_rfl (T.res hle (T.res h₂₁ e)) := by
        rw [T.res_smul, T.res_self, T.res_self]
      have h3 : T.res hle (T.res h₂W s) = T.res (hle.trans h₂W) s := T.res_res hle h₂W s
      exact h2.symm.trans (h1.trans h3)
    have hu : IsUnit (IsFrame.coord (hf₂.restrict hle) le_rfl (T.res (hle.trans h₂W) s)) := by
      rw [hcoord]
      exact X.toRingedSpace.isUnit_res_basicOpen f
    exact IsFrame.of_isUnit_coord (hf₂.restrict hle) hu
  choose! V hVW hxV hfV using key
  refine IsFrame.of_iSup (ι := (W : Set X)) (fun p => V p.1) (fun p => hVW p.1 p.2) ?_ ?_
  · intro p hp
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨p, hp⟩, hxV p hp⟩
  · intro p
    exact hfV p.1 p.2

/-- A morphism of sheaves of modules commutes with restriction (element form; private copy). -/
private theorem app_res_tf {M N : X.Modules} (φ : M ⟶ N) {W W' : X.Opens} (h : W' ≤ W) (x : Γ(M, W)) :
    φ.app W' (M.res h x) = N.res h (φ.app W x) :=
  ConcreteCategory.congr_hom (φ.mapPresheaf.naturality (homOfLE h).op) x

/-- The compatible family of local functionals `m ↦ coord_ε(m)` attached to a frame `ε` of `M` on `V`
(an element of the local dual `LocalDualSections X M V`). -/
private def localDualCf {M : X.Modules} {V : X.Opens} {ε : Γ(M, V)} (hε : IsFrame M V ε) :
    Frame.LH M V :=
  ⟨fun W => (hε.coordEquiv (leOfHom W.hom)).toLinearMap, fun W W' i x => by
    have h := hε.coord_map (leOfHom i.left) (leOfHom W'.hom) x
    have hi : i.left = homOfLE (leOfHom i.left) := Subsingleton.elim _ _
    rw [hi]
    exact h⟩

private theorem localDualCf_apply {M : X.Modules} {V : X.Opens} {ε : Γ(M, V)} (hε : IsFrame M V ε)
    (W : CategoryTheory.Over V) (x : Γ(M, W.left)) :
    (localDualCf hε).1 W x = hε.coord (leOfHom W.hom) x := rfl

/-- The dual frame `ε^∨ := dualUnit (coord_ε) ∈ Γ(V, M^∨)`. -/
private def dualFrameSecCf {M : X.Modules} {V : X.Opens} {ε : Γ(M, V)} (hε : IsFrame M V ε) :
    Γ(AlgebraicGeometry.Scheme.Modules.dual M, V) :=
  Frame.dualUnit M V (localDualCf hε)

/-- **The pairing of the dual frame with the frame is `1`**, on every `W' ≤ V`:
`ev(ε^∨|_{W'} ⊗ ε|_{W'}) = 1` (`dualUnit_res`, `dualEv_app_tensorSections_dualUnit`, `coord_frame`). -/
private theorem dualEv_dualFrameSecCf {M : X.Modules} {V : X.Opens} {ε : Γ(M, V)} (hε : IsFrame M V ε)
    {W' : X.Opens} (h : W' ≤ V) :
    (show Γ(X, W') from (dualEv M).app W'
      (AlgebraicGeometry.Scheme.Modules.tensorSections (AlgebraicGeometry.Scheme.Modules.dual M) M W'
        ((AlgebraicGeometry.Scheme.Modules.dual M).res h (dualFrameSecCf hε)) (M.res h ε))) = 1 := by
  have h1 : (AlgebraicGeometry.Scheme.Modules.dual M).res h (dualFrameSecCf hε) =
      Frame.dualUnit M W' (AlgebraicGeometry.Scheme.Modules.localDualRestrict M (homOfLE h) (localDualCf hε)) :=
    Frame.dualUnit_res M (homOfLE h) (localDualCf hε)
  rw [h1]
  refine (DualZigzag.dualEv_app_tensorSections_dualUnit M W' _ (M.res h ε)).trans ?_
  exact hε.coord_frame h

/-- **The dual frame is a frame of `M^∨`** (`M` a line bundle): locally `ε^∨ = f • g` for a frame `g` of `M^∨`,
and `f · ev(g ⊗ ε) = ev(ε^∨ ⊗ ε) = 1`, so `f` is a unit (`IsFrame.of_isUnit_coord`); glue (`IsFrame.of_iSup`). -/
private theorem dualFrameSecCf_isFrame {M : X.Modules} [M.IsLineBundle] {V : X.Opens} {ε : Γ(M, V)}
    (hε : IsFrame M V ε) :
    IsFrame (AlgebraicGeometry.Scheme.Modules.dual M) V (dualFrameSecCf hε) := by
  let D := AlgebraicGeometry.Scheme.Modules.dual M
  have hD : D.IsLineBundle := moduleSheafDual_isLineBundle M
  let t : Γ(D, V) := (dualFrameSecCf hε)
  have key : ∀ x : X, x ∈ V → ∃ V' : X.Opens, ∃ hV' : V' ≤ V, x ∈ V' ∧ IsFrame D V' (D.res hV' t) := by
    intro x hx
    obtain ⟨W₁, hxW₁, g, hg⟩ := exists_frame D x
    have h₂V : V ⊓ W₁ ≤ V := inf_le_left
    have h₂₁ : V ⊓ W₁ ≤ W₁ := inf_le_right
    refine ⟨V ⊓ W₁, h₂V, ⟨hx, hxW₁⟩, ?_⟩
    have hg₂ : IsFrame D (V ⊓ W₁) (D.res h₂₁ g) := hg.restrict h₂₁
    let f : Γ(X, V ⊓ W₁) := hg₂.coord le_rfl (D.res h₂V t)
    have hft : D.res h₂V t = f • D.res h₂₁ g := by
      have := hg₂.coord_smul_frame le_rfl (D.res h₂V t)
      rw [res_self] at this
      exact this.symm
    have hpair := (dualEv_dualFrameSecCf hε h₂V)
    let z : Γ(D ⊗ M, V ⊓ W₁) := AlgebraicGeometry.Scheme.Modules.tensorSections D M (V ⊓ W₁) (D.res h₂₁ g) (M.res h₂V ε)
    have h2 : AlgebraicGeometry.Scheme.Modules.tensorSections D M (V ⊓ W₁) (D.res h₂V t) (M.res h₂V ε) = f • z := by
      rw [hft]
      exact tensorSections_smul_left D M (V ⊓ W₁) f (D.res h₂₁ g) (M.res h₂V ε) z rfl
    have h3 : (show Γ(X, V ⊓ W₁) from (dualEv M).app (V ⊓ W₁) (f • z)) =
        f * (show Γ(X, V ⊓ W₁) from (dualEv M).app (V ⊓ W₁) z) :=
      Hom.app_smul (dualEv M) f z
    have hu : IsUnit f := by
      refine IsUnit.of_mul_eq_one _ (h3.symm.trans ?_)
      rw [← h2]
      exact hpair
    exact IsFrame.of_isUnit_coord hg₂ hu
  choose! V' hV' hxV' hfr using key
  refine IsFrame.of_iSup (ι := (V : Set X)) (fun q => V' q.1) (fun q => hV' q.1 q.2) ?_ ?_
  · intro q hq
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨q, hq⟩, hxV' q hq⟩
  · intro q
    exact hfr q.1 q.2

/-- Right whiskering on a pure tensor (private copy). -/
private theorem whiskerRight_app_tensorSections_tf {A A' : X.Modules} (f : A ⟶ A') (B : X.Modules) (U : X.Opens)
    (a : Γ(A, U)) (b : Γ(B, U)) :
    (f ▷ B).app U (AlgebraicGeometry.Scheme.Modules.tensorSections A B U a b) = AlgebraicGeometry.Scheme.Modules.tensorSections A' B U (f.app U a) b := by
  rw [← CategoryTheory.MonoidalCategory.tensorHom_id]
  exact tensorHom_tensorSections f (𝟙 B) U a b

/-- The second zigzag identity on a section: `tail2(coev ⊗ v) = v` (`DualZigzag.zigzag2`, element form). -/
private theorem zigzag2_app (M : X.Modules) [M.IsLocallyFree] [M.IsFiniteType] (V : X.Opens) (v : Γ(M, V)) :
    (DualZigzag.tail2 M).app V ((DualZigzag.coevHom M ▷ M).app V ((λ_ M).inv.app V v)) = v := by
  have hZ := DualZigzag.zigzag2 M
  unfold CategoryTheory.MonoidalCategory.Zigzag.Z2 at hZ
  have h0 := congrArg (fun φ => Modules.Hom.app φ V) hZ
  have h1 := ConcreteCategory.congr_hom h0 v
  simp only [Hom.comp_app, ConcreteCategory.comp_apply, Hom.id_app, ConcreteCategory.id_apply] at h1
  simp only [DualZigzag.tail2, Hom.comp_app, ConcreteCategory.comp_apply]
  exact h1

/-- **The coevaluation in a frame**: `coev|_V = ε^∨ ⊗ ε`. Proof: `ε^∨ ⊗ ε` is a frame of `M^∨ ⊗ M` on `V`
(`IsFrame.moduleTensorSection`), so `coev|_V = c • (ε^∨ ⊗ ε)`; the second zigzag identity `Z2` on the section `ε`
(`DualZigzag.zigzag2`, `tail2_app`) gives `c • ε = ε`, hence `c = 1` (`ε` is a frame). -/
private theorem res_coevSection_cf {M : X.Modules} [M.IsLineBundle] {V : X.Opens} {ε : Γ(M, V)}
    (hε : IsFrame M V ε) :
    (AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.Modules.dual M) M).res (le_top : V ≤ ⊤)
        (coevSection M) =
      AlgebraicGeometry.Scheme.Modules.moduleTensorSection (dualFrameSecCf hε) ε := by
  have hD : (AlgebraicGeometry.Scheme.Modules.dual M).IsLineBundle := moduleSheafDual_isLineBundle M
  let t : Γ((AlgebraicGeometry.Scheme.Modules.dual M), V) := (dualFrameSecCf hε)
  have hfrT : IsFrame (AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.Modules.dual M) M) V (AlgebraicGeometry.Scheme.Modules.moduleTensorSection t ε) :=
    isFrame_moduleTensorSection_cf (dualFrameSecCf_isFrame hε) hε
  let c : Γ(X, V) := hfrT.coord le_rfl ((AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.Modules.dual M) M).res le_top (coevSection M))
  have hc : (AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.Modules.dual M) M).res (le_top : V ≤ ⊤) (coevSection M) = c • AlgebraicGeometry.Scheme.Modules.moduleTensorSection t ε := by
    have h1 := hfrT.coord_smul_frame le_rfl ((AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.Modules.dual M) M).res le_top (coevSection M))
    have h0 : (AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.Modules.dual M) M).res le_rfl (AlgebraicGeometry.Scheme.Modules.moduleTensorSection t ε) = AlgebraicGeometry.Scheme.Modules.moduleTensorSection t ε := res_self (AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.Modules.dual M) M) _
    exact h1.symm.trans (congrArg (fun z => c • z) h0)
  -- the zigzag identity `Z2` on `ε`
  have hZε : (DualZigzag.tail2 M).app V ((DualZigzag.coevHom M ▷ M).app V ((λ_ M).inv.app V ε)) = ε :=
    zigzag2_app M V ε
  have e1 : (λ_ M).inv.app V ε = AlgebraicGeometry.Scheme.Modules.tensorSections (𝟙_ X.Modules) M V (DualZigzag.unitOne V) ε :=
    DualZigzag.leftUnitor_inv_app M V ε
  have e2 : (DualZigzag.coevHom M ▷ M).app V (AlgebraicGeometry.Scheme.Modules.tensorSections (𝟙_ X.Modules) M V (DualZigzag.unitOne V) ε) =
      AlgebraicGeometry.Scheme.Modules.tensorSections ((AlgebraicGeometry.Scheme.Modules.dual M) ⊗ M) M V ((DualZigzag.coevHom M).app V (DualZigzag.unitOne V)) ε :=
    whiskerRight_app_tensorSections_tf (DualZigzag.coevHom M) M V _ ε
  let z1 : Γ((AlgebraicGeometry.Scheme.Modules.dual M) ⊗ M, V) := AlgebraicGeometry.Scheme.Modules.tensorSections (AlgebraicGeometry.Scheme.Modules.dual M) M V t ε
  have e3 : (DualZigzag.coevHom M).app V (DualZigzag.unitOne V) = c • z1 := by
    refine (DualZigzag.coevHom_app_one M V).trans ?_
    have h1 : (tensorIsoTensorObj (AlgebraicGeometry.Scheme.Modules.dual M) M).hom.app V ((AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.Modules.dual M) M).res (le_top : V ≤ ⊤) (coevSection M)) =
        (tensorIsoTensorObj (AlgebraicGeometry.Scheme.Modules.dual M) M).hom.app V (c • AlgebraicGeometry.Scheme.Modules.moduleTensorSection t ε) := congrArg _ hc
    refine h1.trans ?_
    exact Hom.app_smul (tensorIsoTensorObj (AlgebraicGeometry.Scheme.Modules.dual M) M).hom c (show Γ((AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.Modules.dual M) M), V) from AlgebraicGeometry.Scheme.Modules.moduleTensorSection t ε)
  let w : Γ(((AlgebraicGeometry.Scheme.Modules.dual M) ⊗ M) ⊗ M, V) := AlgebraicGeometry.Scheme.Modules.tensorSections ((AlgebraicGeometry.Scheme.Modules.dual M) ⊗ M) M V z1 ε
  have e4 : AlgebraicGeometry.Scheme.Modules.tensorSections ((AlgebraicGeometry.Scheme.Modules.dual M) ⊗ M) M V (c • z1) ε = c • w :=
    tensorSections_smul_left ((AlgebraicGeometry.Scheme.Modules.dual M) ⊗ M) M V c z1 ε w rfl
  have hc1' : (localDualCf hε).1 (Frame.topZ V) ε = 1 := by
    have h := hε.coord_frame (le_refl V)
    rw [res_self] at h
    exact h
  have e5 : (DualZigzag.tail2 M).app V w = (1 : Γ(X, V)) • ε := by
    refine (DualZigzag.tail2_app M V (localDualCf hε) ε ε).trans ?_
    exact congrArg (fun r : Γ(X, V) => r • ε) hc1'
  have hcε : c • ε = ε := by
    have a1 := congrArg (fun z => (DualZigzag.tail2 M).app V ((DualZigzag.coevHom M ▷ M).app V z)) e1
    have a2 := congrArg (fun z => (DualZigzag.tail2 M).app V z) e2
    have a3 := congrArg (fun z => (DualZigzag.tail2 M).app V
      (AlgebraicGeometry.Scheme.Modules.tensorSections ((AlgebraicGeometry.Scheme.Modules.dual M) ⊗ M) M V z ε)) e3
    have a4 := congrArg (fun z => (DualZigzag.tail2 M).app V z) e4
    have a5 : (DualZigzag.tail2 M).app V (c • w) = c • (DualZigzag.tail2 M).app V w :=
      Hom.app_smul (DualZigzag.tail2 M) c w
    have a6 := congrArg (fun z : Γ(M, V) => c • z) e5
    have h := a1.trans (a2.trans (a3.trans (a4.trans (a5.trans a6))))
    rw [one_smul] at h
    exact h.symm.trans hZε
  -- `c • ε = ε` ⇒ `c = 1`
  have hc1 : c = 1 := by
    refine (hε V le_rfl).1 ?_
    show c • M.res le_rfl ε = (1 : Γ(X, V)) • M.res le_rfl ε
    rw [res_self, one_smul]
    exact hcε
  rw [hc, hc1, one_smul]

/-- `f.inv.app U y = x ⇒ f.hom.app U x = y`. -/
theorem iso_hom_app_eq_of_inv_app_eq {A B : X.Modules} (f : A ≅ B) (U : X.Opens) {x : Γ(A, U)} {y : Γ(B, U)}
    (h : f.inv.app U y = x) : f.hom.app U x = y := by
  subst h
  exact congrArg (fun k : B ⟶ B => k.app U y) f.inv_hom_id

/-- **`pullbackTensorIso.hom` on the unit section of a pure tensor**: `η_{M ⊗ N}(m ⊗ n) ↦ η_M(m) ⊗ η_N(n)`
(the inverse direction of `pullbackTensorIso_inv_app_moduleTensorSection_unitSec`). -/
theorem pullbackTensorIso_hom_app_unitSec_moduleTensorSection {Y : AlgebraicGeometry.Scheme.{u}} (f : Y ⟶ X)
    (M N : X.Modules) (U : X.Opens) (m : Γ(M, U)) (n : Γ(N, U)) :
    (AlgebraicGeometry.Scheme.Modules.pullbackTensorIso f M N).hom.app (f ⁻¹ᵁ U)
        (MiyaokaMori.DualPullback.unitSec f (AlgebraicGeometry.Scheme.Modules.tensor M N)
          (AlgebraicGeometry.Scheme.Modules.moduleTensorSection m n)) =
      AlgebraicGeometry.Scheme.Modules.moduleTensorSection (MiyaokaMori.DualPullback.unitSec f M m)
        (MiyaokaMori.DualPullback.unitSec f N n) :=
  iso_hom_app_eq_of_inv_app_eq _ _ (pullbackTensorIso_inv_app_moduleTensorSection_unitSec f M N U m n)

end AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.relativeProj

variable {X : AlgebraicGeometry.Scheme.{u}} (S : X.GradedQCAlgebra)

/-- **Local form of the coordinate `(ev_q ∘ π^*ι ⊗ id)(π^* coev_Q)` on a frame open** (variable-level core).
`V` affine, `ε` a frame of the line bundle `Q` on `V`,
`ι : Q^∨ ⟶ S_q`: the restriction to `π⁻¹V` of `Φ (pullbackTensorIso.hom (π^* coev_Q))` (with
`Φ = τ ≫ ((π^*ι ≫ ev_q) ▷ π^*Q) ≫ τ⁻¹`, exactly the body of `splitWeightedCoord`) is the pure tensor
`evaluationLocal S q V (ι ε^∨) ⊗ η(ε)`, `ε^∨ = hε.dualFrameOld`. See the module docstring for the route. -/
theorem coord_res_eq_moduleTensorSection_of_frame (Q : X.Modules) [Q.IsLocallyFree] [Q.IsFiniteType]
    [Q.IsLineBundle] (q : ℕ) (ι : AlgebraicGeometry.Scheme.Modules.dual Q ⟶ S.part q)
    (V : X.affineOpens) {ε : Γ(Q, V.1)} (hε : AlgebraicGeometry.Scheme.Modules.IsFrame Q V.1 ε) :
    AlgebraicGeometry.Scheme.Modules.res
        ((AlgebraicGeometry.Scheme.relativeProj.twist S (q : ℤ)).tensor
          ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).obj Q))
        le_top
        (((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _).hom ≫
            CategoryTheory.MonoidalCategoryStruct.whiskerRight
              ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj S).hom).map ι ≫
                AlgebraicGeometry.Scheme.relativeProj.evaluation S q) _ ≫
            (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _).inv).app ⊤
          ((AlgebraicGeometry.Scheme.Modules.pullbackTensorIso (AlgebraicGeometry.Scheme.relativeProj S).hom
            (AlgebraicGeometry.Scheme.Modules.dual Q) Q).hom.app ⊤
            (sectionPullbackAlong (AlgebraicGeometry.Scheme.relativeProj S).hom
              (AlgebraicGeometry.Scheme.Modules.coevSection Q)))) =
      AlgebraicGeometry.Scheme.Modules.moduleTensorSection
        (AlgebraicGeometry.Scheme.relativeProj.evaluationLocal S q V (ι.app V.1 hε.dualFrameOld))
        (MiyaokaMori.DualPullback.unitSec (AlgebraicGeometry.Scheme.relativeProj S).hom Q ε) := by
  set π := (AlgebraicGeometry.Scheme.relativeProj S).hom with hπ
  let D := AlgebraicGeometry.Scheme.Modules.dual Q
  let T := AlgebraicGeometry.Scheme.Modules.tensor D Q
  set φ : (AlgebraicGeometry.Scheme.Modules.pullback π).obj D ⟶ AlgebraicGeometry.Scheme.relativeProj.twist S (q : ℤ) :=
    (AlgebraicGeometry.Scheme.Modules.pullback π).map ι ≫ AlgebraicGeometry.Scheme.relativeProj.evaluation S q with hφ
  set Φ := (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _).hom ≫
      CategoryTheory.MonoidalCategoryStruct.whiskerRight φ ((AlgebraicGeometry.Scheme.Modules.pullback π).obj Q) ≫
      (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj _ _).inv with hΦ
  set c := sectionPullbackAlong π (AlgebraicGeometry.Scheme.Modules.coevSection Q) with hc
  set z := (AlgebraicGeometry.Scheme.Modules.pullbackTensorIso π D Q).hom.app ⊤ c with hz
  have hV : π ⁻¹ᵁ V.1 ≤ ⊤ := le_top
  -- step A
  have eA : AlgebraicGeometry.Scheme.Modules.res _ hV (Φ.app ⊤ z) = Φ.app (π ⁻¹ᵁ V.1)
      (AlgebraicGeometry.Scheme.Modules.res _ hV z) := (AlgebraicGeometry.Scheme.Modules.Hom.app_res Φ hV z).symm
  -- step B
  have eB : AlgebraicGeometry.Scheme.Modules.res _ hV z =
      (AlgebraicGeometry.Scheme.Modules.pullbackTensorIso π D Q).hom.app (π ⁻¹ᵁ V.1)
        (AlgebraicGeometry.Scheme.Modules.res _ hV c) :=
    (AlgebraicGeometry.Scheme.Modules.Hom.app_res (AlgebraicGeometry.Scheme.Modules.pullbackTensorIso π D Q).hom hV c).symm
  -- step C: c = η(coev), restriction commutes with η
  have eC : AlgebraicGeometry.Scheme.Modules.res _ hV c =
      MiyaokaMori.DualPullback.unitSec π T (AlgebraicGeometry.Scheme.Modules.res T le_top
        (AlgebraicGeometry.Scheme.Modules.coevSection Q)) := by
    have h1 := MiyaokaMori.DualPullback.unitSec_res π T (le_top : V.1 ≤ ⊤)
      (AlgebraicGeometry.Scheme.Modules.coevSection Q)
    exact h1.symm
  -- step D: coev|_V = ε^∨ ⊗ ε
  have eD : AlgebraicGeometry.Scheme.Modules.res T le_top (AlgebraicGeometry.Scheme.Modules.coevSection Q) =
      AlgebraicGeometry.Scheme.Modules.moduleTensorSection hε.dualFrameOld ε := AlgebraicGeometry.Scheme.Modules.res_coevSection_cf hε
  -- step E
  have eE := AlgebraicGeometry.Scheme.Modules.pullbackTensorIso_hom_app_unitSec_moduleTensorSection π D Q V.1
    hε.dualFrameOld ε
  -- step F: Φ on a pure tensor
  have eF : Φ.app (π ⁻¹ᵁ V.1) (AlgebraicGeometry.Scheme.Modules.moduleTensorSection (MiyaokaMori.DualPullback.unitSec π D hε.dualFrameOld)
      (MiyaokaMori.DualPullback.unitSec π Q ε)) =
      AlgebraicGeometry.Scheme.Modules.moduleTensorSection (φ.app (π ⁻¹ᵁ V.1) (MiyaokaMori.DualPullback.unitSec π D hε.dualFrameOld))
        (MiyaokaMori.DualPullback.unitSec π Q ε) := by
    have f1 := AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj_hom_app_moduleTensorSection_tppl
      ((AlgebraicGeometry.Scheme.Modules.pullback π).obj D) ((AlgebraicGeometry.Scheme.Modules.pullback π).obj Q)
      (π ⁻¹ᵁ V.1) (MiyaokaMori.DualPullback.unitSec π D hε.dualFrameOld) (MiyaokaMori.DualPullback.unitSec π Q ε)
    have f2 := AlgebraicGeometry.Scheme.Modules.whiskerRight_app_tensorSections_tppl φ (π ⁻¹ᵁ V.1)
      (MiyaokaMori.DualPullback.unitSec π D hε.dualFrameOld) (MiyaokaMori.DualPullback.unitSec π Q ε)
    have f3 := AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj_inv_app_tensorSections
      (AlgebraicGeometry.Scheme.relativeProj.twist S (q : ℤ)) ((AlgebraicGeometry.Scheme.Modules.pullback π).obj Q)
      (π ⁻¹ᵁ V.1) (φ.app (π ⁻¹ᵁ V.1) (MiyaokaMori.DualPullback.unitSec π D hε.dualFrameOld))
      (MiyaokaMori.DualPullback.unitSec π Q ε)
    have f0 : Φ.app (π ⁻¹ᵁ V.1) (AlgebraicGeometry.Scheme.Modules.moduleTensorSection (MiyaokaMori.DualPullback.unitSec π D hε.dualFrameOld)
        (MiyaokaMori.DualPullback.unitSec π Q ε)) =
        (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj (AlgebraicGeometry.Scheme.relativeProj.twist S (q : ℤ))
          ((AlgebraicGeometry.Scheme.Modules.pullback π).obj Q)).inv.app (π ⁻¹ᵁ V.1)
          ((CategoryTheory.MonoidalCategoryStruct.whiskerRight φ ((AlgebraicGeometry.Scheme.Modules.pullback π).obj Q)).app
            (π ⁻¹ᵁ V.1)
            ((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj ((AlgebraicGeometry.Scheme.Modules.pullback π).obj D)
              ((AlgebraicGeometry.Scheme.Modules.pullback π).obj Q)).hom.app (π ⁻¹ᵁ V.1)
              (AlgebraicGeometry.Scheme.Modules.moduleTensorSection (MiyaokaMori.DualPullback.unitSec π D hε.dualFrameOld)
                (MiyaokaMori.DualPullback.unitSec π Q ε)))) := rfl
    rw [f0, f1, f2, f3]
  -- step G: φ(η ε^∨) = evaluationLocal (ι ε^∨)
  have eG : φ.app (π ⁻¹ᵁ V.1) (MiyaokaMori.DualPullback.unitSec π D hε.dualFrameOld) =
      AlgebraicGeometry.Scheme.relativeProj.evaluationLocal S q V (ι.app V.1 hε.dualFrameOld) := by
    have g0 : φ.app (π ⁻¹ᵁ V.1) (MiyaokaMori.DualPullback.unitSec π D hε.dualFrameOld) =
        (AlgebraicGeometry.Scheme.relativeProj.evaluation S q).app (π ⁻¹ᵁ V.1)
          (((AlgebraicGeometry.Scheme.Modules.pullback π).map ι).app (π ⁻¹ᵁ V.1)
            (MiyaokaMori.DualPullback.unitSec π D hε.dualFrameOld)) := rfl
    rw [g0, MiyaokaMori.DualPullback.unitSec_map]
    exact AlgebraicGeometry.Scheme.relativeProj.evaluation_app_unit S q V (ι.app V.1 hε.dualFrameOld)
  refine eA.trans ?_
  refine (congrArg (fun w => Φ.app (π ⁻¹ᵁ V.1) w) eB).trans ?_
  refine (congrArg (fun w => Φ.app (π ⁻¹ᵁ V.1)
    ((AlgebraicGeometry.Scheme.Modules.pullbackTensorIso π D Q).hom.app (π ⁻¹ᵁ V.1) w)) eC).trans ?_
  refine (congrArg (fun w => Φ.app (π ⁻¹ᵁ V.1)
    ((AlgebraicGeometry.Scheme.Modules.pullbackTensorIso π D Q).hom.app (π ⁻¹ᵁ V.1)
      (MiyaokaMori.DualPullback.unitSec π T w))) eD).trans ?_
  refine (congrArg (fun w => Φ.app (π ⁻¹ᵁ V.1) w) eE).trans ?_
  refine eF.trans ?_
  exact congrArg (fun w => AlgebraicGeometry.Scheme.Modules.moduleTensorSection w (MiyaokaMori.DualPullback.unitSec π Q ε)) eG

end AlgebraicGeometry.Scheme.relativeProj

end
