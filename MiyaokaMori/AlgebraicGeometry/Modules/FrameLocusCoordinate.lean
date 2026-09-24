import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.FrameLocusOn
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.PullbackFrameRankOne
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.PullbackUnitOpenImmersion
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.ModuleSheafFrameIso
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.ModuleSheafFrame

/-! # The frame locus through a trivialization

For an open immersion `ι : Y ⟶ X`, an `O_X`-module `M` with a trivialization `et : ι^*M ≅ O_Y`, and a section
`s ∈ Γ(M, U)` with `Y ⊆ ι⁻¹U`, the **coordinate** `coordOn et s : Γ(Y, ⊤)` of `s` is the image of `ι^*s` under `et`.
Then `ι⁻¹(frame locus of s) = Y.basicOpen (coordOn et s)` (`preimage_frameLocusOn_eq_basicOpen`): `s` is a frame near
`ι y` iff its coordinate is a unit near `y` (Stacks 01O9 / 07RK: "`X_s` is the locus where `s` generates").

Used for the lift into a relative Proj (Stacks 07RM, paragraph 5): on a piece `V₃` of
`relativeProj.lift`, the local ring map sends `π₁(e)` to `coordOn et (φ(e))`, so `r⁻¹D₊(e) ∩ V₃ = X_{φ(e)} ∩ V₃`.

Proof of the main theorem:
1. `ι⁻¹(frameLocusOn s) = frameLocusOn (ι^*s)` in `ι^*M`: frames pull back along `ι` (`isFrame_unitSec_pullback`),
   and conversely a frame of `ι^*M` on `O` is a frame of `M.restrict ι` on `O`
   through `restrictFunctorIsoPullback` (whose section map is the unit, `restrictFunctorIsoPullback_hom_app_apply`),
   hence a frame of `M` on `ι(O)` (`IsFrame.of_restrict_image`, re-proved here to keep the import closure small).
2. Frame loci are invariant under isomorphisms of modules (`IsFrame.map_iso`), so this is the frame locus of the
   coordinate in `O_Y`.
3. For `c ∈ Γ(Y, ⊤)`, `c|_O` is a frame of `O_Y` on `O` iff `c|_O` is a unit iff `O ≤ Y.basicOpen c`
   (`RingedSpace.isUnit_of_isUnit_germ`, `Scheme.mem_basicOpen`); so the frame locus of `c` is `Y.basicOpen c`. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : AlgebraicGeometry.Scheme.{u}}

/-! ## The coordinate of a section through a trivialization of the pullback -/

/-- **Coordinate of `m ∈ Γ(M, W)` on `O ≤ ι⁻¹W`** through `et : ι^*M ≅ O_Y`: `et(ι^*m|_O) ∈ Γ(Y, O)`. -/
def coordOn (ι : Y ⟶ X) (M : X.Modules)
    (et : (AlgebraicGeometry.Scheme.Modules.pullback ι).obj M ≅ SheafOfModules.unit Y.ringCatSheaf)
    {W : X.Opens} (m : Γ(M, W)) {O : Y.Opens} (hO : O ≤ ι ⁻¹ᵁ W) : Γ(Y, O) :=
  et.hom.app O (((AlgebraicGeometry.Scheme.Modules.pullback ι).obj M).res hO
    (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction ι).unit.app M).app W m))

variable (ι : Y ⟶ X) (M : X.Modules)
  (et : (AlgebraicGeometry.Scheme.Modules.pullback ι).obj M ≅ SheafOfModules.unit Y.ringCatSheaf)

/-- The unit commutes with restriction: `ι^*(m|_{W'}) = (ι^*m)|_{ι⁻¹W'}`. -/
theorem unit_app_res {W' W : X.Opens} (h : W' ≤ W) (m : Γ(M, W)) :
    ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction ι).unit.app M).app W' (M.res h m) =
      ((AlgebraicGeometry.Scheme.Modules.pullback ι).obj M).res (ι.preimage_mono h)
        (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction ι).unit.app M).app W m) :=
  Hom.app_res ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction ι).unit.app M) h m

set_option backward.isDefEq.respectTransparency false in
theorem coordOn_res_left {W' W : X.Opens} (h : W' ≤ W) (m : Γ(M, W)) {O : Y.Opens} (hO : O ≤ ι ⁻¹ᵁ W') :
    coordOn ι M et (M.res h m) hO = coordOn ι M et m (hO.trans (ι.preimage_mono h)) := by
  unfold coordOn
  rw [unit_app_res, res_res]

set_option backward.isDefEq.respectTransparency false in
theorem coordOn_res_right {W : X.Opens} (m : Γ(M, W)) {O O' : Y.Opens} (hO : O ≤ ι ⁻¹ᵁ W) (h : O' ≤ O) :
    Y.presheaf.map (homOfLE h).op (coordOn ι M et m hO) = coordOn ι M et m (h.trans hO) := by
  unfold coordOn
  rw [← res_res _ h hO]
  exact (Hom.app_res et.hom h _).symm

set_option backward.isDefEq.respectTransparency false in
/-- **Linearity of the coordinate**: `coordOn (g • m) = ι^♯(g) · coordOn m`. -/
theorem coordOn_smul {W : X.Opens} (g : Γ(X, W)) (m : Γ(M, W)) {O : Y.Opens} (hO : O ≤ ι ⁻¹ᵁ W) :
    coordOn ι M et (g • m) hO = ι.appLE W O hO g * coordOn ι M et m hO := by
  unfold coordOn
  have e1 : @Eq Γ((AlgebraicGeometry.Scheme.Modules.pullback ι).obj M, ι ⁻¹ᵁ W)
      (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction ι).unit.app M).app W (g • m))
      (@HSMul.hSMul Γ(Y, ι ⁻¹ᵁ W) Γ((AlgebraicGeometry.Scheme.Modules.pullback ι).obj M, ι ⁻¹ᵁ W)
        Γ((AlgebraicGeometry.Scheme.Modules.pullback ι).obj M, ι ⁻¹ᵁ W) instHSMul (ι.app W g)
        (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction ι).unit.app M).app W m)) :=
    Hom.app_smul _ g m
  rw [e1, res_smul, Hom.app_smul]
  rfl

/-! ## Frames of the structure sheaf are units -/

set_option backward.isDefEq.respectTransparency false in
/-- `u ∈ Γ(Y, O)` is a frame of `O_Y` on `O` iff it is a unit. -/
theorem isFrame_unit_iff_isUnit {O : Y.Opens} (u : Γ(Y, O)) :
    IsFrame (SheafOfModules.unit Y.ringCatSheaf) O (show Γ(SheafOfModules.unit Y.ringCatSheaf, O) from u) ↔
      IsUnit u := by
  constructor
  · intro hf
    obtain ⟨r, hr⟩ := (hf O le_rfl).2 (show Γ(SheafOfModules.unit Y.ringCatSheaf, O) from (1 : Γ(Y, O)))
    rw [res_self] at hr
    exact isUnit_iff_exists_inv.2 ⟨r, (mul_comm u r).trans hr⟩
  · intro hu W' h
    obtain ⟨v, hv⟩ : IsUnit (Y.presheaf.map (homOfLE h).op u) := hu.map _
    show Function.Bijective (fun r : Γ(Y, W') => r * Y.presheaf.map (homOfLE h).op u)
    rw [← hv]
    exact ⟨v.isUnit.mul_left_injective, fun y => ⟨y * ↑v⁻¹, Units.inv_mul_cancel_right y v⟩⟩

/-- `u ∈ Γ(Y, O)` is a unit iff `O ≤ Y.basicOpen u` (`RingedSpace.isUnit_of_isUnit_germ`, `Scheme.mem_basicOpen`). -/
theorem isUnit_iff_le_basicOpen {O : Y.Opens} (u : Γ(Y, O)) : IsUnit u ↔ O ≤ Y.basicOpen u := by
  constructor
  · intro hu y hy
    exact (Y.mem_basicOpen u y hy).2 (hu.map _)
  · intro h
    exact Y.toLocallyRingedSpace.toRingedSpace.isUnit_of_isUnit_germ O u
      (fun y hy => (Y.mem_basicOpen u y hy).1 (h hy))

/-- **The frame locus of a global function is its basic open.** -/
theorem frameLocusOn_unit_eq_basicOpen (c : Γ(Y, ⊤)) :
    frameLocusOn (X := Y) (SheafOfModules.unit Y.ringCatSheaf) (show Γ(SheafOfModules.unit Y.ringCatSheaf, ⊤) from c) =
      Y.basicOpen c := by
  apply le_antisymm
  · intro y hy
    obtain ⟨O, h, hyO, hf⟩ := mem_frameLocusOn.1 hy
    have hu := (isFrame_unit_iff_isUnit (Y.presheaf.map (homOfLE h).op c)).1 hf
    have hle := (isUnit_iff_le_basicOpen _).1 hu
    have := hle hyO
    rw [AlgebraicGeometry.Scheme.basicOpen_res] at this
    exact this.2
  · intro y hy
    refine mem_frameLocusOn.2 ⟨Y.basicOpen c, le_top, hy, ?_⟩
    refine (isFrame_unit_iff_isUnit _).2 ?_
    exact AlgebraicGeometry.RingedSpace.isUnit_res_basicOpen _ c

/-! ## Frame loci and isomorphisms -/

set_option backward.isDefEq.respectTransparency false in
/-- Frame loci are invariant under isomorphisms of modules. -/
theorem frameLocusOn_map_iso {M N : X.Modules} (e : M ≅ N) {W : X.Opens} (t : Γ(M, W)) :
    N.frameLocusOn (e.hom.app W t) = M.frameLocusOn t := by
  apply TopologicalSpace.Opens.ext
  ext y
  simp only [SetLike.mem_coe]
  rw [mem_frameLocusOn, mem_frameLocusOn]
  constructor
  · rintro ⟨O, h, hyO, hf⟩
    refine ⟨O, h, hyO, ?_⟩
    have hf' := hf.map_iso e.symm
    have : e.symm.hom.app W (e.hom.app W t) = t := modIso_inv_app_hom_app e W t
    rwa [Hom.app_res, this] at hf'
  · rintro ⟨O, h, hyO, hf⟩
    refine ⟨O, h, hyO, ?_⟩
    have hf' := hf.map_iso e
    rwa [Hom.app_res] at hf'

/-! ## Frames along an open immersion -/

/-- Bijectivity of `r ↦ r • e|` depends only on the open (transport along an equality of opens; re-proof of
`bijective_smul_res_congr_opens'`). -/
private theorem bijective_smul_res_congr_opens_fc {N : X.Modules} {W V V' : X.Opens} (hV : V ≤ W) (hV' : V' ≤ W)
    (h : V = V') (e : Γ(N, W))
    (hb : Function.Bijective (fun r : Γ(X, V) => r • N.res hV e)) :
    Function.Bijective (fun r : Γ(X, V') => r • N.res hV' e) := by
  subst h
  exact hb

/-- `e` a frame of `N.restrict g` on `O` ⇒ a frame of `N` on `g ''ᵁ O` (re-proof of
`IsFrame.of_restrict_image` from `Stacks07rm_RelativeChartSections`, to keep the import closure small). -/
private theorem IsFrame.of_restrict_image' (g : Y ⟶ X) [AlgebraicGeometry.IsOpenImmersion g] {N : X.Modules}
    {O : Y.Opens} {e : Γ(N.restrict g, O)} (hf : IsFrame (N.restrict g) O e) :
    IsFrame N (g ''ᵁ O) (e : Γ(N, g ''ᵁ O)) := by
  intro W' h
  have hO' : g ⁻¹ᵁ W' ≤ O := by
    have := g.preimage_mono h
    rwa [g.preimage_image_eq] at this
  have hW' : g ''ᵁ (g ⁻¹ᵁ W') = W' := by
    rw [g.image_preimage_eq_opensRange_inf]
    exact inf_eq_right.mpr (h.trans (g.image_le_opensRange O))
  refine bijective_smul_res_congr_opens_fc (g.image_mono hO') h hW' _ ?_
  have hb := hf (g ⁻¹ᵁ W') hO'
  have hfun : (fun r : Γ(Y, g ⁻¹ᵁ W') => r • (N.restrict g).res hO' e) =
      (fun r' : Γ(X, g ''ᵁ (g ⁻¹ᵁ W')) =>
        r' • N.res (g.image_mono hO') (e : Γ(N, g ''ᵁ O))) ∘
        (g.appIso (g ⁻¹ᵁ W')).inv := rfl
  rw [hfun] at hb
  exact (Function.Bijective.of_comp_iff _
    (ConcreteCategory.bijective_of_isIso (g.appIso (g ⁻¹ᵁ W')).inv)).mp hb

set_option backward.isDefEq.respectTransparency false in
/-- **Frames of `M` near `ι y` and frames of `ι^*M` near `y`**: the preimage of the frame locus of `s` is the
frame locus of `ι^*s`. -/
theorem preimage_frameLocusOn_eq_frameLocusOn_unit [AlgebraicGeometry.IsOpenImmersion ι] {U : X.Opens}
    (s : Γ(M, U)) (hU : (⊤ : Y.Opens) ≤ ι ⁻¹ᵁ U) :
    ι ⁻¹ᵁ M.frameLocusOn s =
      ((AlgebraicGeometry.Scheme.Modules.pullback ι).obj M).frameLocusOn
        (((AlgebraicGeometry.Scheme.Modules.pullback ι).obj M).res hU
          (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction ι).unit.app M).app U s)) := by
  apply TopologicalSpace.Opens.ext
  ext y
  simp only [SetLike.mem_coe]
  rw [AlgebraicGeometry.Scheme.Hom.mem_preimage, mem_frameLocusOn, mem_frameLocusOn]
  constructor
  · rintro ⟨W, h, hyW, hf⟩
    refine ⟨ι ⁻¹ᵁ W, le_top, hyW, ?_⟩
    have hf' := MiyaokaMori.DualPullback.isFrame_unitSec_pullback ι M hf
    have e1 : MiyaokaMori.DualPullback.unitSec ι M (M.res h s) =
        ((AlgebraicGeometry.Scheme.Modules.pullback ι).obj M).res le_top
          (((AlgebraicGeometry.Scheme.Modules.pullback ι).obj M).res hU
            (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction ι).unit.app M).app U s)) := by
      show ((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction ι).unit.app M).app W (M.res h s) = _
      rw [unit_app_res, res_res]
    rwa [e1] at hf'
  · rintro ⟨O, hOtop, hyO, hf⟩
    have hOU : O ≤ ι ⁻¹ᵁ U := le_top.trans hU
    have hWU : ι ''ᵁ O ≤ U := (ι.image_mono hOU).trans (ι.image_preimage_le U)
    refine ⟨ι ''ᵁ O, hWU, ⟨y, hyO, rfl⟩, ?_⟩
    -- transport the frame of `ι^*M` on `O` to a frame of `M.restrict ι` on `O`, then to `M` on `ι(O)`
    have hf₁ := hf.map_iso ((restrictFunctorIsoPullback ι).app M).symm
    have key : ((restrictFunctorIsoPullback ι).app M).symm.hom.app O
        (((AlgebraicGeometry.Scheme.Modules.pullback ι).obj M).res hOtop
          (((AlgebraicGeometry.Scheme.Modules.pullback ι).obj M).res hU
            (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction ι).unit.app M).app U s))) =
        (show Γ(M.restrict ι, O) from M.res hWU s) := by
      refine (congrArg (((restrictFunctorIsoPullback ι).app M).symm.hom.app O) ?_).trans
        (modIso_inv_app_hom_app ((restrictFunctorIsoPullback ι).app M) O _)
      rw [restrictFunctorIsoPullback_hom_app_apply]
      show _ = ((AlgebraicGeometry.Scheme.Modules.pullback ι).obj M).res _
        (((AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction ι).unit.app M).app (ι ''ᵁ O) (M.res hWU s))
      rw [unit_app_res, res_res, res_res]
    rw [key] at hf₁
    exact IsFrame.of_restrict_image' ι hf₁

set_option backward.isDefEq.respectTransparency false in
/-- **Main theorem: `ι⁻¹(frame locus of `s`) = Y.basicOpen (coordinate of `s`)`.** -/
theorem preimage_frameLocusOn_eq_basicOpen_coordOn [AlgebraicGeometry.IsOpenImmersion ι] {U : X.Opens}
    (s : Γ(M, U)) (hU : (⊤ : Y.Opens) ≤ ι ⁻¹ᵁ U) :
    ι ⁻¹ᵁ M.frameLocusOn s = Y.basicOpen (coordOn ι M et s hU) := by
  rw [preimage_frameLocusOn_eq_frameLocusOn_unit ι M s hU, ← frameLocusOn_map_iso et]
  exact frameLocusOn_unit_eq_basicOpen (coordOn ι M et s hU)

end AlgebraicGeometry.Scheme.Modules

end
