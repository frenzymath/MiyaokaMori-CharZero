import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.Frame
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.IsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.SectionTensor
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorMonoidalIso
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModulesTensorStalk
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleNonvanishingLocus
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.NonvanishingLocusIsoInvariant
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensor
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.Stacks01ct

/-! # The nonvanishing locus of a tensor product of sections

The nonvanishing locus of the tensor product `s ⊗ t ∈ Γ(L ⊗ N)` of two global sections of line
bundles is the intersection of the two nonvanishing loci: `X_{s ⊗ t} = X_s ⊓ X_t`.

Proof (on stalks, Stacks 01CB + Nakayama for one generator over a local ring): take frames `e`, `f`
of `L`, `N` at `y` (`exists_frame`), and on a common open `W` write `s = a·e`, `t = b·f`, so
`s ⊗ t = (ab)·(e ⊗ f)`. The germ `e_y` of a frame is a free generator of the stalk `L_y`
(`IsFrame.span_germ_eq_top` + torsion-freeness `IsFrame.germ_smul_eq_zero`), so `L_y ≃ 𝒪_y`
(`IsFrame.stalkEquiv`), likewise `N_y ≃ 𝒪_y`, and `(L ⊗ N)_y ≃ L_y ⊗ N_y ≃ 𝒪_y ⊗ 𝒪_y ≃ 𝒪_y`
(`tensorStalkEquiv`, Stacks 01CB) sends `(e ⊗ f)_y` to `1`. Hence `s_y ∈ 𝔪_y L_y ⟺ a_y ∈ 𝔪_y`,
`t_y ∈ 𝔪_y N_y ⟺ b_y ∈ 𝔪_y`, and
`(s ⊗ t)_y ∈ 𝔪_y (L ⊗ N)_y ⟺ a_y b_y ∈ 𝔪_y ⟺ a_y ∈ 𝔪_y ∨ b_y ∈ 𝔪_y`
(in a local ring `𝔪_y` is the set of non-units, `IsUnit.mul_iff`). Taking complements gives the claim.

References: Stacks 01CB (stalks of tensor products), 01CY (nonvanishing loci). Used for the
algebraic route to the nonvanishing locus of a coordinate power (raising the coordinates to the power
`m/q` does not change their zero loci).

Spelling convention: all stalks in this file are written `M.presheaf.stalk y` (the spelling of
`moduleStalkLinearEquiv`, `tensorStalkEquiv`), which is definitionally but not syntactically equal to
the `↥(M.stalk y)` in the definition of `nonvanishingLocus`; the two are connected only by
`exact` / `Iff.trans`, never by `rw`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory Opposite TopologicalSpace

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- The germ of a frame is torsion-free: `c • e_y = 0 ⇒ c = 0`. Here `c` is the germ of a section `r`
over some `V ≤ W` and `c • e_y` is the germ of `r • e|_V`; if the germ vanishes then on some
`W' ∋ y` we have `r|_{W'} • e|_{W'} = 0 = 0 • e|_{W'}`, and injectivity of the frame gives
`r|_{W'} = 0`, so `c = 0`. -/
theorem IsFrame.germ_smul_eq_zero {M : X.Modules} {W : X.Opens} {e : Γ(M, W)}
    (hf : IsFrame M W e) {y : X} (hy : y ∈ W) (c : X.presheaf.stalk y)
    (hc : c • M.presheaf.germ W y hy e = 0) : c = 0 := by
  obtain ⟨V, hVW, hyV, r, rfl⟩ := X.presheaf.exists_le_germ_eq c hy
  have h1 : (X.presheaf.germ V y hyV r : X.presheaf.stalk y) • M.presheaf.germ W y hy e =
      M.presheaf.germ V y hyV (r • M.res hVW e) := by
    rw [germ_smul', TopCat.Presheaf.germ_res_apply]
  rw [h1] at hc
  have hc' : M.presheaf.germ V y hyV (r • M.res hVW e) = M.presheaf.germ V y hyV 0 := by
    rw [map_zero]; exact hc
  obtain ⟨W', hyW', iU, iV, hW'⟩ := M.presheaf.germ_eq y hyV hyV _ _ hc'
  rw [map_zero] at hW'
  have hres : M.res (leOfHom iU) (r • M.res hVW e) = 0 := hW'
  rw [res_smul, res_res] at hres
  have hfr : IsFrame M W' (M.res ((leOfHom iU).trans hVW) e) := hf.restrict _
  have hr0 : X.presheaf.map (homOfLE (leOfHom iU)).op r = 0 :=
    (hfr W' le_rfl).1 (by simp only [res_self, hres, zero_smul])
  have h2 : X.presheaf.germ V y hyV r =
      X.presheaf.germ W' y hyW' (X.presheaf.map (homOfLE (leOfHom iU)).op r) :=
    (TopCat.Presheaf.germ_res_apply _ _ _ _ _).symm
  rw [h2, hr0, map_zero]

/-- A frame gives a free generator of the stalk: `𝒪_{X,y} ≃ₗ M_y`, `c ↦ c • e_y`
(injective by `IsFrame.germ_smul_eq_zero`, surjective by `IsFrame.span_germ_eq_top`). -/
noncomputable def IsFrame.stalkEquiv {M : X.Modules} {W : X.Opens} {e : Γ(M, W)}
    (hf : IsFrame M W e) {y : X} (hy : y ∈ W) :
    X.presheaf.stalk y ≃ₗ[X.presheaf.stalk y] M.presheaf.stalk y :=
  LinearEquiv.ofBijective
    (LinearMap.toSpanSingleton (X.presheaf.stalk y) (M.presheaf.stalk y) (M.presheaf.germ W y hy e))
    ⟨fun a b hab => by
      have h : (a - b) • (M.presheaf.germ W y hy e : M.presheaf.stalk y) = 0 := by
        rw [sub_smul]
        exact sub_eq_zero.mpr hab
      exact sub_eq_zero.mp (hf.germ_smul_eq_zero hy _ h),
     fun m => by
      have hm : m ∈ Submodule.span (X.presheaf.stalk y)
          ({(M.presheaf.germ W y hy e : M.presheaf.stalk y)} : Set (M.presheaf.stalk y)) :=
        Submodule.eq_top_iff'.mp (hf.span_germ_eq_top hy) m
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp hm
      exact ⟨a, ha⟩⟩

theorem IsFrame.stalkEquiv_apply {M : X.Modules} {W : X.Opens} {e : Γ(M, W)}
    (hf : IsFrame M W e) {y : X} (hy : y ∈ W) (c : X.presheaf.stalk y) :
    hf.stalkEquiv hy c = c • (M.presheaf.germ W y hy e : M.presheaf.stalk y) := rfl

/-- A local ring `R` as a module over itself: `x ∈ 𝔪 • ⊤ ⟺ x ∈ 𝔪`. -/
theorem mem_maximalIdeal_smul_top_iff {R : Type*} [CommRing R] [IsLocalRing R] (x : R) :
    x ∈ (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R R) ↔ x ∈ IsLocalRing.maximalIdeal R := by
  rw [show (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R R) = IsLocalRing.maximalIdeal R * ⊤ from rfl,
    Ideal.mul_top]

/-- Testing `v ∈ 𝔪_y M` along a linear isomorphism `Θ : M ≃ 𝒪_y`: it is equivalent to `Θ v ∈ 𝔪_y`. -/
theorem mem_maximalIdeal_smul_top_iff_of_linearEquiv {R : Type*} [CommRing R] [IsLocalRing R]
    {M : Type*} [AddCommGroup M] [Module R M] (Θ : M ≃ₗ[R] R) (v : M) :
    v ∈ (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R M) ↔ Θ v ∈ IsLocalRing.maximalIdeal R := by
  rw [← Submodule.mem_smul_top_linearEquiv_iff Θ, mem_maximalIdeal_smul_top_iff]

/-- In a frame `(W, e)` at `y`, the germ of `s ∈ Γ(L, ⊤)` lies in `𝔪_y L_y` iff the germ of the
coordinate `a` of `s|_W` lies in `𝔪_y`. -/
theorem IsFrame.germ_mem_maximalIdeal_smul_iff_coord {L : X.Modules} {W : X.Opens} {e : Γ(L, W)}
    (hf : IsFrame L W e) {y : X} (hy : y ∈ W) (s : Γ(L, ⊤)) :
    (L.presheaf.germ ⊤ y trivial s : L.presheaf.stalk y) ∈
        (IsLocalRing.maximalIdeal (X.presheaf.stalk y)) •
          (⊤ : Submodule (X.presheaf.stalk y) (L.presheaf.stalk y)) ↔
      X.presheaf.germ W y hy (hf.coord le_rfl (L.res le_top s)) ∈
        IsLocalRing.maximalIdeal (X.presheaf.stalk y) := by
  have h := hf.coord_smul_frame le_rfl (L.res le_top s)
  rw [res_self] at h
  have hs : (L.presheaf.germ ⊤ y trivial s : L.presheaf.stalk y) =
      hf.stalkEquiv hy (X.presheaf.germ W y hy (hf.coord le_rfl (L.res le_top s))) := by
    rw [IsFrame.stalkEquiv_apply, ← germ_smul', h]
    exact (TopCat.Presheaf.germ_res_apply L.presheaf (homOfLE le_top) y hy s).symm
  refine Iff.trans (mem_maximalIdeal_smul_top_iff_of_linearEquiv (hf.stalkEquiv hy).symm _) ?_
  rw [hs, LinearEquiv.symm_apply_apply]

/-- `(L ⊗ N)_y ≃ 𝒪_y`: the linear isomorphism on stalks induced by `tensorIsoTensorObj` (the
canonical isomorphism between `Modules.tensor` and the monoidal `⊗`), followed by `tensorStalkEquiv`
(Stacks 01CB) and then by `L_y ≃ 𝒪_y`, `N_y ≃ 𝒪_y` given by the two frames and `𝒪_y ⊗ 𝒪_y ≃ 𝒪_y`. -/
noncomputable def IsFrame.tensorStalkEquivOfFrames {L N : X.Modules} {W : X.Opens} {e : Γ(L, W)} {f : Γ(N, W)}
    (he : IsFrame L W e) (hg : IsFrame N W f) {y : X} (hy : y ∈ W) :
    (AlgebraicGeometry.Scheme.Modules.tensor L N).presheaf.stalk y ≃ₗ[X.presheaf.stalk y] X.presheaf.stalk y :=
  moduleStalkLinearEquiv X y (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj L N) ≪≫ₗ
    tensorStalkEquiv L N y ≪≫ₗ
    TensorProduct.congr (he.stalkEquiv hy).symm (hg.stalkEquiv hy).symm ≪≫ₗ
    TensorProduct.lid (X.presheaf.stalk y) (X.presheaf.stalk y)

/-- `tensorIsoTensorObj` on a pair of sections: `moduleTensorSection a b` of `Modules.tensor` (the
image of `a ⊗ₜ b` under the sheafification unit) corresponds to `tensorSections a b` of the monoidal
`⊗` (definitionally). -/
theorem tensorIsoTensorObj_hom_app_moduleTensorSection (L N : X.Modules) (U : X.Opens)
    (a : Γ(L, U)) (b : Γ(N, U)) :
    (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj L N).hom.app U (AlgebraicGeometry.Scheme.Modules.moduleTensorSection a b) =
      AlgebraicGeometry.Scheme.Modules.tensorSections L N U a b := rfl

theorem IsFrame.tensorStalkEquivOfFrames_germ_frame {L N : X.Modules} {W : X.Opens} {e : Γ(L, W)} {f : Γ(N, W)}
    (he : IsFrame L W e) (hg : IsFrame N W f) {y : X} (hy : y ∈ W) :
    he.tensorStalkEquivOfFrames hg hy
        ((AlgebraicGeometry.Scheme.Modules.tensor L N).presheaf.germ W y hy
          (AlgebraicGeometry.Scheme.Modules.moduleTensorSection e f)) = 1 := by
  have step1 : moduleStalkLinearEquiv X y (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj L N)
      ((AlgebraicGeometry.Scheme.Modules.tensor L N).presheaf.germ W y hy
        (AlgebraicGeometry.Scheme.Modules.moduleTensorSection e f)) =
      (CategoryTheory.MonoidalCategoryStruct.tensorObj (C := X.Modules) L N).presheaf.germ W y hy
        (AlgebraicGeometry.Scheme.Modules.tensorSections L N W e f) :=
    moduleStalkLinearEquiv_germ X y (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj L N) W hy
      (AlgebraicGeometry.Scheme.Modules.moduleTensorSection e f)
  have step2 : tensorStalkEquiv L N y
      ((CategoryTheory.MonoidalCategoryStruct.tensorObj (C := X.Modules) L N).presheaf.germ W y hy
        (AlgebraicGeometry.Scheme.Modules.tensorSections L N W e f)) =
      (L.presheaf.germ W y hy) e ⊗ₜ[X.presheaf.stalk y] (N.presheaf.germ W y hy) f :=
    tensorStalkEquiv_germ_tensorSections L N y W hy e f
  unfold IsFrame.tensorStalkEquivOfFrames
  simp only [LinearEquiv.trans_apply]
  rw [step1, step2, TensorProduct.congr_tmul]
  have h1 : (he.stalkEquiv hy).symm (L.presheaf.germ W y hy e) = 1 := by
    rw [LinearEquiv.symm_apply_eq, IsFrame.stalkEquiv_apply, one_smul]
  have h2 : (hg.stalkEquiv hy).symm (N.presheaf.germ W y hy f) = 1 := by
    rw [LinearEquiv.symm_apply_eq, IsFrame.stalkEquiv_apply, one_smul]
  rw [h1, h2, TensorProduct.lid_tmul, one_smul]

/-- **Nonvanishing locus of a tensor product of line bundle sections** (pointwise version):
`y ∈ X_{s ⊗ t} ⟺ y ∈ X_s ∧ y ∈ X_t`. -/
theorem mem_nonvanishingLocus_sectionTensor (L N : X.Modules) [L.IsLineBundle] [N.IsLineBundle]
    (s : Γ(L, ⊤)) (t : Γ(N, ⊤)) (y : X) :
    y ∈ (AlgebraicGeometry.Scheme.Modules.tensor L N).nonvanishingLocus (sectionTensor s t) ↔
      y ∈ L.nonvanishingLocus s ∧ y ∈ N.nonvanishingLocus t := by
  obtain ⟨W₁, hy₁, e₁, he₁⟩ := AlgebraicGeometry.Scheme.Modules.exists_frame L y
  obtain ⟨W₂, hy₂, f₂, hf₂⟩ := AlgebraicGeometry.Scheme.Modules.exists_frame N y
  have hy : y ∈ W₁ ⊓ W₂ := ⟨hy₁, hy₂⟩
  have he : IsFrame L (W₁ ⊓ W₂) (L.res inf_le_left e₁) := he₁.restrict inf_le_left
  have hf : IsFrame N (W₁ ⊓ W₂) (N.res inf_le_right f₂) := hf₂.restrict inf_le_right
  -- s|_W = a • e, t|_W = b • f
  have hsa := he.coord_smul_frame le_rfl (L.res le_top s)
  rw [res_self] at hsa
  have htb := hf.coord_smul_frame le_rfl (N.res le_top t)
  rw [res_self] at htb
  -- (s ⊗ t)|_W = (a * b) • (e ⊗ f)
  have hst : (AlgebraicGeometry.Scheme.Modules.tensor L N).res le_top (sectionTensor s t) =
      (he.coord le_rfl (L.res le_top s) * hf.coord le_rfl (N.res le_top t)) •
        AlgebraicGeometry.Scheme.Modules.moduleTensorSection (L.res inf_le_left e₁) (N.res inf_le_right f₂) := by
    change (AlgebraicGeometry.Scheme.Modules.moduleTensor L N).presheaf.map (homOfLE le_top).op
      (AlgebraicGeometry.Scheme.Modules.moduleTensorSection s t) = _
    rw [AlgebraicGeometry.Scheme.Modules.moduleTensorSection_restrict]
    change AlgebraicGeometry.Scheme.Modules.moduleTensorSection (L.res le_top s) (N.res le_top t) = _
    conv_lhs => rw [← hsa, ← htb]
    rw [AlgebraicGeometry.Scheme.Modules.moduleTensorSection_smul]
  -- germ of s ⊗ t under Θ is the germ of a * b
  have hΘ : he.tensorStalkEquivOfFrames hf hy
      ((AlgebraicGeometry.Scheme.Modules.tensor L N).presheaf.germ ⊤ y trivial (sectionTensor s t)) =
        X.presheaf.germ (W₁ ⊓ W₂) y hy
          (he.coord le_rfl (L.res le_top s) * hf.coord le_rfl (N.res le_top t)) := by
    have hres : (AlgebraicGeometry.Scheme.Modules.tensor L N).presheaf.germ ⊤ y trivial (sectionTensor s t) =
        (AlgebraicGeometry.Scheme.Modules.tensor L N).presheaf.germ (W₁ ⊓ W₂) y hy
          ((AlgebraicGeometry.Scheme.Modules.tensor L N).res le_top (sectionTensor s t)) :=
      (TopCat.Presheaf.germ_res_apply (AlgebraicGeometry.Scheme.Modules.tensor L N).presheaf
        (homOfLE le_top) y hy (sectionTensor s t)).symm
    have hg : (AlgebraicGeometry.Scheme.Modules.tensor L N).presheaf.germ (W₁ ⊓ W₂) y hy
        ((he.coord le_rfl (L.res le_top s) * hf.coord le_rfl (N.res le_top t)) •
          AlgebraicGeometry.Scheme.Modules.moduleTensorSection (L.res inf_le_left e₁) (N.res inf_le_right f₂)) =
        X.presheaf.germ (W₁ ⊓ W₂) y hy
            (he.coord le_rfl (L.res le_top s) * hf.coord le_rfl (N.res le_top t)) •
          (AlgebraicGeometry.Scheme.Modules.tensor L N).presheaf.germ (W₁ ⊓ W₂) y hy
            (AlgebraicGeometry.Scheme.Modules.moduleTensorSection (L.res inf_le_left e₁) (N.res inf_le_right f₂)) :=
      germ_smul' (AlgebraicGeometry.Scheme.Modules.tensor L N) hy _ _
    rw [hres, hst, hg, LinearEquiv.map_smul, he.tensorStalkEquivOfFrames_germ_frame hf hy,
      smul_eq_mul, mul_one]
  have hT : y ∈ (AlgebraicGeometry.Scheme.Modules.tensor L N).nonvanishingLocus (sectionTensor s t) ↔
      ¬ (X.presheaf.germ (W₁ ⊓ W₂) y hy
          (he.coord le_rfl (L.res le_top s) * hf.coord le_rfl (N.res le_top t)) ∈
            IsLocalRing.maximalIdeal (X.presheaf.stalk y)) :=
    (mem_nonvanishingLocus _ _ _).trans (not_congr
      ((mem_maximalIdeal_smul_top_iff_of_linearEquiv (he.tensorStalkEquivOfFrames hf hy) _).trans
        (by rw [hΘ])))
  have hL : y ∈ L.nonvanishingLocus s ↔
      ¬ (X.presheaf.germ (W₁ ⊓ W₂) y hy (he.coord le_rfl (L.res le_top s)) ∈
          IsLocalRing.maximalIdeal (X.presheaf.stalk y)) :=
    (mem_nonvanishingLocus _ _ _).trans (not_congr (he.germ_mem_maximalIdeal_smul_iff_coord hy s))
  have hN : y ∈ N.nonvanishingLocus t ↔
      ¬ (X.presheaf.germ (W₁ ⊓ W₂) y hy (hf.coord le_rfl (N.res le_top t)) ∈
          IsLocalRing.maximalIdeal (X.presheaf.stalk y)) :=
    (mem_nonvanishingLocus _ _ _).trans (not_congr (hf.germ_mem_maximalIdeal_smul_iff_coord hy t))
  rw [hT, hL, hN, map_mul]
  simp only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not, IsUnit.mul_iff]

/-- **The nonvanishing locus of a tensor product of line bundle sections is the intersection of the
two nonvanishing loci**: `X_{s ⊗ t} = X_s ⊓ X_t`. -/
theorem nonvanishingLocus_sectionTensor (L N : X.Modules) [L.IsLineBundle] [N.IsLineBundle]
    (s : Γ(L, ⊤)) (t : Γ(N, ⊤)) :
    (AlgebraicGeometry.Scheme.Modules.tensor L N).nonvanishingLocus (sectionTensor s t) =
      L.nonvanishingLocus s ⊓ N.nonvanishingLocus t :=
  TopologicalSpace.Opens.ext (Set.ext fun y => by
    rw [SetLike.mem_coe, mem_nonvanishingLocus_sectionTensor]
    rfl)

end AlgebraicGeometry.Scheme.Modules

end
