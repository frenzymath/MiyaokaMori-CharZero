import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.SectionTensor
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.Frame
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleNonvanishingLocus
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.QcSectionsBasicOpenLocalization
import MiyaokaMori.AlgebraicGeometry.Modules.Stacks01q1_FrameChartBasicOpen
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.FrameTensorPowSection

/-! # Comparison on overlaps for Stacks 01PW(2)

The "comparison on overlaps" step of Stacks 01PW(2) (properties-lemma-invert-s-sections).

Setting: `L` a line bundle on `X`, `s ∈ Γ(X, L)`, `F` quasi-coherent, `t ∈ Γ(X_s, F)`. Two charts
`(W_x, e_x)`, `(W_y, e_y)` (frames of `L`), with `s|_{W_x} = f_x • e_x`, `s|_{W_y} = f_y • e_y`
(so `W_x ⊓ X_s = D(f_x)`, `W_y ⊓ X_s = D(f_y)`), and local lifts `a_x ∈ Γ(W_x, F)`,
`a_y ∈ Γ(W_y, F)` with `a_x|_{D(f_x)} = f_x^{n₀} • t|_{D(f_x)}`, `a_y|_{D(f_y)} = f_y^{n₀} • t|_{D(f_y)}`.
For every `M` the candidate sections of `F ⊗ L^{⊗(n₀+M)}` are
`g_x(M) := (f_x^M • a_x) ⊗ e_x^{⊗(n₀+M)}` and `g_y(M)` alike; they both restrict to
`t ⊗ s^{⊗(n₀+M)}` on `X_s`.

* `exists_pow_le_res_moduleTensorSection_eq_of_isAffineOpen`: on an affine `V ≤ W_x ⊓ W_y` there is
  `k` with `g_x(M)|_V = g_y(M)|_V` for all `M ≥ k`.
  Proof (self-contained). On `V` write `e_y = u • e_x` (`u := coord_{e_x}(e_y)`), so `f_y u = f_x`
  (frame injectivity) and `e_y^{⊗N} = u^N • e_x^{⊗N}` (`framePow_smul`). Hence
  `g_y(M)|_V = (u^{n₀+M} f_y^M • a_y) ⊗ e_x^{⊗N} = (f_x^M • (u^{n₀} • a_y)) ⊗ e_x^{⊗N}` and
  `g_x(M)|_V = (f_x^M • a_x) ⊗ e_x^{⊗N}`. Let `b := a_x|_V - u^{n₀} • a_y|_V ∈ Γ(V, F)`. On
  `D_V := V ⊓ X_s = D(f_x|_V)` both `a_x` and `u^{n₀} a_y` restrict to `f_x^{n₀} • t`
  (using `(u f_y)^{n₀} = f_x^{n₀}`), so `b|_{D_V} = 0`. `F` is quasi-coherent and `V` is affine, so
  `f_x^k • b = 0` for some `k` (Stacks 01I8: `Γ(D(f), F) = Γ(V, F)_f`,
  `exists_pow_smul_eq_zero_of_map_basicOpen_eq_zero`). For `M ≥ k`,
  `f_x^M • a_x - f_x^M • (u^{n₀} • a_y) = f_x^{M-k} • (f_x^k • b) = 0`, giving the claim.
* `exists_pow_le_res_moduleTensorSection_eq_of_isCompact`: if `W_x ⊓ W_y` is quasi-compact
  (true when `X` is quasi-separated and `W_x`, `W_y` affine), cover it by finitely many affine
  `V`, take the maximum of the `k`'s, and conclude by the separatedness of the sheaf
  `F ⊗ L^{⊗(n₀+M)}` (`TopCat.Sheaf.eq_of_locally_eq'`).

Reference: Stacks 01PW, proof of (2) ("a calculation shows ... `t_j` and `t_{j'}` agree on
`U_j ∩ U_{j'} ∩ X_s`, hence after multiplying by a power of `s`").
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- Restriction of sections of the structure sheaf composes. -/
theorem structurePresheaf_res_res {A B C : X.Opens} (h1 : A ≤ B) (h2 : B ≤ C) (r : Γ(X, C)) :
    X.presheaf.map (homOfLE h1).op (X.presheaf.map (homOfLE h2).op r) =
      X.presheaf.map (homOfLE (h1.trans h2)).op r := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

/-- If `s|_W = f • e` with `e` a frame on `W`, then `W ⊓ X_s = D(f)` (chart description of the
nonvanishing locus, `IsFrame.inf_nonvanishingLocus_eq_basicOpen` with the coordinate named). -/
theorem IsFrame.inf_nonvanishingLocus_eq_basicOpen_of_res_eq (L : X.Modules) [L.IsLineBundle]
    (s : Γ(L, ⊤)) {W : X.Opens} {e : Γ(L, W)} (hf : IsFrame L W e) {f : Γ(X, W)}
    (hs : L.res le_top s = f • e) :
    W ⊓ L.nonvanishingLocus s = X.basicOpen f := by
  rw [hf.inf_nonvanishingLocus_eq_basicOpen L s]
  congr 1
  apply hf.coord_unique
  rw [res_self]
  exact hs.symm

/-- Restricting a chart `s|_W = f • e` to `V ≤ W`. -/
theorem res_top_eq_res_smul_res {L : X.Modules} (s : Γ(L, ⊤)) {W V : X.Opens} (hV : V ≤ W)
    {f : Γ(X, W)} {e : Γ(L, W)} (hs : L.res le_top s = f • e) :
    L.res le_top s = X.presheaf.map (homOfLE hV).op f • L.res hV e := by
  rw [← res_smul, ← hs, res_res]

/-- **Overlap comparison, affine case** (Stacks 01PW(2), "a calculation shows"): on an affine open
`V ≤ W_x ⊓ W_y` the two candidate sections `(f_x^M • a_x) ⊗ e_x^{⊗(n₀+M)}` and
`(f_y^M • a_y) ⊗ e_y^{⊗(n₀+M)}` agree for all `M ≥ k`, for some `k`. See the module docstring for
the proof. -/
theorem exists_pow_le_res_moduleTensorSection_eq_of_isAffineOpen
    (F : X.Modules) [F.IsQuasicoherent] (L : X.Modules) [L.IsLineBundle] (s : Γ(L, ⊤))
    (t : Γ(F, L.nonvanishingLocus s))
    {Wx Wy V : X.Opens} (hV : IsAffineOpen V) (hVx : V ≤ Wx) (hVy : V ≤ Wy)
    {ex : Γ(L, Wx)} (hfx : IsFrame L Wx ex) {ey : Γ(L, Wy)} (hfy : IsFrame L Wy ey)
    {fx : Γ(X, Wx)} (hsx : L.res le_top s = fx • ex) {fy : Γ(X, Wy)} (hsy : L.res le_top s = fy • ey)
    (hDx : X.basicOpen fx ≤ L.nonvanishingLocus s) (hDy : X.basicOpen fy ≤ L.nonvanishingLocus s)
    (n₀ : ℕ) (ax : Γ(F, Wx)) (ay : Γ(F, Wy))
    (hax : F.res (X.basicOpen_le fx) ax =
      (X.presheaf.map (homOfLE (X.basicOpen_le fx)).op fx) ^ n₀ • F.res hDx t)
    (hay : F.res (X.basicOpen_le fy) ay =
      (X.presheaf.map (homOfLE (X.basicOpen_le fy)).op fy) ^ n₀ • F.res hDy t) :
    ∃ k : ℕ, ∀ M : ℕ, k ≤ M →
      (AlgebraicGeometry.Scheme.Modules.tensor F
          (AlgebraicGeometry.Scheme.Modules.tensorPow L (n₀ + M))).res hVx
          (AlgebraicGeometry.Scheme.Modules.moduleTensorSection (fx ^ M • ax) (framePow ex (n₀ + M))) =
        (AlgebraicGeometry.Scheme.Modules.tensor F
          (AlgebraicGeometry.Scheme.Modules.tensorPow L (n₀ + M))).res hVy
          (AlgebraicGeometry.Scheme.Modules.moduleTensorSection (fy ^ M • ay) (framePow ey (n₀ + M))) := by
  -- restricted charts on `V`
  set exV : Γ(L, V) := L.res hVx ex with hexV
  set eyV : Γ(L, V) := L.res hVy ey with heyV
  set fxV : Γ(X, V) := X.presheaf.map (homOfLE hVx).op fx with hfxV
  set fyV : Γ(X, V) := X.presheaf.map (homOfLE hVy).op fy with hfyV
  have hfrx : IsFrame L V exV := hfx.restrict hVx
  have hsxV : L.res le_top s = fxV • exV := res_top_eq_res_smul_res s hVx hsx
  have hsyV : L.res le_top s = fyV • eyV := res_top_eq_res_smul_res s hVy hsy
  -- the unit `u` with `e_y = u • e_x` on `V`, and `f_y u = f_x`
  set u : Γ(X, V) := hfrx.coord le_rfl eyV with hudef
  have hu : eyV = u • exV := by
    have h := hfrx.coord_smul_frame le_rfl eyV
    rw [res_self] at h
    exact h.symm
  have hfu : fyV * u = fxV := by
    apply (hfrx V le_rfl).1
    show (fyV * u) • L.res le_rfl exV = fxV • L.res le_rfl exV
    rw [res_self, mul_smul, ← hu, ← hsyV, hsxV]
  -- `D_V := D(f_x|_V) = V ⊓ X_s`
  have hDV : V ⊓ L.nonvanishingLocus s = X.basicOpen fxV :=
    hfrx.inf_nonvanishingLocus_eq_basicOpen_of_res_eq L s hsxV
  have hDVs : X.basicOpen fxV ≤ L.nonvanishingLocus s := by
    rw [← hDV]; exact inf_le_right
  have hDVV : X.basicOpen fxV ≤ V := X.basicOpen_le fxV
  have hDVx : X.basicOpen fxV ≤ X.basicOpen fx := by
    rw [← hDV, ← hfx.inf_nonvanishingLocus_eq_basicOpen_of_res_eq L s hsx]
    exact inf_le_inf_right _ hVx
  have hDVy : X.basicOpen fxV ≤ X.basicOpen fy := by
    rw [← hDV, ← hfy.inf_nonvanishingLocus_eq_basicOpen_of_res_eq L s hsy]
    exact inf_le_inf_right _ hVy
  -- `b := a_x|_V - u^{n₀} • a_y|_V` vanishes on `D_V`
  set b : Γ(F, V) := F.res hVx ax - u ^ n₀ • F.res hVy ay with hbdef
  have hfDV : X.presheaf.map (homOfLE hDVV).op fxV =
      X.presheaf.map (homOfLE (hDVV.trans hVx)).op fx :=
    structurePresheaf_res_res hDVV hVx fx
  have hb1 : F.res hDVV (F.res hVx ax) =
      (X.presheaf.map (homOfLE hDVV).op fxV) ^ n₀ • F.res hDVs t := by
    have h := congrArg (F.res hDVx) hax
    rw [res_res, res_smul, map_pow, res_res, structurePresheaf_res_res] at h
    rw [res_res, hfDV]
    exact h
  have hb2 : F.res hDVV (u ^ n₀ • F.res hVy ay) =
      (X.presheaf.map (homOfLE hDVV).op fxV) ^ n₀ • F.res hDVs t := by
    have h := congrArg (F.res hDVy) hay
    rw [res_res, res_smul, map_pow, res_res, structurePresheaf_res_res] at h
    rw [res_smul, map_pow, res_res]
    have h' : F.res (hDVV.trans hVy) ay =
        (X.presheaf.map (homOfLE (hDVV.trans hVy)).op fy) ^ n₀ • F.res hDVs t := h
    rw [h', smul_smul, ← mul_pow, ← structurePresheaf_res_res hDVV hVy fy, ← map_mul, mul_comm,
      hfu]
  have hb : F.res hDVV b = 0 := by
    change F.presheaf.map (homOfLE hDVV).op (F.res hVx ax - u ^ n₀ • F.res hVy ay) = 0
    rw [map_sub]
    change F.res hDVV (F.res hVx ax) - F.res hDVV (u ^ n₀ • F.res hVy ay) = 0
    rw [hb1, hb2, sub_self]
  -- quasi-coherence on the affine `V`: `f_x^k • b = 0`
  obtain ⟨k, hk⟩ := F.exists_pow_smul_eq_zero_of_map_basicOpen_eq_zero hV fxV b hb
  refine ⟨k, fun M hM => ?_⟩
  -- restrict both candidate sections to `V`
  have hL : (AlgebraicGeometry.Scheme.Modules.tensor F
        (AlgebraicGeometry.Scheme.Modules.tensorPow L (n₀ + M))).res hVx
        (AlgebraicGeometry.Scheme.Modules.moduleTensorSection (fx ^ M • ax) (framePow ex (n₀ + M))) =
      AlgebraicGeometry.Scheme.Modules.moduleTensorSection (fxV ^ M • F.res hVx ax) (framePow exV (n₀ + M)) := by
    show (AlgebraicGeometry.Scheme.Modules.moduleTensor F (AlgebraicGeometry.Scheme.Modules.tensorPow L (n₀ + M))).presheaf.map
      (homOfLE hVx).op (AlgebraicGeometry.Scheme.Modules.moduleTensorSection (fx ^ M • ax) (framePow ex (n₀ + M))) = _
    rw [AlgebraicGeometry.Scheme.Modules.moduleTensorSection_restrict]
    change AlgebraicGeometry.Scheme.Modules.moduleTensorSection (F.res hVx (fx ^ M • ax))
      ((AlgebraicGeometry.Scheme.Modules.tensorPow L (n₀ + M)).res hVx (framePow ex (n₀ + M))) = _
    rw [framePow_res, res_smul, map_pow]
  have hR : (AlgebraicGeometry.Scheme.Modules.tensor F
        (AlgebraicGeometry.Scheme.Modules.tensorPow L (n₀ + M))).res hVy
        (AlgebraicGeometry.Scheme.Modules.moduleTensorSection (fy ^ M • ay) (framePow ey (n₀ + M))) =
      AlgebraicGeometry.Scheme.Modules.moduleTensorSection (u ^ (n₀ + M) • fyV ^ M • F.res hVy ay)
        (framePow exV (n₀ + M)) := by
    show (AlgebraicGeometry.Scheme.Modules.moduleTensor F (AlgebraicGeometry.Scheme.Modules.tensorPow L (n₀ + M))).presheaf.map
      (homOfLE hVy).op (AlgebraicGeometry.Scheme.Modules.moduleTensorSection (fy ^ M • ay) (framePow ey (n₀ + M))) = _
    rw [AlgebraicGeometry.Scheme.Modules.moduleTensorSection_restrict]
    change AlgebraicGeometry.Scheme.Modules.moduleTensorSection (F.res hVy (fy ^ M • ay))
      ((AlgebraicGeometry.Scheme.Modules.tensorPow L (n₀ + M)).res hVy (framePow ey (n₀ + M))) = _
    rw [framePow_res, res_smul, map_pow]
    change AlgebraicGeometry.Scheme.Modules.moduleTensorSection (fyV ^ M • F.res hVy ay) (framePow eyV (n₀ + M)) = _
    rw [hu, framePow_smul, moduleTensorSection_smul_right, ← moduleTensorSection_smul_left]
  -- the first factors agree for `M ≥ k`
  have hkey : fxV ^ M • F.res hVx ax = u ^ (n₀ + M) • fyV ^ M • F.res hVy ay := by
    have h1 : u ^ (n₀ + M) • fyV ^ M • F.res hVy ay = fxV ^ M • (u ^ n₀ • F.res hVy ay) := by
      rw [smul_smul, smul_smul]
      congr 1
      rw [pow_add, ← hfu, mul_pow]
      ring
    rw [h1, ← sub_eq_zero, ← smul_sub]
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hM
    rw [add_comm, pow_add, mul_smul]
    change fxV ^ d • fxV ^ k • b = 0
    rw [hk, smul_zero]
  rw [hL, hR, hkey]

/-- **Overlap comparison, quasi-compact case** (Stacks 01PW(2)): if `W_x ⊓ W_y` is quasi-compact,
the two candidate sections agree on `W_x ⊓ W_y` for all `M ≥ k`, for some `k`. Cover
`W_x ⊓ W_y` by finitely many affine opens, apply the affine case on each, take the maximum `k`,
and use separatedness of the sheaf `F ⊗ L^{⊗(n₀+M)}`. -/
theorem exists_pow_le_res_moduleTensorSection_eq_of_isCompact
    (F : X.Modules) [F.IsQuasicoherent] (L : X.Modules) [L.IsLineBundle] (s : Γ(L, ⊤))
    (t : Γ(F, L.nonvanishingLocus s))
    {Wx Wy : X.Opens} (hU : IsCompact ((Wx ⊓ Wy : X.Opens) : Set X))
    {ex : Γ(L, Wx)} (hfx : IsFrame L Wx ex) {ey : Γ(L, Wy)} (hfy : IsFrame L Wy ey)
    {fx : Γ(X, Wx)} (hsx : L.res le_top s = fx • ex) {fy : Γ(X, Wy)} (hsy : L.res le_top s = fy • ey)
    (hDx : X.basicOpen fx ≤ L.nonvanishingLocus s) (hDy : X.basicOpen fy ≤ L.nonvanishingLocus s)
    (n₀ : ℕ) (ax : Γ(F, Wx)) (ay : Γ(F, Wy))
    (hax : F.res (X.basicOpen_le fx) ax =
      (X.presheaf.map (homOfLE (X.basicOpen_le fx)).op fx) ^ n₀ • F.res hDx t)
    (hay : F.res (X.basicOpen_le fy) ay =
      (X.presheaf.map (homOfLE (X.basicOpen_le fy)).op fy) ^ n₀ • F.res hDy t) :
    ∃ k : ℕ, ∀ M : ℕ, k ≤ M →
      (AlgebraicGeometry.Scheme.Modules.tensor F
          (AlgebraicGeometry.Scheme.Modules.tensorPow L (n₀ + M))).res
          (inf_le_left : Wx ⊓ Wy ≤ Wx)
          (AlgebraicGeometry.Scheme.Modules.moduleTensorSection (fx ^ M • ax) (framePow ex (n₀ + M))) =
        (AlgebraicGeometry.Scheme.Modules.tensor F
          (AlgebraicGeometry.Scheme.Modules.tensorPow L (n₀ + M))).res
          (inf_le_right : Wx ⊓ Wy ≤ Wy)
          (AlgebraicGeometry.Scheme.Modules.moduleTensorSection (fy ^ M • ay) (framePow ey (n₀ + M))) := by
  classical
  have hVz : ∀ z ∈ ((Wx ⊓ Wy : X.Opens) : Set X),
      ∃ V : X.Opens, IsAffineOpen V ∧ z ∈ V ∧ V ≤ Wx ⊓ Wy := by
    intro z hz
    obtain ⟨V, hV, hzV, hVU⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hz
    exact ⟨V, hV, hzV, hVU⟩
  choose V hVaff hzV hVU using hVz
  have hk : ∀ z (hz : z ∈ ((Wx ⊓ Wy : X.Opens) : Set X)), ∃ k : ℕ, ∀ M : ℕ, k ≤ M →
      (AlgebraicGeometry.Scheme.Modules.tensor F
          (AlgebraicGeometry.Scheme.Modules.tensorPow L (n₀ + M))).res
          ((hVU z hz).trans inf_le_left)
          (AlgebraicGeometry.Scheme.Modules.moduleTensorSection (fx ^ M • ax) (framePow ex (n₀ + M))) =
        (AlgebraicGeometry.Scheme.Modules.tensor F
          (AlgebraicGeometry.Scheme.Modules.tensorPow L (n₀ + M))).res
          ((hVU z hz).trans inf_le_right)
          (AlgebraicGeometry.Scheme.Modules.moduleTensorSection (fy ^ M • ay) (framePow ey (n₀ + M))) :=
    fun z hz => exists_pow_le_res_moduleTensorSection_eq_of_isAffineOpen F L s t (hVaff z hz)
      ((hVU z hz).trans inf_le_left) ((hVU z hz).trans inf_le_right) hfx hfy hsx hsy hDx hDy
      n₀ ax ay hax hay
  choose k hk using hk
  obtain ⟨tV, htV⟩ := hU.elim_nhds_subcover' (fun z hz => ((V z hz : X.Opens) : Set X))
    (fun z hz => (V z hz).isOpen.mem_nhds (hzV z hz))
  refine ⟨tV.sup (fun z => k z.1 z.2), fun M hM => ?_⟩
  let G := AlgebraicGeometry.Scheme.Modules.tensor F
    (AlgebraicGeometry.Scheme.Modules.tensorPow L (n₀ + M))
  let Sh : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨G.val.presheaf, G.isSheaf⟩
  have hcover : Wx ⊓ Wy ≤ ⨆ z : tV, V z.1.1 z.1.2 := by
    intro y hy
    have hy' := htV hy
    rw [Set.mem_iUnion₂] at hy'
    obtain ⟨z, hz, hyz⟩ := hy'
    exact Opens.mem_iSup.mpr ⟨⟨z, hz⟩, hyz⟩
  refine Sh.eq_of_locally_eq' (fun z : tV => V z.1.1 z.1.2) (Wx ⊓ Wy)
    (fun z => homOfLE (hVU z.1.1 z.1.2)) hcover _ _ (fun z => ?_)
  have hkz : k z.1.1 z.1.2 ≤ M :=
    le_trans (Finset.le_sup (f := fun z : ↥((Wx ⊓ Wy : X.Opens) : Set X) => k z.1 z.2) z.2) hM
  have h := hk z.1.1 z.1.2 M hkz
  exact Eq.trans (res_res G (hVU z.1.1 z.1.2) inf_le_left _)
    (Eq.trans h (res_res G (hVU z.1.1 z.1.2) inf_le_right _).symm)

end AlgebraicGeometry.Scheme.Modules

end
