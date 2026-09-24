import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.SectionTensor
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleNonvanishingLocus
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensor
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorPower
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.QcSectionsBasicOpenLocalization
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.Frame
import MiyaokaMori.AlgebraicGeometry.Modules.Stacks01q1_FrameChartBasicOpen
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.FrameTensorPowSection
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.InvertSectionsOverlapComparison

/-! # Sections over the nonvanishing locus of a section of an invertible sheaf (Stacks 01PW)

Stacks 01PW: for `X` quasi-compact quasi-separated, `L` invertible, `s ∈ Γ(X,L)` and `F` quasi-coherent,
every section `t` of `F` over `X_s` has the form `m ⊗ s^{−n}`: there are `n` and `m ∈ Γ(X, F ⊗ L^{⊗n})`
with `m|_{X_s} = t ⊗ s^n|_{X_s}` ((2), surjectivity); for `X` quasi-compact, if `m ∈ Γ(X,F)` vanishes on
`X_s` then `m ⊗ s^e = 0` for some `e` ((1), injectivity). In particular `Γ_*(X,L)_{(s)} ≅ Γ(X_s,O_X)`.

Reference: Stacks 01PW (`properties-lemma-invert-s-sections`).

Proof. Charts: every `x ∈ X` has an affine open `W`
with a frame `e` of `L` (`exists_affine_frame_le`); writing `s|_W = f • e` with `f := coord_e(s|_W)`
we get `W ⊓ X_s = D(f)` (`IsFrame.inf_nonvanishingLocus_eq_basicOpen`). By quasi-compactness
finitely many such charts `W_x` (`x ∈ T`) cover `X`.

(1) `m|_{X_s} = 0`. On each chart `m|_{D(f_x)} = 0`, and `F` is quasi-coherent on the affine `W_x`,
so `f_x^{k_x} • m|_{W_x} = 0` (`exists_pow_smul_eq_zero_of_map_basicOpen_eq_zero`, Stacks 01I8).
With `e := max k_x`: `(m ⊗ s^{⊗e})|_{W_x} = m|_{W_x} ⊗ f_x^e e_x^{⊗e} = (f_x^e • m|_{W_x}) ⊗ e_x^{⊗e} = 0`
(`res_tensorPowSection_eq_pow_smul_framePow`), so `m ⊗ s^{⊗e} = 0` by separatedness.

(2) `t ∈ Γ(X_s, F)`. On each chart, `t|_{D(f_x)} = t'_x / f_x^{n_x}` with `t'_x ∈ Γ(W_x, F)`
(`exists_pow_smul_eq_map_basicOpen`). With `n₀ := max n_x` and `a_x := f_x^{n₀-n_x} • t'_x` we have
`a_x|_{D(f_x)} = f_x^{n₀} • t|_{D(f_x)}`. For `M ≥ 0` the candidate sections of `F ⊗ L^{⊗(n₀+M)}` on
`W_x` are `g_x(M) := (f_x^M • a_x) ⊗ e_x^{⊗(n₀+M)}`; they restrict to `t ⊗ s^{⊗(n₀+M)}` on `D(f_x)`.
Since `X` is quasi-separated, `W_x ⊓ W_y` is quasi-compact, and
`exists_pow_le_res_moduleTensorSection_eq_of_isCompact` (module `Stacks01pw_Overlap`) gives `k_{xy}`
such that `g_x(M)` and `g_y(M)` agree on `W_x ⊓ W_y` for `M ≥ k_{xy}` (the difference of the first
factors vanishes on `X_s`, hence is killed by a power of `f_x` by quasi-coherence). With
`M := max k_{xy}` the `g_x(M)` glue (`TopCat.Sheaf.existsUnique_gluing'`) to
`m ∈ Γ(X, F ⊗ L^{⊗(n₀+M)})`, and `m|_{X_s} = t ⊗ s^{⊗(n₀+M)}|_{X_s}` since both agree on every
`D(f_x)`, which cover `X_s`.

Differences from the Stacks text: we do not form the graded module `Γ_*(X, L, F)` nor identify
`(F ⊗ L^{⊗n}) ⊗ L^{⊗e}` with `F ⊗ L^{⊗(n+e)}`; the exponent is raised directly on the affine pieces
(where the sections are pure tensors with the frame power as second factor), so no rearrangement
isomorphism is needed.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- Affine charts with frames of a line bundle exist at every point. -/
theorem exists_affine_isFrame (L : X.Modules) [L.IsLineBundle] (x : X) :
    ∃ (W : X.Opens) (e : Γ(L, W)), IsAffineOpen W ∧ x ∈ W ∧ IsFrame L W e := by
  obtain ⟨W, hW, -, hxW, e, hf⟩ := exists_affine_frame_le L (U := ⊤) (p := x) trivial
  exact ⟨W, e, hW, hxW, hf⟩

/-- A finite family of opens covering `X` covers `⊤`. -/
theorem top_le_iSup_of_subset_biUnion {W : X → X.Opens} (T : Finset X)
    (hT : (Set.univ : Set X) ⊆ ⋃ x ∈ T, ((W x : X.Opens) : Set X)) :
    (⊤ : X.Opens) ≤ ⨆ x : T, W x.1 := by
  intro y _
  have hy := hT (Set.mem_univ y)
  rw [Set.mem_iUnion₂] at hy
  obtain ⟨x, hx, hyx⟩ := hy
  exact Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hyx⟩

end AlgebraicGeometry.Scheme.Modules

/- Stacks 01PW(2): for `X` quasi-compact quasi-separated, a section `t` of a quasi-coherent sheaf over `X_s`,
   multiplied by a sufficiently high power of `s`, extends to a global section
   (`m ∈ Γ(X, F ⊗ L^{⊗n})`, `m|_{X_s} = t ⊗ s^{⊗n}|_{X_s}`; tensor sections are `moduleTensorSection`,
   `Modules.tensor` is `moduleTensor`, and `s^{⊗n}` is `tensorPowSection`). -/

theorem AlgebraicGeometry.Scheme.Modules.exists_tensorPow_section_restrict_eq
    {X : AlgebraicGeometry.Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    (L : X.Modules) [L.IsLineBundle] (s : Γ(L, ⊤)) (F : X.Modules) [F.IsQuasicoherent]
    (t : Γ(F, L.nonvanishingLocus s)) :
    ∃ (n : ℕ) (m : Γ(AlgebraicGeometry.Scheme.Modules.tensor F
        (AlgebraicGeometry.Scheme.Modules.tensorPow L n), ⊤)),
      (AlgebraicGeometry.Scheme.Modules.tensor F
          (AlgebraicGeometry.Scheme.Modules.tensorPow L n)).presheaf.map
          (CategoryTheory.homOfLE (le_top : L.nonvanishingLocus s ≤ ⊤)).op m =
        AlgebraicGeometry.Scheme.Modules.moduleTensorSection t
          ((AlgebraicGeometry.Scheme.Modules.tensorPow L n).presheaf.map
            (CategoryTheory.homOfLE (le_top : L.nonvanishingLocus s ≤ ⊤)).op
            (AlgebraicGeometry.Scheme.Modules.tensorPowSection s n)) := by
  classical
  open AlgebraicGeometry.Scheme.Modules in
  -- charts
  choose W e hW hxW hf using exists_affine_isFrame L
  let f : ∀ x : X, Γ(X, W x) := fun x => (hf x).coord le_rfl (L.res le_top s)
  have hs : ∀ x, L.res le_top s = f x • e x := fun x => (hf x).res_top_eq_coord_smul s
  have hD : ∀ x, W x ⊓ L.nonvanishingLocus s = X.basicOpen (f x) := fun x =>
    (hf x).inf_nonvanishingLocus_eq_basicOpen L s
  have hDs : ∀ x, X.basicOpen (f x) ≤ L.nonvanishingLocus s := fun x => by
    rw [← hD x]; exact inf_le_right
  -- local lifts of `t` on the charts
  have hlift : ∀ x, ∃ (n : ℕ) (t' : Γ(F, W x)), F.res (X.basicOpen_le (f x)) t' =
      (X.presheaf.map (homOfLE (X.basicOpen_le (f x))).op (f x)) ^ n • F.res (hDs x) t :=
    fun x => F.exists_pow_smul_eq_map_basicOpen (hW x) (f x) (F.res (hDs x) t)
  choose n t' ht' using hlift
  -- finite subcover
  obtain ⟨T, -, hT⟩ := isCompact_univ.elim_nhds_subcover (fun x => ((W x : X.Opens) : Set X))
    (fun x _ => (W x).isOpen.mem_nhds (hxW x))
  have hcover : (⊤ : X.Opens) ≤ ⨆ x : T, W x.1 := top_le_iSup_of_subset_biUnion T hT
  -- common exponent `n₀`, normalized lifts `a₀ x`
  let n₀ : ℕ := T.sup n
  let a₀ : ∀ x : X, Γ(F, W x) := fun x => (f x) ^ (n₀ - n x) • t' x
  have ha₀ : ∀ x ∈ T, F.res (X.basicOpen_le (f x)) (a₀ x) =
      (X.presheaf.map (homOfLE (X.basicOpen_le (f x))).op (f x)) ^ n₀ • F.res (hDs x) t := by
    intro x hx
    have hnx : n₀ - n x + n x = n₀ := Nat.sub_add_cancel (Finset.le_sup (f := n) hx)
    show F.res (X.basicOpen_le (f x)) ((f x) ^ (n₀ - n x) • t' x) = _
    rw [res_smul, map_pow, ht' x, smul_smul, ← pow_add, hnx]
  -- overlaps
  have hov : ∀ x ∈ T, ∀ y ∈ T, ∃ k : ℕ, ∀ M : ℕ, k ≤ M →
      (AlgebraicGeometry.Scheme.Modules.tensor F
          (AlgebraicGeometry.Scheme.Modules.tensorPow L (n₀ + M))).res
          (inf_le_left : W x ⊓ W y ≤ W x)
          (AlgebraicGeometry.Scheme.Modules.moduleTensorSection ((f x) ^ M • a₀ x) (framePow (e x) (n₀ + M))) =
        (AlgebraicGeometry.Scheme.Modules.tensor F
          (AlgebraicGeometry.Scheme.Modules.tensorPow L (n₀ + M))).res
          (inf_le_right : W x ⊓ W y ≤ W y)
          (AlgebraicGeometry.Scheme.Modules.moduleTensorSection ((f y) ^ M • a₀ y) (framePow (e y) (n₀ + M))) := by
    intro x hx y hy
    exact exists_pow_le_res_moduleTensorSection_eq_of_isCompact F L s t
      (QuasiSeparatedSpace.inter_isCompact _ _ (W x).isOpen (hW x).isCompact (W y).isOpen
        (hW y).isCompact)
      (hf x) (hf y) (hs x) (hs y) (hDs x) (hDs y) n₀ (a₀ x) (a₀ y) (ha₀ x hx) (ha₀ y hy)
  choose! k hk using hov
  let M : ℕ := (T ×ˢ T).sup (fun p : X × X => k p.1 p.2)
  let G := AlgebraicGeometry.Scheme.Modules.tensor F
    (AlgebraicGeometry.Scheme.Modules.tensorPow L (n₀ + M))
  let g : ∀ x : X, Γ(G, W x) := fun x =>
    AlgebraicGeometry.Scheme.Modules.moduleTensorSection ((f x) ^ M • a₀ x) (framePow (e x) (n₀ + M))
  let Sh : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨G.val.presheaf, G.isSheaf⟩
  -- gluing
  have hcompat : TopCat.Presheaf.IsCompatible Sh.1 (fun x : T => W x.1) (fun x => g x.1) := by
    intro i j
    have hkM : k i.1 j.1 ≤ M :=
      Finset.le_sup (f := fun p : X × X => k p.1 p.2) (b := (i.1, j.1))
        (Finset.mem_product.mpr ⟨i.2, j.2⟩)
    exact hk i.1 i.2 j.1 j.2 M hkM
  obtain ⟨m, hm, -⟩ := Sh.existsUnique_gluing' (fun x : T => W x.1) ⊤ (fun x => homOfLE le_top)
    hcover (fun x => g x.1) hcompat
  refine ⟨n₀ + M, m, ?_⟩
  -- `m|_{X_s} = t ⊗ s^{⊗(n₀+M)}`: check on the cover `D(f x)` of `X_s`
  have hcover' : L.nonvanishingLocus s ≤ ⨆ x : T, X.basicOpen (f x.1) := by
    intro y hy
    have hy' := hT (Set.mem_univ y)
    rw [Set.mem_iUnion₂] at hy'
    obtain ⟨x, hx, hyx⟩ := hy'
    refine Opens.mem_iSup.mpr ⟨⟨x, hx⟩, ?_⟩
    rw [← hD x]
    exact ⟨hyx, hy⟩
  refine Sh.eq_of_locally_eq' (fun x : T => X.basicOpen (f x.1)) (L.nonvanishingLocus s)
    (fun x => homOfLE (hDs x.1)) hcover' _ _ (fun x => ?_)
  have hmx : G.res le_top m = g x.1 := hm x
  have h1 : G.res (hDs x.1) (G.res le_top m) = G.res (X.basicOpen_le (f x.1)) (g x.1) := by
    rw [← hmx]
    exact (res_res G (hDs x.1) le_top m).trans (res_res G (X.basicOpen_le (f x.1)) le_top m).symm
  have hsD : L.res le_top s = X.presheaf.map (homOfLE (X.basicOpen_le (f x.1))).op (f x.1) •
      L.res (X.basicOpen_le (f x.1)) (e x.1) :=
    res_top_eq_res_smul_res s (X.basicOpen_le (f x.1)) (hs x.1)
  have hexp : M + n₀ = n₀ + M := add_comm _ _
  change G.res (hDs x.1) (G.res le_top m) = G.res (hDs x.1) (AlgebraicGeometry.Scheme.Modules.moduleTensorSection t
    ((AlgebraicGeometry.Scheme.Modules.tensorPow L (n₀ + M)).res le_top
      (AlgebraicGeometry.Scheme.Modules.tensorPowSection s (n₀ + M))))
  rw [h1]
  show (AlgebraicGeometry.Scheme.Modules.moduleTensor F (AlgebraicGeometry.Scheme.Modules.tensorPow L (n₀ + M))).presheaf.map
      (homOfLE (X.basicOpen_le (f x.1))).op
      (AlgebraicGeometry.Scheme.Modules.moduleTensorSection ((f x.1) ^ M • a₀ x.1) (framePow (e x.1) (n₀ + M))) =
    (AlgebraicGeometry.Scheme.Modules.moduleTensor F (AlgebraicGeometry.Scheme.Modules.tensorPow L (n₀ + M))).presheaf.map
      (homOfLE (hDs x.1)).op (AlgebraicGeometry.Scheme.Modules.moduleTensorSection t
        ((AlgebraicGeometry.Scheme.Modules.tensorPow L (n₀ + M)).res le_top
          (AlgebraicGeometry.Scheme.Modules.tensorPowSection s (n₀ + M))))
  rw [AlgebraicGeometry.Scheme.Modules.moduleTensorSection_restrict, AlgebraicGeometry.Scheme.Modules.moduleTensorSection_restrict]
  change AlgebraicGeometry.Scheme.Modules.moduleTensorSection (F.res (X.basicOpen_le (f x.1)) ((f x.1) ^ M • a₀ x.1))
      ((AlgebraicGeometry.Scheme.Modules.tensorPow L (n₀ + M)).res (X.basicOpen_le (f x.1))
        (framePow (e x.1) (n₀ + M))) =
    AlgebraicGeometry.Scheme.Modules.moduleTensorSection (F.res (hDs x.1) t)
      ((AlgebraicGeometry.Scheme.Modules.tensorPow L (n₀ + M)).res (hDs x.1)
        ((AlgebraicGeometry.Scheme.Modules.tensorPow L (n₀ + M)).res le_top
          (AlgebraicGeometry.Scheme.Modules.tensorPowSection s (n₀ + M))))
  have hres2 : (AlgebraicGeometry.Scheme.Modules.tensorPow L (n₀ + M)).res (hDs x.1)
      ((AlgebraicGeometry.Scheme.Modules.tensorPow L (n₀ + M)).res le_top
        (AlgebraicGeometry.Scheme.Modules.tensorPowSection s (n₀ + M))) =
      (AlgebraicGeometry.Scheme.Modules.tensorPow L (n₀ + M)).res le_top
        (AlgebraicGeometry.Scheme.Modules.tensorPowSection s (n₀ + M)) :=
    res_res _ _ _ _
  rw [framePow_res, res_smul, map_pow, ha₀ x.1 x.2, smul_smul, ← pow_add, hexp, hres2,
    res_tensorPowSection_eq_pow_smul_framePow s _ _ hsD (n₀ + M), moduleTensorSection_smul_right,
    ← moduleTensorSection_smul_left]

/- Stacks 01PW(1): for `X` quasi-compact, a global section vanishing on `X_s` is killed by some power of `s`. -/

theorem AlgebraicGeometry.Scheme.Modules.exists_sectionTensor_tensorPowSection_eq_zero
    {X : AlgebraicGeometry.Scheme.{u}} [CompactSpace X]
    (L : X.Modules) [L.IsLineBundle] (s : Γ(L, ⊤)) (F : X.Modules) [F.IsQuasicoherent]
    (m : Γ(F, ⊤))
    (hm : F.presheaf.map (CategoryTheory.homOfLE (le_top : L.nonvanishingLocus s ≤ ⊤)).op m = 0) :
    ∃ e : ℕ, sectionTensor m (AlgebraicGeometry.Scheme.Modules.tensorPowSection s e) = 0 := by
  classical
  open AlgebraicGeometry.Scheme.Modules in
  choose W e hW hxW hf using exists_affine_isFrame L
  let f : ∀ x : X, Γ(X, W x) := fun x => (hf x).coord le_rfl (L.res le_top s)
  have hs : ∀ x, L.res le_top s = f x • e x := fun x => (hf x).res_top_eq_coord_smul s
  have hD : ∀ x, W x ⊓ L.nonvanishingLocus s = X.basicOpen (f x) := fun x =>
    (hf x).inf_nonvanishingLocus_eq_basicOpen L s
  have hDs : ∀ x, X.basicOpen (f x) ≤ L.nonvanishingLocus s := fun x => by
    rw [← hD x]; exact inf_le_right
  -- `m` vanishes on each `D(f x)`
  have hmD : ∀ x, F.res (X.basicOpen_le (f x)) (F.res le_top m) = 0 := by
    intro x
    have h : F.res (hDs x) (F.res le_top m) = 0 := by
      change F.presheaf.map (homOfLE (hDs x)).op (F.presheaf.map (homOfLE le_top).op m) = 0
      rw [hm, map_zero]
    rw [res_res] at h ⊢
    exact h
  have hk : ∀ x, ∃ k : ℕ, (f x) ^ k • F.res le_top m = 0 := fun x =>
    F.exists_pow_smul_eq_zero_of_map_basicOpen_eq_zero (hW x) (f x) _ (hmD x)
  choose k hk using hk
  obtain ⟨T, -, hT⟩ := isCompact_univ.elim_nhds_subcover (fun x => ((W x : X.Opens) : Set X))
    (fun x _ => (W x).isOpen.mem_nhds (hxW x))
  have hcover : (⊤ : X.Opens) ≤ ⨆ x : T, W x.1 := top_le_iSup_of_subset_biUnion T hT
  refine ⟨T.sup k, ?_⟩
  let G := AlgebraicGeometry.Scheme.Modules.tensor F
    (AlgebraicGeometry.Scheme.Modules.tensorPow L (T.sup k))
  let Sh : TopCat.Sheaf AddCommGrpCat.{u} X := ⟨G.val.presheaf, G.isSheaf⟩
  refine Sh.eq_of_locally_eq' (fun x : T => W x.1) ⊤ (fun x => homOfLE le_top) hcover _ 0
    (fun x => ?_)
  change G.res le_top (sectionTensor m (AlgebraicGeometry.Scheme.Modules.tensorPowSection s (T.sup k))) =
    G.presheaf.map (homOfLE le_top).op 0
  rw [map_zero]
  show (AlgebraicGeometry.Scheme.Modules.moduleTensor F (AlgebraicGeometry.Scheme.Modules.tensorPow L (T.sup k))).presheaf.map
    (homOfLE le_top).op (AlgebraicGeometry.Scheme.Modules.moduleTensorSection m
      (AlgebraicGeometry.Scheme.Modules.tensorPowSection s (T.sup k))) = 0
  have hr := AlgebraicGeometry.Scheme.Modules.moduleTensorSection_restrict (M := F)
    (N := AlgebraicGeometry.Scheme.Modules.tensorPow L (T.sup k)) (homOfLE (le_top : W x.1 ≤ ⊤)) m
    (AlgebraicGeometry.Scheme.Modules.tensorPowSection s (T.sup k))
  rw [hr]
  change AlgebraicGeometry.Scheme.Modules.moduleTensorSection (F.res le_top m)
    ((AlgebraicGeometry.Scheme.Modules.tensorPow L (T.sup k)).res le_top
      (AlgebraicGeometry.Scheme.Modules.tensorPowSection s (T.sup k))) = 0
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (Finset.le_sup (f := k) x.2)
  rw [res_tensorPowSection_eq_pow_smul_framePow s _ _ (hs x.1) (T.sup k), moduleTensorSection_smul_right,
    ← moduleTensorSection_smul_left, hd, add_comm, pow_add, mul_smul, hk x.1, smul_zero,
    AlgebraicGeometry.Scheme.Modules.moduleTensorSection_zero_left]

end
