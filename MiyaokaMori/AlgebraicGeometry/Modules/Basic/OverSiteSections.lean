import MiyaokaMori.Prelude

/-! # Sections of sheaves of modules on a general site

**Section-level toolkit for sheaves of modules on a general site, specialised to the sites
`(Opens X).over U` used by Mathlib's `SheafOfModules.IsFinitePresentation` / `QuasicoherentData`.**

Mathlib defines finite presentation of `F : X.Modules` through presentations of `F.over U`, a sheaf of
modules on the site `Over U` (`SheafOfModules.over`). The section-level lemmas of this library
(`epi_iff_locally_surjective_sections`, `KernelSections`, `FreeModuleStalkBasisSpan.section_decomp`, …)
are stated only for `X.Modules`; this module provides the same facts for an arbitrary site `J` on a
category `C : Type u` (sheaves of `R`-modules with `HasSheafify J AddCommGrpCat`,
`J.WEqualsLocallyBijective AddCommGrpCat`) and the bridge to `X`:

* generic (`SheafOfModules` namespace):
  - `imageSieve_mem_of_epi`: `Epi φ` ⇒ the image sieve of every section is covering
    (`toSheaf` preserves finite colimits via the sheafification adjunction, hence epis;
    `Sheaf.isLocallySurjective_iff_epi'`);
  - `freeE I i W = (freeSection i).val (op W)` (standard sections), `freeCoord I i : free I ⟶ unit`
    (coordinate projections, `Cofan.IsColimit.desc`), `free_section_eq_sum` (`I` finite: every section is
    `Σ_i coord_i(u) • e_i`), `freeCoord_app_sum` (coefficient extraction), `free_map_sum` (restriction of a
    combination), `GeneratingSections.π_app_sum` (`π (Σ c_i e_i) = Σ c_i s_i`);
  - `kernel_ι_val_app_*`: sections of `kernel f` are the kernel of `f` on sections
    (`SheafOfModules.evaluation` preserves kernels; same proofs as `KernelSections`);
* scheme-specific (`AlgebraicGeometry.Scheme.Modules` namespace): `ov h : Over U` for `h : W ≤ U`
  (sections of `F.over U` at `ov h` are **definitionally** `Γ(F, W)`), `over_epi_locally_surjective`
  (covering sieves of `J.over U` unwound to points via `GrothendieckTopology.mem_over_iff`,
  `Opens.mem_grothendieckTopology`, `Sieve.overEquiv_iff`), `exists_mem_of_coversTop`,
  `over_π_app_sum` (the formula for `π = freeHomEquiv.symm s` on `Σ c_i e_i` in terms of `Γ(F, W)`).

References: Stacks 01AG (epi of sheaves = locally surjective), 01AH (kernels of sheaves are computed on
sections), 01AI (sections of finite direct sums); Mathlib `Algebra/Category/ModuleCat/Sheaf/{Free,Generators,
Limits,Abelian}.lean`, `CategoryTheory/Sites/{Over,EpiMono,LocallySurjective}.lean`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace SheafOfModules

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}

/-! ### Sections of `unit R` -/

/-- A ring section viewed as a section of `unit R` (definitionally the same element). -/
def uSec (W : C) (r : R.obj.obj (op W)) : (unit R).val.obj (op W) := r

/-- A section of `unit R` viewed as a ring section (definitionally the same element). -/
def ofUSec (W : C) (t : (unit R).val.obj (op W)) : R.obj.obj (op W) := t

@[simp] lemma uSec_ofUSec (W : C) (t : (unit R).val.obj (op W)) : uSec W (ofUSec W t) = t := rfl

@[simp] lemma ofUSec_uSec (W : C) (r : R.obj.obj (op W)) : ofUSec (R := R) W (uSec W r) = r := rfl

lemma uSec_eq_smul (W : C) (r : R.obj.obj (op W)) : uSec (R := R) W r = r • uSec W 1 :=
  (mul_one r).symm

lemma uSec_smul (W : C) (d r : R.obj.obj (op W)) : uSec (R := R) W (d • r) = d • uSec W r := rfl

/-- `uSec` as an additive map. -/
def uSecAddHom (W : C) : R.obj.obj (op W) →+ (unit R).val.obj (op W) where
  toFun := uSec W
  map_zero' := rfl
  map_add' _ _ := rfl

lemma uSec_sum {ι : Type*} (W : C) (s : Finset ι) (f : ι → R.obj.obj (op W)) :
    uSec (R := R) W (∑ i ∈ s, f i) = ∑ i ∈ s, uSec W (f i) :=
  map_sum (uSecAddHom W) f s

/-! ### Sections of a kernel (same proofs as `KernelSections`, any site) -/

section kernel

variable {M N : SheafOfModules.{u} R} (f : M ⟶ N) (W : C)

/-- `kernel.ι f` is injective on sections: `kernel.ι` is a mono, `SheafOfModules.forget` preserves
limits hence monos, and monos of presheaves of modules are injective on sections. -/
theorem kernel_ι_val_app_injective :
    Function.Injective ((kernel.ι f).val.app (op W)).hom := by
  have hmono : Mono (kernel.ι f) := equalizer.ι_mono
  have : Mono (kernel.ι f).val :=
    @Functor.map_mono _ _ _ _ (SheafOfModules.forget _) inferInstance _ _ (kernel.ι f) hmono
  intro a b hab
  exact PresheafOfModules.injective_of_mono (kernel.ι f).val (op W) hab

/-- Sections of the kernel are killed by `f` (`kernel.condition` on sections). -/
theorem kernel_ι_val_app_apply_eq_zero (x : (kernel f).val.obj (op W)) :
    f.val.app (op W) ((kernel.ι f).val.app (op W) x) = 0 := by
  have h : kernel.ι f ≫ f = 0 := kernel.condition f
  exact congrArg (fun g : kernel f ⟶ N => g.val.app (op W) x) h

/-- `f y = 0` ⇒ `y` comes from `(kernel f)(W)`: `SheafOfModules.evaluation` preserves kernels
(`PreservesKernel.iso`) and kernels in `ModuleCat` are `LinearMap.ker` (`ModuleCat.kernelIsoKer`). -/
theorem exists_kernel_ι_val_app_eq (y : M.val.obj (op W)) (hy : f.val.app (op W) y = 0) :
    ∃ x : (kernel f).val.obj (op W), (kernel.ι f).val.app (op W) x = y := by
  have hGa : (SheafOfModules.evaluation R (op W)).Additive :=
    inferInstanceAs (SheafOfModules.forget R ⋙ PresheafOfModules.evaluation R.obj (op W)).Additive
  have hGf : ((SheafOfModules.evaluation R (op W)).map f).hom y = 0 := hy
  let z : ((kernel ((SheafOfModules.evaluation R (op W)).map f) : ModuleCat.{u} (R.obj.obj (op W))) : Type u) :=
    (ModuleCat.kernelIsoKer ((SheafOfModules.evaluation R (op W)).map f)).inv.hom ⟨y, hGf⟩
  refine ⟨(PreservesKernel.iso (SheafOfModules.evaluation R (op W)) f).inv.hom z, ?_⟩
  have h1 := congrArg (fun φ : kernel ((SheafOfModules.evaluation R (op W)).map f) ⟶
      (SheafOfModules.evaluation R (op W)).obj M => φ.hom z)
    (PreservesKernel.iso_inv_ι (SheafOfModules.evaluation R (op W)) f)
  have h3 := ModuleCat.kernelIsoKer_inv_kernel_ι_apply ((SheafOfModules.evaluation R (op W)).map f) ⟨y, hGf⟩
  simp only [ModuleCat.hom_comp] at h1
  exact h1.trans h3

end kernel

variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-! ### Epimorphisms are locally surjective -/

/-- `toSheaf` preserves finite colimits: it is (up to the natural isomorphism
`sheafificationCompToSheaf`) the composite of the sheafification adjunction's right adjoint with the
left adjoint sheafification (same argument as `FreeModuleStalkBasisSpan.toSheaf_preservesFiniteColimits`,
here for an arbitrary site in universe `u`). -/
lemma toSheaf_preservesFiniteColimits' :
    PreservesFiniteColimits (SheafOfModules.toSheaf.{u} R) := by
  constructor
  intro K _ _
  apply (Adjunction.preservesColimitsOfShape_iff
    (PresheafOfModules.sheafificationAdjunction.{u} (𝟙 R.obj))
    (SheafOfModules.toSheaf.{u} R) K).mpr
  exact preservesColimitsOfShape_of_natIso
    (PresheafOfModules.sheafificationCompToSheaf.{u} (𝟙 R.obj)).symm

/-- **Epi ⇒ locally surjective on sections**: for `φ : M ⟶ N` an epimorphism of sheaves of modules and
`t ∈ N(W)`, the sieve of arrows `V ⟶ W` along which `t` restricts into the image of `φ` is covering. -/
theorem imageSieve_mem_of_epi {M N : SheafOfModules.{u} R} (φ : M ⟶ N) [Epi φ]
    {W : C} (t : N.val.obj (op W)) :
    Presheaf.imageSieve ((SheafOfModules.toSheaf R).map φ).hom t ∈ J W := by
  have := toSheaf_preservesFiniteColimits' (R := R)
  have hepi : Epi ((SheafOfModules.toSheaf.{u} R).map φ) :=
    (SheafOfModules.toSheaf.{u} R).map_epi φ
  have hloc : Sheaf.IsLocallySurjective ((SheafOfModules.toSheaf.{u} R).map φ) :=
    (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat.{u} _).mpr hepi
  have hloc' : Presheaf.IsLocallySurjective J ((SheafOfModules.toSheaf.{u} R).map φ).hom := hloc
  exact @Presheaf.imageSieve_mem _ _ J _ _ _ _ _ _ ((SheafOfModules.toSheaf R).obj M).obj
    ((SheafOfModules.toSheaf R).obj N).obj ((SheafOfModules.toSheaf R).map φ).hom hloc' (op W) t

/-! ### Sections of a finite free sheaf -/

/-- The standard section `e_i` of `free I` over `W`. -/
abbrev freeE (I : Type u) (i : I) (W : C) : (free (R := R) I).val.obj (op W) :=
  (freeSection (R := R) i).val (op W)

open Classical in
/-- The `i`-th coordinate projection `free I ⟶ unit R` (`e_j ↦ δ_{ij}`). -/
def freeCoord (I : Type u) (i : I) : free (R := R) I ⟶ unit R :=
  Cofan.IsColimit.desc (isColimitFreeCofan (R := R) I) (fun j => if j = i then 𝟙 _ else 0)

open Classical in
lemma ιFree_freeCoord (I : Type u) (i j : I) :
    ιFree j ≫ freeCoord (R := R) I i = if j = i then 𝟙 _ else 0 :=
  Cofan.IsColimit.fac (isColimitFreeCofan (R := R) I) _ _

lemma freeE_eq (I : Type u) (i : I) (W : C) :
    freeE (R := R) I i W = (ιFree i).val.app (op W) (uSec W 1) := by
  simp [freeE, freeSection, freeHomEquiv]
  rfl

lemma ιFree_app (I : Type u) (i : I) (W : C) (r : R.obj.obj (op W)) :
    (ιFree (R := R) i).val.app (op W) (uSec W r) = r • freeE (R := R) I i W := by
  rw [freeE_eq, uSec_eq_smul]
  exact map_smul ((ιFree (R := R) i).val.app (op W)).hom r (uSec W 1)

lemma freeE_map (I : Type u) (i : I) {W W' : C} (f : W' ⟶ W) :
    (free (R := R) I).val.map f.op (freeE I i W) = freeE I i W' :=
  PresheafOfModules.sections_property (freeSection (R := R) i) f.op

/-- `φ ↦ φ.val.app (op W)` is additive. -/
def appAddHom (M N : SheafOfModules.{u} R) (W : C) :
    (M ⟶ N) →+ (M.val.obj (op W) →+ N.val.obj (op W)) where
  toFun φ := (φ.val.app (op W)).hom
  map_zero' := rfl
  map_add' _ _ := rfl

open Classical in
lemma freeCoord_app_freeE (I : Type u) (i j : I) (W : C) :
    (freeCoord (R := R) I i).val.app (op W) (freeE I j W) = if j = i then uSec W 1 else 0 := by
  have h := congrArg (fun φ => appAddHom _ _ W φ (uSec W 1)) (ιFree_freeCoord (R := R) I i j)
  rw [freeE_eq]
  refine Eq.trans ?_ (h.trans ?_)
  · rfl
  · split_ifs <;> rfl

open Classical in
lemma id_free_eq_sum (I : Type u) [Fintype I] :
    𝟙 (free (R := R) I) = ∑ i, freeCoord I i ≫ ιFree i := by
  refine Cofan.IsColimit.hom_ext (isColimitFreeCofan (R := R) I) _ _ (fun k => ?_)
  change ιFree k ≫ 𝟙 _ = ιFree k ≫ _
  rw [Preadditive.comp_sum, Category.comp_id]
  have h : ∀ i, ιFree k ≫ freeCoord (R := R) I i ≫ ιFree i = if k = i then ιFree i else 0 := by
    intro i
    rw [← Category.assoc, ιFree_freeCoord]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl fun i _ => h i]
  simp

/-- **Sections of a finite free sheaf are combinations of the standard sections**:
`u = Σ_i coord_i(u) • e_i`. -/
lemma free_section_eq_sum (I : Type u) [Fintype I] (W : C) (u : (free (R := R) I).val.obj (op W)) :
    u = ∑ i, ofUSec W ((freeCoord I i).val.app (op W) u) • freeE I i W := by
  have h := congrArg (fun φ => appAddHom _ _ W φ u) (id_free_eq_sum (R := R) I)
  simp only [map_sum, AddMonoidHom.finsetSum_apply] at h
  refine h.trans (Finset.sum_congr rfl fun i _ => ?_)
  rw [← ιFree_app, uSec_ofUSec]
  rfl

/-- Coefficient extraction: `coord_j (Σ_i c_i • e_i) = c_j`. -/
lemma freeCoord_app_sum (I : Type u) [Fintype I] (W : C) (c : I → R.obj.obj (op W)) (j : I) :
    (freeCoord (R := R) I j).val.app (op W) (∑ i, c i • freeE I i W) = uSec W (c j) := by
  classical
  rw [map_sum]
  simp only [map_smul, freeCoord_app_freeE]
  rw [Finset.sum_eq_single j]
  · rw [if_pos rfl]; exact (uSec_eq_smul W (c j)).symm
  · intro i _ hij; rw [if_neg hij, smul_zero]
  · intro h; exact absurd (Finset.mem_univ j) h

/-- Coefficient extraction from a double sum `Σ_j d_j • Σ_i b_{j i} • e_i`. -/
lemma freeCoord_app_sum_smul_sum (I : Type u) [Fintype I] {I' : Type u} [Fintype I'] (W : C)
    (d : I' → R.obj.obj (op W)) (b : I' → I → R.obj.obj (op W)) (i : I) :
    (freeCoord (R := R) I i).val.app (op W) (∑ j, d j • ∑ i', b j i' • freeE I i' W) =
      uSec W (∑ j, d j • b j i) := by
  rw [map_sum, uSec_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [_root_.map_smul ((freeCoord (R := R) I i).val.app (op W)).hom, freeCoord_app_sum, uSec_smul]

/-- Restriction of a combination of standard sections: `(free I).map f (Σ c_i • e_i) = Σ (R.map f c_i) • e_i`. -/
lemma free_map_sum (I : Type u) [Fintype I] {W W' : C} (f : W' ⟶ W) (c : I → R.obj.obj (op W)) :
    (free (R := R) I).val.map f.op (∑ i, c i • freeE I i W) =
      ∑ i, R.obj.map f.op (c i) • freeE I i W' := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [PresheafOfModules.map_smul, freeE_map]
  rfl

/-- `π = freeHomEquiv.symm s` sends `e_i` to `s i` on sections. -/
lemma freeHomEquiv_symm_app_freeE {M : SheafOfModules.{u} R} {I : Type u} (s : I → M.sections)
    (i : I) (W : C) :
    (M.freeHomEquiv.symm s).val.app (op W) (freeE I i W) = (s i).val (op W) := by
  have h : M.freeHomEquiv (M.freeHomEquiv.symm s) i = s i := by
    rw [Equiv.apply_symm_apply]
  rw [freeHomEquiv_apply] at h
  exact congrArg (fun σ : M.sections => σ.val (op W)) h

/-- `π = freeHomEquiv.symm s` on a combination of standard sections. -/
lemma freeHomEquiv_symm_app_sum {M : SheafOfModules.{u} R} {I : Type u} [Fintype I]
    (s : I → M.sections) (W : C) (c : I → R.obj.obj (op W)) :
    (M.freeHomEquiv.symm s).val.app (op W) (∑ i, c i • freeE I i W) =
      ∑ i, c i • PresheafOfModules.sections.eval (s i) (op W) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [_root_.map_smul ((M.freeHomEquiv.symm s).val.app (op W)).hom, freeHomEquiv_symm_app_freeE]

/-- `sections_property` written with `sections.eval` (so that both sides live in the `ModuleCat` carrier
`M.val.obj Y`, not in `(M.val.presheaf ⋙ forget Ab).obj Y`; this matters for `rw` when `M` is a kernel). -/
lemma sections_eval_map {M : SheafOfModules.{u} R} (s : M.sections) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    M.val.map f (PresheafOfModules.sections.eval s X) = PresheafOfModules.sections.eval s Y :=
  PresheafOfModules.sections_property s f

/-- `σ.π (Σ c_i • e_i) = Σ c_i • σ.s i` for generating sections `σ` (syntactic form with `σ.π`). -/
lemma GeneratingSections.π_app_sum {M : SheafOfModules.{u} R} (σ : M.GeneratingSections) [Fintype σ.I]
    (W : C) (c : σ.I → R.obj.obj (op W)) :
    σ.π.val.app (op W) (∑ i, c i • freeE σ.I i W) =
      ∑ i, c i • PresheafOfModules.sections.eval (σ.s i) (op W) :=
  freeHomEquiv_symm_app_sum σ.s W c

end SheafOfModules

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

/-! ### The site `(Opens X).over U` -/

/-- `W ≤ U` as an object of `Over U`. Sections of `F.over U` at `ov h` are definitionally `Γ(F, W)`,
and `(F.over U).val.map (ovHom h h').op` is definitionally `F.presheaf.map (homOfLE h').op`. -/
abbrev ov {U W : X.Opens} (h : W ≤ U) : Over U := Over.mk (homOfLE h)

/-- `W' ≤ W ≤ U` as a morphism `ov (h'.trans h) ⟶ ov h` of `Over U`. -/
abbrev ovHom {U W W' : X.Opens} (h : W ≤ U) (h' : W' ≤ W) : ov (h'.trans h) ⟶ ov h :=
  Over.homMk (homOfLE h')

/-- `W ≤ U` as a morphism `ov hW ⟶ ov (le_refl U)` of `Over U` (syntactically with source `ov hW`). -/
abbrev ovHomTop {U W : X.Opens} (hW : W ≤ U) : ov hW ⟶ ov (le_refl U) := Over.homMk (homOfLE hW)

/-- A section of `O_X` over `W ≤ U` as a section of the ring sheaf `O_X.over U` at `ov hW`
(definitionally the same element). -/
def toOv {U W : X.Opens} (hW : W ≤ U) (c : Γ(X, W)) : (X.ringCatSheaf.over U).obj.obj (op (ov hW)) := c

/-- Inverse of `toOv`. -/
def fromOv {U W : X.Opens} (hW : W ≤ U) (c : (X.ringCatSheaf.over U).obj.obj (op (ov hW))) : Γ(X, W) := c

@[simp] lemma toOv_fromOv {U W : X.Opens} (hW : W ≤ U) (c : (X.ringCatSheaf.over U).obj.obj (op (ov hW))) :
    toOv hW (fromOv hW c) = c := rfl

@[simp] lemma fromOv_toOv {U W : X.Opens} (hW : W ≤ U) (c : Γ(X, W)) : fromOv hW (toOv hW c) = c := rfl

/-- Restriction in the ring sheaf `O_X.over U` is restriction in `O_X`. -/
lemma over_ring_map_apply {U W W' : X.Opens} (hW : W ≤ U) (hW' : W' ≤ W) (c : Γ(X, W)) :
    (X.ringCatSheaf.over U).obj.map (ovHom hW hW').op (toOv hW c) =
      toOv (hW'.trans hW) (X.presheaf.map (homOfLE hW').op c) := rfl

/-- **Epimorphisms of sheaves of modules on `Over U` are locally surjective on sections**, pointwise:
for `t` a section of `B` over `W ≤ U` and `y ∈ W` there is `y ∈ W' ≤ W` and `u ∈ A(W')` with
`φ u = t|_{W'}`. Proof: `imageSieve_mem_of_epi` gives a covering sieve of `J.over U`; a sieve of
`J.over U` covers iff its transport to `Opens X` covers (`GrothendieckTopology.mem_over_iff`), which is
read pointwise by `Opens.mem_grothendieckTopology` and translated back by `Sieve.overEquiv_iff`. -/
theorem over_epi_locally_surjective {U : X.Opens} {A B : SheafOfModules.{u} (X.ringCatSheaf.over U)}
    (φ : A ⟶ B) [Epi φ] {W : X.Opens} (hW : W ≤ U) (t : B.val.obj (op (ov hW))) (y : X) (hy : y ∈ W) :
    ∃ (W' : X.Opens) (hW' : W' ≤ W), y ∈ W' ∧ ∃ u : A.val.obj (op (ov (hW'.trans hW))),
      φ.val.app (op (ov (hW'.trans hW))) u = B.val.map (ovHom hW hW').op t := by
  have hmem := SheafOfModules.imageSieve_mem_of_epi φ t
  rw [GrothendieckTopology.mem_over_iff, Opens.mem_grothendieckTopology] at hmem
  obtain ⟨V, f, hf, hyV⟩ := hmem y hy
  rw [Sieve.overEquiv_iff] at hf
  obtain ⟨u, hu⟩ := hf
  exact ⟨V, leOfHom f, hyV, u, hu⟩

/-- A family covering the terminal object of `Opens X` covers every point (`Opens.coversTop_iff`). -/
theorem exists_mem_of_coversTop {ι : Type*} (V : ι → X.Opens)
    (h : (Opens.grothendieckTopology X).CoversTop V) (x : X) : ∃ i, x ∈ V i := by
  rw [Opens.coversTop_iff] at h
  have hx : x ∈ (⨆ i, V i : X.Opens) := by rw [h]; trivial
  exact Opens.mem_iSup.mp hx

/-- Sections of `F.over U` restrict like sections of `F`: the value at `ov hW` is the restriction of
the value at `ov (le_refl U)` (i.e. over `U`). -/
lemma over_sections_val (F : X.Modules) {U : X.Opens} (σ : (F.over U).sections) {W : X.Opens} (hW : W ≤ U) :
    σ.val (op (ov hW)) = F.presheaf.map (homOfLE hW).op (σ.val (op (ov (le_refl U)))) :=
  (PresheafOfModules.sections_property σ (ovHom (le_refl U) hW).op).symm

/-- `π = σ.π` for `σ : (F.over U).GeneratingSections`, on a combination of standard sections over `W ≤ U`,
written with sections of `F`: `π (Σ c_i • e_i) = Σ c_i • (σ.s i)|_W`. -/
lemma over_π_app_sum (F : X.Modules) {U : X.Opens} (σ : (F.over U).GeneratingSections) [Fintype σ.I]
    {W : X.Opens} (hW : W ≤ U) (c : σ.I → (X.ringCatSheaf.over U).obj.obj (op (ov hW))) :
    σ.π.val.app (op (ov hW)) (∑ i, c i • SheafOfModules.freeE (R := X.ringCatSheaf.over U) σ.I i (ov hW)) =
      ∑ i, fromOv hW (c i) • F.presheaf.map (homOfLE hW).op ((σ.s i).val (op (ov (le_refl U)))) := by
  change ((F.over U).freeHomEquiv.symm σ.s).val.app (op (ov hW)) _ = _
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [_root_.map_smul (((F.over U).freeHomEquiv.symm σ.s).val.app (op (ov hW))).hom,
    SheafOfModules.freeHomEquiv_symm_app_freeE, over_sections_val F (σ.s i) hW]
  rfl

lemma presheaf_map_le_refl (F : X.Modules) (U : X.Opens) (t : Γ(F, U)) :
    F.presheaf.map (homOfLE (le_refl U)).op t = t := by
  change F.presheaf.map (𝟙 (op U)) t = t
  rw [F.presheaf.map_id]
  rfl

end AlgebraicGeometry.Scheme.Modules

end
