import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.TrivialLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModuleSheafStalk
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModuleSheafStalkStmt
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.Frame
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle

/-! # The nonvanishing locus of a section of a line bundle

The nonvanishing locus `X_s = {x | s_x ∉ m_x L_x}` of a global section `s` of a line bundle `L`
(Stacks 01CY): it is open, and on `X_s` the section `s` trivializes `L`; on a chart `L|_U ≅ O_U` with
`s = f·e`, `X_s ∩ U` is `D(f)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- Germs are compatible with scalar multiplication (`PresheafOfModules.germ_smul` for sheaves of modules). -/
theorem germ_smul' (M : X.Modules) {V : X.Opens} {y : X} (hy : y ∈ V) (r : Γ(X, V)) (m : Γ(M, V)) :
    M.presheaf.germ V y hy (r • m) = X.presheaf.germ V y hy r • M.presheaf.germ V y hy m :=
  PresheafOfModules.germ_smul (R := X.presheaf) M.val y V hy r m

/-- The germ of a frame spans the stalk: every element of the stalk is the germ of a section over some
`V ≤ W`, and that section is a multiple of `e|_V`. -/
theorem IsFrame.span_germ_eq_top {M : X.Modules} {W : X.Opens} {e : Γ(M, W)}
    (hf : IsFrame M W e) {y : X} (hy : y ∈ W) :
    Submodule.span (X.presheaf.stalk y)
      ({(M.presheaf.germ W y hy e : ↥(M.stalk y))} : Set ↥(M.stalk y)) = ⊤ := by
  rw [eq_top_iff]
  rintro m -
  obtain ⟨V, hVW, hyV, t, rfl⟩ := M.presheaf.exists_le_germ_eq m hy
  have ht : t = hf.coord hVW t • M.res hVW e := (hf.coord_smul_frame hVW t).symm
  rw [ht, germ_smul', TopCat.Presheaf.germ_res_apply]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

/-- **The germ of a frame does not lie in `𝔪_y · M_y`** (Nakayama for one generator): if `e_y ∈ 𝔪_y • ⊤`,
then `span {e_y} = ⊤` gives `e_y = a • e_y` (`a ∈ 𝔪_y`), so `(1 - a) • e_y = 0` with `1 - a` a unit, hence
`e_y = 0`; a vanishing germ gives `e|_{W'} = 0` on some neighbourhood `W'`, and the bijection `r ↦ r • 0`
given by the frame on `W'` forces `Γ(X, W')` to be trivial; taking germs, `(1 : 𝒪_{X,y}) = 0`,
contradicting the nontriviality of the local ring. -/
theorem IsFrame.germ_notMem_maximalIdeal_smul {M : X.Modules} {W : X.Opens} {e : Γ(M, W)}
    (hf : IsFrame M W e) {y : X} (hy : y ∈ W) :
    M.presheaf.germ W y hy e ∉
      (IsLocalRing.maximalIdeal (X.presheaf.stalk y)) •
        (⊤ : Submodule (X.presheaf.stalk y) (M.stalk y)) := by
  intro hmem
  rw [← hf.span_germ_eq_top hy] at hmem
  obtain ⟨a, ha, hae'⟩ :=
    (Submodule.mem_smul_span_singleton (M := ↥(M.stalk y))).mp hmem
  have hu : IsUnit (1 - a) :=
    IsLocalRing.isUnit_one_sub_self_of_mem_nonunits a ((IsLocalRing.mem_maximalIdeal a).mp ha)
  have hz : (1 - a) • (M.presheaf.germ W y hy e : ↥(M.stalk y)) = 0 := by
    rw [sub_smul, one_smul]
    exact sub_eq_zero_of_eq hae'.symm
  have hey : (M.presheaf.germ W y hy e : ↥(M.stalk y)) = 0 := by
    obtain ⟨u, hu'⟩ := hu
    have h2 : ((u⁻¹ : (X.presheaf.stalk y)ˣ) : X.presheaf.stalk y) •
        ((1 - a) • (M.presheaf.germ W y hy e : ↥(M.stalk y))) = 0 := by
      rw [hz, smul_zero]
    rwa [smul_smul, ← hu', Units.inv_mul, one_smul] at h2
  have hzero : M.presheaf.germ W y hy e = M.presheaf.germ W y hy 0 := by
    rw [map_zero]; exact hey
  obtain ⟨W', hyW', iU, iV, hW'⟩ := M.presheaf.germ_eq y hy hy e 0 hzero
  rw [map_zero] at hW'
  have hres : M.res (leOfHom iU) e = 0 := hW'
  have hfr : IsFrame M W' (M.res (leOfHom iU) e) := hf.restrict (leOfHom iU)
  have h10 : (1 : Γ(X, W')) = 0 := (hfr W' le_rfl).1 (by simp [res_self, hres])
  have h1 := congrArg (X.presheaf.germ W' y hyW') h10
  simp at h1

/-- **The nonvanishing locus is open** (Stacks 01CY). Take a frame `(W, e)` at `x` and let `f :=` the
coordinate of `s|_W` in this frame; for `y ∈ W`, `s_y = f_y · e_y`. Then `X.basicOpen f`
(= `{y ∈ W | f_y is a unit}`, open) contains `x` and is contained in the nonvanishing locus: if `f_y` is a
unit then `e_y = f_y⁻¹ · s_y`, and `s_y ∈ 𝔪_y L_y` would give `e_y ∈ 𝔪_y L_y`, contradicting
`IsFrame.germ_notMem_maximalIdeal_smul`; conversely, if `f_x` is not a unit then `f_x ∈ 𝔪_x` and
`s_x = f_x · e_x ∈ 𝔪_x L_x`. -/
theorem isOpen_setOf_germ_notMem_maximalIdeal_smul (L : X.Modules) [L.IsLineBundle] (s : Γ(L, ⊤)) :
    IsOpen {x : X | L.presheaf.germ ⊤ x trivial s ∉
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) •
        (⊤ : Submodule (X.presheaf.stalk x) (L.stalk x))} := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨W, hxW, e, hf⟩ := exists_frame L x
  set f : Γ(X, W) := hf.coord le_rfl (L.res le_top s) with hfdef
  have hse : L.res le_top s = f • e := by
    have h := hf.coord_smul_frame le_rfl (L.res le_top s)
    rw [res_self] at h
    exact h.symm
  have key : ∀ (y : X) (hy : y ∈ W),
      L.presheaf.germ ⊤ y trivial s = X.presheaf.germ W y hy f • L.presheaf.germ W y hy e := by
    intro y hy
    have h0 : L.presheaf.germ W y hy (L.res le_top s) = L.presheaf.germ ⊤ y trivial s :=
      TopCat.Presheaf.germ_res_apply _ _ _ _ _
    rw [← h0, hse, germ_smul']
  refine ⟨(X.basicOpen f : Set X), ?_, (X.basicOpen f).isOpen, ?_⟩
  · intro y hy
    have hyW : y ∈ W := X.basicOpen_le f hy
    obtain ⟨u, hu'⟩ := (X.mem_basicOpen f y hyW).mp hy
    intro hcon
    refine hf.germ_notMem_maximalIdeal_smul hyW ?_
    have he : L.presheaf.germ W y hyW e =
        (↑u⁻¹ : X.presheaf.stalk y) • L.presheaf.germ ⊤ y trivial s := by
      rw [key y hyW, ← hu', smul_smul, Units.inv_mul, one_smul]
    rw [he]
    exact Submodule.smul_mem _ _ hcon
  · rw [SetLike.mem_coe, X.mem_basicOpen f x hxW]
    by_contra hnu
    refine hx ?_
    rw [key x hxW]
    exact Submodule.smul_mem_smul (N := (⊤ : Submodule (X.presheaf.stalk x) (L.stalk x)))
      ((IsLocalRing.mem_maximalIdeal _).mpr hnu) Submodule.mem_top

end AlgebraicGeometry.Scheme.Modules

open AlgebraicGeometry in

/-- `X_s = {x | s_x ∉ m_x L_x}`; openness is `isOpen_setOf_germ_notMem_maximalIdeal_smul` (Stacks 01CY). -/
noncomputable def AlgebraicGeometry.Scheme.Modules.nonvanishingLocus {X : AlgebraicGeometry.Scheme.{u}}
    (L : X.Modules) [L.IsLineBundle] (s : Γ(L, ⊤)) : X.Opens :=
  ⟨{x | TopCat.Presheaf.germ L.presheaf ⊤ x trivial s ∉
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) • (⊤ : Submodule (X.presheaf.stalk x) (L.stalk x))},
    AlgebraicGeometry.Scheme.Modules.isOpen_setOf_germ_notMem_maximalIdeal_smul L s⟩

open AlgebraicGeometry in

theorem AlgebraicGeometry.Scheme.Modules.mem_nonvanishingLocus {X : AlgebraicGeometry.Scheme.{u}}
    (L : X.Modules) [L.IsLineBundle] (s : Γ(L, ⊤)) (x : X) :
    x ∈ L.nonvanishingLocus s ↔
      TopCat.Presheaf.germ L.presheaf ⊤ x trivial s ∉
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) • (⊤ : Submodule (X.presheaf.stalk x) (L.stalk x)) :=
  Iff.rfl

end
