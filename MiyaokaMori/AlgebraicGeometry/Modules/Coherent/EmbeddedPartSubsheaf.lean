import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModulesStalkExact
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModulesStalkFunctor
import MiyaokaMori.AlgebraicGeometry.Modules.Coherent.ModuleSupportGenericPoints

/-! # The embedded part of a coherent sheaf

The subsheaf `K ⊆ F` of Stacks 02OL, constructed directly on the scheme:

`Γ(U, K) := {s ∈ Γ(U, F) | ∀ y ∈ genericPoints F ∩ U, germ_y s = 0}`.

On an affine open `Spec A` with `F = M~` this is Stacks 02M6's submodule `K(M)` (the elements of `M`
whose image in `M_q` vanishes for every minimal prime `q` of `Supp M`, `Module.embeddedPart`), so no
gluing over affines is needed: `K` is a sheaf because the membership condition is checked germ by germ
(`embeddedPartSubmodule_isSheaf`, same proof as `genericSaturationSubmodule_isSheaf`), and the inclusion
`ι : K ⟶ F` is a monomorphism (`embeddedPart.mono_ι`, a theorem, not a global instance).

Stalks (`X` locally Noetherian, `F` coherent):
* `germ_embeddedPart_eq_zero`: at a generic point `y` every germ of `K` is `0` (`K_y → F_y` is
  injective since the stalk functor is exact, and germs of `K`-sections
  vanish at `y` by definition).
* `exists_res_mem_embeddedPartSections`: if `s ∈ Γ(U, F)`, `x ∈ U`, and `germ_y s = 0` for every
  generic point `y ⤳ x`, then `s` restricts to a section of `K` on a neighbourhood of `x`. Proof: take an
  affine `W ∋ x` inside `U`; the generic points in `W` are finitely many
  (`finite_genericPoints_inter`); remove the closures of those not specializing to `x`
  (a closed set not containing `x`); on the remaining open `V ∋ x` every generic point specializes to
  `x`, so `germ_y s = 0`.
* `germ_eq_zero_of_mem_range_moduleStalkMap_ι` / `mem_range_moduleStalkMap_ι_iff`: the image of
  `K_x → F_x` is exactly the set of germs `germ_x t` with `germ_y t = 0` for every generic point
  `y ⤳ x` (the stalkwise form of Stacks 02M6's description of `K`).

Source: Stacks 02OL, 02M6 (K = {m | Supp(Rm) ⊆ ⋃ V(p_i)} for the embedded primes p_i, equivalently
the elements vanishing at the minimal primes of the support).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.style.haveILetI false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Topology
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- Sections of `F` over `U` whose germs vanish at every generic point of `Supp F` lying in `U`. -/
def embeddedPartSections (F : X.Modules) (U : X.Opens) : Submodule Γ(X, U) Γ(F, U) where
  carrier := {s | ∀ (y : X) (hy : y ∈ U), y ∈ F.genericPoints → F.presheaf.germ U y hy s = 0}
  zero_mem' := by
    intro y hy _
    rw [map_zero]
  add_mem' := by
    intro s t hs ht y hy hyg
    rw [map_add, hs y hy hyg, ht y hy hyg, add_zero]
  smul_mem' := by
    intro r s hs y hy hyg
    change F.presheaf.germ U y hy (r • s) = 0
    rw [CoherentFreeStalksAux.germ_smul', hs y hy hyg, smul_zero]

theorem mem_embeddedPartSections_iff (F : X.Modules) (U : X.Opens) (s : Γ(F, U)) :
    s ∈ F.embeddedPartSections U ↔
      ∀ (y : X) (hy : y ∈ U), y ∈ F.genericPoints → F.presheaf.germ U y hy s = 0 :=
  Iff.rfl

/-- The sub-presheaf of modules `K ⊆ F`. -/
def embeddedPartSubmodule (F : X.Modules) : F.val.Submodule where
  obj U := F.embeddedPartSections U.unop
  map {U V} f := by
    intro s hs y hy hyg
    change F.presheaf.germ V.unop y hy (F.presheaf.map f s) = 0
    rw [F.presheaf.germ_res_apply' f y hy s]
    exact hs y (f.unop.le hy) hyg

/-- `K` is a sheaf: glue in `F`; the membership condition is checked germ by germ, on a member of the
cover containing the generic point. -/
theorem embeddedPartSubmodule_isSheaf (F : X.Modules) :
    CategoryTheory.Presheaf.IsSheaf (Opens.grothendieckTopology X)
      (F.embeddedPartSubmodule).toPresheafOfModules.presheaf := by
  apply (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing _).mpr
  intro ι U sf hsf
  have hcompat : F.presheaf.IsCompatible U (fun i ↦ (sf i).val) := by
    intro i j
    exact congrArg Subtype.val (hsf i j)
  obtain ⟨s, hs, hunique⟩ :=
    (show F.presheaf.IsSheaf from F.isSheaf).isSheafUniqueGluing U (fun i ↦ (sf i).val) hcompat
  have hsK : s ∈ F.embeddedPartSections (iSup U) := by
    intro y hy hyg
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hy
    rw [← F.presheaf.germ_res_apply (Opens.leSupr U i) y hi s, hs i]
    exact (sf i).property y hi hyg
  refine ⟨⟨s, hsK⟩, ?_, ?_⟩
  · intro i
    apply Subtype.ext
    exact hs i
  · intro t ht
    apply Subtype.ext
    apply hunique t.val
    intro i
    exact congrArg Subtype.val (ht i)

/-- The subsheaf `K ⊆ F` of Stacks 02OL: sections whose germs vanish at the generic points of the
support (Stacks 02M6's `K(M)` on affines). -/
def embeddedPart (F : X.Modules) : X.Modules where
  val := (F.embeddedPartSubmodule).toPresheafOfModules
  isSheaf := embeddedPartSubmodule_isSheaf F

/-- The inclusion `ι : K ⟶ F`. -/
def embeddedPart.ι (F : X.Modules) : F.embeddedPart ⟶ F :=
  ⟨(F.embeddedPartSubmodule).ι⟩

theorem embeddedPart.mono_ι (F : X.Modules) : CategoryTheory.Mono (embeddedPart.ι F) where
  right_cancellation f g h := by
    apply SheafOfModules.Hom.ext
    apply (CategoryTheory.cancel_mono (F.embeddedPartSubmodule).ι).mp
    exact congrArg SheafOfModules.Hom.val h

theorem embeddedPart.ι_app (F : X.Modules) (U : X.Opens) (s : Γ(F.embeddedPart, U)) :
    (embeddedPart.ι F).app U s = s.1 :=
  rfl

theorem embeddedPart.property (F : X.Modules) {U : X.Opens} (s : Γ(F.embeddedPart, U)) {y : X}
    (hy : y ∈ U) (hyg : y ∈ F.genericPoints) : F.presheaf.germ U y hy s.1 = 0 :=
  s.property y hy hyg

/-- The stalk map `K_x → F_x` is injective (the stalk functor preserves finite limits). -/
theorem embeddedPart.moduleStalkMap_ι_injective (F : X.Modules) (x : X) :
    Function.Injective (AlgebraicGeometry.Scheme.Modules.moduleStalkMap X x (embeddedPart.ι F)) := by
  have hpres : PreservesFiniteLimits (AlgebraicGeometry.Scheme.Modules.stalkFunctor x) :=
    (stalk_preservesFiniteLimits_colimits x).1
  haveI := embeddedPart.mono_ι F
  have hmono : Mono ((AlgebraicGeometry.Scheme.Modules.stalkFunctor x).map (embeddedPart.ι F)) :=
    preserves_mono_of_preservesLimit _ (embeddedPart.ι F)
  exact (ModuleCat.mono_iff_injective _).mp hmono

/-- At a generic point of `Supp F`, every germ of `K` vanishes. -/
theorem germ_embeddedPart_eq_zero (F : X.Modules) {U : X.Opens} {y : X} (hy : y ∈ U)
    (hyg : y ∈ F.genericPoints) (s : Γ(F.embeddedPart, U)) :
    F.embeddedPart.presheaf.germ U y hy s = 0 := by
  apply embeddedPart.moduleStalkMap_ι_injective F y
  rw [AlgebraicGeometry.Scheme.Modules.moduleStalkMap_germ, map_zero, embeddedPart.ι_app]
  exact embeddedPart.property F s hy hyg

/-- The stalk of `K` at a generic point of `Supp F` is zero. -/
theorem subsingleton_stalk_embeddedPart (F : X.Modules) {y : X} (hyg : y ∈ F.genericPoints) :
    Subsingleton (F.embeddedPart.presheaf.stalk y) := by
  refine subsingleton_of_forall_eq 0 fun e => ?_
  obtain ⟨U, hy, s, rfl⟩ := F.embeddedPart.presheaf.exists_germ_eq e
  exact germ_embeddedPart_eq_zero F hy hyg s

/-- If the germs of `s ∈ Γ(U, F)` vanish at every generic point specializing to `x`, then `s`
restricts to a section of `K` on a neighbourhood of `x` (see the module docstring). -/
theorem exists_res_mem_embeddedPartSections (F : X.Modules) [AlgebraicGeometry.IsLocallyNoetherian X]
    [F.IsCoherent] {U : X.Opens} {x : X} (hx : x ∈ U) (s : Γ(F, U))
    (h : ∀ y ∈ F.genericPoints, y ⤳ x → ∀ hy : y ∈ U, F.presheaf.germ U y hy s = 0) :
    ∃ (V : X.Opens) (_ : x ∈ V) (hVU : V ≤ U),
      F.presheaf.map (homOfLE hVU).op s ∈ F.embeddedPartSections V := by
  obtain ⟨W, hW, hxW, hWU⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hx
  have hW : AlgebraicGeometry.IsAffineOpen W := hW
  -- the generic points in `W` not specializing to `x`
  let B : Set X := (F.genericPoints ∩ (W : Set X)) ∩ {y | ¬ y ⤳ x}
  have hBfin : B.Finite := (finite_genericPoints_inter F hW).subset Set.inter_subset_left
  let C : Set X := ⋃ y ∈ B, closure {y}
  have hCcl : IsClosed C := hBfin.isClosed_biUnion fun _ _ => isClosed_closure
  have hxC : x ∉ C := by
    intro hxC
    obtain ⟨y, hyB, hxy⟩ := Set.mem_iUnion₂.mp hxC
    exact hyB.2 (specializes_iff_mem_closure.mpr hxy)
  let V : X.Opens := W ⊓ ⟨Cᶜ, hCcl.isOpen_compl⟩
  have hVU : V ≤ U := inf_le_left.trans hWU
  refine ⟨V, ⟨hxW, hxC⟩, hVU, ?_⟩
  intro y hyV hyg
  have hyx : y ⤳ x := by
    by_contra hnot
    exact hyV.2 (Set.mem_iUnion₂.mpr ⟨y, ⟨⟨hyg, hyV.1⟩, hnot⟩, subset_closure rfl⟩)
  rw [F.presheaf.germ_res_apply (homOfLE hVU) y hyV s]
  exact h y hyg hyx (hVU hyV)

/-- A germ in the image of `K_x → F_x` has vanishing germ at every generic point `y ⤳ x`. -/
theorem germ_eq_zero_of_mem_range_moduleStalkMap_ι (F : X.Modules) {U : X.Opens} {x : X}
    (hx : x ∈ U) (t : Γ(F, U))
    (ht : F.presheaf.germ U x hx t ∈ LinearMap.range (AlgebraicGeometry.Scheme.Modules.moduleStalkMap X x (embeddedPart.ι F)))
    {y : X} (hyg : y ∈ F.genericPoints) (hyx : y ⤳ x) (hy : y ∈ U) :
    F.presheaf.germ U y hy t = 0 := by
  obtain ⟨k, hk⟩ := ht
  obtain ⟨W, hxW, k', rfl⟩ := F.embeddedPart.presheaf.exists_germ_eq k
  rw [AlgebraicGeometry.Scheme.Modules.moduleStalkMap_germ, embeddedPart.ι_app] at hk
  obtain ⟨V, hxV, iVW, iVU, heq⟩ := TopCat.Presheaf.germ_eq F.presheaf x hxW hx k'.1 t hk
  have hyV : y ∈ V := hyx.mem_open V.2 hxV
  rw [← F.presheaf.germ_res_apply iVU y hyV t, ← heq, F.presheaf.germ_res_apply iVW y hyV k'.1]
  exact embeddedPart.property F k' (iVW.le hyV) hyg

/-- **Stalkwise description of `K`** (Stacks 02M6, on stalks): `germ_x t` lies in the image of
`K_x → F_x` iff `germ_y t = 0` for every generic point `y ⤳ x`. -/
theorem mem_range_moduleStalkMap_ι_iff (F : X.Modules) [AlgebraicGeometry.IsLocallyNoetherian X]
    [F.IsCoherent] {U : X.Opens} {x : X} (hx : x ∈ U) (t : Γ(F, U)) :
    F.presheaf.germ U x hx t ∈ LinearMap.range (AlgebraicGeometry.Scheme.Modules.moduleStalkMap X x (embeddedPart.ι F)) ↔
      ∀ y ∈ F.genericPoints, y ⤳ x → ∀ hy : y ∈ U, F.presheaf.germ U y hy t = 0 := by
  constructor
  · intro ht y hyg hyx hy
    exact germ_eq_zero_of_mem_range_moduleStalkMap_ι F hx t ht hyg hyx hy
  · intro h
    obtain ⟨V, hxV, hVU, hmem⟩ := exists_res_mem_embeddedPartSections F hx t h
    refine ⟨F.embeddedPart.presheaf.germ V x hxV ⟨F.presheaf.map (homOfLE hVU).op t, hmem⟩, ?_⟩
    refine (AlgebraicGeometry.Scheme.Modules.moduleStalkMap_germ X x (embeddedPart.ι F) V hxV
      ⟨F.presheaf.map (homOfLE hVU).op t, hmem⟩).trans ?_
    exact F.presheaf.germ_res_apply (homOfLE hVU) x hxV t

end AlgebraicGeometry.Scheme.Modules

end
