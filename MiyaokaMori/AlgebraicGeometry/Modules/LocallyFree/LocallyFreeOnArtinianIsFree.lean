import Mathlib.AlgebraicGeometry.Artinian
import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.ModuleStalkIso
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.ModulesPow
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundleRank
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.FreeModuleStalkBasisSpan
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.LocallyFreeStalkBasis

/-! # Locally free modules of constant rank on an Artinian scheme are free

**A locally free module of constant positive rank `n` on an Artinian scheme is free**:
`E ≅ O_Z^{⊕ n}`. This is the step "`i^*E` is trivial on `Z`" of Stacks 0AYT (`Z` is a finite disjoint
union of spectra of Artinian local rings; on a local ring a finite locally free module is free, Stacks 00NX).

Route: only discreteness of `Z` is used. Every point `z` is open;
`E_z` has an `O_{Z,z}`-basis `c_z` indexed by `Fin n` (`LocallyFreeStalkBasis`); each basis
vector is the germ of a section over the open point `{z}`; these sections glue (disjoint cover of a
sheaf) to `n` global sections `s_j`, which define `φ : O_Z^{⊕ n} ⟶ E`; on every stalk `φ` maps the standard
basis to `c_z`, so it is bijective on stalks, hence an isomorphism (`AlgebraicGeometry.Scheme.Modules.moduleHom_isIso_iff_stalk_bijective`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace MiyaokaMori.FreeOfArtinian

open AlgebraicGeometry

variable {Z : Scheme.{u}}

/-- The family of sections (over all opens) obtained by restricting a global section. -/
def sectionOfTop (P : Z.Modules) (a : Γ(P, ⊤)) : P.sections :=
  PresheafOfModules.sectionsMk (fun W => (P.presheaf.map (homOfLE le_top).op a : Γ(P, W.unop)))
    (by
      intro W W' k
      change P.presheaf.map k (P.presheaf.map _ a) = P.presheaf.map _ a
      rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl)

theorem sectionOfTop_val (P : Z.Modules) (a : Γ(P, ⊤)) (W : Z.Opens) :
    (sectionOfTop P a).val (op W) = P.presheaf.map (homOfLE le_top).op a := rfl

/-- `unitHomEquiv.symm s` sends `1` to the value of the family `s`. -/
theorem unitHomEquiv_symm_app_one (P : Z.Modules) (s : P.sections) (W : Z.Opens) :
    Scheme.Modules.Hom.app (P.unitHomEquiv.symm s) W (1 : Γ(Z, W)) = s.val (op W) :=
  congrArg (fun z => z.val (op W)) (P.unitHomEquiv.apply_symm_apply s)

/-- Sections of a sheaf of modules over the empty open set form a subsingleton
(`TopCat.Sheaf.isTerminalOfEmpty`; same proof as `Scheme.Modules.subsingleton_sections_bot` in
`ModulesCoevaluation`, repeated to avoid that import). -/
theorem subsingleton_sections_bot (N : Z.Modules) : Subsingleton Γ(N, ⊥) := by
  have t : IsTerminal (N.val.presheaf.obj (op (⊥ : Z.Opens))) :=
    TopCat.Sheaf.isTerminalOfEmpty (⟨N.val.presheaf, N.isSheaf⟩ : TopCat.Sheaf AddCommGrpCat.{u} Z)
  have h : (𝟙 (N.val.presheaf.obj (op (⊥ : Z.Opens)))) = 0 := t.hom_ext _ _
  refine ⟨fun x y => ?_⟩
  have hx : ∀ z : Γ(N, ⊥), z = 0 := fun z => by
    have := congrArg (fun φ => (ConcreteCategory.hom φ) z) h
    exact this
  rw [hx x, hx y]

theorem subsingleton_sections_of_eq_bot (N : Z.Modules) (V : Z.Opens) (hV : V = ⊥) :
    Subsingleton Γ(N, V) := by
  subst hV
  exact subsingleton_sections_bot N

/-- The open point `{z}` of a discrete scheme. -/
def pt [DiscreteTopology Z] (z : Z) : Z.Opens := ⟨{z}, isOpen_discrete _⟩

theorem mem_pt [DiscreteTopology Z] (z : Z) : z ∈ pt z := Set.mem_singleton z

theorem pt_le [DiscreteTopology Z] {z : Z} {V : Z.Opens} (hz : z ∈ V) : pt z ≤ V := by
  intro w hw
  have hw' : w = z := hw
  rw [hw']
  exact hz

theorem pt_inf_eq_bot [DiscreteTopology Z] {z w : Z} (h : z ≠ w) : pt z ⊓ pt w = ⊥ := by
  apply le_bot_iff.mp
  intro v hv
  have h1 : v = z := hv.1
  have h2 : v = w := hv.2
  exact absurd (h1.symm.trans h2) h

theorem le_iSup_pt [DiscreteTopology Z] : (⊤ : Z.Opens) ≤ ⨆ z, pt z :=
  fun z _ => Opens.mem_iSup.mpr ⟨z, mem_pt z⟩

/-- **Gluing over the open points of a discrete scheme.** For a sheaf of modules `E` on a discrete
scheme `Z`, any family `u z ∈ Γ(E, {z})` comes from a global section (the open points form a disjoint
open cover, so compatibility is automatic: pairwise intersections are empty and `Γ(E, ∅)` is a
subsingleton). Mathlib `TopCat.Sheaf.existsUnique_gluing'`. -/
theorem exists_glue [DiscreteTopology Z] (E : Z.Modules) (u : ∀ z : Z, Γ(E, pt z)) :
    ∃ s : Γ(E, ⊤), ∀ z, E.presheaf.map (homOfLE le_top).op s = u z := by
  let F : TopCat.Sheaf AddCommGrpCat.{u} Z := ⟨E.val.presheaf, E.isSheaf⟩
  have hcompat : TopCat.Presheaf.IsCompatible F.1 pt u := by
    intro i j
    by_cases hij : i = j
    · subst hij
      rw [Subsingleton.elim (Opens.infLELeft (pt i) (pt i)) (Opens.infLERight (pt i) (pt i))]
    · exact @Subsingleton.elim _ (subsingleton_sections_of_eq_bot E (pt i ⊓ pt j) (pt_inf_eq_bot hij)) _ _
  obtain ⟨s, hs, -⟩ := F.existsUnique_gluing' pt ⊤ (fun z => homOfLE le_top) le_iSup_pt u hcompat
  exact ⟨s, hs⟩

end MiyaokaMori.FreeOfArtinian

/-- **Locally free of constant rank `n > 0` on an Artinian scheme ⇒ free of rank `n`.**
`Z` Artinian (Mathlib `IsArtinianScheme`: locally Noetherian, `dim ≤ 0`, quasi-compact; hence finite and
discrete — Mathlib instances `IsArtinianScheme.finite`, `IsLocallyArtinian.discreteTopology`), `E` locally
free with `rankAtStalk E z = n` at every point and `n > 0`. Then `E ≅ pow O_Z n = ⨁_{Fin n} O_Z`.

Source: Stacks 0AYT (proof: "`Z` is a finite discrete scheme, hence `i^*E` is free"); Stacks 00NX
(finite projective modules over a local ring are free). Only the discreteness of `Z` is used.

Proof (as formalised):
1. For each `z`, `E_z` has an `O_{Z,z}`-basis `c_z` indexed by `ULift (Fin n)`
   (`nonempty_stalk_basis_fin_of_isLocallyFree`: a local
   trivialisation `E|_U ≅ O^{(I)}` has `I` finite of cardinality `n` because `rankAtStalk E z = n > 0`).
2. Each `c_z j` is the germ of a section over some open neighbourhood (`exists_germ_eq`), which restricts to
   the open point `{z}`: `u_{z,j} ∈ Γ(E, {z})` with `germ u_{z,j} = c_z j`.
3. For each `j`, the `u_{z,j}` glue to `s_j ∈ Γ(Z, E)` (`exists_glue`: disjoint open cover).
4. `φ : O_Z^{(Fin n)} ⟶ E` is the morphism with `ιFree j ≫ φ ↔ s_j` (`freeHomEquiv`). At every stalk `z`,
   `φ_z` sends the standard basis `b_j = germ e_j` (`FreeStalk.linearIndependent_b`, `span_b_eq_top`) to
   `germ s_j = c_z j`, so `φ_z` coincides with the basis-change equivalence and is bijective; hence `φ` is an
   isomorphism (`AlgebraicGeometry.Scheme.Modules.moduleHom_isIso_iff_stalk_bijective`).
5. `O_Z^{(ULift (Fin n))} = ∐_{ULift (Fin n)} O_Z ≅ ∐_{Fin n} O_Z ≅ ⨁_{Fin n} O_Z = pow O_Z n`
   (`Sigma.whiskerEquiv`, `biproduct.isoCoproduct`).

Edge cases: `Z = ∅` — steps 1–4 are vacuous and the glued sections are the unique elements of `Γ(∅, E)`;
the argument needs no `Nonempty Z`. `n = 0` is excluded on purpose (with `rankAtStalk = 0` the module may be
free of infinite rank; that case is `Stacks0ayt_ArtinianRankZero.lean`). -/
theorem AlgebraicGeometry.Scheme.Modules.nonempty_iso_pow_unit_of_isLocallyFree_of_isArtinianScheme
    {Z : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsArtinianScheme Z]
    (E : Z.Modules) [E.IsLocallyFree] (n : ℕ) (hn : 0 < n)
    (hE : ∀ z, AlgebraicGeometry.Scheme.Modules.rankAtStalk E z = n) :
    Nonempty (E ≅ AlgebraicGeometry.Scheme.Modules.pow (SheafOfModules.unit Z.ringCatSheaf) n) := by
  classical
  open MiyaokaMori.FreeOfArtinian in
  -- Step 1: a basis of each stalk.
  let c : ∀ z : Z, Module.Basis (ULift.{u} (Fin n)) (Z.presheaf.stalk z) (E.presheaf.stalk z) :=
    fun z => (AlgebraicGeometry.Scheme.Modules.nonempty_stalk_basis_fin_of_isLocallyFree
      E z n hn (hE z)).some
  -- Step 2: representatives over the open points.
  have hu : ∀ (z : Z) (j : ULift.{u} (Fin n)), ∃ u : Γ(E, pt z),
      E.presheaf.germ (pt z) z (mem_pt z) u = c z j := by
    intro z j
    obtain ⟨V, hzV, t, ht⟩ := TopCat.Presheaf.exists_germ_eq E.presheaf (c z j)
    refine ⟨E.presheaf.map (homOfLE (pt_le hzV)).op t, ?_⟩
    rw [TopCat.Presheaf.germ_res_apply]
    exact ht
  choose u hu using hu
  -- Step 3: glue.
  have hs : ∀ j : ULift.{u} (Fin n), ∃ s : Γ(E, ⊤),
      ∀ z, E.presheaf.map (homOfLE le_top).op s = u z j :=
    fun j => exists_glue E (fun z => u z j)
  choose s hs using hs
  -- Step 4: the morphism and its stalks.
  let φ : MiyaokaMori.FreeStalk.freeM Z (ULift.{u} (Fin n)) ⟶ E :=
    (SheafOfModules.freeHomEquiv E).symm (fun j => sectionOfTop E (s j))
  have hιφ : ∀ j, MiyaokaMori.FreeStalk.inc Z (ULift.{u} (Fin n)) j ≫ φ =
      E.unitHomEquiv.symm (sectionOfTop E (s j)) := by
    intro j
    have h1 : E.freeHomEquiv φ j = sectionOfTop E (s j) :=
      congrFun (Equiv.apply_symm_apply (SheafOfModules.freeHomEquiv E) _) j
    rw [← h1]
    exact (E.unitHomEquiv.symm_apply_apply (SheafOfModules.ιFree j ≫ φ)).symm
  have happ : ∀ j, AlgebraicGeometry.Scheme.Modules.Hom.app φ ⊤
        (MiyaokaMori.FreeStalk.e (ULift.{u} (Fin n)) j ⊤) =
      E.presheaf.map (homOfLE le_top).op (s j) := by
    intro j
    rw [MiyaokaMori.FreeStalk.e_eq]
    change AlgebraicGeometry.Scheme.Modules.Hom.app
      (MiyaokaMori.FreeStalk.inc Z (ULift.{u} (Fin n)) j ≫ φ) ⊤ (1 : Γ(Z, ⊤)) = _
    rw [hιφ j, unitHomEquiv_symm_app_one, sectionOfTop_val]
  have hφ : ∀ (z : Z) (j : ULift.{u} (Fin n)),
      AlgebraicGeometry.Scheme.Modules.moduleStalkMap Z z φ (MiyaokaMori.FreeStalk.b (ULift.{u} (Fin n)) j z) = c z j := by
    intro z j
    refine (AlgebraicGeometry.Scheme.Modules.moduleStalkMap_germ Z z φ ⊤ (Opens.mem_top z) (MiyaokaMori.FreeStalk.e _ j ⊤)).trans ?_
    rw [happ, ← hu z j, ← hs j z]
    exact (TopCat.Presheaf.germ_res_apply E.presheaf (homOfLE le_top) z (Opens.mem_top z) (s j)).trans
      (TopCat.Presheaf.germ_res_apply E.presheaf (homOfLE le_top) z (mem_pt z) (s j)).symm
  have hbij : ∀ z : Z, Function.Bijective (AlgebraicGeometry.Scheme.Modules.moduleStalkMap Z z φ) := by
    intro z
    let bF : Module.Basis (ULift.{u} (Fin n)) (Z.presheaf.stalk z)
        ((MiyaokaMori.FreeStalk.freeM Z (ULift.{u} (Fin n))).presheaf.stalk z) :=
      Module.Basis.mk (MiyaokaMori.FreeStalk.linearIndependent_b _ z)
        (MiyaokaMori.FreeStalk.span_b_eq_top _ z).ge
    have heq : AlgebraicGeometry.Scheme.Modules.moduleStalkMap Z z φ = (bF.equiv (c z) (Equiv.refl _)).toLinearMap := by
      apply bF.ext
      intro j
      rw [LinearEquiv.coe_coe, Module.Basis.equiv_apply, Equiv.refl_apply]
      simp only [bF, Module.Basis.mk_apply]
      exact hφ z j
    rw [heq]
    exact (bF.equiv (c z) (Equiv.refl _)).bijective
  have hiso : IsIso φ := (AlgebraicGeometry.Scheme.Modules.moduleHom_isIso_iff_stalk_bijective φ).mpr hbij
  -- Step 5: `free (ULift (Fin n)) ≅ pow unit n`.
  let fam : Fin n → Z.Modules := fun _ => SheafOfModules.unit Z.ringCatSheaf
  let fam' : ULift.{u} (Fin n) → Z.Modules := fun _ => SheafOfModules.unit Z.ringCatSheaf
  let e1 : AlgebraicGeometry.Scheme.Modules.pow (SheafOfModules.unit Z.ringCatSheaf) n ≅
      MiyaokaMori.FreeStalk.freeM Z (ULift.{u} (Fin n)) :=
    biproduct.isoCoproduct fam ≪≫
      Sigma.whiskerEquiv (f := fam) (g := fam') Equiv.ulift.symm (fun _ => Iso.refl _)
  exact ⟨(asIso φ).symm ≪≫ e1.symm⟩

end
