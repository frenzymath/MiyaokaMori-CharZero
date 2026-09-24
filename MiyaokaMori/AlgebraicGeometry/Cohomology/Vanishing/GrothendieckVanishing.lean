import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafHasextInstance
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafCohomologyModule
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafCohomologyTopIso
import MiyaokaMori.AlgebraicGeometry.Cohomology.Vanishing.Stacks01xb
import MiyaokaMori.AlgebraicGeometry.Cohomology.Basic.SheafCohomologyTopLinearEquiv
import Mathlib.CategoryTheory.Sites.SheafCohomology.MayerVietoris
import Mathlib.Topology.Sheaves.MayerVietoris

/-! # Vanishing of quasi-coherent cohomology above the size of an affine cover (Stacks 01XI)

Quasi-coherent cohomology vanishes above the number of affine opens in a cover (Stacks 01XI): on a scheme
with affine diagonal (e.g. separated), for `W` a union of `t` affine opens, `H^n(W, F) = 0` for `n ≥ t`.
Corollary: on a quasi-compact separated scheme the cohomology of a quasi-coherent sheaf vanishes above some
bound (this is all the paper needs for `χ` to be a finite sum).

Route (the first proof of Stacks 01XI, Mayer–Vietoris induction):
* `t = 0`: the `⨆` is `⊥`, and `H'^n(∅, F) = 0` for all `n` — the empty sieve covers `⊥`, so `ℤ[h_⊥]^#` is
  the zero sheaf (`Sheaf.isTerminalOfBotCover` + the three adjunctions sheafification / free abelian group
  / Yoneda), and `Ext` out of a zero object is trivial;
* `t + 1`: `W = ⨆_{i<t} U_i`, `V = U_t`; `W ⊓ V = ⨆_i (U_i ⊓ V)` is again a union of `t` affine opens
  (`IsAffineOpen.inf`, affine diagonal); Mathlib's Mayer–Vietoris sequence `MayerVietorisSquare.sequence_exact`
  (`Opens.mayerVietorisSquare W V`) is exact at `H'^{n-1}(W ⊓ V) → H'^n(W ⊔ V) → H'^n(W) ⊞ H'^n(V)`, and both
  ends vanish by induction and by 01XB (`sheafCohomology'_affineOpen_vanishing`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace GrothendieckVanishingAux

section Site

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [HasSheafify J AddCommGrpCat.{v}]

/-- If the empty sieve covers `X`, the free abelian sheaf `ℤ[h_X]^#` is a zero object. -/
theorem isZero_freeSheaf_yoneda_of_bot_mem {X : C} (hX : ⊥ ∈ J X) :
    IsZero ((presheafToSheaf J AddCommGrpCat.{v}).obj
      (((Functor.whiskeringRight Cᵒᵖ (Type v) AddCommGrpCat.{v}).obj AddCommGrpCat.free).obj
        (yoneda.obj X))) := by
  set Z := (presheafToSheaf J AddCommGrpCat.{v}).obj
      (((Functor.whiskeringRight Cᵒᵖ (Type v) AddCommGrpCat.{v}).obj AddCommGrpCat.free).obj
        (yoneda.obj X)) with hZ
  have hT : IsTerminal (Z.obj.obj (op X)) := Sheaf.isTerminalOfBotCover Z X hX
  have hzero : IsZero (Z.obj.obj (op X)) :=
    IsZero.of_iso (isZero_zero _) (hT.uniqueUpToIso HasZeroObject.zeroIsTerminal)
  have hsub : Subsingleton ((((Functor.whiskeringRight Cᵒᵖ AddCommGrpCat.{v} (Type v)).obj
      (forget AddCommGrpCat.{v})).obj Z.obj).obj (op X)) :=
    AddCommGrpCat.subsingleton_of_isZero hzero
  have hhom : Subsingleton (Z ⟶ Z) :=
    (((sheafificationAdjunction J AddCommGrpCat.{v}).homEquiv _ Z).trans
      (((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv (yoneda.obj X) Z.obj).trans
        yonedaEquiv)).subsingleton
  rw [IsZero.iff_id_eq_zero]
  exact Subsingleton.elim _ _

end Site

section ExtZero

variable {A : Type u} [Category.{v} A] [Abelian A] [HasExt.{w} A]

/-- `Ext` groups out of a zero object are trivial. -/
theorem ext_subsingleton_of_isZero_left {X Y : A} (hX : IsZero X) (n : ℕ) :
    Subsingleton (Abelian.Ext.{w} X Y n) := by
  constructor
  intro a b
  have key : ∀ c : Abelian.Ext.{w} X Y n, c = 0 := fun c => by
    rw [← Abelian.Ext.mk₀_id_comp c, hX.eq_zero_of_src (𝟙 X), Abelian.Ext.mk₀_zero,
      Abelian.Ext.zero_comp]
  rw [key a, key b]

end ExtZero

section HBot

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{v}] [HasExt.{w} (Sheaf J AddCommGrpCat.{v})]

/-- If the empty sieve covers `X`, then `H'^n(X, F) = 0` for all `n`. -/
theorem H'_subsingleton_of_bot_mem (F : Sheaf J AddCommGrpCat.{v}) (n : ℕ) {X : C}
    (hX : ⊥ ∈ J X) : Subsingleton (F.H' n X) :=
  ext_subsingleton_of_isZero_left (isZero_freeSheaf_yoneda_of_bot_mem J hX) n

end HBot

section MV

variable {T : Type u} [TopologicalSpace T]
  [HasExt.{w} (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u})]

/-- `H'^n(∅, F) = 0`. -/
theorem H'_bot_subsingleton (F : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u}) (n : ℕ) :
    Subsingleton (F.H' n (⊥ : Opens T)) :=
  H'_subsingleton_of_bot_mem F n (fun _ h => h.elim)

/-- The Mayer–Vietoris vanishing step: if `H^n(U ⊓ V)`, `H^{n+1}(U)`, `H^{n+1}(V)` vanish, so does
`H^{n+1}(U ⊔ V)`. -/
theorem H'_sup_subsingleton (F : Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u})
    (U V : Opens T) (n : ℕ) (h₁ : Subsingleton (F.H' n (U ⊓ V)))
    (h₂ : Subsingleton (F.H' (n + 1) U)) (h₃ : Subsingleton (F.H' (n + 1) V)) :
    Subsingleton (F.H' (n + 1) (U ⊔ V)) := by
  have hex := ((Opens.mayerVietorisSquare U V).sequence_exact F n (n + 1) rfl).exact 2
  have hz := hex.isZero_of_both_isZero
    (AddCommGrpCat.isZero_of_subsingleton (F.H' n (U ⊓ V)))
    ((biprod_isZero_iff _ _).2 ⟨AddCommGrpCat.isZero_of_subsingleton (F.H' (n + 1) U),
      AddCommGrpCat.isZero_of_subsingleton (F.H' (n + 1) V)⟩)
  exact AddCommGrpCat.subsingleton_of_isZero hz

end MV

/-- An `iSup` over `Fin (t+1)` splits into the `iSup` of the first `t` terms and the last term. -/
theorem iSup_fin_succ {α : Type*} [CompleteLattice α] (t : ℕ) (U : Fin (t + 1) → α) :
    (⨆ i, U i) = (⨆ i : Fin t, U (Fin.castSucc i)) ⊔ U (Fin.last t) := by
  apply le_antisymm
  · refine iSup_le fun i => ?_
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact le_sup_right
    · exact le_sup_of_le_left (le_iSup (fun j : Fin t => U (Fin.castSucc j)) j)
  · exact sup_le (iSup_le fun j => le_iSup U _) (le_iSup U _)

end GrothendieckVanishingAux

theorem sheafCohomology'_vanishing_of_affine_cover {X : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsAffineHom
      (CategoryTheory.Limits.pullback.diagonal (CategoryTheory.Limits.terminal.from X))]
    (M : X.Modules) [M.IsQuasicoherent] (t : ℕ) (U : Fin t → X.Opens)
    (hU : ∀ i, AlgebraicGeometry.IsAffineOpen (U i)) (n : ℕ) (hn : t ≤ n) :
    Subsingleton (M.toAddCommGrpSheaf.H' n (⨆ i, U i)) := by
  induction t generalizing n with
  | zero =>
    rw [iSup_of_empty]
    exact GrothendieckVanishingAux.H'_bot_subsingleton M.toAddCommGrpSheaf n
  | succ t ih =>
    rw [GrothendieckVanishingAux.iSup_fin_succ]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    refine GrothendieckVanishingAux.H'_sup_subsingleton M.toAddCommGrpSheaf _ _ m ?_ ?_ ?_
    · rw [iSup_inf_eq]
      exact ih (fun i => U (Fin.castSucc i) ⊓ U (Fin.last t))
        (fun i => (hU _).inf (hU _)) m (by omega)
    · exact ih (fun i => U (Fin.castSucc i)) (fun i => hU _) (m + 1) (by omega)
    · exact sheafCohomology'_affineOpen_vanishing M (hU _) (m + 1) (by omega)

/-- A quasi-compact scheme has a finite affine open cover (`iSup_affineOpens_eq_top` + a finite subcover by
compactness, reindexed as a `Fin t`-family via `Finset.equivFin`). -/
theorem AlgebraicGeometry.exists_finite_affineOpen_cover (X : AlgebraicGeometry.Scheme.{u})
    [CompactSpace X] :
    ∃ (t : ℕ) (U : Fin t → X.Opens), (∀ i, AlgebraicGeometry.IsAffineOpen (U i)) ∧
      ⨆ i, U i = ⊤ := by
  classical
  have hcov : (Set.univ : Set X) ⊆ ⋃ i : X.affineOpens, ((i : X.Opens) : Set X) := by
    intro x _
    have hx : x ∈ (⨆ i : X.affineOpens, (i : X.Opens)) := by
      rw [AlgebraicGeometry.iSup_affineOpens_eq_top]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
    exact Set.mem_iUnion.mpr ⟨i, hi⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun i : X.affineOpens => ((i : X.Opens) : Set X))
    (fun i => (i : X.Opens).isOpen) hcov
  refine ⟨s.card, fun i => ((s.equivFin.symm i : X.affineOpens) : X.Opens),
    fun i => (s.equivFin.symm i : X.affineOpens).2, ?_⟩
  refine le_antisymm le_top (fun x _ => ?_)
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hs (Set.mem_univ x))
  obtain ⟨hmem, hx⟩ := Set.mem_iUnion.mp hi
  refine TopologicalSpace.Opens.mem_iSup.mpr ⟨s.equivFin ⟨i, hmem⟩, ?_⟩
  simpa [Equiv.symm_apply_apply] using hx

theorem sheafCohomology_eventually_subsingleton {X : AlgebraicGeometry.Scheme.{u}}
    [CompactSpace X]
    [AlgebraicGeometry.IsAffineHom
      (CategoryTheory.Limits.pullback.diagonal (CategoryTheory.Limits.terminal.from X))]
    (M : X.Modules) [M.IsQuasicoherent] :
    ∃ N : ℕ, ∀ n, N ≤ n → Subsingleton (CategoryTheory.Sheaf.H M.toAddCommGrpSheaf n) := by
  obtain ⟨t, U, hU, hcov⟩ := AlgebraicGeometry.exists_finite_affineOpen_cover X
  refine ⟨t, fun n hn => ?_⟩
  have h := sheafCohomology'_vanishing_of_affine_cover M t U hU n hn
  rw [hcov] at h
  exact Equiv.subsingleton
    (CategoryTheory.Sheaf.H'TopAddEquiv _ isTerminalTop M.toAddCommGrpSheaf n).symm.toEquiv

/-- **Stacks 01XB for `sheafCohomology`**: `X` affine, `M` quasi-coherent, `p > 0` ⇒
`sheafCohomology X M p = 0` (affine vanishing for the cohomology used by `χ` / `h^i`). -/
theorem AlgebraicGeometry.sheafCohomology_subsingleton_of_isAffine
    {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsAffine X]
    (M : X.Modules) [M.IsQuasicoherent] (p : ℕ) (hp : 0 < p) :
    Subsingleton (AlgebraicGeometry.sheafCohomology X M p) :=
  haveI := sheafCohomology'_affineOpen_vanishing M (AlgebraicGeometry.isAffineOpen_top X) p hp
  Equiv.subsingleton
    (AlgebraicGeometry.sheafCohomologyTopLinearEquiv M p).symm.toEquiv

/-- The same statement in `Sheaf.H` form. -/
theorem AlgebraicGeometry.sheafCohomology_subsingleton_of_isAffine'
    {X : AlgebraicGeometry.Scheme.{u}} [AlgebraicGeometry.IsAffine X]
    (M : X.Modules) [M.IsQuasicoherent] (p : ℕ) (hp : 0 < p) :
    Subsingleton (CategoryTheory.Sheaf.H M.toAddCommGrpSheaf p) :=
  AlgebraicGeometry.sheafCohomology_subsingleton_of_isAffine M p hp

end
