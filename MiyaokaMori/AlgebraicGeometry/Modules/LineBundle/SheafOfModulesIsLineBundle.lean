import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.IsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.VarietyLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.RankAtStalkLocalIso
import MiyaokaMori.AlgebraicGeometry.Varieties.Basic.Variety
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.VectorBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.FreeSheaf
import MiyaokaMori.AlgebraicGeometry.Modules.FiniteTypeRestrictFreeIndexFinite
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.LocalTrivializationPullback

/-! # Line bundles: the `SheafOfModules` spelling

An `O_X`-module `M` is a line bundle (invertible sheaf) if it is locally free of rank 1, i.e. there is an
open cover on each member of which `M` is isomorphic to the structure sheaf. Many statements use the
unbundled form `[M.IsLineBundle]` (carrying the same data as the bundled `LineBundle X`).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- `SheafOfModules.IsLineBundle` is an abbreviation of `AlgebraicGeometry.Scheme.Modules.IsLineBundle`
(the definitions agree verbatim); the instances `pullback` / `unit` / `isLocallyFree` / `isFiniteType` are
those of the latter, and the names below are aliases. -/
abbrev SheafOfModules.IsLineBundle {X : AlgebraicGeometry.Scheme.{u}}
    (M : SheafOfModules.{u} X.ringCatSheaf) : Prop :=
  AlgebraicGeometry.Scheme.Modules.IsLineBundle (X := X) M

alias SheafOfModules.IsLineBundle.locally_trivial :=
  AlgebraicGeometry.Scheme.Modules.IsLineBundle.locally_trivial

/- The pullback of a line bundle is a line bundle. -/
alias SheafOfModules.IsLineBundle.pullback := AlgebraicGeometry.Scheme.Modules.IsLineBundle.pullback

/- The structure sheaf is a line bundle (for tensor products, duals and tensor powers see `Stacks01ct`). -/
alias SheafOfModules.IsLineBundle.unit := AlgebraicGeometry.Scheme.Modules.IsLineBundle.unit

/- A line bundle is a locally free sheaf (of finite type): this provides the instances required by
   `totalSpace`, `dual_pullback`, etc. -/
alias SheafOfModules.IsLineBundle.isLocallyFree :=
  AlgebraicGeometry.Scheme.Modules.IsLineBundle.isLocallyFree

alias SheafOfModules.IsLineBundle.isFiniteType :=
  AlgebraicGeometry.Scheme.Modules.IsLineBundle.isFiniteType

/- The underlying module of a bundled line bundle is a line bundle in the unbundled sense. -/

instance LineBundle.toModules_isLineBundle {k : Type u} [Field k] {X : Variety k}
    (L : LineBundle X) : L.toModules.IsLineBundle := by
  refine ⟨fun x => ?_⟩
  obtain ⟨U, I, hx, ⟨e⟩⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_pullback_iso_free_of_isLocallyFree L.toModules x
  have hfin : Finite I :=
    AlgebraicGeometry.Scheme.Modules.finite_index_of_restrict_iso_free L.toModules U I e x hx
  have := Fintype.ofFinite I
  have hcard : Fintype.card I = 1 := by
    have h := AlgebraicGeometry.Scheme.Modules.rankAtStalk_of_restrict_iso_free L.toModules U I e x hx
    rw [L.rankAtStalk_eq x, L.rank_eq_one] at h
    exact_mod_cast h.symm
  have : Unique I := (Fintype.card_eq_one_iff_nonempty_unique.mp hcard).some
  exact ⟨U, hx, ⟨(AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback U.ι).app L.toModules ≪≫
    e ≪≫ CategoryTheory.Limits.coproductUniqueIso
      (fun _ : I => SheafOfModules.unit U.toScheme.ringCatSheaf)⟩⟩

end
