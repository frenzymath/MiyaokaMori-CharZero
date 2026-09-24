import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.LocalTrivializationPullback
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.RankAtStalkLocalIso
import MiyaokaMori.AlgebraicGeometry.Modules.FiniteTypeRestrictFreeIndexFinite

/-! # Local frames of fixed rank versus `IsLocallyFree`, `IsFiniteType` and `rankAtStalk`

The datum "every point has a local frame of rank `n`" is translated into the three Mathlib-side
conclusions `IsLocallyFree` / `IsFiniteType` / `rankAtStalk = n`. The special case
`AlgebraicGeometry.Scheme.Modules.IsLocallyFreeRank X M n` (by definition `∀ x, ∃ U ∋ x, M|_U ≅ O_U^{ULift (Fin n)}`) is
the bridge to the fields of `VectorBundle`.

Proof sketch:
1. Locally free: feed `M|_U ≅ O_U^{ULift (Fin n)}` to `isLocallyFree_of_restrict_free` (with the open
   immersion `U.ι`; `x ∈ Set.range U.ι.base` by `⟨⟨x, hx⟩, rfl⟩`).
2. Finite type: the restriction/pullback isomorphism (`restrictFunctorIsoPullback`) turns the frame
   into `(U.ι)^*M ≅ O_U^{ULift (Fin n)}`; its inverse is an epimorphism from a free sheaf on the finite
   index type `ULift (Fin n)`, and `isFiniteType_of_epi_free_pullback` applies.
3. Rank: the same pullback isomorphism fed to `rankAtStalk_of_restrict_iso_free` gives
   `rankAtStalk M x = Fintype.card (ULift (Fin n)) = n`.

References: Stacks 01C6 (locally free), 01B5 (finite type).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open AlgebraicGeometry

/-- A local frame in restriction form, transported to pullback form. -/
private def lfRankBridge.pullbackIso {X : Scheme.{u}} (M : X.Modules) (U : X.Opens) (n : ℕ)
    (e : M.restrict U.ι ≅
      SheafOfModules.free (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin n))) :
    (Scheme.Modules.pullback U.ι).obj M ≅
      SheafOfModules.free (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin n)) :=
  ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app M).symm ≪≫ e

/-- A local frame of rank `n` at every point ⟹ the sheaf is locally free. -/
theorem AlgebraicGeometry.Scheme.Modules.isLocallyFree_of_localFrames
    {X : AlgebraicGeometry.Scheme.{u}} (M : X.Modules) (n : ℕ)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Nonempty (M.restrict U.ι ≅
        SheafOfModules.free (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin n)))) :
    M.IsLocallyFree := by
  refine AlgebraicGeometry.Scheme.Modules.isLocallyFree_of_restrict_free M fun x => ?_
  obtain ⟨U, hxU, ⟨e⟩⟩ := h x
  exact ⟨U.toScheme, U.ι, inferInstance, ULift.{u} (Fin n), ⟨⟨x, hxU⟩, rfl⟩, ⟨e⟩⟩

/-- A local frame of rank `n` at every point ⟹ the sheaf is of finite type. -/
theorem AlgebraicGeometry.Scheme.Modules.isFiniteType_of_localFrames
    {X : AlgebraicGeometry.Scheme.{u}} (M : X.Modules) (n : ℕ)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Nonempty (M.restrict U.ι ≅
        SheafOfModules.free (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin n)))) :
    M.IsFiniteType := by
  refine AlgebraicGeometry.Scheme.Modules.isFiniteType_of_epi_free_pullback M fun x => ?_
  obtain ⟨U, hxU, ⟨e⟩⟩ := h x
  exact ⟨U, ULift.{u} (Fin n), inferInstance, (lfRankBridge.pullbackIso M U n e).inv, hxU,
    @IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_inv (lfRankBridge.pullbackIso M U n e))⟩

/-- A local frame of rank `n` at every point ⟹ the rank at every stalk is `n`. -/
theorem AlgebraicGeometry.Scheme.Modules.rankAtStalk_eq_of_localFrames
    {X : AlgebraicGeometry.Scheme.{u}} (M : X.Modules) (n : ℕ)
    (h : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      Nonempty (M.restrict U.ι ≅
        SheafOfModules.free (R := U.toScheme.ringCatSheaf) (ULift.{u} (Fin n))))
    (x : X) :
    AlgebraicGeometry.Scheme.Modules.rankAtStalk M x = n := by
  obtain ⟨U, hxU, ⟨e⟩⟩ := h x
  rw [AlgebraicGeometry.Scheme.Modules.rankAtStalk_of_restrict_iso_free M U
      (ULift.{u} (Fin n)) (lfRankBridge.pullbackIso M U n e) x hxU,
    Fintype.card_ulift, Fintype.card_fin]

namespace AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Proj

variable {k : Type u} [Field k] {X : AlgebraicGeometry.Proj.SchemeOver k} {M : X.scheme.Modules} {n : ℕ}

/-- Bridge (locally free): `IsLocallyFreeRank` ⟹ Mathlib's `IsLocallyFree`. -/
theorem IsLocallyFreeRank.isLocallyFree (h : AlgebraicGeometry.Scheme.Modules.IsLocallyFreeRank X M n) :
    M.IsLocallyFree :=
  AlgebraicGeometry.Scheme.Modules.isLocallyFree_of_localFrames M n h.local_frame

/-- Bridge (finite type): `IsLocallyFreeRank` ⟹ Mathlib's `IsFiniteType`. -/
theorem IsLocallyFreeRank.isFiniteType (h : AlgebraicGeometry.Scheme.Modules.IsLocallyFreeRank X M n) :
    M.IsFiniteType :=
  AlgebraicGeometry.Scheme.Modules.isFiniteType_of_localFrames M n h.local_frame

/-- Bridge (rank): `IsLocallyFreeRank X M n` ⟹ `rankAtStalk M x = n` at every point. -/
theorem IsLocallyFreeRank.rankAtStalk_eq (h : AlgebraicGeometry.Scheme.Modules.IsLocallyFreeRank X M n)
    (x : X.scheme) :
    AlgebraicGeometry.Scheme.Modules.rankAtStalk M x = n :=
  AlgebraicGeometry.Scheme.Modules.rankAtStalk_eq_of_localFrames M n h.local_frame x

/-- Converse bridge: "locally free + finite type + rank `n` at every stalk" ⟹
`IsLocallyFreeRank X M n`. Used to feed results into lemmas whose hypothesis is
`IsLocallyFreeRank`. -/
theorem isLocallyFreeRank_of_rankAtStalk_eq [M.IsLocallyFree] [M.IsFiniteType]
    (hr : ∀ x : X.scheme, AlgebraicGeometry.Scheme.Modules.rankAtStalk M x = n) :
    AlgebraicGeometry.Scheme.Modules.IsLocallyFreeRank X M n := by
  refine ⟨fun x => ?_⟩
  obtain ⟨U, I, hxU, ⟨e⟩⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_pullback_iso_free_of_isLocallyFree M x
  have : Finite I :=
    AlgebraicGeometry.Scheme.Modules.finite_index_of_restrict_iso_free M U I e x hxU
  have := Fintype.ofFinite I
  have hcard : Fintype.card I = Fintype.card (ULift.{u} (Fin n)) := by
    rw [Fintype.card_ulift, Fintype.card_fin,
      ← AlgebraicGeometry.Scheme.Modules.rankAtStalk_of_restrict_iso_free M U I e x hxU, hr x]
  refine ⟨U, hxU, ⟨?_⟩⟩
  exact (AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback U.ι).app M ≪≫ e ≪≫
    (SheafOfModules.freeFunctor (R := U.toScheme.ringCatSheaf)).mapIso
      (Fintype.equivOfCardEq hcard).toIso

/-- Bridge (packaged): the three `Prop` fields of `VectorBundle` at once. -/
theorem IsLocallyFreeRank.toVectorBundleFields (h : AlgebraicGeometry.Scheme.Modules.IsLocallyFreeRank X M n) :
    M.IsLocallyFree ∧ M.IsFiniteType ∧
      ∀ x : X.scheme, AlgebraicGeometry.Scheme.Modules.rankAtStalk M x = n :=
  ⟨h.isLocallyFree, h.isFiniteType, h.rankAtStalk_eq⟩

end AlgebraicGeometry.Scheme.Modules

end
