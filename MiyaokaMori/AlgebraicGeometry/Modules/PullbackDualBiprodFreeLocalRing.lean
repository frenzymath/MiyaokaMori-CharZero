import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.IsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModulesDual
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.SheafDualLocallyFree
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.ModulesBiprodLocallyFree
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.LocalTrivializationPullback
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.RankAtStalkLocalIso
import MiyaokaMori.AlgebraicGeometry.Modules.QuasiCoherent.ModulesFiniteTypeInstances
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.UnitBiprodLineBundleRank
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModulesPullbackRank
import MiyaokaMori.AlgebraicGeometry.Modules.FiniteTypeRestrictFreeIndexFinite
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.SchemeModulesPullbackFreeIso

/-! # The pullback of `(O ⊕ M)^∨` to the spectrum of a local ring is free of rank 2

For a line bundle `M` on `X` and a morphism `g : Spec R → X` with `R` a local ring, the pullback
`g^*(O_X ⊕ M)^∨` is a free sheaf of rank `2` on `Spec R`. (Applied with `R = κ(y)` the residue
field of a point and `g` the canonical `Spec κ(y) → X`: the fibre of the vector bundle
`(O ⊕ M)^∨` at `y` is a 2-dimensional `κ(y)`-vector space.)

References: Stacks 01C9 (finite locally free modules) and 00NX (a finite locally free module over a
local ring is free) in the sheaf form: on the spectrum of a local ring every open set containing
the closed point is the whole space, so a local trivialisation at the closed point is a global
one. Used for the fibres of `P(O ⊕ L)`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- **The fibre of `(O ⊕ M)^∨` over a local base is free of rank 2.**

Proof (as formalized). Write `V := O_X ⊕ M`, `D := V^∨`, `E := g^*D = (Modules.pullback g).obj D`,
`s := IsLocalRing.closedPoint R ∈ Spec R`.
1. `V` is locally free of finite type (`biprod_isLocallyFree`, `biprod_isFiniteType`), hence so is
   `D` (`isLocallyFree_dual'`, `dual_isFiniteType`), and `rankAtStalk D x = 2` for every `x : X`
   (`rankAtStalk_dual_unit_biprod_of_isLineBundle`).
2. Pullback preserves local freeness, finite type and the rank at stalks
   (`isLocallyFree_pullback`, `pullback_isFiniteType`): `E` is locally free of finite type on
   `Spec R` with `rankAtStalk E s = rankAtStalk D (g s) = 2`.
3. Local frame of `E` at `s`: `exists_pullback_iso_free_of_isLocallyFree` gives an open `W ∋ s`
   and an index type `I` with `e : (pullback W.ι).obj E ≅ free I`; `I` is finite because `E` is of
   finite type (`finite_index_of_restrict_iso_free`), and `Fintype.card I = rankAtStalk E s = 2`
   (`rankAtStalk_of_restrict_iso_free`), so `ULift (Fin 2) ≃ I` (`Equiv.ulift`,
   `Fintype.equivFinOfCardEq`) and `free I ≅ free (ULift (Fin 2))` (`Sigma.reindex`).
4. `W = ⊤`: on the spectrum of a local ring every open set containing the closed point is the
   whole space (`IsLocalRing.closedPoint_mem_iff`; every prime specialises to the closed point and
   open sets are stable under generalisation).
5. Transport along `⊤.ι`, whose inverse is `(Spec R).topIso.inv` (`Scheme.toIso_inv_ι`):
   `E ≅ (pullback (𝟙)).obj E ≅ (pullback (topIso.inv ≫ ⊤.ι)).obj E
   ≅ (pullback topIso.inv).obj ((pullback ⊤.ι).obj E) ≅ (pullback topIso.inv).obj (free I) ≅ free I`
   (`pullbackId`, `pullbackCongr`, `pullbackComp`, `pullbackObjFreeIso`). Composing with step 3
   gives `E ≅ free (ULift (Fin 2))`.

Edge cases: `X` empty is impossible (`Spec R ≠ ∅` maps to it). The statement does not need `g`
to be a closed point or `R` to be a field: any local ring works, since only "an open set containing
the closed point is everything" is used. -/
theorem AlgebraicGeometry.Scheme.Modules.pullback_dual_unit_biprod_iso_free_of_isLocalRing
    {X : AlgebraicGeometry.Scheme.{u}} (M : X.Modules) [M.IsLineBundle]
    (R : CommRingCat.{u}) [IsLocalRing R] (g : AlgebraicGeometry.Spec R ⟶ X) :
    Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback g).obj
        (AlgebraicGeometry.Scheme.Modules.dual
          (CategoryTheory.Limits.biprod (C := X.Modules)
            (show X.Modules from SheafOfModules.unit X.ringCatSheaf) M)) ≅
      SheafOfModules.free (R := (AlgebraicGeometry.Spec R).ringCatSheaf) (ULift.{u} (Fin 2))) := by
  classical
  -- Step 1: the dual `D` of `V = O ⊕ M` is locally free of finite type.
  let V : X.Modules :=
    CategoryTheory.Limits.biprod (C := X.Modules)
      (show X.Modules from SheafOfModules.unit X.ringCatSheaf) M
  let D : X.Modules := AlgebraicGeometry.Scheme.Modules.dual V
  have hD : D.IsLocallyFree := AlgebraicGeometry.Scheme.Modules.isLocallyFree_dual' V
  -- Step 2: the pullback `E = g^*D` is locally free of finite type of rank 2 at every point.
  let E : (AlgebraicGeometry.Spec R).Modules := (AlgebraicGeometry.Scheme.Modules.pullback g).obj D
  obtain ⟨hEfree, hrank⟩ := AlgebraicGeometry.Scheme.Modules.isLocallyFree_pullback g D
  have : E.IsLocallyFree := hEfree
  let s : AlgebraicGeometry.Spec R := IsLocalRing.closedPoint R
  -- Step 3: a local frame at the closed point, of rank 2.
  obtain ⟨W, I, hsW, ⟨e⟩⟩ :=
    AlgebraicGeometry.Scheme.Modules.exists_pullback_iso_free_of_isLocallyFree E s
  have : Finite I :=
    AlgebraicGeometry.Scheme.Modules.finite_index_of_restrict_iso_free E W I e s hsW
  let _ : Fintype I := Fintype.ofFinite I
  have hcard : Fintype.card I = 2 := by
    rw [← AlgebraicGeometry.Scheme.Modules.rankAtStalk_of_restrict_iso_free E W I e s hsW,
      hrank s, AlgebraicGeometry.Scheme.Modules.rankAtStalk_dual_unit_biprod_of_isLineBundle M]
  -- Step 4: an open set of `Spec R` containing the closed point is everything.
  have hW : W = ⊤ := (IsLocalRing.closedPoint_mem_iff W).mp hsW
  subst hW
  -- Reindex `free I ≅ free (ULift (Fin 2))`.
  let ε : ULift.{u} (Fin 2) ≃ I :=
    Equiv.ulift.trans (Fintype.equivFinOfCardEq hcard).symm
  let r : (SheafOfModules.free (R := (AlgebraicGeometry.Spec R).ringCatSheaf) (ULift.{u} (Fin 2)) :
      (AlgebraicGeometry.Spec R).Modules) ≅
      SheafOfModules.free (R := (AlgebraicGeometry.Spec R).ringCatSheaf) I :=
    Sigma.reindex ε (fun _ : I => SheafOfModules.unit (AlgebraicGeometry.Spec R).ringCatSheaf)
  -- Step 5: transport along `⊤.ι` (an isomorphism with inverse `topIso.inv`).
  let j : AlgebraicGeometry.Spec R ⟶ (⊤ : (AlgebraicGeometry.Spec R).Opens).toScheme :=
    (AlgebraicGeometry.Spec R).topIso.inv
  have hj : j ≫ (⊤ : (AlgebraicGeometry.Spec R).Opens).ι = 𝟙 _ :=
    AlgebraicGeometry.Scheme.toIso_inv_ι _
  refine ⟨((AlgebraicGeometry.Scheme.Modules.pullbackId _).app E).symm ≪≫
    (AlgebraicGeometry.Scheme.Modules.pullbackCongr hj.symm).app E ≪≫
    ((AlgebraicGeometry.Scheme.Modules.pullbackComp j
      (⊤ : (AlgebraicGeometry.Spec R).Opens).ι).app E).symm ≪≫
    (AlgebraicGeometry.Scheme.Modules.pullback j).mapIso e ≪≫
    AlgebraicGeometry.Scheme.Modules.pullbackObjFreeIso j I ≪≫ r.symm⟩

end
