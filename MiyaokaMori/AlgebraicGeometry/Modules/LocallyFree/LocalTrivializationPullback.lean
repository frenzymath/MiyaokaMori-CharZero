import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.LocallyFreeOfRestrictFreeCover
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.SchemeModulesPullbackFreeIso

/-! # Local trivializations in terms of pullback along open immersions

Let `X` be a scheme and `M` an `O_X`-module. (1) `M` is locally free iff every point `x` has an open
neighbourhood `U` and an index type `I` with `(U.ι)^*M ≅ O_U^{(I)}`; (2) `M` is of finite type iff every
point `x` has an open neighbourhood `U`, a finite index type `J` and an epimorphism
`O_U^{(J)} → (U.ι)^*M`; (3) for opens `V ≤ U`, `(V.ι)^*M ≅ j^*((U.ι)^*M)` with `j : V → U` the inclusion.
This translates Mathlib's definitions, written with `M.over U` and `GeneratingSections`, into the
pullback functor `Scheme.Modules.pullback U.ι`, which composes well with pullbacks, biproducts and
other functorial constructions.

Proof sketch:
1. (⇒, locally free) Take the `LocalGeneratorsData` `q` of Mathlib's definition (`IsLocallyFreeData`);
   `x` lies in some `q.X i` (`Opens.coversTop_iff`), and `(q.generators i).π : free I ⟶ M.over (q.X i)`
   is an isomorphism. The forward functor `F` of the equivalence `Scheme.Modules.overEquiv U` preserves
   colimits and sends the structure sheaf to the structure sheaf (`restrictUnitIso`,
   `overFunctorEquiv`), so `mapFreeIso` gives `F(free I) ≅ free I`; and
   `F(M.over U) ≅ M.restrict U.ι` (`overFunctorEquiv`) `≅ (U.ι)^*M` (`restrictFunctorIsoPullback`).
2. (⇐, locally free) `(U.ι)^*M ≅ free I` composed with `restrictFunctorIsoPullback` gives
   `M.restrict U.ι ≅ free I` with `x ∈ range U.ι`; apply `isLocallyFree_of_restrict_free`.
3. (⇒, finite type) As in step 1, move `G.π : free J ⟶ M.over V` (epi, `J` finite) through `F` to
   `free J ⟶ (V.ι)^*M`; equivalences preserve epimorphisms, and composing with an isomorphism keeps
   them.
4. (⇐, finite type) Given an epimorphism `π : free J ⟶ (U.ι)^*M`, compose with the inverse of
   `restrictFunctorIsoPullback` to get finite `GeneratingSections` of `M.restrict U.ι`
   (`ofEpi` of `free.generatingSections`); then move them with `GeneratingSections.map` through
   (restriction along `image of U.ι ≅ U`) `⋙` (inverse of `overEquiv`) to `M.over (image of U.ι)`, with
   the same index type. The opens `(U_x.ι).opensRange ∋ x` cover `X`; assemble the finite type
   `LocalGeneratorsData`.
5. (3) `V.ι = j ≫ U.ι` (`Scheme.homOfLE_ι`); use `pullbackCongr` and `pullbackComp`.
6. (Shrinking) For `V ≤ U`, a trivialization on `U` (resp. an epimorphism from a free sheaf) moves to
   `V` through `j^*`: `j^*` sends free sheaves to free sheaves and, as a left adjoint, preserves
   epimorphisms; compose with (3). Finitely many open neighbourhoods of `x` intersect in an open
   neighbourhood, so finitely many sheaves admit a common open.

References: Stacks 01C6 (locally free), 01B5 (finite type), rewritten on open subschemes.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open AlgebraicGeometry

/-- The forward functor of `overEquiv` moves `free I ⟶ M.over U` to `free I ⟶ (U.ι)^*M`. -/
private theorem localTriv.transport {X : Scheme.{u}} (M : X.Modules) (U : X.Opens)
    (I : Type u) (p : SheafOfModules.free I ⟶ M.over U) :
    ∃ π : (SheafOfModules.free (R := U.toScheme.ringCatSheaf) I : U.toScheme.Modules) ⟶
        (Scheme.Modules.pullback U.ι).obj M, (Epi p → Epi π) ∧ (IsIso p → IsIso π) := by
  let F : SheafOfModules.{u} (X.ringCatSheaf.over U) ⥤ SheafOfModules.{u} U.toScheme.ringCatSheaf :=
    (Scheme.Modules.overEquiv U).functor
  have : F.IsEquivalence := inferInstanceAs (Scheme.Modules.overEquiv U).functor.IsEquivalence
  have : PreservesColimitsOfShape (Discrete I) F :=
    (F.asEquivalence.toAdjunction.leftAdjoint_preservesColimits.{u, u}).preservesColimitsOfShape
  let e1 : F.obj (M.over U) ≅ (Scheme.Modules.restrictFunctor U.ι).obj M :=
    (Scheme.Modules.overFunctorEquiv U).app M
  let e2 := (Scheme.Modules.restrictFunctorIsoPullback U.ι).app M
  let η : SheafOfModules.unit U.toScheme.ringCatSheaf ≅
      F.obj (SheafOfModules.unit (X.ringCatSheaf.over U)) :=
    (Scheme.Modules.restrictUnitIso U.ι).symm ≪≫
      ((Scheme.Modules.overFunctorEquiv U).app (SheafOfModules.unit X.ringCatSheaf)).symm
  let e3 := SheafOfModules.mapFreeIso F I η
  let e12 : F.obj (M.over U) ≅ (Scheme.Modules.pullback U.ι).obj M := e1 ≪≫ e2
  refine ⟨e3.hom ≫ F.map p ≫ e12.hom, fun hp => ?_, fun hp => ?_⟩
  · have h1 : Epi (F.map p) := F.map_epi p
    have h0 : Epi e12.hom := @IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_hom e12)
    have h2 : Epi (F.map p ≫ e12.hom) := epi_comp _ _
    exact epi_comp _ _
  · have h1 : IsIso (F.map p) := Functor.map_isIso F p
    have h2 : IsIso (F.map p ≫ e12.hom) := IsIso.comp_isIso' h1 (Iso.isIso_hom _)
    exact IsIso.comp_isIso' (Iso.isIso_hom _) h2

theorem AlgebraicGeometry.Scheme.Modules.exists_pullback_iso_free_of_isLocallyFree
    {X : AlgebraicGeometry.Scheme.{u}} (M : X.Modules) [M.IsLocallyFree] (x : X) :
    ∃ (U : X.Opens) (I : Type u), x ∈ U ∧
      Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback U.ι).obj M ≅
        SheafOfModules.free (R := U.toScheme.ringCatSheaf) I) := by
  obtain ⟨q, hq⟩ := SheafOfModules.IsLocallyFree.exists_isLocallyFreeData (M := M)
  have hcov := q.coversTop
  rw [Opens.coversTop_iff] at hcov
  have hx : x ∈ (⨆ i, q.X i : X.Opens) := by rw [hcov]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  have hiso : IsIso (q.generators i).π := hq.isIso i
  obtain ⟨π, -, hπ⟩ := localTriv.transport M (q.X i) _ (q.generators i).π
  have := hπ hiso
  exact ⟨q.X i, (q.generators i).I, hi, ⟨(asIso π).symm⟩⟩

theorem AlgebraicGeometry.Scheme.Modules.isLocallyFree_of_pullback_iso_free
    {X : AlgebraicGeometry.Scheme.{u}} (M : X.Modules)
    (h : ∀ x : X, ∃ (U : X.Opens) (I : Type u), x ∈ U ∧
      Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback U.ι).obj M ≅
        SheafOfModules.free (R := U.toScheme.ringCatSheaf) I)) :
    M.IsLocallyFree := by
  refine AlgebraicGeometry.Scheme.Modules.isLocallyFree_of_restrict_free M fun x => ?_
  obtain ⟨U, I, hx, ⟨e⟩⟩ := h x
  exact ⟨U.toScheme, U.ι, inferInstance, I, ⟨⟨x, hx⟩, rfl⟩,
    ⟨(Scheme.Modules.restrictFunctorIsoPullback U.ι).app M ≪≫ e⟩⟩

theorem AlgebraicGeometry.Scheme.Modules.exists_epi_free_pullback_of_isFiniteType
    {X : AlgebraicGeometry.Scheme.{u}} (M : X.Modules) [M.IsFiniteType] (x : X) :
    ∃ (U : X.Opens) (J : Type u) (_ : Finite J)
      (π : (SheafOfModules.free (R := U.toScheme.ringCatSheaf) J : U.toScheme.Modules) ⟶
        (AlgebraicGeometry.Scheme.Modules.pullback U.ι).obj M), x ∈ U ∧ Epi π := by
  obtain ⟨σ, hσ⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData (M := M)
  have hcov := σ.coversTop
  rw [Opens.coversTop_iff] at hcov
  have hx' : x ∈ (⨆ i, σ.X i : X.Opens) := by rw [hcov]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx'
  have hfin : (σ.generators i).IsFiniteType := hσ.isFiniteType i
  obtain ⟨π, hπ, -⟩ := localTriv.transport M (σ.X i) _ (σ.generators i).π
  exact ⟨σ.X i, (σ.generators i).I, hfin.finite, π, hi, hπ inferInstance⟩

/-- `Y`-modules → `X.ringCatSheaf.over (image of g)`-modules: restrict along `image ≅ Y`, then apply
`overEquiv`. -/
private def localTriv.overF {X Y : Scheme.{u}} (g : Y ⟶ X) [IsOpenImmersion g] :
    SheafOfModules.{u} Y.ringCatSheaf ⥤ SheafOfModules.{u} (X.ringCatSheaf.over g.opensRange) :=
  Scheme.Modules.restrictFunctor g.isoOpensRange.inv ⋙ (Scheme.Modules.overEquiv g.opensRange).inverse

private instance localTriv.overF_pres {X Y : Scheme.{u}} (g : Y ⟶ X) [IsOpenImmersion g] :
    PreservesColimitsOfSize.{u, u} (localTriv.overF g) := by
  have h1 : PreservesColimitsOfSize.{u, u} (Scheme.Modules.restrictFunctor g.isoOpensRange.inv) :=
    inferInstance
  have h2 : PreservesColimitsOfSize.{u, u} (Scheme.Modules.overEquiv g.opensRange).inverse :=
    inferInstance
  exact @comp_preservesColimits _ _ _ _ _ _ _ _ h1 h2

/-- Generating sections of `M.restrict g` become generating sections of `M.over (image of g)`, with
the same index type. -/
private theorem localTriv.over_gen {X Y : Scheme.{u}} (M : X.Modules) (g : Y ⟶ X)
    [IsOpenImmersion g] (σ0 : (M.restrict g).GeneratingSections) [Finite σ0.I] :
    ∃ σ : (M.over g.opensRange).GeneratingSections, σ.IsFiniteType := by
  let U := g.opensRange
  let η : SheafOfModules.unit (X.ringCatSheaf.over U) ≅
      (localTriv.overF g).obj (SheafOfModules.unit Y.ringCatSheaf) :=
    (U.sheafOfModulesEquivOverInverseUnit X.ringCatSheaf).symm ≪≫
      (Scheme.Modules.overEquiv U).inverse.mapIso
        (Scheme.Modules.restrictUnitIso g.isoOpensRange.inv).symm
  let i : (localTriv.overF g).obj (M.restrict g) ≅ M.over U :=
    (Scheme.Modules.overEquiv U).inverse.mapIso
      ((Scheme.Modules.restrictFunctorComp g.isoOpensRange.inv g).symm.app M ≪≫
        (Scheme.Modules.restrictFunctorCongr g.isoOpensRange_inv_comp).app M ≪≫
        (Scheme.Modules.overFunctorEquiv U).symm.app M) ≪≫
      ((Scheme.Modules.overEquiv U).unitIso.app (M.over U)).symm
  have : Finite (σ0.map (localTriv.overF g) η).I := inferInstanceAs (Finite σ0.I)
  exact ⟨(σ0.map (localTriv.overF g) η).ofEpi i.hom, ⟨this⟩⟩

theorem AlgebraicGeometry.Scheme.Modules.isFiniteType_of_epi_free_pullback
    {X : AlgebraicGeometry.Scheme.{u}} (M : X.Modules)
    (h : ∀ x : X, ∃ (U : X.Opens) (J : Type u) (_ : Finite J)
      (π : (SheafOfModules.free (R := U.toScheme.ringCatSheaf) J : U.toScheme.Modules) ⟶
        (AlgebraicGeometry.Scheme.Modules.pullback U.ι).obj M), x ∈ U ∧ Epi π) :
    M.IsFiniteType := by
  choose U J hJ π hx hπ using h
  have hgen : ∀ x, ∃ σ : (M.over (U x).ι.opensRange).GeneratingSections, σ.IsFiniteType := by
    intro x
    let N : SheafOfModules.{u} (U x).toScheme.ringCatSheaf := M.restrict (U x).ι
    let p : SheafOfModules.free (R := (U x).toScheme.ringCatSheaf) (J x) ⟶ N :=
      π x ≫ (Scheme.Modules.restrictFunctorIsoPullback (U x).ι).inv.app M
    have hp : Epi p := by
      have := hπ x
      have h0 : Epi ((Scheme.Modules.restrictFunctorIsoPullback (U x).ι).inv.app M) :=
        @IsIso.epi_of_iso _ _ _ _ _
          (Iso.isIso_inv ((Scheme.Modules.restrictFunctorIsoPullback (U x).ι).app M))
      exact @epi_comp _ _ _ _ _ _ (hπ x) _ h0
    let σ0 : N.GeneratingSections :=
      (SheafOfModules.free.generatingSections (R := (U x).toScheme.ringCatSheaf) (J x)).ofEpi p
    have : Finite σ0.I := hJ x
    exact localTriv.over_gen M (U x).ι σ0
  choose σ hσ using hgen
  have hc : (Opens.grothendieckTopology X).CoversTop (fun x => (U x).ι.opensRange) := by
    rw [Opens.coversTop_iff]
    refine eq_top_iff.mpr fun x _ => Opens.mem_iSup.mpr ⟨x, ⟨⟨x, hx x⟩, rfl⟩⟩
  let d : SheafOfModules.LocalGeneratorsData.{u} M :=
    { I := X, X := fun x => (U x).ι.opensRange, coversTop := hc, generators := σ }
  have hd : d.IsFiniteType := { isFiniteType := hσ }
  exact { exists_localGeneratorsData := ⟨d, hd⟩ }

/-- For opens `V ≤ U`: `(V.ι)^*M ≅ j^*((U.ι)^*M)`, with `j : V → U` the inclusion. -/
noncomputable def AlgebraicGeometry.Scheme.Modules.pullbackOpensLEIso
    {X : AlgebraicGeometry.Scheme.{u}} (M : X.Modules) {V U : X.Opens} (hVU : V ≤ U) :
    (AlgebraicGeometry.Scheme.Modules.pullback V.ι).obj M ≅
      (AlgebraicGeometry.Scheme.Modules.pullback (X.homOfLE hVU)).obj
        ((AlgebraicGeometry.Scheme.Modules.pullback U.ι).obj M) :=
  (Scheme.Modules.pullbackCongr (X.homOfLE_ι hVU).symm).app M ≪≫
    ((Scheme.Modules.pullbackComp (X.homOfLE hVU) U.ι).app M).symm

/-- A trivialization shrinks to a smaller open. -/
theorem AlgebraicGeometry.Scheme.Modules.pullback_iso_free_of_le
    {X : AlgebraicGeometry.Scheme.{u}} (M : X.Modules) {V U : X.Opens} (hVU : V ≤ U) (I : Type u)
    (e : (AlgebraicGeometry.Scheme.Modules.pullback U.ι).obj M ≅
      SheafOfModules.free (R := U.toScheme.ringCatSheaf) I) :
    Nonempty ((AlgebraicGeometry.Scheme.Modules.pullback V.ι).obj M ≅
      SheafOfModules.free (R := V.toScheme.ringCatSheaf) I) :=
  ⟨Scheme.Modules.pullbackOpensLEIso M hVU ≪≫
    (Scheme.Modules.pullback (X.homOfLE hVU)).mapIso e ≪≫
    Scheme.Modules.pullbackObjFreeIso (X.homOfLE hVU) I⟩

/-- An epimorphism from a free sheaf shrinks to a smaller open. -/
theorem AlgebraicGeometry.Scheme.Modules.epi_free_pullback_of_le
    {X : AlgebraicGeometry.Scheme.{u}} (M : X.Modules) {V U : X.Opens} (hVU : V ≤ U) (J : Type u)
    (π : (SheafOfModules.free (R := U.toScheme.ringCatSheaf) J : U.toScheme.Modules) ⟶
      (AlgebraicGeometry.Scheme.Modules.pullback U.ι).obj M) (hπ : Epi π) :
    ∃ π' : (SheafOfModules.free (R := V.toScheme.ringCatSheaf) J : V.toScheme.Modules) ⟶
      (AlgebraicGeometry.Scheme.Modules.pullback V.ι).obj M, Epi π' := by
  have h1 : Epi ((Scheme.Modules.pullback (X.homOfLE hVU)).map π) :=
    @Functor.map_epi _ _ _ _ (Scheme.Modules.pullback (X.homOfLE hVU)) _ _ _ π hπ
  have h2 : Epi (Scheme.Modules.pullbackOpensLEIso M hVU).inv :=
    @IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_inv _)
  have h3 : Epi (Scheme.Modules.pullbackObjFreeIso (X.homOfLE hVU) J).inv :=
    @IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_inv _)
  have h4 := @epi_comp _ _ _ _ _ _ h1 _ h2
  exact ⟨_, @epi_comp _ _ _ _ _ _ h3 _ h4⟩

/-- Properties holding on finitely many open neighbourhoods of a point, each stable under shrinking,
hold simultaneously on a common open neighbourhood. -/
theorem AlgebraicGeometry.Scheme.Modules.exists_common_open
    {X : AlgebraicGeometry.Scheme.{u}} {ι : Type*} [Fintype ι] (x : X) (P : ι → X.Opens → Prop)
    (hmono : ∀ i (V U : X.Opens), V ≤ U → P i U → P i V)
    (h : ∀ i, ∃ U : X.Opens, x ∈ U ∧ P i U) :
    ∃ V : X.Opens, x ∈ V ∧ ∀ i, P i V := by
  choose U hx hP using h
  refine ⟨Finset.univ.inf U, ?_, fun i => hmono i _ _ (Finset.inf_le (Finset.mem_univ i)) (hP i)⟩
  rw [← SetLike.mem_coe, Opens.coe_finset_inf, Finset.inf_set_eq_iInter]
  exact Set.mem_iInter₂.mpr fun i _ => hx i

end
