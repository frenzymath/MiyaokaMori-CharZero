import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Basic.ModulesPow
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.LocalTrivializationPullback

/-! # Finite biproducts of locally free sheaves

A finite direct sum (the biproduct in `X.Modules`) of locally free (resp. finite type) `O_X`-modules
is locally free (resp. of finite type). Registered as instances, so that calls such as
`weightedSymAlgebra (fun _ => ⊕_i Q_i)` find their hypotheses automatically.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open AlgebraicGeometry

/-- The family of free sheaves `i ↦ O_Y^{(I_i)}` (a named definition, so that instance search
recognizes its biproduct). -/
def biproductLF.fam (Y : Scheme.{u}) {ι : Type} (I : ι → Type u) : ι → Y.Modules :=
  fun i => SheafOfModules.free (R := Y.ringCatSheaf) (I i)

/-- A finite biproduct of free sheaves is free: `⨁_i O^{(I_i)} ≅ O^{(Σ_i I_i)}`. -/
def biproductLF.freeSigmaIso {Y : Scheme.{u}} {ι : Type} [Fintype ι] (I : ι → Type u) :
    biproduct (biproductLF.fam Y I) ≅
      (SheafOfModules.free (R := Y.ringCatSheaf) (Σ i, I i) : Y.Modules) :=
  biproduct.isoCoproduct _ ≪≫
    sigmaSigmaIso (C := Y.Modules) I (fun _ _ => SheafOfModules.unit Y.ringCatSheaf)

/-- A finite biproduct of sheaves each isomorphic to a free sheaf is isomorphic to a free sheaf (on
the disjoint union of the index types). -/
theorem AlgebraicGeometry.Scheme.Modules.biproduct_iso_free {Y : AlgebraicGeometry.Scheme.{u}}
    {ι : Type} [Fintype ι] (G : ι → Y.Modules) (I : ι → Type u)
    (e : ∀ i, G i ≅ SheafOfModules.free (R := Y.ringCatSheaf) (I i)) :
    Nonempty (biproduct G ≅ SheafOfModules.free (R := Y.ringCatSheaf) (Σ i, I i)) :=
  ⟨biproduct.mapIso (g := biproductLF.fam Y I) e ≪≫ biproductLF.freeSigmaIso I⟩

/-- Pullback along an open commutes with finite biproducts. -/
private def biproductLF.pullbackBiproductIso {X : Scheme.{u}} {ι : Type} [Fintype ι]
    (F : ι → X.Modules) (V : X.Opens) :
    (Scheme.Modules.pullback V.ι).obj (biproduct F) ≅
      biproduct fun i => (Scheme.Modules.pullback V.ι).obj (F i) :=
  (Scheme.Modules.pullback V.ι).mapBiproduct F

instance AlgebraicGeometry.Scheme.Modules.biproduct_isLocallyFree {X : AlgebraicGeometry.Scheme.{u}}
    {ι : Type} [Fintype ι] (F : ι → X.Modules) [∀ i, (F i).IsLocallyFree] :
    (CategoryTheory.Limits.biproduct F).IsLocallyFree := by
  refine Scheme.Modules.isLocallyFree_of_pullback_iso_free _ fun x => ?_
  obtain ⟨V, hxV, hV⟩ := Scheme.Modules.exists_common_open (ι := ι) x
    (fun i U => ∃ I : Type u, Nonempty ((Scheme.Modules.pullback U.ι).obj (F i) ≅
      SheafOfModules.free (R := U.toScheme.ringCatSheaf) I))
    (fun i V U hVU ⟨I, ⟨e⟩⟩ => ⟨I, Scheme.Modules.pullback_iso_free_of_le (F i) hVU I e⟩)
    (fun i => by
      obtain ⟨U, I, hx, he⟩ := Scheme.Modules.exists_pullback_iso_free_of_isLocallyFree (F i) x
      exact ⟨U, hx, I, he⟩)
  choose I e using hV
  exact ⟨V, Σ i, I i, hxV, ⟨biproductLF.pullbackBiproductIso F V ≪≫
    biproduct.mapIso (g := biproductLF.fam V.toScheme I) (fun i => (e i).some) ≪≫
    biproductLF.freeSigmaIso I⟩⟩

instance AlgebraicGeometry.Scheme.Modules.biproduct_isFiniteType {X : AlgebraicGeometry.Scheme.{u}}
    {ι : Type} [Fintype ι] (F : ι → X.Modules) [∀ i, (F i).IsFiniteType] :
    (CategoryTheory.Limits.biproduct F).IsFiniteType := by
  refine Scheme.Modules.isFiniteType_of_epi_free_pullback _ fun x => ?_
  obtain ⟨V, hxV, hV⟩ := Scheme.Modules.exists_common_open (ι := ι) x
    (fun i U => ∃ (J : Type u) (_ : Finite J)
      (π : (SheafOfModules.free (R := U.toScheme.ringCatSheaf) J : U.toScheme.Modules) ⟶
        (Scheme.Modules.pullback U.ι).obj (F i)), Epi π)
    (fun i V U hVU ⟨J, hJ, π, hπ⟩ =>
      ⟨J, hJ, Scheme.Modules.epi_free_pullback_of_le (F i) hVU J π hπ⟩)
    (fun i => by
      obtain ⟨U, J, hJ, π, hx, hπ⟩ :=
        Scheme.Modules.exists_epi_free_pullback_of_isFiniteType (F i) x
      exact ⟨U, hx, J, hJ, π, hπ⟩)
  choose J hJ π hπ using hV
  have h1 : Epi (biproduct.map (f := biproductLF.fam V.toScheme J) π) :=
    @biproduct.map_epi _ _ _ _ (biproductLF.fam V.toScheme J) _ _ _ π hπ
  have h2 : Epi (biproductLF.pullbackBiproductIso F V).inv :=
    @IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_inv _)
  have h3 : Epi (biproductLF.freeSigmaIso (Y := V.toScheme) J).inv :=
    @IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_inv _)
  have h4 := @epi_comp _ _ _ _ _ _ h1 _ h2
  exact ⟨V, Σ i, J i, inferInstance, _, hxV, @epi_comp _ _ _ _ _ _ h3 _ h4⟩

end
