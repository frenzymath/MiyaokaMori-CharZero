import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.ShortExactLocallySplit
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.ModulesBiproductLocallyFree
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.LocalTrivializationPullback
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.PullbackOpenImmersionShortExact

/-! # Extensions of locally free sheaves are locally free

In a short exact sequence `0 → F → G → H → 0` with `F`, `H` locally free (`H` of finite type), `G` is
locally free (the sequence splits locally). Used for the extensions of weighted bundles in §2 of the
paper.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open AlgebraicGeometry

/-- For opens `V ≤ U`: `(V.ι)^* ≅ (U.ι)^* ⋙ j^*` (a natural isomorphism of functors), `j : V → U` the
inclusion. -/
private def extLF.natIso {X : Scheme.{u}} {V U : X.Opens} (hVU : V ≤ U) :
    Scheme.Modules.pullback V.ι ≅
      Scheme.Modules.pullback U.ι ⋙ Scheme.Modules.pullback (X.homOfLE hVU) :=
  Scheme.Modules.pullbackCongr (X.homOfLE_ι hVU).symm ≪≫
    (Scheme.Modules.pullbackComp (X.homOfLE hVU) U.ι).symm

/-- A section (right inverse) on `U` shrinks to a smaller open `V`. -/
theorem extLF.section_of_le {X : Scheme.{u}} {M N : X.Modules} (g : M ⟶ N) {V U : X.Opens}
    (hVU : V ≤ U)
    (σ : (Scheme.Modules.pullback U.ι).obj N ⟶ (Scheme.Modules.pullback U.ι).obj M)
    (hσ : σ ≫ (Scheme.Modules.pullback U.ι).map g = 𝟙 _) :
    ∃ σ' : (Scheme.Modules.pullback V.ι).obj N ⟶ (Scheme.Modules.pullback V.ι).obj M,
      σ' ≫ (Scheme.Modules.pullback V.ι).map g = 𝟙 _ := by
  refine ⟨(extLF.natIso hVU).hom.app N ≫ (Scheme.Modules.pullback (X.homOfLE hVU)).map σ ≫
    (extLF.natIso hVU).inv.app M, ?_⟩
  have hnat := (extLF.natIso hVU).inv.naturality g
  simp only [Functor.comp_map] at hnat
  rw [Category.assoc, Category.assoc, ← hnat, ← Functor.map_comp_assoc, hσ,
    CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id_app]

theorem AlgebraicGeometry.Scheme.Modules.isLocallyFree_of_shortExact {X : AlgebraicGeometry.Scheme.{u}}
    {S : CategoryTheory.ShortComplex X.Modules} (hS : S.ShortExact)
    [S.X₁.IsLocallyFree] [S.X₃.IsLocallyFree] [S.X₃.IsFiniteType] :
    S.X₂.IsLocallyFree := by
  refine Scheme.Modules.isLocallyFree_of_pullback_iso_free _ fun x => ?_
  obtain ⟨U, hxU, σ, hσ⟩ := Scheme.Modules.shortExact_locallySplit hS x
  obtain ⟨U₁, I₁, hx₁, ⟨e₁⟩⟩ := Scheme.Modules.exists_pullback_iso_free_of_isLocallyFree S.X₁ x
  obtain ⟨U₃, I₃, hx₃, ⟨e₃⟩⟩ := Scheme.Modules.exists_pullback_iso_free_of_isLocallyFree S.X₃ x
  -- the common open V = U ⊓ U₁ ⊓ U₃
  let V : X.Opens := U ⊓ U₁ ⊓ U₃
  have hxV : x ∈ V := ⟨⟨hxU, hx₁⟩, hx₃⟩
  obtain ⟨σ', hσ'⟩ := extLF.section_of_le S.g (inf_le_left.trans inf_le_left : V ≤ U) σ hσ
  obtain ⟨e₁'⟩ := Scheme.Modules.pullback_iso_free_of_le S.X₁
    (inf_le_left.trans inf_le_right : V ≤ U₁) I₁ e₁
  obtain ⟨e₃'⟩ := Scheme.Modules.pullback_iso_free_of_le S.X₃ (inf_le_right : V ≤ U₃) I₃ e₃
  -- the short exact sequence on V has a section, hence splits
  have hSV := Scheme.Modules.shortExact_map_pullback_of_isOpenImmersion V.ι hS
  have := hSV.mono_f
  let spl : (S.map (Scheme.Modules.pullback V.ι)).Splitting :=
    ShortComplex.Splitting.ofExactOfSection _ hSV.exact σ' hσ' hSV.mono_f
  let G : WalkingPair → V.toScheme.Modules :=
    pairFunction ((Scheme.Modules.pullback V.ι).obj S.X₁) ((Scheme.Modules.pullback V.ι).obj S.X₃)
  let e₂ : (Scheme.Modules.pullback V.ι).obj S.X₂ ≅ biproduct G :=
    spl.isoBinaryBiproduct ≪≫
      biproduct.uniqueUpToIso G
        ((BinaryBicone.toBiconeIsBilimit _).symm (BinaryBiproduct.isBilimit _ _))
  let I : WalkingPair → Type u := fun i => WalkingPair.casesOn i I₁ I₃
  obtain ⟨e⟩ := Scheme.Modules.biproduct_iso_free G I
    (fun i => match i with
      | WalkingPair.left => e₁'
      | WalkingPair.right => e₃')
  exact ⟨V, _, hxV, ⟨e₂ ≪≫ e⟩⟩

end
