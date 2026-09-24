import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.LocalTrivializationPullback
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.PullbackOpenImmersionShortExact
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.ShortExactLocallySplit
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.RankAtStalkLocalIso
import MiyaokaMori.AlgebraicGeometry.Modules.FiniteTypeRestrictFreeIndexFinite

/-! # Additivity of the rank in short exact sequences

The rank is additive in a short exact sequence of locally free sheaves: `rk G = rk F + rk H`
(pointwise, the dimension of the fibre is additive). Used for `rk E = n+1` in the tangent sequence
(2.2) of §2.1 of the paper.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open AlgebraicGeometry

private def rankAdd.pullbackLEIso {X : Scheme.{u}} {V U : X.Opens} (hVU : V ≤ U) :
    Scheme.Modules.pullback V.ι ≅
      Scheme.Modules.pullback U.ι ⋙ Scheme.Modules.pullback (X.homOfLE hVU) :=
  Scheme.Modules.pullbackCongr (X.homOfLE_ι hVU).symm ≪≫
    (Scheme.Modules.pullbackComp (X.homOfLE hVU) U.ι).symm

private theorem rankAdd.section_of_le {X : Scheme.{u}} {M N : X.Modules} (g : M ⟶ N)
    {V U : X.Opens} (hVU : V ≤ U)
    (σ : (Scheme.Modules.pullback U.ι).obj N ⟶
      (Scheme.Modules.pullback U.ι).obj M)
    (hσ : σ ≫ (Scheme.Modules.pullback U.ι).map g = 𝟙 _) :
    ∃ σ' : (Scheme.Modules.pullback V.ι).obj N ⟶
        (Scheme.Modules.pullback V.ι).obj M,
      σ' ≫ (Scheme.Modules.pullback V.ι).map g = 𝟙 _ := by
  refine ⟨(rankAdd.pullbackLEIso hVU).hom.app N ≫
    (Scheme.Modules.pullback (X.homOfLE hVU)).map σ ≫
    (rankAdd.pullbackLEIso hVU).inv.app M, ?_⟩
  have hnat := (rankAdd.pullbackLEIso hVU).inv.naturality g
  simp only [Functor.comp_map] at hnat
  rw [Category.assoc, Category.assoc, ← hnat, ← Functor.map_comp_assoc, hσ,
    CategoryTheory.Functor.map_id, Category.id_comp, Iso.hom_inv_id_app]

/-- The rank at a stalk is additive in a short exact sequence of locally free sheaves of finite type:
`rk X₂ = rk X₁ + rk X₃`. -/
theorem AlgebraicGeometry.Scheme.Modules.rankAtStalk_add_of_shortExact
    {X : AlgebraicGeometry.Scheme.{u}} {S : CategoryTheory.ShortComplex X.Modules}
    (hS : S.ShortExact) [S.X₁.IsLocallyFree] [S.X₁.IsFiniteType]
    [S.X₃.IsLocallyFree] [S.X₃.IsFiniteType] (x : X) :
    AlgebraicGeometry.Scheme.Modules.rankAtStalk S.X₂ x =
      AlgebraicGeometry.Scheme.Modules.rankAtStalk S.X₁ x +
        AlgebraicGeometry.Scheme.Modules.rankAtStalk S.X₃ x := by
  obtain ⟨U, hxU, σ, hσ⟩ := Scheme.Modules.shortExact_locallySplit hS x
  obtain ⟨U₁, I₁, hx₁, ⟨e₁⟩⟩ :=
    Scheme.Modules.exists_pullback_iso_free_of_isLocallyFree S.X₁ x
  obtain ⟨U₃, I₃, hx₃, ⟨e₃⟩⟩ :=
    Scheme.Modules.exists_pullback_iso_free_of_isLocallyFree S.X₃ x
  let V : X.Opens := U ⊓ U₁ ⊓ U₃
  have hxV : x ∈ V := ⟨⟨hxU, hx₁⟩, hx₃⟩
  obtain ⟨σ', hσ'⟩ :=
    rankAdd.section_of_le S.g (inf_le_left.trans inf_le_left : V ≤ U) σ hσ
  obtain ⟨e₁'⟩ := Scheme.Modules.pullback_iso_free_of_le S.X₁
    (inf_le_left.trans inf_le_right : V ≤ U₁) I₁ e₁
  obtain ⟨e₃'⟩ := Scheme.Modules.pullback_iso_free_of_le S.X₃
    (inf_le_right : V ≤ U₃) I₃ e₃
  let : Finite I₁ := Scheme.Modules.finite_index_of_restrict_iso_free
    S.X₁ V I₁ e₁' x hxV
  let : Finite I₃ := Scheme.Modules.finite_index_of_restrict_iso_free
    S.X₃ V I₃ e₃' x hxV
  let : Fintype I₁ := Fintype.ofFinite I₁
  let : Fintype I₃ := Fintype.ofFinite I₃
  have hSV := Scheme.Modules.shortExact_map_pullback_of_isOpenImmersion V.ι hS
  let spl : (S.map (Scheme.Modules.pullback V.ι)).Splitting :=
    ShortComplex.Splitting.ofExactOfSection _ hSV.exact σ' hσ' hSV.mono_f
  let K : V.toScheme.Modules :=
    SheafOfModules.free (R := V.toScheme.ringCatSheaf) I₁
  let L : V.toScheme.Modules :=
    SheafOfModules.free (R := V.toScheme.ringCatSheaf) I₃
  let : HasBinaryBiproduct K L :=
    CategoryTheory.Abelian.hasBinaryBiproducts.has_binary_biproduct _ _
  let e₂ : (Scheme.Modules.pullback V.ι).obj S.X₂ ≅
      SheafOfModules.free (R := V.toScheme.ringCatSheaf) (I₁ ⊕ I₃) :=
    spl.isoBinaryBiproduct ≪≫
      biprod.mapIso e₁' e₃' ≪≫
      (@biprod.isoCoprod V.toScheme.Modules _ _ K L _) ≪≫
      SheafOfModules.freeSumIso (R := V.toScheme.ringCatSheaf) I₁ I₃
  rw [Scheme.Modules.rankAtStalk_of_restrict_iso_free S.X₂ V (I₁ ⊕ I₃) e₂ x hxV,
    Scheme.Modules.rankAtStalk_of_restrict_iso_free S.X₁ V I₁ e₁' x hxV,
    Scheme.Modules.rankAtStalk_of_restrict_iso_free S.X₃ V I₃ e₃' x hxV]
  exact Fintype.card_sum

end
