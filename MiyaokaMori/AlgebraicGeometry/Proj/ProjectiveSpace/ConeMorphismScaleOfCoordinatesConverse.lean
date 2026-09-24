import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.ProjectiveSpace.ConeMorphismScaleOfCoordinatesCone

/-! # Scaling a cone morphism from its coordinates: the converse

Converse of `twistedAffineCone.comp_eq_scale_of_coordinates`: if a
`C`-morphism `J : S → Z` into a twisted affine cone satisfies `i ≫ J = scale u (i ≫ q ≫ s)` on `i : W → S`, then
every coordinate of `J` pulled back along `i` is `u` times the pulled-back seed coordinate. Together with the
reverse transport lemma `sectionPullbackAlong_coord_transport_rev` this gives the based-jet statement
`BasedJet.coneCoordinate_restrict_of_eq_scale`.

Source: §3 of the paper (Section 3): scalar jets and their exclusion in the proof of
Lemma 4.1.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

private theorem iso_val_app_top_injective' {X : AlgebraicGeometry.Scheme.{u}} {A B : X.Modules} (e : A ≅ B)
    {x y : (A.val.obj (Opposite.op ⊤) : Type u)}
    (h : (e.hom.val.app (Opposite.op ⊤)).hom x = (e.hom.val.app (Opposite.op ⊤)).hom y) : x = y := by
  have hx : ∀ z : (A.val.obj (Opposite.op ⊤) : Type u),
      (e.inv.val.app (Opposite.op ⊤)).hom ((e.hom.val.app (Opposite.op ⊤)).hom z) = z := by
    intro z
    exact congrArg (fun ψ : A ⟶ A => (ψ.val.app (Opposite.op ⊤)).hom z) e.hom_inv_id
  exact (hx x).symm.trans ((congrArg (fun z => (e.inv.val.app (Opposite.op ⊤)).hom z) h).trans (hx y))

/-- Converse of `twistedAffineCone.comp_eq_scale_of_coordinates`: if `i ≫ J = scale u (i ≫ q ≫ s)`, then the
`ℓ`-th coordinate of `J` pulled back along `i` is `u • i^* q^* fs_ℓ`. -/
theorem twistedAffineCone.coordinate_of_comp_eq_scale {k : Type u} [Field k] {C : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] (A : C.Modules) [A.IsLineBundle]
    (N : ℕ) {ι : Type u} (deg : ι → ℕ) (F : ι → MvPolynomial (Fin (N + 1)) k)
    (hF : ∀ j, (F j).IsHomogeneous (deg j))
    (fs : Fin (N + 1) → (A.val.obj (Opposite.op ⊤) : Type u))
    (hvanish : ∀ j, evalHomogeneousAtSections A (F j) (hF j) fs = 0)
    {S : AlgebraicGeometry.Scheme.{u}} (q : S ⟶ C) (J : S ⟶ (twistedAffineCone A N deg F hF).left)
    (m : CategoryTheory.Over.mk q ⟶
      AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A (N + 1)))
    (hm : m.left = J ≫ twistedAffineCone.ι A N deg F hF)
    {W : AlgebraicGeometry.Scheme.{u}} (i : W ⟶ S) (u : Γ(W, ⊤)ˣ)
    (h : i ≫ J = twistedAffineCone.scale A N deg F hF u (i ≫ q ≫ (seedSection A N fs deg F hF hvanish).1))
    (ℓ : Fin (N + 1)) :
    sectionPullbackAlong i
        ((((AlgebraicGeometry.Scheme.Modules.pullback q).map
            (biproduct.π (fun _ : Fin (N + 1) => A) ℓ)).val.app (Opposite.op ⊤)).hom
          (AlgebraicGeometry.Scheme.totalSpaceHomEquiv (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))
            (CategoryTheory.Over.mk q) m))
      = (show W.ringCatSheaf.obj.obj (Opposite.op ⊤) from (u : Γ(W, ⊤))) •
          sectionPullbackAlong i (sectionPullbackAlong q (fs ℓ)) := by
  have hLF : (⨁ fun _ : Fin (N + 1) => A).IsLocallyFree :=
    inferInstanceAs (AlgebraicGeometry.Scheme.Modules.pow A (N + 1)).IsLocallyFree
  have hFT : (⨁ fun _ : Fin (N + 1) => A).IsFiniteType :=
    inferInstanceAs (AlgebraicGeometry.Scheme.Modules.pow A (N + 1)).IsFiniteType
  have hZι : twistedAffineCone.ι A N deg F hF ≫
      (AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))).hom
      = (twistedAffineCone A N deg F hF).hom := rfl
  have hsι : (seedSection A N fs deg F hF hvanish).1 ≫ twistedAffineCone.ι A N deg F hF
      = (seedSection.totSection A N fs).1 :=
    AlgebraicGeometry.IsClosedImmersion.lift_fac (twistedAffineCone.ι A N deg F hF) _ _
  have hs : (seedSection A N fs deg F hF hvanish).1 ≫ (twistedAffineCone A N deg F hF).hom = 𝟙 C :=
    (seedSection A N fs deg F hF hvanish).2
  generalize (seedSection A N fs deg F hF hvanish).1 = s at hsι hs h ⊢
  have hb : i ≫ q = (i ≫ q ≫ s) ≫ (twistedAffineCone A N deg F hF).hom := by
    simp only [CategoryTheory.Category.assoc, hs, CategoryTheory.Category.comp_id]
  have hL : ((CategoryTheory.Over.homMk i hb :
      CategoryTheory.Over.mk ((i ≫ q ≫ s) ≫ (twistedAffineCone A N deg F hF).hom) ⟶ CategoryTheory.Over.mk q)
        ≫ m).left = (i ≫ J) ≫ twistedAffineCone.ι A N deg F hF := by
    exact (congrArg (fun x => i ≫ x) hm).trans (CategoryTheory.Category.assoc _ _ _).symm
  -- the two `Over`-morphisms agree: `(i ≫ J) ≫ ι_Z = scaleTot u (i ≫ q ≫ s)`
  have hOver : (CategoryTheory.Over.homMk i hb :
      CategoryTheory.Over.mk ((i ≫ q ≫ s) ≫ (twistedAffineCone A N deg F hF).hom) ⟶ CategoryTheory.Over.mk q) ≫ m
      = (AlgebraicGeometry.Scheme.totalSpaceHomEquiv (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))
          (CategoryTheory.Over.mk ((i ≫ q ≫ s) ≫ (twistedAffineCone A N deg F hF).hom))).symm
        ((show W.ringCatSheaf.val.obj (Opposite.op ⊤) from (u : Γ(W, ⊤))) •
          AlgebraicGeometry.Scheme.totalSpaceHomEquiv (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))
            (CategoryTheory.Over.mk ((i ≫ q ≫ s) ≫ (twistedAffineCone A N deg F hF).hom))
            (CategoryTheory.Over.homMk ((i ≫ q ≫ s) ≫ twistedAffineCone.ι A N deg F hF)
              (CategoryTheory.Category.assoc _ _ _))) := by
    apply CategoryTheory.Over.OverMorphism.ext
    rw [hL, h, twistedAffineCone.scale_comp_ι]
    rfl
  have hcoordEq := congrArg (fun φ : CategoryTheory.Over.mk ((i ≫ q ≫ s) ≫ (twistedAffineCone A N deg F hF).hom) ⟶
      AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A (N + 1)) =>
    (((AlgebraicGeometry.Scheme.Modules.pullback ((i ≫ q ≫ s) ≫ (twistedAffineCone A N deg F hF).hom)).map
        (biproduct.π (fun _ : Fin (N + 1) => A) ℓ)).val.app (Opposite.op ⊤)).hom
      (AlgebraicGeometry.Scheme.totalSpaceHomEquiv (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))
        (CategoryTheory.Over.mk ((i ≫ q ≫ s) ≫ (twistedAffineCone A N deg F hF).hom)) φ)) hOver
  simp only [Equiv.apply_symm_apply] at hcoordEq
  -- the second `Over`-morphism: `g ≫ ι_Z = i ≫ (q ≫ s ≫ ι_Z)`
  have h₂ : (q ≫ s ≫ twistedAffineCone.ι A N deg F hF) ≫
      (AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))).hom = q := by
    rw [CategoryTheory.Category.assoc, CategoryTheory.Category.assoc, hZι, hs, CategoryTheory.Category.comp_id]
  have h₃ : (s ≫ twistedAffineCone.ι A N deg F hF) ≫
      (AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))).hom
      = (CategoryTheory.Over.mk (𝟙 C)).hom := by
    rw [CategoryTheory.Category.assoc, hZι, hs]; rfl
  have hq₀ : q ≫ (CategoryTheory.Over.mk (𝟙 C)).hom = q := CategoryTheory.Category.comp_id q
  have hm₂ : (CategoryTheory.Over.homMk ((i ≫ q ≫ s) ≫ twistedAffineCone.ι A N deg F hF)
        (CategoryTheory.Category.assoc _ _ _) :
        CategoryTheory.Over.mk ((i ≫ q ≫ s) ≫ (twistedAffineCone A N deg F hF).hom) ⟶
          AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A (N + 1)))
      = (CategoryTheory.Over.homMk i hb :
          CategoryTheory.Over.mk ((i ≫ q ≫ s) ≫ (twistedAffineCone A N deg F hF).hom) ⟶
            CategoryTheory.Over.mk q) ≫
        ((CategoryTheory.Over.homMk q hq₀ : CategoryTheory.Over.mk q ⟶ CategoryTheory.Over.mk (𝟙 C)) ≫
          CategoryTheory.Over.homMk (s ≫ twistedAffineCone.ι A N deg F hF) h₃) := by
    apply CategoryTheory.Over.OverMorphism.ext
    change (i ≫ q ≫ s) ≫ twistedAffineCone.ι A N deg F hF = i ≫ (q ≫ (s ≫ twistedAffineCone.ι A N deg F hF))
    simp only [CategoryTheory.Category.assoc]
  rw [hm₂] at hcoordEq
  -- both coordinates via naturality along `i`
  have hnatL : (((AlgebraicGeometry.Scheme.Modules.pullback ((i ≫ q ≫ s) ≫ (twistedAffineCone A N deg F hF).hom)).map
        (biproduct.π (fun _ : Fin (N + 1) => A) ℓ)).val.app (Opposite.op ⊤)).hom
        (AlgebraicGeometry.Scheme.totalSpaceHomEquiv (AlgebraicGeometry.Scheme.Modules.pow A (N + 1)) (CategoryTheory.Over.mk ((i ≫ q ≫ s) ≫ (twistedAffineCone A N deg F hF).hom)) ((CategoryTheory.Over.homMk i hb : (CategoryTheory.Over.mk ((i ≫ q ≫ s) ≫ (twistedAffineCone A N deg F hF).hom)) ⟶ (CategoryTheory.Over.mk q)) ≫ m))
      = (((AlgebraicGeometry.Scheme.Modules.pullbackCongr hb).hom.app A).val.app (Opposite.op ⊤)).hom
        ((((AlgebraicGeometry.Scheme.Modules.pullbackComp i q).hom.app A).val.app (Opposite.op ⊤)).hom
        (sectionPullbackAlong i ((((AlgebraicGeometry.Scheme.Modules.pullback q).map
        (biproduct.π (fun _ : Fin (N + 1) => A) ℓ)).val.app (Opposite.op ⊤)).hom
        (AlgebraicGeometry.Scheme.totalSpaceHomEquiv (AlgebraicGeometry.Scheme.Modules.pow A (N + 1)) (CategoryTheory.Over.mk q) m)))) :=
    AlgebraicGeometry.Scheme.totalSpaceHomEquiv_naturality_coordinate_of_eq
      (fun _ : Fin (N + 1) => A) (CategoryTheory.Over.mk q) i _ hb m ℓ
  have hnatR : (((AlgebraicGeometry.Scheme.Modules.pullback ((i ≫ q ≫ s) ≫ (twistedAffineCone A N deg F hF).hom)).map
        (biproduct.π (fun _ : Fin (N + 1) => A) ℓ)).val.app (Opposite.op ⊤)).hom
        (AlgebraicGeometry.Scheme.totalSpaceHomEquiv (AlgebraicGeometry.Scheme.Modules.pow A (N + 1)) (CategoryTheory.Over.mk ((i ≫ q ≫ s) ≫ (twistedAffineCone A N deg F hF).hom)) ((CategoryTheory.Over.homMk i hb : (CategoryTheory.Over.mk ((i ≫ q ≫ s) ≫ (twistedAffineCone A N deg F hF).hom)) ⟶ (CategoryTheory.Over.mk q)) ≫
        ((CategoryTheory.Over.homMk q hq₀ : CategoryTheory.Over.mk q ⟶ CategoryTheory.Over.mk (𝟙 C)) ≫
        CategoryTheory.Over.homMk (s ≫ twistedAffineCone.ι A N deg F hF) h₃)))
      = (((AlgebraicGeometry.Scheme.Modules.pullbackCongr hb).hom.app A).val.app (Opposite.op ⊤)).hom
        ((((AlgebraicGeometry.Scheme.Modules.pullbackComp i q).hom.app A).val.app (Opposite.op ⊤)).hom
        (sectionPullbackAlong i ((((AlgebraicGeometry.Scheme.Modules.pullback q).map
        (biproduct.π (fun _ : Fin (N + 1) => A) ℓ)).val.app (Opposite.op ⊤)).hom
        (AlgebraicGeometry.Scheme.totalSpaceHomEquiv (AlgebraicGeometry.Scheme.Modules.pow A (N + 1)) (CategoryTheory.Over.mk q)
        ((CategoryTheory.Over.homMk q hq₀ : CategoryTheory.Over.mk q ⟶ CategoryTheory.Over.mk (𝟙 C)) ≫
        CategoryTheory.Over.homMk (s ≫ twistedAffineCone.ι A N deg F hF) h₃))))) :=
    AlgebraicGeometry.Scheme.totalSpaceHomEquiv_naturality_coordinate_of_eq
      (fun _ : Fin (N + 1) => A) (CategoryTheory.Over.mk q) i _ hb
      ((CategoryTheory.Over.homMk q hq₀ : CategoryTheory.Over.mk q ⟶ CategoryTheory.Over.mk (𝟙 C)) ≫
        CategoryTheory.Over.homMk (s ≫ twistedAffineCone.ι A N deg F hF) h₃) ℓ
  -- the coordinate of the seed section over `q`
  have hnat0 := AlgebraicGeometry.Scheme.totalSpaceHomEquiv_naturality_coordinate_of_eq
    (fun _ : Fin (N + 1) => A) (CategoryTheory.Over.mk (𝟙 C)) q _ hq₀
    (CategoryTheory.Over.homMk (s ≫ twistedAffineCone.ι A N deg F hF) h₃) ℓ
  have hseed := seedSection.totSection_coordinate A N fs ℓ
    (CategoryTheory.Over.homMk (s ≫ twistedAffineCone.ι A N deg F hF) h₃) hsι
  have hid : (((AlgebraicGeometry.Scheme.Modules.pullbackId C).inv.app A).val.app (Opposite.op ⊤)).hom (fs ℓ)
      = sectionPullbackAlong (𝟙 C) (fs ℓ) := by
    conv_lhs => rw [← sectionPullbackAlong_id (fs ℓ)]
    exact congrArg (fun ψ => (ψ.val.app (Opposite.op ⊤)).hom (sectionPullbackAlong (𝟙 C) (fs ℓ)))
      (CategoryTheory.Iso.hom_inv_id_app (AlgebraicGeometry.Scheme.Modules.pullbackId C) A)
  have hcomp0 := sectionPullbackAlong_comp q (𝟙 C) (fs ℓ)
  have hcongr0 := sectionPullbackAlong_congr hq₀ (fs ℓ)
  have hseedq : (((AlgebraicGeometry.Scheme.Modules.pullback q).map
        (biproduct.π (fun _ : Fin (N + 1) => A) ℓ)).val.app (Opposite.op ⊤)).hom
        (AlgebraicGeometry.Scheme.totalSpaceHomEquiv (AlgebraicGeometry.Scheme.Modules.pow A (N + 1)) (CategoryTheory.Over.mk q)
        ((CategoryTheory.Over.homMk q hq₀ : CategoryTheory.Over.mk q ⟶ CategoryTheory.Over.mk (𝟙 C)) ≫
        CategoryTheory.Over.homMk (s ≫ twistedAffineCone.ι A N deg F hF) h₃))
      = sectionPullbackAlong q (fs ℓ) := by
    exact hnat0.trans ((congrArg (fun z => (((AlgebraicGeometry.Scheme.Modules.pullbackCongr hq₀).hom.app A).val.app (Opposite.op ⊤)).hom
        ((((AlgebraicGeometry.Scheme.Modules.pullbackComp q (𝟙 C)).hom.app A).val.app (Opposite.op ⊤)).hom
        (sectionPullbackAlong q z))) (hseed.trans hid)).trans
      ((congrArg (fun z => (((AlgebraicGeometry.Scheme.Modules.pullbackCongr hq₀).hom.app A).val.app (Opposite.op ⊤)).hom
        (z)) hcomp0).trans hcongr0))
  have hlin1 : (((AlgebraicGeometry.Scheme.Modules.pullbackComp i q).hom.app A).val.app (Opposite.op ⊤)).hom
        ((show W.ringCatSheaf.val.obj (Opposite.op ⊤) from (u : Γ(W, ⊤))) • sectionPullbackAlong i (sectionPullbackAlong q (fs ℓ)))
      = (show W.ringCatSheaf.val.obj (Opposite.op ⊤) from (u : Γ(W, ⊤))) • (((AlgebraicGeometry.Scheme.Modules.pullbackComp i q).hom.app A).val.app (Opposite.op ⊤)).hom
        (sectionPullbackAlong i (sectionPullbackAlong q (fs ℓ))) :=
    AlgebraicGeometry.Scheme.Modules.modules_hom_app_top_smul _ (u : Γ(W, ⊤)) _
  have hlin2 : (((AlgebraicGeometry.Scheme.Modules.pullbackCongr hb).hom.app A).val.app (Opposite.op ⊤)).hom
        ((show W.ringCatSheaf.val.obj (Opposite.op ⊤) from (u : Γ(W, ⊤))) • (((AlgebraicGeometry.Scheme.Modules.pullbackComp i q).hom.app A).val.app (Opposite.op ⊤)).hom
        (sectionPullbackAlong i (sectionPullbackAlong q (fs ℓ))))
      = (show W.ringCatSheaf.val.obj (Opposite.op ⊤) from (u : Γ(W, ⊤))) • (((AlgebraicGeometry.Scheme.Modules.pullbackCongr hb).hom.app A).val.app (Opposite.op ⊤)).hom
        ((((AlgebraicGeometry.Scheme.Modules.pullbackComp i q).hom.app A).val.app (Opposite.op ⊤)).hom
        (sectionPullbackAlong i (sectionPullbackAlong q (fs ℓ)))) :=
    AlgebraicGeometry.Scheme.Modules.modules_hom_app_top_smul _ (u : Γ(W, ⊤)) _
  have hB : (((AlgebraicGeometry.Scheme.Modules.pullbackCongr hb).hom.app A).val.app (Opposite.op ⊤)).hom
        ((((AlgebraicGeometry.Scheme.Modules.pullbackComp i q).hom.app A).val.app (Opposite.op ⊤)).hom
        ((show W.ringCatSheaf.val.obj (Opposite.op ⊤) from (u : Γ(W, ⊤))) • sectionPullbackAlong i (sectionPullbackAlong q (fs ℓ))))
      = (show W.ringCatSheaf.val.obj (Opposite.op ⊤) from (u : Γ(W, ⊤))) • (((AlgebraicGeometry.Scheme.Modules.pullbackCongr hb).hom.app A).val.app (Opposite.op ⊤)).hom
        ((((AlgebraicGeometry.Scheme.Modules.pullbackComp i q).hom.app A).val.app (Opposite.op ⊤)).hom
        (sectionPullbackAlong i (sectionPullbackAlong q (fs ℓ)))) :=
    (congrArg (fun z => (((AlgebraicGeometry.Scheme.Modules.pullbackCongr hb).hom.app A).val.app (Opposite.op ⊤)).hom
        (z)) hlin1).trans hlin2
  have hC : (((AlgebraicGeometry.Scheme.Modules.pullbackCongr hb).hom.app A).val.app (Opposite.op ⊤)).hom
        ((((AlgebraicGeometry.Scheme.Modules.pullbackComp i q).hom.app A).val.app (Opposite.op ⊤)).hom
        (sectionPullbackAlong i (sectionPullbackAlong q (fs ℓ))))
      = (((AlgebraicGeometry.Scheme.Modules.pullbackCongr hb).hom.app A).val.app (Opposite.op ⊤)).hom
        ((((AlgebraicGeometry.Scheme.Modules.pullbackComp i q).hom.app A).val.app (Opposite.op ⊤)).hom
        (sectionPullbackAlong i ((((AlgebraicGeometry.Scheme.Modules.pullback q).map
        (biproduct.π (fun _ : Fin (N + 1) => A) ℓ)).val.app (Opposite.op ⊤)).hom
        (AlgebraicGeometry.Scheme.totalSpaceHomEquiv (AlgebraicGeometry.Scheme.Modules.pow A (N + 1)) (CategoryTheory.Over.mk q)
        ((CategoryTheory.Over.homMk q hq₀ : CategoryTheory.Over.mk q ⟶ CategoryTheory.Over.mk (𝟙 C)) ≫
        CategoryTheory.Over.homMk (s ≫ twistedAffineCone.ι A N deg F hF) h₃))))) := by
    rw [hseedq]
  have hsm : (((AlgebraicGeometry.Scheme.Modules.pullback ((i ≫ q ≫ s) ≫ (twistedAffineCone A N deg F hF).hom)).map
        (biproduct.π (fun _ : Fin (N + 1) => A) ℓ)).val.app (Opposite.op ⊤)).hom
        ((show W.ringCatSheaf.val.obj (Opposite.op ⊤) from (u : Γ(W, ⊤))) • AlgebraicGeometry.Scheme.totalSpaceHomEquiv (AlgebraicGeometry.Scheme.Modules.pow A (N + 1)) (CategoryTheory.Over.mk ((i ≫ q ≫ s) ≫ (twistedAffineCone A N deg F hF).hom)) ((CategoryTheory.Over.homMk i hb : (CategoryTheory.Over.mk ((i ≫ q ≫ s) ≫ (twistedAffineCone A N deg F hF).hom)) ⟶ (CategoryTheory.Over.mk q)) ≫
        ((CategoryTheory.Over.homMk q hq₀ : CategoryTheory.Over.mk q ⟶ CategoryTheory.Over.mk (𝟙 C)) ≫
        CategoryTheory.Over.homMk (s ≫ twistedAffineCone.ι A N deg F hF) h₃)))
      = (show W.ringCatSheaf.val.obj (Opposite.op ⊤) from (u : Γ(W, ⊤))) • (((AlgebraicGeometry.Scheme.Modules.pullback ((i ≫ q ≫ s) ≫ (twistedAffineCone A N deg F hF).hom)).map
        (biproduct.π (fun _ : Fin (N + 1) => A) ℓ)).val.app (Opposite.op ⊤)).hom
        (AlgebraicGeometry.Scheme.totalSpaceHomEquiv (AlgebraicGeometry.Scheme.Modules.pow A (N + 1)) (CategoryTheory.Over.mk ((i ≫ q ≫ s) ≫ (twistedAffineCone A N deg F hF).hom)) ((CategoryTheory.Over.homMk i hb : (CategoryTheory.Over.mk ((i ≫ q ≫ s) ≫ (twistedAffineCone A N deg F hF).hom)) ⟶ (CategoryTheory.Over.mk q)) ≫
        ((CategoryTheory.Over.homMk q hq₀ : CategoryTheory.Over.mk q ⟶ CategoryTheory.Over.mk (𝟙 C)) ≫
        CategoryTheory.Over.homMk (s ≫ twistedAffineCone.ι A N deg F hF) h₃))) :=
    AlgebraicGeometry.Scheme.Modules.modules_hom_app_top_smul _ (u : Γ(W, ⊤)) _
  -- assemble: `pullbackCongr (pullbackComp (i^* coord_ℓ m)) = pullbackCongr (pullbackComp (u • i^* q^* fs ℓ))`
  have hmain : (((AlgebraicGeometry.Scheme.Modules.pullbackCongr hb).hom.app A).val.app (Opposite.op ⊤)).hom
        ((((AlgebraicGeometry.Scheme.Modules.pullbackComp i q).hom.app A).val.app (Opposite.op ⊤)).hom
        (sectionPullbackAlong i ((((AlgebraicGeometry.Scheme.Modules.pullback q).map
        (biproduct.π (fun _ : Fin (N + 1) => A) ℓ)).val.app (Opposite.op ⊤)).hom
        (AlgebraicGeometry.Scheme.totalSpaceHomEquiv (AlgebraicGeometry.Scheme.Modules.pow A (N + 1)) (CategoryTheory.Over.mk q) m))))
      = (((AlgebraicGeometry.Scheme.Modules.pullbackCongr hb).hom.app A).val.app (Opposite.op ⊤)).hom
        ((((AlgebraicGeometry.Scheme.Modules.pullbackComp i q).hom.app A).val.app (Opposite.op ⊤)).hom
        ((show W.ringCatSheaf.val.obj (Opposite.op ⊤) from (u : Γ(W, ⊤))) • sectionPullbackAlong i (sectionPullbackAlong q (fs ℓ)))) := by
    refine hnatL.symm.trans (hcoordEq.trans (hsm.trans ?_))
    rw [hnatR, hseedq]
    exact hlin2.symm.trans (congrArg (fun z => (((AlgebraicGeometry.Scheme.Modules.pullbackCongr hb).hom.app A).val.app (Opposite.op ⊤)).hom z) hlin1).symm
  exact iso_val_app_top_injective' ((AlgebraicGeometry.Scheme.Modules.pullbackComp i q).app A)
    (iso_val_app_top_injective' ((AlgebraicGeometry.Scheme.Modules.pullbackCongr hb).app A) hmain)

/-- Reverse of `sectionPullbackAlong_coord_transport`: transport of a raw coordinate identity
`i^* c = u • i^* (p ≫ ρ)^* x` through `(pullbackComp p ρ).inv` and a change of bundle `φ : A ⟶ B`, giving the
identity in the form of `BasedJet.coneCoordinate` / `seedCoordPullback`. -/
theorem sectionPullbackAlong_coord_transport_rev {W S C' C : AlgebraicGeometry.Scheme.{u}}
    (i : W ⟶ S) (p : S ⟶ C') (ρ : C' ⟶ C) {A B : C.Modules} (φ : A ⟶ B)
    (u : Γ(W, ⊤)ˣ)
    (c : ((((AlgebraicGeometry.Scheme.Modules.pullback (p ≫ ρ)).obj A).val.obj (Opposite.op ⊤)) : Type u))
    (x : (A.val.obj (Opposite.op ⊤) : Type u))
    (h : sectionPullbackAlong i c
      = (show W.ringCatSheaf.obj.obj (Opposite.op ⊤) from (u : Γ(W, ⊤))) •
        sectionPullbackAlong i (sectionPullbackAlong (p ≫ ρ) x)) :
    sectionPullbackAlong i
        ((((AlgebraicGeometry.Scheme.Modules.pullback p).map ((AlgebraicGeometry.Scheme.Modules.pullback ρ).map φ)).val.app (Opposite.op ⊤)).hom
          ((((AlgebraicGeometry.Scheme.Modules.pullbackComp p ρ).inv.app A).val.app (Opposite.op ⊤)).hom c))
      = (show W.ringCatSheaf.obj.obj (Opposite.op ⊤) from (u : Γ(W, ⊤))) •
        sectionPullbackAlong i (sectionPullbackAlong p
          ((((AlgebraicGeometry.Scheme.Modules.pullback ρ).map φ).val.app (Opposite.op ⊤)).hom
            (sectionPullbackAlong ρ x))) := by
  -- `(pullbackComp p ρ).inv ((p ≫ ρ)^* x) = p^* ρ^* x`
  have hinv : (((AlgebraicGeometry.Scheme.Modules.pullbackComp p ρ).inv.app A).val.app (Opposite.op ⊤)).hom
      (sectionPullbackAlong (p ≫ ρ) x) = sectionPullbackAlong p (sectionPullbackAlong ρ x) := by
    rw [← sectionPullbackAlong_comp p ρ x]
    exact congrArg (fun ψ : (AlgebraicGeometry.Scheme.Modules.pullback p).obj ((AlgebraicGeometry.Scheme.Modules.pullback ρ).obj A) ⟶ _ =>
      (ψ.val.app (Opposite.op ⊤)).hom (sectionPullbackAlong p (sectionPullbackAlong ρ x)))
      (CategoryTheory.Iso.hom_inv_id_app (AlgebraicGeometry.Scheme.Modules.pullbackComp p ρ) A)
  rw [sectionPullbackAlong_naturality, sectionPullbackAlong_naturality, h,
    AlgebraicGeometry.Scheme.Modules.modules_hom_app_top_smul,
    AlgebraicGeometry.Scheme.Modules.modules_hom_app_top_smul,
    ← sectionPullbackAlong_naturality, ← sectionPullbackAlong_naturality, hinv,
    ← sectionPullbackAlong_naturality]

end
