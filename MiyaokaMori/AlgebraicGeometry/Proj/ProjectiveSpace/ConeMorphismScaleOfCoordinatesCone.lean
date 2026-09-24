import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Morphisms.ConeScalingAction
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ConeMorphismScaleOfCoordinatesHelpers

/-! # Scaling a cone morphism from its coordinates: the general cone form

`twistedAffineCone.comp_eq_scale_of_coordinates`: for an arbitrary twisted affine cone `Z ⊂ Tot(A^{⊕(N+1)})`
with seed section `s`, a `C`-morphism `J : S → Z` over `q`, `i : W → S` and a unit `u` on `W`,
coordinatewise equality `i^*(coord_ℓ J) = u • i^* q^* fs_ℓ` (for all `ℓ`) gives `i ≫ J = scale u (i ≫ q ≫ s)`.
The concrete statement for based jets (`BasedJet.restrict_eq_scale_of_coneCoordinate`, module
`MiyaokaMori.Paper.S3PositiveLine.ConeMorphismScaleOfCoordinates`) is this lemma applied to `MMSetup.cone f`,
after unpacking `BasedJet.coneCoordinate` / `seedCoordPullback`. Kept in its own module because the proof takes
about 30 s to compile.

Source: §3 of the paper (Section 3), the definition of a scalar jet `ȷ = u · (s ∘ ρ ∘ p_L)` and the
exclusion of purely scalar jets in the proof of Lemma 4.1.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- General form of the lemma, for an arbitrary twisted affine cone `Z = V(F_j) ⊂ Tot(A^{⊕(N+1)})` with
seed tuple `fs` and seed section `s = (fs_0, …, fs_N) : C → Z`. Given a `C`-morphism `J : S → Z` over `q : S → C`,
`i : W → S` and a unit `u` on `W`: if for every `ℓ` the `ℓ`-th coordinate of `J` (via `totalSpaceHomEquiv`, as the
`C`-morphism `m` over `q` with `m.left = J ≫ ι_Z`) pulled back along `i` equals `u • i^* q^* fs_ℓ`, then
`i ≫ J = scale u (i ≫ q ≫ s)`. Proof: `ι_Z` is a closed immersion, hence mono; `scale u g ≫ ι_Z = scaleTot u g`
(`IsClosedImmersion.lift_fac`); both sides are `C`-morphisms `W → Tot(A^{⊕(N+1)})` over `g ≫ Z.hom = i ≫ q`, and
such morphisms are determined by their coordinate sections (`pullback_biproduct_section_ext`). The coordinates are
computed with `totalSpaceHomEquiv_naturality_coordinate_of_eq` (precomposition = pullback of sections),
`totalSpaceHomEquiv_symm_smul_coordinate` (scaling), `seedSection.totSection_coordinate` (the seed section has
coordinates `fs_ℓ`) and the `sectionPullbackAlong` compatibilities with `pullbackComp`/`pullbackId`/`pullbackCongr`. -/
theorem twistedAffineCone.comp_eq_scale_of_coordinates {k : Type u} [Field k] {C : AlgebraicGeometry.Scheme.{u}}
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
    (hcoord : ∀ ℓ, sectionPullbackAlong i
        ((((AlgebraicGeometry.Scheme.Modules.pullback q).map
            (biproduct.π (fun _ : Fin (N + 1) => A) ℓ)).val.app (Opposite.op ⊤)).hom
          (AlgebraicGeometry.Scheme.totalSpaceHomEquiv (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))
            (CategoryTheory.Over.mk q) m))
      = (show W.ringCatSheaf.obj.obj (Opposite.op ⊤) from (u : Γ(W, ⊤))) •
          sectionPullbackAlong i (sectionPullbackAlong q (fs ℓ))) :
    i ≫ J = twistedAffineCone.scale A N deg F hF u (i ≫ q ≫ (seedSection A N fs deg F hF hvanish).1) := by
  have hLF : (⨁ fun _ : Fin (N + 1) => A).IsLocallyFree :=
    inferInstanceAs (AlgebraicGeometry.Scheme.Modules.pow A (N + 1)).IsLocallyFree
  have hFT : (⨁ fun _ : Fin (N + 1) => A).IsFiniteType :=
    inferInstanceAs (AlgebraicGeometry.Scheme.Modules.pow A (N + 1)).IsFiniteType
  have hJ : J ≫ (twistedAffineCone A N deg F hF).hom = q := by
    have := CategoryTheory.Over.w m
    rw [hm, CategoryTheory.Category.assoc] at this
    exact this
  have hZι : twistedAffineCone.ι A N deg F hF ≫
      (AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))).hom
      = (twistedAffineCone A N deg F hF).hom := rfl
  have hsι : (seedSection A N fs deg F hF hvanish).1 ≫ twistedAffineCone.ι A N deg F hF
      = (seedSection.totSection A N fs).1 :=
    AlgebraicGeometry.IsClosedImmersion.lift_fac (twistedAffineCone.ι A N deg F hF) _ _
  have hs : (seedSection A N fs deg F hF hvanish).1 ≫ (twistedAffineCone A N deg F hF).hom = 𝟙 C :=
    (seedSection A N fs deg F hF hvanish).2
  generalize (seedSection A N fs deg F hF hvanish).1 = s at hsι hs ⊢
  -- the base morphism of `scaleTot`
  have hb : i ≫ q = (i ≫ q ≫ s) ≫ (twistedAffineCone A N deg F hF).hom := by
    simp only [CategoryTheory.Category.assoc, hs, CategoryTheory.Category.comp_id]
  -- reduce to Tot via the mono `ι_Z`
  rw [← cancel_mono (twistedAffineCone.ι A N deg F hF)]
  unfold twistedAffineCone.scale
  rw [AlgebraicGeometry.IsClosedImmersion.lift_fac]
  unfold twistedAffineCone.scaleTot
  have hL : ((CategoryTheory.Over.homMk i hb :
      CategoryTheory.Over.mk ((i ≫ q ≫ s) ≫ (twistedAffineCone A N deg F hF).hom) ⟶ CategoryTheory.Over.mk q)
        ≫ m).left = (i ≫ J) ≫ twistedAffineCone.ι A N deg F hF := by
    exact (congrArg (fun x => i ≫ x) hm).trans (CategoryTheory.Category.assoc _ _ _).symm
  rw [← hL]
  refine congrArg (fun φ : (CategoryTheory.Over.mk ((i ≫ q ≫ s) ≫ (twistedAffineCone A N deg F hF).hom) ⟶
      AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))) =>
    CategoryTheory.Over.Hom.left φ) ?_
  rw [Equiv.eq_symm_apply]
  apply AlgebraicGeometry.Scheme.Modules.pullback_biproduct_section_ext
    ((i ≫ q ≫ s) ≫ (twistedAffineCone A N deg F hF).hom) (fun _ : Fin (N + 1) => A)
  intro ℓ
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
  rw [hm₂]
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
  -- assemble
  have hA : (((AlgebraicGeometry.Scheme.Modules.pullbackCongr hb).hom.app A).val.app (Opposite.op ⊤)).hom
        ((((AlgebraicGeometry.Scheme.Modules.pullbackComp i q).hom.app A).val.app (Opposite.op ⊤)).hom
        (sectionPullbackAlong i ((((AlgebraicGeometry.Scheme.Modules.pullback q).map
        (biproduct.π (fun _ : Fin (N + 1) => A) ℓ)).val.app (Opposite.op ⊤)).hom
        (AlgebraicGeometry.Scheme.totalSpaceHomEquiv (AlgebraicGeometry.Scheme.Modules.pow A (N + 1)) (CategoryTheory.Over.mk q) m))))
      = (((AlgebraicGeometry.Scheme.Modules.pullbackCongr hb).hom.app A).val.app (Opposite.op ⊤)).hom
        ((((AlgebraicGeometry.Scheme.Modules.pullbackComp i q).hom.app A).val.app (Opposite.op ⊤)).hom
        ((show W.ringCatSheaf.val.obj (Opposite.op ⊤) from (u : Γ(W, ⊤))) • sectionPullbackAlong i (sectionPullbackAlong q (fs ℓ)))) := by
    rw [hcoord ℓ]
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
  exact hnatL.trans (hA.trans (hB.trans ((congrArg (fun z => (show W.ringCatSheaf.val.obj (Opposite.op ⊤) from (u : Γ(W, ⊤))) • z) (hC.trans hnatR.symm)).trans hsm.symm)))

end
