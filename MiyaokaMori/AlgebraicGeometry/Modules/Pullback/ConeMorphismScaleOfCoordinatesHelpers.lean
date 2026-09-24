import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ModuleSectionPullback
import MiyaokaMori.Paper.S2WeightedJets.Cone.SeedSection
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotalSpaceHomEquivCoordinates

/-! # Helpers for the scaling of cone coordinates under morphisms

General (variable-level) facts about `sectionPullbackAlong` and the coordinates of `totalSpaceHomEquiv`,
built for `BasedJet.restrict_eq_scale_of_coneCoordinate` (module
`MiyaokaMori.Paper.S3PositiveLine.ConeMorphismScaleOfCoordinates`).

* `sectionPullbackAlong_comp` / `sectionPullbackAlong_congr` / `sectionPullbackAlong_id`: the pullback of a global
  section along a composite / along equal morphisms / along the identity, compared through `pullbackComp`,
  `pullbackCongr`, `pullbackId` (the first two are `AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback_comp`,
  `pullbackCongr_apply`; the third is `unit_conjugateEquiv` + `conjugateEquiv_pullbackId_hom`, Stacks 01LQ-style
  mate computation).
* `totalSpaceHomEquiv_naturality_coordinate_of_eq`: `totalSpaceHomEquiv_naturality_coordinate` for a base object
  `Over.mk b` with `hb : j ≫ T.hom = b` (the discrepancy is absorbed by `pullbackCongr hb`).
* `biproduct_π_val_app_sum`, `seedSection.totSection_coordinate`: the `ℓ`-th coordinate of the seed tuple section
  `σ_f = (f_0, …, f_N) : C → Tot(A^{⊕(N+1)})` is `f_ℓ` (transported by `pullbackId`).

The seed section `s = (f_0, …, f_N)` is the one of §2 of the paper; the remaining content is
categorical bookkeeping.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

theorem sectionPullbackAlong_comp {X Y Z : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {M : Z.Modules} (s : (M.val.obj (Opposite.op ⊤) : Type u)) :
    (((AlgebraicGeometry.Scheme.Modules.pullbackComp f g).hom.app M).val.app (Opposite.op ⊤)).hom
        (sectionPullbackAlong f (sectionPullbackAlong g s))
      = sectionPullbackAlong (f ≫ g) s :=
  AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback_comp f g s

theorem sectionPullbackAlong_congr {X Y : AlgebraicGeometry.Scheme.{u}} {f g : X ⟶ Y} (h : f = g)
    {M : Y.Modules} (s : (M.val.obj (Opposite.op ⊤) : Type u)) :
    (((AlgebraicGeometry.Scheme.Modules.pullbackCongr h).hom.app M).val.app (Opposite.op ⊤)).hom
        (sectionPullbackAlong f s)
      = sectionPullbackAlong g s :=
  AlgebraicGeometry.Scheme.Modules.ModuleSections.pullbackCongr_apply h s

theorem sectionPullbackAlong_id {X : AlgebraicGeometry.Scheme.{u}} {M : X.Modules}
    (s : (M.val.obj (Opposite.op ⊤) : Type u)) :
    (((AlgebraicGeometry.Scheme.Modules.pullbackId X).hom.app M).val.app (Opposite.op ⊤)).hom
        (sectionPullbackAlong (𝟙 X) s) = s := by
  have h := unit_conjugateEquiv Adjunction.id
    (AlgebraicGeometry.Scheme.Modules.pullbackPushforwardAdjunction (𝟙 X))
    (AlgebraicGeometry.Scheme.Modules.pullbackId X).hom M
  rw [AlgebraicGeometry.Scheme.Modules.conjugateEquiv_pullbackId_hom] at h
  have hs := congrArg (fun φ : M ⟶ (AlgebraicGeometry.Scheme.Modules.pushforward (𝟙 X)).obj M =>
    φ.app ⊤ s) h
  convert hs.symm using 1 <;> rfl

/-- Generalised form of `totalSpaceHomEquiv_naturality_coordinate`: the base object is an arbitrary
`Over.mk b` with `hb : j ≫ T.hom = b`; the discrepancy is absorbed by `pullbackCongr hb`. -/
theorem AlgebraicGeometry.Scheme.totalSpaceHomEquiv_naturality_coordinate_of_eq
    {X : AlgebraicGeometry.Scheme.{u}}
    {n : ℕ} (A : Fin n → X.Modules) [(⨁ A).IsLocallyFree] [(⨁ A).IsFiniteType]
    (T : CategoryTheory.Over X) {S : AlgebraicGeometry.Scheme.{u}} (j : S ⟶ T.left)
    (b : S ⟶ X) (hb : j ≫ T.hom = b)
    (m : T ⟶ AlgebraicGeometry.Scheme.totalSpace (⨁ A)) (ℓ : Fin n) :
    (((AlgebraicGeometry.Scheme.Modules.pullback b).map (biproduct.π A ℓ)).val.app (Opposite.op ⊤)).hom
        (AlgebraicGeometry.Scheme.totalSpaceHomEquiv (⨁ A) (CategoryTheory.Over.mk b)
          ((CategoryTheory.Over.homMk j hb : CategoryTheory.Over.mk b ⟶ T) ≫ m))
      = (((AlgebraicGeometry.Scheme.Modules.pullbackCongr hb).hom.app (A ℓ)).val.app (Opposite.op ⊤)).hom
          ((((AlgebraicGeometry.Scheme.Modules.pullbackComp j T.hom).hom.app (A ℓ)).val.app
              (Opposite.op ⊤)).hom
            (sectionPullbackAlong j
              ((((AlgebraicGeometry.Scheme.Modules.pullback T.hom).map (biproduct.π A ℓ)).val.app
                (Opposite.op ⊤)).hom (AlgebraicGeometry.Scheme.totalSpaceHomEquiv (⨁ A) T m)))) := by
  subst hb
  exact AlgebraicGeometry.Scheme.totalSpaceHomEquiv_naturality_coordinate A T j m ℓ


/-- `π_ℓ (∑ i, ι_i (f i)) = f ℓ` on global sections of a finite biproduct of sheaves of modules. -/
theorem biproduct_π_val_app_sum {C : AlgebraicGeometry.Scheme.{u}} (A : C.Modules) (N : ℕ)
    (f : Fin (N + 1) → (A.val.obj (Opposite.op ⊤) : Type u)) (ℓ : Fin (N + 1)) :
    ((biproduct.π (fun _ : Fin (N + 1) => A) ℓ).val.app (Opposite.op ⊤)).hom
        (∑ i : Fin (N + 1),
          ((CategoryTheory.Limits.biproduct.ι (fun _ : Fin (N + 1) => A) i).val.app (Opposite.op ⊤)).hom (f i))
      = f ℓ := by
  rw [map_sum, Finset.sum_eq_single ℓ]
  · have h2 := congrArg (fun ψ => (ψ.val.app (Opposite.op ⊤)).hom (f ℓ))
      (biproduct.ι_π_self (fun _ : Fin (N + 1) => A) ℓ)
    exact h2
  · intro i _ hi
    have h2 := congrArg (fun ψ => (ψ.val.app (Opposite.op ⊤)).hom (f i))
      (biproduct.ι_π_ne (fun _ : Fin (N + 1) => A) hi)
    exact h2
  · intro h; exact absurd (Finset.mem_univ ℓ) h

/-- The `ℓ`-th coordinate of the seed tuple section `σ_f : C → Tot(A^{⊕(N+1)})` (as a `C`-morphism over
`𝟙 C`) is `f ℓ`, transported by `pullbackId`. -/
theorem seedSection.totSection_coordinate {C : AlgebraicGeometry.Scheme.{u}} (A : C.Modules) [A.IsLineBundle]
    (N : ℕ) (f : Fin (N + 1) → (A.val.obj (Opposite.op ⊤) : Type u)) (ℓ : Fin (N + 1))
    (m : CategoryTheory.Over.mk (𝟙 C) ⟶
      AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A (N + 1)))
    (hm : m.left = (seedSection.totSection A N f).1) :
    (((AlgebraicGeometry.Scheme.Modules.pullback (𝟙 C)).map
        (biproduct.π (fun _ : Fin (N + 1) => A) ℓ)).val.app (Opposite.op ⊤)).hom
        (AlgebraicGeometry.Scheme.totalSpaceHomEquiv (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))
          (CategoryTheory.Over.mk (𝟙 C)) m)
      = (((AlgebraicGeometry.Scheme.Modules.pullbackId C).inv.app A).val.app (Opposite.op ⊤)).hom (f ℓ) := by
  set V := AlgebraicGeometry.Scheme.Modules.pow A (N + 1)
  set x : (V.val.obj (Opposite.op ⊤) : Type u) := ∑ i : Fin (N + 1),
    ((CategoryTheory.Limits.biproduct.ι (fun _ : Fin (N + 1) => A) i).val.app (Opposite.op ⊤)).hom (f i)
  have hm' : m = (AlgebraicGeometry.Scheme.totalSpaceHomEquiv V (CategoryTheory.Over.mk (𝟙 C))).symm
      ((((AlgebraicGeometry.Scheme.Modules.pullbackId C).inv.app V).val.app (Opposite.op ⊤)).hom x) := by
    apply CategoryTheory.Over.OverMorphism.ext
    rw [hm]
    rfl
  rw [hm', Equiv.apply_symm_apply]
  have hnat := (AlgebraicGeometry.Scheme.Modules.pullbackId C).inv.naturality
    (biproduct.π (fun _ : Fin (N + 1) => A) ℓ)
  have h1 := congrArg (fun ψ => (ψ.val.app (Opposite.op ⊤)).hom x) hnat
  simp only [Functor.id_map] at h1
  change (((AlgebraicGeometry.Scheme.Modules.pullbackId C).inv.app A).val.app (Opposite.op ⊤)).hom
    (((biproduct.π (fun _ : Fin (N + 1) => A) ℓ).val.app (Opposite.op ⊤)).hom x) = _ at h1
  refine h1.symm.trans ?_
  congr 1
  exact biproduct_π_val_app_sum A N f ℓ

/-- Applying a composite of module-sheaf morphisms to a global section, as iterated application (by definition). -/
theorem AlgebraicGeometry.Scheme.Modules.comp_val_app_top_apply_cone {X : AlgebraicGeometry.Scheme.{u}}
    {M N P : X.Modules} (f : M ⟶ N) (g : N ⟶ P) (z : (M.val.obj (Opposite.op ⊤) : Type u)) :
    (((f ≫ g).val.app (Opposite.op ⊤)).hom z) = (g.val.app (Opposite.op ⊤)).hom ((f.val.app (Opposite.op ⊤)).hom z) :=
  rfl

/-- Transport of a coordinate identity through `pullbackComp p ρ` and an invertible change of bundle `φ : A ⟶ B`
(inverse `ψ`): if `i^*(φ((pullbackComp p ρ)⁻¹ c)) = u • i^* p^*(φ(ρ^* x))` then `i^* c = u • i^*((p ≫ ρ)^* x)`.
This is the bookkeeping that relates `BasedJet.coneCoordinate` (which carries the `OX_toModules` transport and
`(pullbackComp p ρ).inv`) and `seedCoordPullback` to the raw coordinates of `totalSpaceHomEquiv`. -/
theorem sectionPullbackAlong_coord_transport {W S C' C : AlgebraicGeometry.Scheme.{u}}
    (i : W ⟶ S) (p : S ⟶ C') (ρ : C' ⟶ C) {A B : C.Modules} (φ : A ⟶ B) (ψ : B ⟶ A) (hφψ : φ ≫ ψ = 𝟙 A)
    (u : Γ(W, ⊤)ˣ)
    (c : ((((AlgebraicGeometry.Scheme.Modules.pullback (p ≫ ρ)).obj A).val.obj (Opposite.op ⊤)) : Type u))
    (x : (A.val.obj (Opposite.op ⊤) : Type u))
    (h : sectionPullbackAlong i
        ((((AlgebraicGeometry.Scheme.Modules.pullback p).map ((AlgebraicGeometry.Scheme.Modules.pullback ρ).map φ)).val.app (Opposite.op ⊤)).hom
          ((((AlgebraicGeometry.Scheme.Modules.pullbackComp p ρ).inv.app A).val.app (Opposite.op ⊤)).hom
          (c)))
      = (show W.ringCatSheaf.obj.obj (Opposite.op ⊤) from (u : Γ(W, ⊤))) •
        sectionPullbackAlong i (sectionPullbackAlong p
          ((((AlgebraicGeometry.Scheme.Modules.pullback ρ).map φ).val.app (Opposite.op ⊤)).hom
          (sectionPullbackAlong ρ x)))) :
    sectionPullbackAlong i c
      = (show W.ringCatSheaf.obj.obj (Opposite.op ⊤) from (u : Γ(W, ⊤))) •
        sectionPullbackAlong i (sectionPullbackAlong (p ≫ ρ) x) := by
  have hcomp : (AlgebraicGeometry.Scheme.Modules.pullbackComp p ρ).inv.app A ≫ (AlgebraicGeometry.Scheme.Modules.pullback p).map ((AlgebraicGeometry.Scheme.Modules.pullback ρ).map φ) ≫ (AlgebraicGeometry.Scheme.Modules.pullback p).map ((AlgebraicGeometry.Scheme.Modules.pullback ρ).map ψ) ≫ (AlgebraicGeometry.Scheme.Modules.pullbackComp p ρ).hom.app A = 𝟙 _ := by
    rw [← CategoryTheory.Category.assoc ((AlgebraicGeometry.Scheme.Modules.pullback p).map _),
      ← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, hφψ, CategoryTheory.Functor.map_id,
      CategoryTheory.Functor.map_id, CategoryTheory.Category.id_comp, CategoryTheory.Iso.inv_hom_id_app]
  have hcomp2 : (AlgebraicGeometry.Scheme.Modules.pullback p).map ((AlgebraicGeometry.Scheme.Modules.pullback ρ).map φ) ≫ (AlgebraicGeometry.Scheme.Modules.pullback p).map ((AlgebraicGeometry.Scheme.Modules.pullback ρ).map ψ) ≫ (AlgebraicGeometry.Scheme.Modules.pullbackComp p ρ).hom.app A = (AlgebraicGeometry.Scheme.Modules.pullbackComp p ρ).hom.app A := by
    rw [← CategoryTheory.Category.assoc, ← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, hφψ,
      CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, CategoryTheory.Category.id_comp]
  calc sectionPullbackAlong i c
      = (((AlgebraicGeometry.Scheme.Modules.pullback i).map ((AlgebraicGeometry.Scheme.Modules.pullback p).map ((AlgebraicGeometry.Scheme.Modules.pullback ρ).map ψ) ≫ (AlgebraicGeometry.Scheme.Modules.pullbackComp p ρ).hom.app A)).val.app (Opposite.op ⊤)).hom
          (sectionPullbackAlong i
        ((((AlgebraicGeometry.Scheme.Modules.pullback p).map ((AlgebraicGeometry.Scheme.Modules.pullback ρ).map φ)).val.app (Opposite.op ⊤)).hom
          ((((AlgebraicGeometry.Scheme.Modules.pullbackComp p ρ).inv.app A).val.app (Opposite.op ⊤)).hom
          (c)))) := by
        rw [sectionPullbackAlong_naturality, sectionPullbackAlong_naturality,
          ← AlgebraicGeometry.Scheme.Modules.comp_val_app_top_apply_cone,
          ← AlgebraicGeometry.Scheme.Modules.comp_val_app_top_apply_cone,
          ← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp, hcomp, CategoryTheory.Functor.map_id]
        rfl
    _ = (((AlgebraicGeometry.Scheme.Modules.pullback i).map ((AlgebraicGeometry.Scheme.Modules.pullback p).map ((AlgebraicGeometry.Scheme.Modules.pullback ρ).map ψ) ≫ (AlgebraicGeometry.Scheme.Modules.pullbackComp p ρ).hom.app A)).val.app (Opposite.op ⊤)).hom
          ((show W.ringCatSheaf.obj.obj (Opposite.op ⊤) from (u : Γ(W, ⊤))) • sectionPullbackAlong i (sectionPullbackAlong p
          ((((AlgebraicGeometry.Scheme.Modules.pullback ρ).map φ).val.app (Opposite.op ⊤)).hom
          (sectionPullbackAlong ρ x)))) := by rw [h]
    _ = (show W.ringCatSheaf.obj.obj (Opposite.op ⊤) from (u : Γ(W, ⊤))) • (((AlgebraicGeometry.Scheme.Modules.pullback i).map ((AlgebraicGeometry.Scheme.Modules.pullback p).map ((AlgebraicGeometry.Scheme.Modules.pullback ρ).map ψ) ≫ (AlgebraicGeometry.Scheme.Modules.pullbackComp p ρ).hom.app A)).val.app (Opposite.op ⊤)).hom
          (sectionPullbackAlong i (sectionPullbackAlong p
          ((((AlgebraicGeometry.Scheme.Modules.pullback ρ).map φ).val.app (Opposite.op ⊤)).hom
          (sectionPullbackAlong ρ x)))) :=
        AlgebraicGeometry.Scheme.Modules.modules_hom_app_top_smul _ (u : Γ(W, ⊤)) _
    _ = (show W.ringCatSheaf.obj.obj (Opposite.op ⊤) from (u : Γ(W, ⊤))) • sectionPullbackAlong i (sectionPullbackAlong (p ≫ ρ) x) := by
        rw [sectionPullbackAlong_naturality p, sectionPullbackAlong_naturality i,
          ← AlgebraicGeometry.Scheme.Modules.comp_val_app_top_apply_cone, ← CategoryTheory.Functor.map_comp, hcomp2,
          ← sectionPullbackAlong_naturality, sectionPullbackAlong_comp]

end
