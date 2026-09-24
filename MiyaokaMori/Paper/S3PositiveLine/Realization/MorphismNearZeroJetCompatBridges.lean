import MiyaokaMori.Paper.S3PositiveLine.Realization.ProjectivizationMorphismCongrIso
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotalSpaceHomEquivCoordinates

/-! # Generic bridges for the jet compatibility of the morphism near the zero section

Helper statements, all on *variables* (schemes, functors, modules), used by
`MiyaokaMori.Paper.S3PositiveLine.Realization.MorphismNearZeroJetCompat`.

Why they exist: several library statements are phrased with
`φ.app ⊤ x` (`Modules.Hom.app`, whose codomain `Γ(N, ⊤)` is a restriction of scalars of
`N.val.obj (op ⊤)`), or with `(pullbackComp f g).app M` whose source is `(g^* ⋙ f^*).obj M`, while
`restrictToThickening`, `BasedJet.coneCoordinate`, `puncturedConeToProduct.coord` and the coordinate
lemmas are phrased with `(φ.val.app (op ⊤)).hom x` and nested pullbacks `f^*(g^*M)`. The two
spellings are definitionally equal, but on the concrete modules of the main theorem (three nested
pullbacks along the jet neighbourhood of a twice pulled-back line bundle) letting the unifier or the
kernel discover this makes it unfold the pullback sheaves and is far too slow. Here each
identification is done once, on variables, where it is a cheap `rfl`. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
noncomputable section

/-- Transport of the `ℓ`-th coordinate of a morphism `T → Tot(⨁ A)` over `X` along an equality
`g = g'` of the structure morphism of `T = Over.mk g`: the coordinate of `m` over `Over.mk g`,
moved by `pullbackCongr`, is the coordinate of `m'` over `Over.mk g'` as soon as `m.left = m'.left`.
(Both `pullbackCongr rfl` and the identification of `m` with `m'` are definitional after `subst`.) -/
theorem AlgebraicGeometry.Scheme.totalSpaceHomEquiv_coordinate_congr_base
    {X : AlgebraicGeometry.Scheme.{u}} {n : ℕ} (A : Fin n → X.Modules)
    [(⨁ A).IsLocallyFree] [(⨁ A).IsFiniteType]
    {S : AlgebraicGeometry.Scheme.{u}} {g g' : S ⟶ X} (h : g = g')
    (m : CategoryTheory.Over.mk g ⟶ AlgebraicGeometry.Scheme.totalSpace (⨁ A))
    (m' : CategoryTheory.Over.mk g' ⟶ AlgebraicGeometry.Scheme.totalSpace (⨁ A))
    (hm : m.left = m'.left) (ℓ : Fin n) :
    (((AlgebraicGeometry.Scheme.Modules.pullbackCongr h).app (A ℓ)).hom.val.app (Opposite.op ⊤)).hom
        ((((AlgebraicGeometry.Scheme.Modules.pullback g).map (biproduct.π A ℓ)).val.app
          (Opposite.op ⊤)).hom
          (AlgebraicGeometry.Scheme.totalSpaceHomEquiv (⨁ A) (CategoryTheory.Over.mk g) m))
      = (((AlgebraicGeometry.Scheme.Modules.pullback g').map (biproduct.π A ℓ)).val.app
          (Opposite.op ⊤)).hom
          (AlgebraicGeometry.Scheme.totalSpaceHomEquiv (⨁ A) (CategoryTheory.Over.mk g') m') := by
  subst h
  obtain rfl : m = m' := CategoryTheory.Over.OverMorphism.ext hm
  rfl

namespace MorphismNearZeroJetCompat

/-- `(pullbackComp f g).app M`, with its source spelled `f^*(g^*M)` instead of `(g^* ⋙ f^*).obj M`. -/
def pullbackCompApp {X Y Z : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules) :
    (AlgebraicGeometry.Scheme.Modules.pullback f).obj ((AlgebraicGeometry.Scheme.Modules.pullback g).obj M) ≅
      (AlgebraicGeometry.Scheme.Modules.pullback (f ≫ g)).obj M :=
  (AlgebraicGeometry.Scheme.Modules.pullbackComp f g).app M

theorem pullbackCompApp_apply {X Y Z : AlgebraicGeometry.Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {M : Z.Modules} (s : (M.val.obj (Opposite.op ⊤) : Type u)) :
    (((pullbackCompApp f g M).hom.val.app (Opposite.op ⊤)).hom
      (sectionPullbackAlong f (sectionPullbackAlong g s))) = sectionPullbackAlong (f ≫ g) s :=
  AlgebraicGeometry.Scheme.Modules.ModuleSections.pullback_comp f g s

theorem pullbackCongr_apply_val {X Y : AlgebraicGeometry.Scheme.{u}} {f g : X ⟶ Y} (h : f = g)
    {M : Y.Modules} (s : (M.val.obj (Opposite.op ⊤) : Type u)) :
    ((((AlgebraicGeometry.Scheme.Modules.pullbackCongr h).app M).hom.val.app (Opposite.op ⊤)).hom
      (sectionPullbackAlong f s)) = sectionPullbackAlong g s :=
  AlgebraicGeometry.Scheme.Modules.ModuleSections.pullbackCongr_apply h s

theorem trans_hom_val_app_top_apply {X : AlgebraicGeometry.Scheme.{u}} {M₁ M₂ M₃ : X.Modules}
    (α : M₁ ≅ M₂) (β : M₂ ≅ M₃) (x : (M₁.val.obj (Opposite.op ⊤) : Type u)) :
    (((α ≪≫ β).hom.val.app (Opposite.op ⊤)).hom x) =
      (β.hom.val.app (Opposite.op ⊤)).hom ((α.hom.val.app (Opposite.op ⊤)).hom x) :=
  rfl

/-- The isomorphism `i^*π^*N ≅ p^*N` (for `i ≫ π = p`) whose `hom` is literally the morphism used in
`restrictToThickening` (`pullbackComp` followed by the `eqToHom` transport). -/
def thickIso {X Z W : AlgebraicGeometry.Scheme.{u}} (i : X ⟶ Z) (π : Z ⟶ W) (p : X ⟶ W)
    (hp : i ≫ π = p) (N : W.Modules) :
    (AlgebraicGeometry.Scheme.Modules.pullback i).obj ((AlgebraicGeometry.Scheme.Modules.pullback π).obj N) ≅
      (AlgebraicGeometry.Scheme.Modules.pullback p).obj N where
  hom := ((AlgebraicGeometry.Scheme.Modules.pullbackComp i π).app N).hom ≫
    CategoryTheory.eqToHom (congrArg (fun g => (AlgebraicGeometry.Scheme.Modules.pullback g).obj N) hp)
  inv := CategoryTheory.eqToHom
      (congrArg (fun g => (AlgebraicGeometry.Scheme.Modules.pullback g).obj N) hp).symm ≫
    ((AlgebraicGeometry.Scheme.Modules.pullbackComp i π).app N).inv
  hom_inv_id := by
    rw [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, Iso.hom_inv_id]
  inv_hom_id := by
    rw [Category.assoc, Iso.inv_hom_id_assoc, eqToHom_trans, eqToHom_refl]

/-- The `hom` of `thickIso`, as an equation at the type `i^*(π^*N) ⟶ p^*N`. -/
theorem thickIso_hom {X Z W : AlgebraicGeometry.Scheme.{u}} (i : X ⟶ Z) (π : Z ⟶ W) (p : X ⟶ W)
    (hp : i ≫ π = p) (N : W.Modules) :
    (thickIso i π p hp N).hom = ((AlgebraicGeometry.Scheme.Modules.pullbackComp i π).app N).hom ≫
      CategoryTheory.eqToHom (congrArg (fun g => (AlgebraicGeometry.Scheme.Modules.pullback g).obj N) hp) :=
  rfl

/-- The two spellings `G.obj (F.obj N)` and `(F ⋙ G).obj N` of the source of a morphism, on global
sections (a `rfl` on functor variables). -/
theorem val_app_top_apply_comp_obj {X Y Z : AlgebraicGeometry.Scheme.{u}}
    (F : Z.Modules ⥤ Y.Modules) (G : Y.Modules ⥤ X.Modules) (N : Z.Modules) {B : X.Modules}
    (f : (F ⋙ G).obj N ⟶ B) (x : ((G.obj (F.obj N)).val.obj (Opposite.op ⊤) : Type u)) :
    (((@SheafOfModules.Hom.val _ _ _ _ (G.obj (F.obj N)) B f).app (Opposite.op ⊤)).hom x) =
      ((f.val.app (Opposite.op ⊤)).hom x) :=
  rfl

/-- `ν^*ι^*M ≅ (ν ≫ ι)^*M = i^*M ≅ M'` applied to `ν^*ι^*s` is `φ` applied to `i^*s`, on variables. -/
theorem pullbackCompApp_chain_apply {X Y Z : AlgebraicGeometry.Scheme.{u}}
    (nu : X ⟶ Y) (ι : Y ⟶ Z) (i : X ⟶ Z) (hnu : nu ≫ ι = i) (M : Z.Modules) {M' : X.Modules}
    (φ : (AlgebraicGeometry.Scheme.Modules.pullback i).obj M ≅ M')
    (s : (M.val.obj (Opposite.op ⊤) : Type u)) :
    (((pullbackCompApp nu ι M ≪≫ (AlgebraicGeometry.Scheme.Modules.pullbackCongr hnu).app M ≪≫ φ).hom.val.app
        (Opposite.op ⊤)).hom (sectionPullbackAlong nu (sectionPullbackAlong ι s))) =
      ((φ.hom.val.app (Opposite.op ⊤)).hom (sectionPullbackAlong i s)) := by
  rw [trans_hom_val_app_top_apply, trans_hom_val_app_top_apply, pullbackCompApp_apply,
    pullbackCongr_apply_val]

theorem exists_not_isZeroAt_iso_val {X : AlgebraicGeometry.Scheme.{u}} {M M' : X.Modules}
    (θ : M ≅ M') {N : ℕ} (P : Fin (N + 1) → (M.val.obj (Opposite.op ⊤) : Type u))
    (hP : ∀ v : X, ∃ ℓ, ¬ IsZeroAt (P ℓ) v) (v : X) :
    ∃ ℓ, ¬ IsZeroAt ((θ.hom.val.app (Opposite.op ⊤)).hom (P ℓ)) v :=
  exists_not_isZeroAt_iso θ P hP v

theorem projectivizationMorphism_congr_iso_val {k : Type u} [Field k]
    {V : AlgebraicGeometry.Scheme.{u}} [V.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    (M M' : V.Modules) [M.IsLineBundle] [M'.IsLineBundle] (θ : M ≅ M') {N : ℕ}
    (P : Fin (N + 1) → (M.val.obj (Opposite.op ⊤) : Type u))
    (hP : ∀ v : V, ∃ ℓ, ¬ IsZeroAt (P ℓ) v)
    (hP' : ∀ v : V, ∃ ℓ, ¬ IsZeroAt ((θ.hom.val.app (Opposite.op ⊤)).hom (P ℓ)) v) :
    projectivizationMorphism (k := k) M P hP =
      projectivizationMorphism (k := k) M' (fun ℓ => (θ.hom.val.app (Opposite.op ⊤)).hom (P ℓ)) hP' :=
  projectivizationMorphism_congr_iso M M' θ P hP hP'

end MorphismNearZeroJetCompat

end
