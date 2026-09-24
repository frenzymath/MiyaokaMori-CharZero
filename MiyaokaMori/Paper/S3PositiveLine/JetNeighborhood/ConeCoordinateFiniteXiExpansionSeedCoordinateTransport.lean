import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.ConeMorphismScaleOfCoordinatesHelpers

/-! # Transport bookkeeping for the restriction of cone coordinates to the zero section

Variable-level facts (schemes, morphisms and sheaves are all variables) used to prove
`BasedJet.restrictToZeroSection_coneCoordinate` (module `ConeCoordinateFiniteXiExpansionSeedCoordinate`).

* `natTrans_app_val_app_top_map`: a natural transformation commutes with `F.map φ` on global sections.
* `pullbackCongr_hom_app_val_app_top_trans`: two `pullbackCongr` transports compose.
* `pullbackComp_assoc_val_app_top`, `pullbackComp_id_val_app_top`: Mathlib's pseudofunctor coherence of
  `Scheme.Modules.pullback` (`pseudofunctor_associativity`, `pseudofunctor_right_unitality`) read off on a
  global section.
* `restrictTransport_naturality`: the iso chain `σ^*p^*M → (σ ≫ p)^*M → (𝟙)^*M → M` of
  `jetNeighborhood.restrictToZeroSection` / `Scheme.restrictToZeroSection` is natural in `M`.
* `restrictTransport_pullbackComp_inv`: that iso chain, applied to `σ^*((pullbackComp p ρ)⁻¹ w)`, is
  `pullbackCongr` of `pullbackComp σ (p ≫ ρ)` of `σ^* w`.
* `pullbackId_inv_app_val_app_top`: `(pullbackId).inv s = (𝟙)^* s`.
* `restrictTransport_coneCoordinate_aux`: the variable-level form of the target lemma (see its docstring).

Source: §3 of the paper (based jets) and Lemma 4.1 (the constant term of the
expansion); the categorical compatibilities are Mathlib's `pseudofunctor_*` lemmas for `Scheme.Modules.pullback`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

/-- A natural transformation between functors on sheaves of modules commutes with the action of a
morphism on global sections. -/
theorem natTrans_app_val_app_top_map {X Y : AlgebraicGeometry.Scheme.{u}} {F G : X.Modules ⥤ Y.Modules}
    (α : F ⟶ G) {M N : X.Modules} (φ : M ⟶ N) (x : ((F.obj M).val.obj (Opposite.op ⊤) : Type u)) :
    ((α.app N).val.app (Opposite.op ⊤)).hom (((F.map φ).val.app (Opposite.op ⊤)).hom x)
      = ((G.map φ).val.app (Opposite.op ⊤)).hom (((α.app M).val.app (Opposite.op ⊤)).hom x) :=
  congrArg (fun ψ => (ψ.val.app (Opposite.op ⊤)).hom x) (α.naturality φ)

/-- `pullbackCongr h₁` followed by `pullbackCongr h₂` is `pullbackCongr (h₁.trans h₂)` on global sections. -/
theorem pullbackCongr_hom_app_val_app_top_trans {X Y : AlgebraicGeometry.Scheme.{u}} {f g h : X ⟶ Y}
    (h₁ : f = g) (h₂ : g = h) (M : Y.Modules) (x : (((pullback f).obj M).val.obj (Opposite.op ⊤) : Type u)) :
    (((pullbackCongr h₂).hom.app M).val.app (Opposite.op ⊤)).hom
        ((((pullbackCongr h₁).hom.app M).val.app (Opposite.op ⊤)).hom x)
      = (((pullbackCongr (h₁.trans h₂)).hom.app M).val.app (Opposite.op ⊤)).hom x := by
  subst h₁; subst h₂; rfl

/-- Associativity of `pullbackComp` on global sections (Mathlib `pseudofunctor_associativity`, read off
at a module `A` and a section `x`): moving `x ∈ Γ(σ^*(p ≫ ρ)^*A)` to `Γ((σ ≫ p)^*ρ^*A)` via
`σ^*(pullbackComp p ρ)⁻¹` then `pullbackComp σ p` agrees with `pullbackComp σ (p ≫ ρ)` then the
transport along `σ ≫ (p ≫ ρ) = (σ ≫ p) ≫ ρ` and `(pullbackComp (σ ≫ p) ρ)⁻¹`. -/
theorem pullbackComp_assoc_val_app_top {S T C : AlgebraicGeometry.Scheme.{u}} (σ : S ⟶ T) (p : T ⟶ S)
    (ρ : S ⟶ C) (A : C.Modules)
    (x : (((pullback σ).obj ((pullback (p ≫ ρ)).obj A)).val.obj (Opposite.op ⊤) : Type u)) :
    (((pullbackComp σ p).hom.app ((pullback ρ).obj A)).val.app (Opposite.op ⊤)).hom
        ((((pullback σ).map ((pullbackComp p ρ).inv.app A)).val.app (Opposite.op ⊤)).hom x)
      = (((pullbackComp (σ ≫ p) ρ).inv.app A).val.app (Opposite.op ⊤)).hom
          ((((pullbackCongr (Category.assoc σ p ρ).symm).hom.app A).val.app (Opposite.op ⊤)).hom
            ((((pullbackComp σ (p ≫ ρ)).hom.app A).val.app (Opposite.op ⊤)).hom x)) := by
  have h := congrArg (fun α => α.app A) (pseudofunctor_associativity σ p ρ)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, eqToHom_app, Category.id_comp] at h
  have h' := congrArg (fun ψ => (ψ.val.app (Opposite.op ⊤)).hom
    ((((pullbackComp σ (p ≫ ρ)).hom.app A).val.app (Opposite.op ⊤)).hom x)) h
  have hx : (((pullbackComp σ (p ≫ ρ)).inv.app A).val.app (Opposite.op ⊤)).hom
      ((((pullbackComp σ (p ≫ ρ)).hom.app A).val.app (Opposite.op ⊤)).hom x) = x :=
    congrArg (fun ψ => (ψ.val.app (Opposite.op ⊤)).hom x) ((pullbackComp σ (p ≫ ρ)).hom_inv_id_app A)
  change (((pullbackComp (σ ≫ p) ρ).hom.app A).val.app (Opposite.op ⊤)).hom
      ((((pullbackComp σ p).hom.app ((pullback ρ).obj A)).val.app (Opposite.op ⊤)).hom
        ((((pullback σ).map ((pullbackComp p ρ).inv.app A)).val.app (Opposite.op ⊤)).hom
          ((((pullbackComp σ (p ≫ ρ)).inv.app A).val.app (Opposite.op ⊤)).hom
            ((((pullbackComp σ (p ≫ ρ)).hom.app A).val.app (Opposite.op ⊤)).hom x)))) = _ at h'
  rw [hx] at h'
  have hinv := congrArg (fun y => (((pullbackComp (σ ≫ p) ρ).inv.app A).val.app (Opposite.op ⊤)).hom y) h'
  have hy : ∀ y, (((pullbackComp (σ ≫ p) ρ).inv.app A).val.app (Opposite.op ⊤)).hom
      ((((pullbackComp (σ ≫ p) ρ).hom.app A).val.app (Opposite.op ⊤)).hom y) = y := fun y =>
    congrArg (fun ψ => (ψ.val.app (Opposite.op ⊤)).hom y) ((pullbackComp (σ ≫ p) ρ).hom_inv_id_app A)
  simp only [hy] at hinv
  exact hinv

/-- Right unitality of `pullbackComp` on global sections (Mathlib `pseudofunctor_right_unitality`):
for `q = 𝟙 S`, `(pullbackComp q ρ)⁻¹` followed by `pullbackCongr hq` and `pullbackId` is the
transport along `q ≫ ρ = ρ`. -/
theorem pullbackComp_id_val_app_top {S C : AlgebraicGeometry.Scheme.{u}} (q : S ⟶ S) (hq : q = 𝟙 S)
    (ρ : S ⟶ C) (A : C.Modules) (hq' : q ≫ ρ = ρ)
    (y : (((pullback (q ≫ ρ)).obj A).val.obj (Opposite.op ⊤) : Type u)) :
    (((pullbackId S).hom.app ((pullback ρ).obj A)).val.app (Opposite.op ⊤)).hom
        ((((pullbackCongr hq).hom.app ((pullback ρ).obj A)).val.app (Opposite.op ⊤)).hom
          ((((pullbackComp q ρ).inv.app A).val.app (Opposite.op ⊤)).hom y))
      = (((pullbackCongr hq').hom.app A).val.app (Opposite.op ⊤)).hom y := by
  subst hq
  have h := congrArg (fun α => α.app A) (pseudofunctor_right_unitality ρ)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app, eqToHom_app] at h
  have h' := congrArg (fun ψ => (ψ.val.app (Opposite.op ⊤)).hom y) h
  exact h'

/-- Naturality of the restriction-to-a-section transport
`σ^*p^*M → (σ ≫ p)^*M → (𝟙)^*M → M` (the iso chain of `restrictToZeroSection`) in the module `M`:
it commutes with `φ : M ⟶ N` applied inside `p^*` and outside. -/
theorem restrictTransport_naturality {S T : AlgebraicGeometry.Scheme.{u}} (σ : S ⟶ T) (p : T ⟶ S)
    (h : σ ≫ p = 𝟙 S) {M N : S.Modules} (φ : M ⟶ N)
    (x : (((pullback p).obj M).val.obj (Opposite.op ⊤) : Type u)) :
    (((pullbackId S).hom.app N).val.app (Opposite.op ⊤)).hom
        ((((pullbackCongr h).hom.app N).val.app (Opposite.op ⊤)).hom
          ((((pullbackComp σ p).hom.app N).val.app (Opposite.op ⊤)).hom
            (sectionPullbackAlong σ ((((pullback p).map φ).val.app (Opposite.op ⊤)).hom x))))
      = (φ.val.app (Opposite.op ⊤)).hom
          ((((pullbackId S).hom.app M).val.app (Opposite.op ⊤)).hom
            ((((pullbackCongr h).hom.app M).val.app (Opposite.op ⊤)).hom
              ((((pullbackComp σ p).hom.app M).val.app (Opposite.op ⊤)).hom
                (sectionPullbackAlong σ x)))) := by
  rw [sectionPullbackAlong_naturality]
  have h1 := natTrans_app_val_app_top_map (F := pullback p ⋙ pullback σ) (pullbackComp σ p).hom φ
    (sectionPullbackAlong σ x)
  have h2 := natTrans_app_val_app_top_map (F := pullback (σ ≫ p)) (pullbackCongr h).hom φ
    ((((pullbackComp σ p).hom.app M).val.app (Opposite.op ⊤)).hom (sectionPullbackAlong σ x))
  have h3 := natTrans_app_val_app_top_map (F := pullback (𝟙 S)) (G := 𝟭 _) (pullbackId S).hom φ
    ((((pullbackCongr h).hom.app M).val.app (Opposite.op ⊤)).hom
      ((((pullbackComp σ p).hom.app M).val.app (Opposite.op ⊤)).hom (sectionPullbackAlong σ x)))
  simp only [Functor.comp_map, Functor.id_map] at h1 h2 h3
  rw [h1, h2, h3]

/-- The restriction-to-a-section transport applied to `σ^*((pullbackComp p ρ)⁻¹ w)`, `w ∈ Γ(T, (p ≫ ρ)^*A)`,
is `pullbackCongr h'` of `pullbackComp σ (p ≫ ρ)` of `σ^* w` (pseudofunctor coherence: associativity
plus right unitality). -/
theorem restrictTransport_pullbackComp_inv {S T C : AlgebraicGeometry.Scheme.{u}} (σ : S ⟶ T) (p : T ⟶ S)
    (h : σ ≫ p = 𝟙 S) (ρ : S ⟶ C) (h' : σ ≫ (p ≫ ρ) = ρ) (A : C.Modules)
    (w : (((pullback (p ≫ ρ)).obj A).val.obj (Opposite.op ⊤) : Type u)) :
    (((pullbackId S).hom.app ((pullback ρ).obj A)).val.app (Opposite.op ⊤)).hom
        ((((pullbackCongr h).hom.app ((pullback ρ).obj A)).val.app (Opposite.op ⊤)).hom
          ((((pullbackComp σ p).hom.app ((pullback ρ).obj A)).val.app (Opposite.op ⊤)).hom
            (sectionPullbackAlong σ ((((pullbackComp p ρ).inv.app A).val.app (Opposite.op ⊤)).hom w))))
      = (((pullbackCongr h').hom.app A).val.app (Opposite.op ⊤)).hom
          ((((pullbackComp σ (p ≫ ρ)).hom.app A).val.app (Opposite.op ⊤)).hom
            (sectionPullbackAlong σ w)) := by
  rw [sectionPullbackAlong_naturality, pullbackComp_assoc_val_app_top,
    pullbackComp_id_val_app_top (σ ≫ p) h ρ A (by rw [h, Category.id_comp]),
    pullbackCongr_hom_app_val_app_top_trans]

end AlgebraicGeometry.Scheme.Modules

/-- `(pullbackId C).inv (s) = (𝟙 C)^* s` on global sections (inverse form of `sectionPullbackAlong_id`). -/
theorem pullbackId_inv_app_val_app_top {C : AlgebraicGeometry.Scheme.{u}} {M : C.Modules}
    (s : (M.val.obj (Opposite.op ⊤) : Type u)) :
    (((AlgebraicGeometry.Scheme.Modules.pullbackId C).inv.app M).val.app (Opposite.op ⊤)).hom s
      = sectionPullbackAlong (𝟙 C) s := by
  conv_lhs => rw [← sectionPullbackAlong_id s]
  exact congrArg (fun ψ => (ψ.val.app (Opposite.op ⊤)).hom (sectionPullbackAlong (𝟙 C) s))
    ((AlgebraicGeometry.Scheme.Modules.pullbackId C).hom_inv_id_app M)

/-- **Variable-level form of `BasedJet.restrictToZeroSection_coneCoordinate`.**
Data: a section `σ : S → T` of `p : T → S` (`σ ≫ p = 𝟙`), `ρ : S → C`, a line bundle `A` on `C` with
coordinates `fc : Fin (N+1) → Γ(C, A)`, the seed section `σ_f = totSection A N fc : C → Tot(A^{⊕(N+1)})`,
a scheme `Z` with `coneι : Z → Tot`, `s : C → Z` lifting `σ_f` (`hs`), and `J : T → Z` over `p ≫ ρ`
(`hover`) restricting to `ρ ≫ s` along `σ` (`hrestrict`). Then the `ℓ`-th coordinate of
`Over.homMk (J ≫ coneι)`, transported by `(pullbackComp p ρ)⁻¹`, `p^*φ` (`φ : ρ^*A ⟶ M`), and restricted
along `σ` (`pullbackComp σ p`, `pullbackCongr`, `pullbackId`), equals `φ(ρ^* fc ℓ)`.

Proof: naturality of the restriction transport in `M` (`restrictTransport_naturality`); pseudofunctor
coherence (`restrictTransport_pullbackComp_inv`); naturality of `totalSpaceHomEquiv` along `σ`
(`totalSpaceHomEquiv_naturality_coordinate_of_eq` with base `ρ`); `σ ≫ J ≫ coneι = ρ ≫ σ_f`
(`hrestrict`, `hs`, `Over.OverMorphism.ext`); naturality along `ρ` with `T' = (C, 𝟙)`; the coordinate of
`σ_f` is `(pullbackId).inv (fc ℓ)` (`seedSection.totSection_coordinate`); finally
`sectionPullbackAlong_id/comp/congr`. -/
theorem restrictTransport_coneCoordinate_aux {S T C Z : AlgebraicGeometry.Scheme.{u}}
    (σ : S ⟶ T) (p : T ⟶ S) (hσp : σ ≫ p = 𝟙 S) (ρ : S ⟶ C)
    (A : C.Modules) [A.IsLineBundle] (N : ℕ) (fc : Fin (N + 1) → (A.val.obj (Opposite.op ⊤) : Type u))
    (coneι : Z ⟶ (AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))).left)
    (s : C ⟶ Z) (hs : s ≫ coneι = (seedSection.totSection A N fc).1)
    (J : T ⟶ Z)
    (hover : (J ≫ coneι) ≫ (AlgebraicGeometry.Scheme.totalSpace
      (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))).hom = p ≫ ρ)
    (hrestrict : σ ≫ J = ρ ≫ s)
    {M : S.Modules} (φ : (AlgebraicGeometry.Scheme.Modules.pullback ρ).obj A ⟶ M) (ℓ : Fin (N + 1)) :
    ((AlgebraicGeometry.Scheme.Modules.pullbackComp σ p).app M ≪≫
      (AlgebraicGeometry.Scheme.Modules.pullbackCongr hσp).app M ≪≫
      (AlgebraicGeometry.Scheme.Modules.pullbackId S).app M).hom.app ⊤
      (sectionPullbackAlong σ
        ((((AlgebraicGeometry.Scheme.Modules.pullback p).map φ).val.app (Opposite.op ⊤)).hom
          ((((AlgebraicGeometry.Scheme.Modules.pullbackComp p ρ).inv.app A).val.app (Opposite.op ⊤)).hom
            ((((AlgebraicGeometry.Scheme.Modules.pullback (CategoryTheory.Over.mk (p ≫ ρ)).hom).map
                (CategoryTheory.Limits.biproduct.π (fun _ : Fin (N + 1) => A) ℓ)).val.app (Opposite.op ⊤)).hom
              (AlgebraicGeometry.Scheme.totalSpaceHomEquiv (AlgebraicGeometry.Scheme.Modules.pow A (N + 1))
                (CategoryTheory.Over.mk (p ≫ ρ)) (CategoryTheory.Over.homMk (J ≫ coneι) hover))))))
      = (φ.val.app (Opposite.op ⊤)).hom (sectionPullbackAlong ρ (fc ℓ)) := by
  have h' : σ ≫ (p ≫ ρ) = ρ := by rw [← Category.assoc, hσp, Category.id_comp]
  -- Step 0: the iso chain, written out
  change (((AlgebraicGeometry.Scheme.Modules.pullbackId S).hom.app M).val.app (Opposite.op ⊤)).hom
    ((((AlgebraicGeometry.Scheme.Modules.pullbackCongr hσp).hom.app M).val.app (Opposite.op ⊤)).hom
      ((((AlgebraicGeometry.Scheme.Modules.pullbackComp σ p).hom.app M).val.app (Opposite.op ⊤)).hom
        (sectionPullbackAlong σ _))) = _
  -- Step 1: naturality in M; Step 2: coherence
  rw [AlgebraicGeometry.Scheme.Modules.restrictTransport_naturality σ p hσp φ,
    AlgebraicGeometry.Scheme.Modules.restrictTransport_pullbackComp_inv σ p hσp ρ h' A]
  congr 1
  -- Step 3: naturality of totalSpaceHomEquiv along σ, base ρ
  have h3 := AlgebraicGeometry.Scheme.totalSpaceHomEquiv_naturality_coordinate_of_eq
    (fun _ : Fin (N + 1) => A) (CategoryTheory.Over.mk (p ≫ ρ)) σ ρ h'
    (CategoryTheory.Over.homMk (J ≫ coneι) hover) ℓ
  refine h3.symm.trans ?_
  -- Step 4: identify the morphism with ρ ≫ σ_f, factored through T' = (C, 𝟙)
  have h4 : (CategoryTheory.Over.homMk σ h' : CategoryTheory.Over.mk ρ ⟶ CategoryTheory.Over.mk (p ≫ ρ)) ≫
        (CategoryTheory.Over.homMk (J ≫ coneι) hover : CategoryTheory.Over.mk (p ≫ ρ) ⟶
          AlgebraicGeometry.Scheme.totalSpace (⨁ fun _ : Fin (N + 1) => A))
      = (CategoryTheory.Over.homMk ρ (Category.comp_id ρ) :
          CategoryTheory.Over.mk ρ ⟶ CategoryTheory.Over.mk (𝟙 C)) ≫
        (CategoryTheory.Over.homMk (seedSection.totSection A N fc).1 (seedSection.totSection A N fc).2 :
          CategoryTheory.Over.mk (𝟙 C) ⟶ AlgebraicGeometry.Scheme.totalSpace (⨁ fun _ : Fin (N + 1) => A)) := by
    apply CategoryTheory.Over.OverMorphism.ext
    change σ ≫ J ≫ coneι = ρ ≫ (seedSection.totSection A N fc).1
    rw [← Category.assoc, hrestrict, Category.assoc, hs]
  -- Step 5: naturality along ρ
  rw [h4, AlgebraicGeometry.Scheme.totalSpaceHomEquiv_naturality_coordinate_of_eq
    (fun _ : Fin (N + 1) => A) (CategoryTheory.Over.mk (𝟙 C)) ρ ρ (Category.comp_id ρ)]
  -- Step 6: the coordinate of σ_f
  erw [seedSection.totSection_coordinate A N fc ℓ _ rfl]
  -- Steps 7–9
  rw [pullbackId_inv_app_val_app_top]
  have hc : (((AlgebraicGeometry.Scheme.Modules.pullbackComp ρ (CategoryTheory.Over.mk (𝟙 C)).hom).hom.app A).val.app
        (Opposite.op ⊤)).hom (sectionPullbackAlong ρ (sectionPullbackAlong (𝟙 C) (fc ℓ)))
      = sectionPullbackAlong (ρ ≫ 𝟙 C) (fc ℓ) :=
    sectionPullbackAlong_comp ρ (𝟙 C) (fc ℓ)
  exact (congrArg (fun y => (((AlgebraicGeometry.Scheme.Modules.pullbackCongr (Category.comp_id ρ)).hom.app A).val.app
    (Opposite.op ⊤)).hom y) hc).trans (sectionPullbackAlong_congr (Category.comp_id ρ) (fc ℓ))

end
