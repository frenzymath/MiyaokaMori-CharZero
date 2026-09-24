import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Pullback.SectionPullbackAlong
import MiyaokaMori.AlgebraicGeometry.Modules.TotalSpace.TotalSpaceHomEquivCoordinates
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.ConeCoordinateFiniteXiExpansionSeedCoordinateTransport

/-! # Transport bookkeeping for the backward morphism

Variable-level coherence facts for `Scheme.Modules.pullback` (schemes, morphisms and modules are all variables),
used to prove the coordinate identity of `IsTotalSpaceToConeHom` in
`MiyaokaMori.Paper.S2WeightedJets.Cone.PuncturedConeIsPuncturedLineBundleBackward`.

* `pullbackComp_hom_sectionPullbackAlong_pullbackCongr`, `pullbackCongr_hom_pullbackComp_inv`: `pullbackCongr`
  commutes past `pullbackComp` / `sectionPullbackAlong` (`subst; rfl`).
* `pullbackComp_assoc_val_app_top'`: Mathlib `pseudofunctor_associativity` on a global section, for four schemes
  (the existing `pullbackComp_assoc_val_app_top` needs `p : T ⟶ S`).
* `pullbackCongr_hom_app_val_app_congr`: change of target of a `pullbackCongr` transport.
* `coordinate_transport_of`, `coordinate_transport_of'`, `coordinate_transport_of_y`: the coordinate identity itself, with the conclusion spelled with `Modules.Hom.app`
  exactly as the body of `IsTotalSpaceToConeHom`, so that it can be instantiated on the goal without retyping it.

Source: eq. (2.1) of the paper (the definition `β^*z_i = z_i` of `β`); categorical bookkeeping. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

/-- `pullbackComp β g` after `β^*` after `pullbackCongr (h : f = g)` is `pullbackCongr (β ≫ f = β ≫ g)` after
`pullbackComp β f` after `β^*`, on global sections. -/
theorem pullbackComp_hom_sectionPullbackAlong_pullbackCongr {S T C : AlgebraicGeometry.Scheme.{u}}
    (β : S ⟶ T) {f g : T ⟶ C} (h : f = g) (A : C.Modules)
    (x : (((pullback f).obj A).val.obj (Opposite.op ⊤) : Type u)) :
    (((pullbackComp β g).hom.app A).val.app (Opposite.op ⊤)).hom
        (sectionPullbackAlong β ((((pullbackCongr h).hom.app A).val.app (Opposite.op ⊤)).hom x))
      = (((pullbackCongr (congrArg (fun m => β ≫ m) h)).hom.app A).val.app (Opposite.op ⊤)).hom
          ((((pullbackComp β f).hom.app A).val.app (Opposite.op ⊤)).hom (sectionPullbackAlong β x)) := by
  subst h; rfl

/-- `pullbackCongr (h : f = f')` on `p^*A` commutes past `(pullbackComp f p)⁻¹`, on global sections. -/
theorem pullbackCongr_hom_pullbackComp_inv {S P C : AlgebraicGeometry.Scheme.{u}} {f f' : S ⟶ P} (h : f = f')
    (p : P ⟶ C) (A : C.Modules) (h' : f ≫ p = f' ≫ p)
    (y : (((pullback (f ≫ p)).obj A).val.obj (Opposite.op ⊤) : Type u)) :
    (((pullbackCongr h).hom.app ((pullback p).obj A)).val.app (Opposite.op ⊤)).hom
        ((((pullbackComp f p).inv.app A).val.app (Opposite.op ⊤)).hom y)
      = (((pullbackComp f' p).inv.app A).val.app (Opposite.op ⊤)).hom
          ((((pullbackCongr h').hom.app A).val.app (Opposite.op ⊤)).hom y) := by
  subst h; rfl

/-- Associativity of `pullbackComp` on global sections, for four schemes (Mathlib `pseudofunctor_associativity`
read off at a module `A` and a section `x`; generalizes `pullbackComp_assoc_val_app_top`, whose `p` has to land
back in the source). -/
theorem pullbackComp_assoc_val_app_top' {S T P C : AlgebraicGeometry.Scheme.{u}} (σ : S ⟶ T) (p : T ⟶ P)
    (ρ : P ⟶ C) (A : C.Modules)
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

/-- **Variable-level form of the coordinate identity of `IsTotalSpaceToConeHom`.**
`β : S → T`, `g : T → P`, `π = β ≫ g`, `pr₁ : P → C`, `t = g ≫ pr₁ : T → C`; `x ∈ Γ(T, t^*A)`,
`z ∈ Γ(S, π^*pr₁^*A)`. If `β^*x`, transported to `Γ(S, (π ≫ pr₁)^*A)`, is the transport of `z`, then `β^*` of the
transport of `x` to `Γ(T, g^*pr₁^*A)`, moved to `Γ(S, π^*pr₁^*A)`, is `z`. Pure pseudofunctor coherence
(`pullbackComp_assoc_val_app_top`, `sectionPullbackAlong_naturality`). The conclusion is spelled with
`Modules.Hom.app` exactly as the body of `IsTotalSpaceToConeHom`. -/
theorem coordinate_transport_of {S T P C : AlgebraicGeometry.Scheme.{u}} (β : S ⟶ T) (g : T ⟶ P) (π : S ⟶ P)
    (hβ : β ≫ g = π) (pr₁ : P ⟶ C) (t : T ⟶ C) (ht : g ≫ pr₁ = t) (hπ : β ≫ t = π ≫ pr₁) (A : C.Modules)
    (x : (((pullback t).obj A).val.obj (Opposite.op ⊤) : Type u))
    (z : (((pullback π).obj ((pullback pr₁).obj A)).val.obj (Opposite.op ⊤) : Type u))
    (hx : (((pullbackCongr hπ).hom.app A).val.app (Opposite.op ⊤)).hom
        ((((pullbackComp β t).hom.app A).val.app (Opposite.op ⊤)).hom (sectionPullbackAlong β x))
      = (((pullbackComp π pr₁).hom.app A).val.app (Opposite.op ⊤)).hom z) :
    ((pullbackCongr hβ).hom.app _).app ⊤
        (((pullbackComp β g).hom.app _).app ⊤
          (sectionPullbackAlong β
            (((pullbackComp g pr₁).inv.app A).app ⊤ (((pullbackCongr ht.symm).hom.app A).app ⊤ x)))) = z := by
  show (((pullbackCongr hβ).hom.app _).val.app (Opposite.op ⊤)).hom
      ((((pullbackComp β g).hom.app _).val.app (Opposite.op ⊤)).hom
        (sectionPullbackAlong β
          ((((pullbackComp g pr₁).inv.app A).val.app (Opposite.op ⊤)).hom
            ((((pullbackCongr ht.symm).hom.app A).val.app (Opposite.op ⊤)).hom x)))) = z
  rw [sectionPullbackAlong_naturality, pullbackComp_assoc_val_app_top' β g pr₁ A,
    pullbackComp_hom_sectionPullbackAlong_pullbackCongr, pullbackCongr_hom_app_val_app_top_trans,
    pullbackCongr_hom_pullbackComp_inv hβ pr₁ A (congrArg (fun m => m ≫ pr₁) hβ),
    pullbackCongr_hom_app_val_app_top_trans]
  have hx' : (((pullbackCongr (((congrArg (fun m => β ≫ m) ht.symm).trans (Category.assoc β g pr₁).symm).trans
      (congrArg (fun m => m ≫ pr₁) hβ))).hom.app A).val.app (Opposite.op ⊤)).hom
        ((((pullbackComp β t).hom.app A).val.app (Opposite.op ⊤)).hom (sectionPullbackAlong β x))
      = (((pullbackComp π pr₁).hom.app A).val.app (Opposite.op ⊤)).hom z := hx
  rw [hx']
  exact congrArg (fun ψ => (ψ.val.app (Opposite.op ⊤)).hom z) ((pullbackComp π pr₁).hom_inv_id_app A)

/-- `pullbackCongr rfl` is the identity on global sections (definitional). -/
theorem pullbackCongr_rfl_hom_app_val_app_apply {S C : AlgebraicGeometry.Scheme.{u}} (f : S ⟶ C) (A : C.Modules)
    (x : (((pullback f).obj A).val.obj (Opposite.op ⊤) : Type u)) :
    (((pullbackCongr (rfl : f = f)).hom.app A).val.app (Opposite.op ⊤)).hom x = x := rfl

/-- Evaluating a composite of two isomorphisms on a global section (definitional). -/
theorem Iso.trans_hom_val_app_apply' {X : AlgebraicGeometry.Scheme.{u}} {M N P : X.Modules} (α : M ≅ N) (β : N ≅ P)
    (x : (M.val.obj (Opposite.op ⊤) : Type u)) :
    ((α ≪≫ β).hom.val.app (Opposite.op ⊤)).hom x =
      (β.hom.val.app (Opposite.op ⊤)).hom ((α.hom.val.app (Opposite.op ⊤)).hom x) := rfl

/-- **`coordinate_transport_of` with the target base morphism `t'` and the transport `Θ` kept as variables.**
`t' = β ≫ t = π ≫ pr₁` is given by two separate equations `hπ`, `hcomp`, and the transport
`Θ : π^*pr₁^*A ≅ t'^*A` by the equation `hΘ : Θ = pullbackComp ≪≫ pullbackCongr hcomp`; so at the use site every
occurrence of `t'` stays in its own spelling (e.g. `base e A`) and never has to be unfolded inside a section type
(such a comparison under `Functor.obj`/`DFunLike.coe` heads costs ≈ 45 s). -/
theorem coordinate_transport_of' {S T P C : AlgebraicGeometry.Scheme.{u}} (β : S ⟶ T) (g : T ⟶ P) (π : S ⟶ P)
    (hβ : β ≫ g = π) (pr₁ : P ⟶ C) (t : T ⟶ C) (ht : g ≫ pr₁ = t) (t' : S ⟶ C) (hπ : β ≫ t = t')
    (hcomp : π ≫ pr₁ = t') (A : C.Modules)
    (Θ : (pullback π).obj ((pullback pr₁).obj A) ≅ (pullback t').obj A)
    (hΘ : Θ = (pullbackComp π pr₁).app A ≪≫ (pullbackCongr hcomp).app A)
    (x : (((pullback t).obj A).val.obj (Opposite.op ⊤) : Type u))
    (z : (((pullback π).obj ((pullback pr₁).obj A)).val.obj (Opposite.op ⊤) : Type u))
    (hx : (((pullbackCongr hπ).hom.app A).val.app (Opposite.op ⊤)).hom
        ((((pullbackComp β t).hom.app A).val.app (Opposite.op ⊤)).hom (sectionPullbackAlong β x))
      = (Θ.hom.val.app (Opposite.op ⊤)).hom z) :
    ((pullbackCongr hβ).hom.app _).app ⊤
        (((pullbackComp β g).hom.app _).app ⊤
          (sectionPullbackAlong β
            (((pullbackComp g pr₁).inv.app A).app ⊤ (((pullbackCongr ht.symm).hom.app A).app ⊤ x)))) = z := by
  subst hΘ hcomp
  refine coordinate_transport_of β g π hβ pr₁ t ht hπ A x z (hx.trans ?_)
  exact (Iso.trans_hom_val_app_apply' _ _ z).trans (pullbackCongr_rfl_hom_app_val_app_apply (π ≫ pr₁) A _)

/-- Changing the target of a `pullbackCongr` transport: `pullbackCongr h'` is `pullbackCongr h` followed by
`pullbackCongr hgg'`, on global sections (`subst; rfl`). Used to restate `hom_pullback_coord` with the base spelled
`π ≫ pr₁` without ever comparing two `pullbackCongr`s with different proofs. -/
theorem pullbackCongr_hom_app_val_app_congr {S C : AlgebraicGeometry.Scheme.{u}} {f g g' : S ⟶ C} (h : f = g)
    (h' : f = g') (hgg' : g = g') (A : C.Modules) (x : (((pullback f).obj A).val.obj (Opposite.op ⊤) : Type u)) :
    (((pullbackCongr h').hom.app A).val.app (Opposite.op ⊤)).hom x =
      (((pullbackCongr hgg').hom.app A).val.app (Opposite.op ⊤)).hom
        ((((pullbackCongr h).hom.app A).val.app (Opposite.op ⊤)).hom x) := by
  subst hgg'; subst h; rfl

/-- `coordinate_transport_of` with the transported coordinate `y` and its defining equation `hy` as separate
arguments, so that `y` can be instantiated by an opaque constant (`puncturedConeToProduct.coordOverProduct`). -/
theorem coordinate_transport_of_y {S T P C : AlgebraicGeometry.Scheme.{u}} (β : S ⟶ T) (g : T ⟶ P) (π : S ⟶ P)
    (hβ : β ≫ g = π) (pr₁ : P ⟶ C) (t : T ⟶ C) (ht : g ≫ pr₁ = t) (hπ : β ≫ t = π ≫ pr₁) (A : C.Modules)
    (x : (((pullback t).obj A).val.obj (Opposite.op ⊤) : Type u))
    (y : (((pullback g).obj ((pullback pr₁).obj A)).val.obj (Opposite.op ⊤) : Type u))
    (hy : y = ((pullbackComp g pr₁).inv.app A).app ⊤ (((pullbackCongr ht.symm).hom.app A).app ⊤ x))
    (z : (((pullback π).obj ((pullback pr₁).obj A)).val.obj (Opposite.op ⊤) : Type u))
    (hx : (((pullbackCongr hπ).hom.app A).val.app (Opposite.op ⊤)).hom
        ((((pullbackComp β t).hom.app A).val.app (Opposite.op ⊤)).hom (sectionPullbackAlong β x))
      = (((pullbackComp π pr₁).hom.app A).val.app (Opposite.op ⊤)).hom z) :
    ((pullbackCongr hβ).hom.app _).app ⊤
        (((pullbackComp β g).hom.app _).app ⊤ (sectionPullbackAlong β y)) = z := by
  subst hy
  exact coordinate_transport_of β g π hβ pr₁ t ht hπ A x z hx

end AlgebraicGeometry.Scheme.Modules

end
