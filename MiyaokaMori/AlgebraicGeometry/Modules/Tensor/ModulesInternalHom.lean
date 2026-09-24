import MiyaokaMori.Prelude

/-! # The internal Hom of sheaves of modules

The internal Hom of sheaves of modules, `U ↦ Hom_{O_U}(V|_U, W|_U)`, as a presheaf of modules and its
sheafification.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

/-- Sections of the Hom sheaf over an open `U`: for every open `V ⊆ U` a `Γ(X,V)`-linear map
`Γ(M,V) → Γ(N,V)`, compatible with restriction (i.e. `Hom_{O_U}(M|_U, N|_U)`; the same pattern as
`AlgebraicGeometry.Scheme.Modules.localDualSubmodule`, with target `N` instead of `O_X`). -/

def AlgebraicGeometry.Scheme.Modules.localHomSubmodule {X : AlgebraicGeometry.Scheme.{u}}
    (M N : X.Modules) (U : X.Opens) :
    letI : ∀ V : CategoryTheory.Over U, Module Γ(X, U) (Γ(M, V.left) →ₗ[Γ(X, V.left)] Γ(N, V.left)) :=
      fun V => Module.compHom _ (X.presheaf.map V.hom.op).hom
    Submodule Γ(X, U) ((V : CategoryTheory.Over U) → Γ(M, V.left) →ₗ[Γ(X, V.left)] Γ(N, V.left)) :=
  letI : ∀ V : CategoryTheory.Over U, Module Γ(X, U) (Γ(M, V.left) →ₗ[Γ(X, V.left)] Γ(N, V.left)) :=
    fun V => Module.compHom _ (X.presheaf.map V.hom.op).hom
  { carrier := {φ | ∀ (V W : CategoryTheory.Over U) (i : V ⟶ W) (x : Γ(M, W.left)),
      φ V (M.presheaf.map i.left.op x) = N.presheaf.map i.left.op (φ W x)}
    zero_mem' := by simp
    add_mem' := by
      intro φ ψ hφ hψ V W i x
      simp only [Pi.add_apply, LinearMap.add_apply, map_add]
      rw [hφ V W i x, hψ V W i x]
    smul_mem' := by
      intro r φ hφ V W i x
      change X.presheaf.map V.hom.op r • φ V (M.presheaf.map i.left.op x) =
        N.presheaf.map i.left.op (X.presheaf.map W.hom.op r • φ W x)
      rw [hφ V W i x]
      erw [N.val.map_smul]
      have h : V.hom = i.left ≫ W.hom := (CategoryTheory.Over.w i).symm
      rw [h, op_comp, X.presheaf.map_comp]
      rfl }

set_option backward.isDefEq.respectTransparency false in

/-- Restriction to a smaller open: view the opens of `Over V` as opens of `Over U` along `i`. -/

def AlgebraicGeometry.Scheme.Modules.localHomRestrict {X : AlgebraicGeometry.Scheme.{u}}
    (M N : X.Modules) {U V : X.Opens} (i : V ⟶ U) :
    AlgebraicGeometry.Scheme.Modules.localHomSubmodule M N U →ₛₗ[(X.presheaf.map i.op).hom]
      AlgebraicGeometry.Scheme.Modules.localHomSubmodule M N V where
  toFun φ := ⟨fun W ↦ φ.1 ((CategoryTheory.Over.map i).obj W), by
    intro W Z j x
    exact φ.2 ((CategoryTheory.Over.map i).obj W) ((CategoryTheory.Over.map i).obj Z)
      ((CategoryTheory.Over.map i).map j) x⟩
  map_add' φ ψ := rfl
  map_smul' r φ := by
    apply Subtype.ext
    funext W
    ext x
    change (X.presheaf.map (W.hom ≫ i).op r : Γ(X, W.left)) •
        (show Γ(N, W.left) from φ.1 ((CategoryTheory.Over.map i).obj W) x) =
      X.presheaf.map W.hom.op (X.presheaf.map i.op r) •
        (show Γ(N, W.left) from φ.1 ((CategoryTheory.Over.map i).obj W) x)
    rw [op_comp, X.presheaf.map_comp]
    rfl

set_option backward.isDefEq.respectTransparency false in

/-- The Hom presheaf `U ↦ Hom_{O_U}(M|_U, N|_U)`. -/

def AlgebraicGeometry.Scheme.Modules.internalHomPresheaf {X : AlgebraicGeometry.Scheme.{u}}
    (M N : X.Modules) : X.PresheafOfModules where
  obj U := ModuleCat.of _ (AlgebraicGeometry.Scheme.Modules.localHomSubmodule M N U.unop)
  map {U V} i := ModuleCat.ofHom (Y :=
      (ModuleCat.restrictScalars (X.ringCatSheaf.obj.map i).hom).obj
        (ModuleCat.of _ (AlgebraicGeometry.Scheme.Modules.localHomSubmodule M N V.unop)))
    { toFun := AlgebraicGeometry.Scheme.Modules.localHomRestrict M N i.unop
      map_add' := (AlgebraicGeometry.Scheme.Modules.localHomRestrict M N i.unop).map_add
      map_smul' := (AlgebraicGeometry.Scheme.Modules.localHomRestrict M N i.unop).map_smulₛₗ }
  map_id U := by
    ext φ
    rfl
  map_comp i j := by
    ext φ
    rfl

/-- The internal Hom `Hom(V, W)`: the sheafification of the Hom presheaf. -/
noncomputable def AlgebraicGeometry.Scheme.Modules.internalHom {X : AlgebraicGeometry.Scheme.{u}}
    (V W : X.Modules) : X.Modules :=
  (_root_.PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
    (AlgebraicGeometry.Scheme.Modules.internalHomPresheaf V W)

end
