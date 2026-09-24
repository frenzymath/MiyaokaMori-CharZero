import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModuleDual

/-!
# Contravariance of the existing module dual

Precomposing each compatible local functional with an actual module-sheaf
morphism gives a morphism of the existing dual presheaves. The same identity-ring
sheafification used by `moduleSheafDual` then gives its contravariant functor and
transports module isomorphisms to dual isomorphisms.

Sources: Stacks Project, `modules.tex`, Internal Hom; Mathlib's module-sheaf
morphism naturality and module sheafification functor. Used for the transport of finite free dual
frames and for the canonical/exterior-dual comparison (tangent and dual coefficient blocks in §2 of
the paper).
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Scheme.Modules

universe u

variable {X : Scheme.{u}} {M N P : X.Modules}

set_option backward.isDefEq.respectTransparency false in
/-- Precompose every local functional with the given morphism on the same subopen. -/
def localDualSectionsPrecomp (φ : M ⟶ N) (U : X.Opens) :
    LocalDualSections X N U →ₗ[Γ(X, U)] LocalDualSections X M U where
  toFun α := ⟨fun V ↦ (α.val V).comp (φ.val.app (op V.left)).hom, by
    intro V W i x
    change α.val V (φ.app V.left (M.presheaf.map i.left.op x)) =
      X.presheaf.map i.left.op (α.val W (φ.app W.left x))
    have hφ : φ.app V.left (M.presheaf.map i.left.op x) =
        N.presheaf.map i.left.op (φ.app W.left x) :=
      ConcreteCategory.congr_hom (φ.mapPresheaf.naturality i.left.op) x
    exact (congrArg (α.val V) hφ).trans (α.property V W i (φ.app W.left x))⟩
  map_add' α β := by
    apply Subtype.ext
    funext V
    apply LinearMap.ext
    intro x
    rfl
  map_smul' r α := by
    apply Subtype.ext
    funext V
    apply LinearMap.ext
    intro x
    rfl

/-- The pulled-back functional evaluates the original functional on the actual image section. -/
@[simp]
theorem localDualSectionsPrecomp_apply (φ : M ⟶ N) (U : X.Opens)
    (α : LocalDualSections X N U) (V : Over U) (x : Γ(M, V.left)) :
    (localDualSectionsPrecomp φ U α).val V x = α.val V (φ.app V.left x) := rfl

/-- Precomposition commutes with the original restriction of compatible functionals. -/
theorem localDualSectionsPrecomp_restrict (φ : M ⟶ N) {U V : X.Opens}
    (i : V ⟶ U) (α : LocalDualSections X N U) :
    localDualRestrict M i (localDualSectionsPrecomp φ U α) =
      localDualSectionsPrecomp φ V (localDualRestrict N i α) := rfl

/-- Precomposition with the identity fixes every compatible functional. -/
@[simp]
theorem localDualSectionsPrecomp_id (M : X.Modules) (U : X.Opens) :
    localDualSectionsPrecomp (𝟙 M) U = LinearMap.id := by
  apply LinearMap.ext
  intro α
  apply Subtype.ext
  funext V
  apply LinearMap.ext
  intro x
  rfl

/-- Precomposition reverses the order of composition of module-sheaf morphisms. -/
theorem localDualSectionsPrecomp_comp (φ : M ⟶ N) (ψ : N ⟶ P) (U : X.Opens) :
    localDualSectionsPrecomp (φ ≫ ψ) U =
      (localDualSectionsPrecomp φ U).comp (localDualSectionsPrecomp ψ U) := by
  apply LinearMap.ext
  intro α
  apply Subtype.ext
  funext V
  apply LinearMap.ext
  intro x
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The local precomposition maps assemble into a morphism of the existing dual presheaves. -/
def moduleDualPresheafPrecomp (φ : M ⟶ N) :
    moduleDualPresheaf N ⟶ moduleDualPresheaf M where
  app U := ModuleCat.ofHom (localDualSectionsPrecomp φ U.unop)
  naturality {U V} i := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro α
    change localDualSectionsPrecomp φ V.unop (localDualRestrict N i.unop α) =
      localDualRestrict M i.unop (localDualSectionsPrecomp φ U.unop α)
    exact (localDualSectionsPrecomp_restrict φ i.unop α).symm

set_option backward.isDefEq.respectTransparency false in
/-- Evaluation of the presheaf morphism is the original pointwise precomposition. -/
@[simp]
theorem moduleDualPresheafPrecomp_apply (φ : M ⟶ N) (U : X.Opens)
    (α : LocalDualSections X N U) (V : Over U) (x : Γ(M, V.left)) :
    ((moduleDualPresheafPrecomp φ).app (op U) α).val V x =
      α.val V (φ.app V.left x) := rfl

/-- The dual-presheaf morphism sends an identity to the identity. -/
@[simp]
theorem moduleDualPresheafPrecomp_id (M : X.Modules) :
    moduleDualPresheafPrecomp (𝟙 M) = 𝟙 (moduleDualPresheaf M) := by
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  exact localDualSectionsPrecomp_id M U.unop

/-- The dual-presheaf morphism reverses the order of composition. -/
theorem moduleDualPresheafPrecomp_comp (φ : M ⟶ N) (ψ : N ⟶ P) :
    moduleDualPresheafPrecomp (φ ≫ ψ) =
      moduleDualPresheafPrecomp ψ ≫ moduleDualPresheafPrecomp φ := by
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  exact localDualSectionsPrecomp_comp φ ψ U.unop

/-- The existing dual presheaf, now contravariantly functorial in the module sheaf. -/
def moduleDualPresheafFunctor (X : Scheme.{u}) : X.Modulesᵒᵖ ⥤ X.PresheafOfModules where
  obj M := moduleDualPresheaf M.unop
  map φ := moduleDualPresheafPrecomp φ.unop
  map_id M := moduleDualPresheafPrecomp_id M.unop
  map_comp φ ψ := moduleDualPresheafPrecomp_comp ψ.unop φ.unop

/-- Sheafification gives a contravariant functor with the original `moduleSheafDual` objects. -/
def moduleSheafDualFunctor (X : Scheme.{u}) : X.Modulesᵒᵖ ⥤ X.Modules :=
  moduleDualPresheafFunctor X ⋙ PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)

/-- The induced morphism between the same sheafified duals. -/
def moduleSheafDualMap (φ : M ⟶ N) : moduleSheafDual N ⟶ moduleSheafDual M :=
  (moduleSheafDualFunctor X).map φ.op

/-- The dual-sheaf morphism is induced by the actual presheaf precomposition under the unit. -/
theorem moduleSheafDualMap_unit (φ : M ⟶ N) :
    moduleDualPresheafPrecomp φ ≫
        (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
          (moduleDualPresheaf M) =
      (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
          (moduleDualPresheaf N) ≫
        (PresheafOfModules.restrictScalars (𝟙 X.ringCatSheaf.obj)).map
          (moduleSheafDualMap φ).val :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.naturality
    (moduleDualPresheafPrecomp φ)

/-- The dual-sheaf morphism sends an identity to the identity. -/
@[simp]
theorem moduleSheafDualMap_id (M : X.Modules) :
    moduleSheafDualMap (𝟙 M) = 𝟙 (moduleSheafDual M) :=
  (moduleSheafDualFunctor X).map_id (op M)

/-- The dual-sheaf morphism reverses the order of composition. -/
theorem moduleSheafDualMap_comp (φ : M ⟶ N) (ψ : N ⟶ P) :
    moduleSheafDualMap (φ ≫ ψ) = moduleSheafDualMap ψ ≫ moduleSheafDualMap φ :=
  (moduleSheafDualFunctor X).map_comp ψ.op φ.op

/-- An actual module-sheaf isomorphism gives an isomorphism of its original dual sheaves. -/
def moduleSheafDualIso (e : M ≅ N) : moduleSheafDual N ≅ moduleSheafDual M :=
  (moduleSheafDualFunctor X).mapIso e.op

/-- The forward dual isomorphism is precomposition with the original forward morphism. -/
@[simp]
theorem moduleSheafDualIso_hom (e : M ≅ N) :
    (moduleSheafDualIso e).hom = moduleSheafDualMap e.hom := rfl

/-- The inverse dual isomorphism is precomposition with the original inverse morphism. -/
@[simp]
theorem moduleSheafDualIso_inv (e : M ≅ N) :
    (moduleSheafDualIso e).inv = moduleSheafDualMap e.inv := rfl

end AlgebraicGeometry.Scheme.Modules
