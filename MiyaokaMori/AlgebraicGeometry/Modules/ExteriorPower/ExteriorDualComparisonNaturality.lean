import MiyaokaMori.AlgebraicGeometry.Modules.ExteriorPower.ExteriorDualSheafComparison
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModuleDualFunctor
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModuleDualSectionEquiv

/-!
# Naturality of the original exterior-dual comparison

The original dual map acts by precomposition on compatible local functionals.
The determinant pairing is therefore natural on two wedge generators. The
sheafification adjunction and the two exterior universal properties extend this
identity to the actual tensor sheaves. Currying gives naturality of the already
constructed exterior-dual comparison on every section and every smaller open.

Transport by a supplied module-sheaf isomorphism then preserves invertibility of
that same comparison. All schemes, modules and exterior degrees are arbitrary.

Sources: Stacks Project, `modules.tex`,
Internal Hom, Tensor product and Symmetric and exterior powers; Mathlib's exterior
and tensor universal properties and module-sheafification adjunction.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Modules.ExteriorDualComparisonNaturality

universe u

set_option backward.isDefEq.respectTransparency false



variable {X : Scheme.{u}} {M N : X.Modules}

/- `Scheme.ringCatSheaf` is a plain, non-reducible `def`, so typeclass search cannot see through it
and does not find the `CommRing` structure on the section ring (needed by `ModuleCat.exteriorPower.mk`).
The upstream bridge is a `local instance`, whose attribute does not cross files, so it is repeated
here; the name carries a file prefix since the name is global. -/
local instance exteriorDualComparisonNaturalitySectionCommRing (U : X.Opensᵒᵖ) :
    CommRing (X.ringCatSheaf.obj.obj U) :=
  inferInstanceAs (CommRing Γ(X, U.unop))

/-- The original dual map carries a unit image to the unit image of precomposition. -/
theorem dualMap_sectionEquiv (φ : M ⟶ N) (U : X.Opens)
    (α : LocalDualSections X N U) :
    (moduleSheafDualMap φ).app U (MiyaokaMori.ModuleDualSectionEquiv.sectionEquiv N U α) =
      MiyaokaMori.ModuleDualSectionEquiv.sectionEquiv M U (localDualSectionsPrecomp φ U α) := by
  exact (congrArg (fun f ↦ f.app (op U) α) (moduleSheafDualMap_unit φ)).symm

/-- Recovering compatible functionals from a dual-map image gives actual precomposition. -/
theorem dualMap_sectionEquiv_symm (φ : M ⟶ N) (U : X.Opens)
    (s : Γ(moduleSheafDual N, U)) :
    (MiyaokaMori.ModuleDualSectionEquiv.sectionEquiv M U).symm ((moduleSheafDualMap φ).app U s) =
      localDualSectionsPrecomp φ U ((MiyaokaMori.ModuleDualSectionEquiv.sectionEquiv N U).symm s) := by
  apply (MiyaokaMori.ModuleDualSectionEquiv.sectionEquiv M U).injective
  rw [LinearEquiv.apply_symm_apply, ← dualMap_sectionEquiv, LinearEquiv.apply_symm_apply]

/-- On every subopen the original dual map evaluates by the original forward map. -/
theorem dualMap_eval (φ : M ⟶ N) (U : X.Opens) (s : Γ(moduleSheafDual N, U))
    (V : Over U) (t : Γ(M, V.left)) :
    ((MiyaokaMori.ModuleDualSectionEquiv.sectionEquiv M U).symm
        ((moduleSheafDualMap φ).app U s)).val V t =
      ((MiyaokaMori.ModuleDualSectionEquiv.sectionEquiv N U).symm s).val V (φ.app V.left t) := by
  rw [dualMap_sectionEquiv_symm]
  rfl

/-- Morphisms out of the tensor of two exterior sheaves are determined by tensors of
wedge sections on all opens, via the actual sheafification adjunction. -/
theorem tensorExterior_hom_ext (P Q : X.Modules) (n : ℕ) {K : X.Modules}
    {f g : moduleTensor (moduleExteriorPower X P n) (moduleExteriorPower X Q n) ⟶ K}
    (h : ∀ (U : X.Opens) (v : Fin n → Γ(P, U)) (w : Fin n → Γ(Q, U)),
      f.app U (moduleTensorSection (moduleExteriorWedge X P n U v)
        (moduleExteriorWedge X Q n U w)) =
      g.app U (moduleTensorSection (moduleExteriorWedge X P n U v)
        (moduleExteriorWedge X Q n U w))) : f = g := by
  let A := moduleExteriorPresheaf X P.val n
  let B := moduleExteriorPresheaf X Q.val n
  let e : moduleSheafification X
      (PresheafOfModules.Monoidal.tensorObj (R := X.presheaf) A B) ≅
      moduleTensor (moduleExteriorPower X P n) (moduleExteriorPower X Q n) :=
    ModuleTensorAssociator.leftUnitIso A B ≪≫
      ModuleTensorAssociator.rightUnitIso (moduleExteriorPower X P n).val B
  have he (U : X.Opens) (a : A.obj (op U)) (b : B.obj (op U)) :
      e.hom.app U (moduleSheafificationUnit X
        (PresheafOfModules.Monoidal.tensorObj (R := X.presheaf) A B) U
        (a ⊗ₜ[Γ(X, U)] b)) =
      moduleTensorSection (moduleSheafificationUnit X A U a)
        (moduleSheafificationUnit X B U b) := by
    change (ModuleTensorAssociator.rightUnitIso (moduleExteriorPower X P n).val B).hom.app U
      ((ModuleTensorAssociator.leftUnitIso A B).hom.app U _) = _
    rw [ModuleTensorAssociator.leftUnitIso_section]
    -- `rw` needs the same `?P` at both occurrences in the goal, but here one is
    -- `(moduleExteriorPower X P n).val` and the other `(moduleSheafification X A).val` (only defeq),
    -- so use `exact` with all arguments explicit; defeq is checked once at the end.
    exact ModuleTensorAssociator.rightUnitIso_section
      (moduleExteriorPower X P n).val B U (moduleSheafificationUnit X A U a) b
  apply (cancel_epi e.hom).1
  apply ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv
    (PresheafOfModules.Monoidal.tensorObj (R := X.presheaf) A B) K).injective
  rw [(PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv_unit,
    (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv_unit]
  apply PresheafOfModules.hom_ext
  intro U
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro w
  change f.app U.unop (e.hom.app U.unop
      (moduleSheafificationUnit X
        (PresheafOfModules.Monoidal.tensorObj (R := X.presheaf) A B) U.unop
        (ModuleCat.exteriorPower.mk v ⊗ₜ[Γ(X, U.unop)] ModuleCat.exteriorPower.mk w))) =
    g.app U.unop (e.hom.app U.unop
      (moduleSheafificationUnit X
        (PresheafOfModules.Monoidal.tensorObj (R := X.presheaf) A B) U.unop
        (ModuleCat.exteriorPower.mk v ⊗ₜ[Γ(X, U.unop)] ModuleCat.exteriorPower.mk w)))
  -- After `simpa only [he]` the two sides would be only defeq, not syntactically equal
  -- (`moduleExteriorWedge` vs `moduleSheafificationUnit … (mk v)`), so `simp` cannot close the goal;
  -- use `rw` + `exact` instead.
  rw [he U.unop (ModuleCat.exteriorPower.mk v) (ModuleCat.exteriorPower.mk w)]
  exact h U.unop v w

/-- The two actual tensor pairings agree after applying the forward and dual exterior maps. -/
theorem sheafPairing_naturality (φ : M ⟶ N) (n : ℕ) :
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
        (PresheafOfModules.Monoidal.tensorHom (R := X.presheaf)
          (moduleExteriorMap X n (moduleSheafDualMap φ)).val
          (𝟙 (moduleExteriorPower X M n).val)) ≫
      ExteriorDualSheafComparison.sheafPairing M n =
    (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
        (PresheafOfModules.Monoidal.tensorHom (R := X.presheaf)
          (𝟙 (moduleExteriorPower X (moduleSheafDual N) n).val)
          (moduleExteriorMap X n φ).val) ≫
      ExteriorDualSheafComparison.sheafPairing N n := by
  apply tensorExterior_hom_ext (moduleSheafDual N) M n
  intro U Φ v
  change (ExteriorDualSheafComparison.sheafPairing M n).app U
      (((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
        (PresheafOfModules.Monoidal.tensorHom (R := X.presheaf)
          (moduleExteriorMap X n (moduleSheafDualMap φ)).val
          (𝟙 (moduleExteriorPower X M n).val))).val.app (op U)
        (moduleSheafificationUnit X
          (PresheafOfModules.Monoidal.tensorObj (R := X.presheaf)
            (moduleExteriorPower X (moduleSheafDual N) n).val
            (moduleExteriorPower X M n).val) U
          (moduleExteriorWedge X (moduleSheafDual N) n U Φ ⊗ₜ[Γ(X, U)]
            moduleExteriorWedge X M n U v))) =
    (ExteriorDualSheafComparison.sheafPairing N n).app U
      (((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
        (PresheafOfModules.Monoidal.tensorHom (R := X.presheaf)
          (𝟙 (moduleExteriorPower X (moduleSheafDual N) n).val)
          (moduleExteriorMap X n φ).val)).val.app (op U)
        (moduleSheafificationUnit X
          (PresheafOfModules.Monoidal.tensorObj (R := X.presheaf)
            (moduleExteriorPower X (moduleSheafDual N) n).val
            (moduleExteriorPower X M n).val) U
          (moduleExteriorWedge X (moduleSheafDual N) n U Φ ⊗ₜ[Γ(X, U)]
            moduleExteriorWedge X M n U v)))
  rw [moduleSheafificationUnit_naturality, moduleSheafificationUnit_naturality]
  change (ExteriorDualSheafComparison.sheafPairing M n).app U
      (moduleTensorSection
        ((moduleExteriorMap X n (moduleSheafDualMap φ)).app U
          (moduleExteriorWedge X (moduleSheafDual N) n U Φ))
        (moduleExteriorWedge X M n U v)) =
    (ExteriorDualSheafComparison.sheafPairing N n).app U
      (moduleTensorSection (moduleExteriorWedge X (moduleSheafDual N) n U Φ)
        ((moduleExteriorMap X n φ).app U (moduleExteriorWedge X M n U v)))
  rw [moduleExteriorMap_wedge, moduleExteriorMap_wedge,
    ExteriorDualSheafComparison.sheafPairing_wedge,
    ExteriorDualSheafComparison.sheafPairing_wedge]
  congr 1
  ext i j
  exact dualMap_eval φ U (Φ j) (Over.mk (𝟙 U)) (v i)

/-- Pairing naturality applies to arbitrary sections of the exterior sheaves. -/
theorem sheafPairing_naturality_sections (φ : M ⟶ N) (n : ℕ) (U : X.Opens)
    (s : Γ(moduleExteriorPower X (moduleSheafDual N) n, U))
    (t : Γ(moduleExteriorPower X M n, U)) :
    (ExteriorDualSheafComparison.sheafPairing M n).app U
        (moduleTensorSection ((moduleExteriorMap X n (moduleSheafDualMap φ)).app U s) t) =
      (ExteriorDualSheafComparison.sheafPairing N n).app U
        (moduleTensorSection s ((moduleExteriorMap X n φ).app U t)) := by
  -- Both sides of `sheafPairing_naturality` have type `SheafOfModules.Hom` (not a hom of `X.Modules`),
  -- which has no `.app`; write `.val.app (op U)`.
  have h := congrArg (fun f ↦ f.val.app (op U) (moduleTensorSection s t))
    (sheafPairing_naturality φ n)
  change (ExteriorDualSheafComparison.sheafPairing M n).app U
      (((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
        (PresheafOfModules.Monoidal.tensorHom (R := X.presheaf)
          (moduleExteriorMap X n (moduleSheafDualMap φ)).val
          (𝟙 (moduleExteriorPower X M n).val))).val.app (op U)
        (moduleSheafificationUnit X
          (PresheafOfModules.Monoidal.tensorObj (R := X.presheaf)
            (moduleExteriorPower X (moduleSheafDual N) n).val
            (moduleExteriorPower X M n).val) U (s ⊗ₜ[Γ(X, U)] t))) =
    (ExteriorDualSheafComparison.sheafPairing N n).app U
      (((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
        (PresheafOfModules.Monoidal.tensorHom (R := X.presheaf)
          (𝟙 (moduleExteriorPower X (moduleSheafDual N) n).val)
          (moduleExteriorMap X n φ).val)).val.app (op U)
        (moduleSheafificationUnit X
          (PresheafOfModules.Monoidal.tensorObj (R := X.presheaf)
            (moduleExteriorPower X (moduleSheafDual N) n).val
            (moduleExteriorPower X M n).val) U (s ⊗ₜ[Γ(X, U)] t))) at h
  rw [moduleSheafificationUnit_naturality, moduleSheafificationUnit_naturality] at h
  exact h

/-- The original exterior-dual comparison is contravariantly natural in every module map. -/
theorem naturality (φ : M ⟶ N) (n : ℕ) :
    moduleExteriorMap X n (moduleSheafDualMap φ) ≫ exteriorDualComparison M n =
      exteriorDualComparison N n ≫ moduleSheafDualMap (moduleExteriorMap X n φ) := by
  apply Scheme.Modules.hom_ext
  intro U
  apply ConcreteCategory.hom_ext
  intro s
  apply (MiyaokaMori.ModuleDualSectionEquiv.sectionEquiv (moduleExteriorPower X M n) U).symm.injective
  apply Subtype.ext
  funext V
  apply LinearMap.ext
  intro t
  change ((MiyaokaMori.ModuleDualSectionEquiv.sectionEquiv (moduleExteriorPower X M n) U).symm
      ((exteriorDualComparison M n).app U
        ((moduleExteriorMap X n (moduleSheafDualMap φ)).app U s))).val V t =
    ((MiyaokaMori.ModuleDualSectionEquiv.sectionEquiv (moduleExteriorPower X M n) U).symm
      ((moduleSheafDualMap (moduleExteriorMap X n φ)).app U
        ((exteriorDualComparison N n).app U s))).val V t
  rw [exteriorDualComparison_eval, dualMap_eval, exteriorDualComparison_eval]
  -- The pattern of `rw [← naturality_apply …]` uses `.val.map` / `.val.app`, while the goal has
  -- `.presheaf.map` / `Scheme.Modules.Hom.app` (only defeq), so it does not match. State a `have` in
  -- the shape of the goal, so that defeq is checked only once.
  have hnat : (moduleExteriorPower X (moduleSheafDual M) n).presheaf.map V.hom.op
      ((moduleExteriorMap X n (moduleSheafDualMap φ)).app U s) =
      (moduleExteriorMap X n (moduleSheafDualMap φ)).app V.left
        ((moduleExteriorPower X (moduleSheafDual N) n).presheaf.map V.hom.op s) :=
    (PresheafOfModules.naturality_apply
      (moduleExteriorMap X n (moduleSheafDualMap φ)).val V.hom.op s).symm
  rw [hnat]
  exact sheafPairing_naturality_sections φ n V.left
    ((moduleExteriorPower X (moduleSheafDual N) n).presheaf.map V.hom.op s) t

/-- A supplied module-sheaf isomorphism preserves invertibility of the original comparison. -/
theorem isIso_iff (e : M ≅ N) (n : ℕ) :
    IsIso (exteriorDualComparison M n) ↔ IsIso (exteriorDualComparison N n) := by
  let a := moduleExteriorIso X n (moduleSheafDualIso e)
  let b := moduleSheafDualIso (moduleExteriorIso X n e)
  have h : a.hom ≫ exteriorDualComparison M n = exteriorDualComparison N n ≫ b.hom :=
    naturality e.hom n
  constructor
  · intro hM
    letI := hM
    have hn : exteriorDualComparison N n = a.hom ≫ exteriorDualComparison M n ≫ b.inv := by
      have h' := congrArg (fun f ↦ f ≫ b.inv) h
      simpa only [Category.assoc, b.hom_inv_id, Category.comp_id] using h'.symm
    rw [hn]
    infer_instance
  · intro hN
    letI := hN
    have hm : exteriorDualComparison M n = a.inv ≫ exteriorDualComparison N n ≫ b.hom := by
      have h' := congrArg (fun f ↦ a.inv ≫ f) h
      simpa only [← Category.assoc, a.inv_hom_id, Category.id_comp] using h'
    rw [hm]
    infer_instance

end AlgebraicGeometry.Scheme.Modules.ExteriorDualComparisonNaturality
