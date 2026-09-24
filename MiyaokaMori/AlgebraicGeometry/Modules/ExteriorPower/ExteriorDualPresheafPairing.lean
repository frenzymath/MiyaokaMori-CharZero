import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModuleDual
import MiyaokaMori.AlgebraicGeometry.Modules.ExteriorPower.ModuleExteriorPower
import Mathlib.LinearAlgebra.ExteriorPower.Pairing
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal

/-!
# Exterior pairing of compatible local functionals

Evaluation at the identity subopen sends a compatible local functional to an actual
linear functional on sections. Its exterior power, followed by Mathlib's canonical
dual pairing, gives a bilinear pairing on the original exterior presheaves. The
determinant formula and compatibility of local functionals prove restriction
naturality, first on wedge generators and then on all sections by their spanning
property. Tensor lifting therefore gives a morphism to the structure presheaf.

Sources: Stacks Project, `modules.tex`, Internal Hom, Tensor product, and Symmetric and exterior
powers; Mathlib's canonical exterior pairing and tensor universal property.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Modules.ExteriorDualPresheafPairing

universe u

variable {X : Scheme.{u}}

/- All statements in this file are written in the **spelling of `moduleExteriorPresheaf … .obj (op U)`
   itself**: the scalar ring is `X.ringCatSheaf.obj.obj (op U)`, the carrier is the presheaf object and
   the module structure is the native `isModule` of `ModuleCat`. Writing
   `⋀[Γ(X, U)]^n (LocalDualSections X M U)` instead would be defeq but syntactically different, and as
   soon as the carriers of exterior powers differ syntactically, `isDefEq` does not compare the
   arguments of `exteriorPower` but unfolds `↥(⋀[R]^n M)` all the way to `CliffordAlgebra` (measured:
   the type 0.67 s, `AddCommMonoid` 1.6 s, `Module` 5.2 s, repeated about 6 times in
   `presheafPairing.app` = 45 s and 1.1 M heartbeats). With one spelling these comparisons are
   syntactic equalities, and the file needs no `set_option` and no `local instance` connecting
   `Γ(X, U)` to the presheaf module structure.

   The `CommRing` instance below is kept: the object of `moduleExteriorPresheaf` is
   `⋀[X.ringCatSheaf.obj.obj U]^n _`, and `X.ringCatSheaf` is defined through `sheafCompose` (a
   semireducible `def`), which typeclass search does not see through; the same instance in
   `ModuleExteriorPower` is `local` and not exported. -/
local instance (U : X.Opensᵒᵖ) : CommRing (X.ringCatSheaf.obj.obj U) :=
  inferInstanceAs (CommRing Γ(X, U.unop))

/-- Evaluate compatible local functionals at the identity subopen. -/
def localDualAtOpen (M : X.Modules) (U : X.Opens) :
    (moduleDualPresheaf M).obj (op U) →ₗ[X.ringCatSheaf.obj.obj (op U)]
      Module.Dual (X.ringCatSheaf.obj.obj (op U)) (M.val.obj (op U)) where
  toFun φ := φ.val (Over.mk (𝟙 U))
  map_add' φ ψ := rfl
  map_smul' r φ := by
    ext s
    change ((X.presheaf.map (Over.mk (𝟙 U)).hom.op).hom r •
      φ.val (Over.mk (𝟙 U))) s = _
    erw [X.presheaf.map_id]
    rfl

/-- Identity-subopen evaluation is the original local functional on those sections. -/
@[simp]
theorem localDualAtOpen_apply (M : X.Modules) (U : X.Opens)
    (φ : LocalDualSections X M U) (s : Γ(M, U)) :
    localDualAtOpen M U φ s = φ.val (Over.mk (𝟙 U)) s := rfl

/-- Restricting both a functional and its argument restricts their actual evaluation. -/
theorem localDualAtOpen_restrict (M : X.Modules) {U V : X.Opens} (i : V ⟶ U)
    (φ : LocalDualSections X M U) (s : Γ(M, U)) :
    localDualAtOpen M V (localDualRestrict M i φ) (M.presheaf.map i.op s) =
      X.presheaf.map i.op (localDualAtOpen M U φ s) := by
  exact φ.property ((Over.map i).obj (Over.mk (𝟙 V))) (Over.mk (𝟙 U))
    (Over.homMk i (by simp)) s

/-- The exterior pairing induced by evaluation of the original compatible functionals,
as a bilinear pairing between the sections of the two exterior presheaves over `U`. -/
def sectionPairing (M : X.Modules) (n : ℕ) (U : X.Opens) :
    (moduleExteriorPresheaf X (moduleDualPresheaf M) n).obj (op U)
      →ₗ[X.ringCatSheaf.obj.obj (op U)]
        Module.Dual (X.ringCatSheaf.obj.obj (op U))
          ((moduleExteriorPresheaf X M.val n).obj (op U)) :=
  (exteriorPower.pairingDual (X.ringCatSheaf.obj.obj (op U)) (M.val.obj (op U)) n).comp
    (exteriorPower.map n (localDualAtOpen M U))

/-- Pure wedges pair by the determinant of their original evaluation matrix. -/
theorem sectionPairing_pure (M : X.Modules) (n : ℕ) (U : X.Opens)
    (Φ : Fin n → LocalDualSections X M U) (v : Fin n → Γ(M, U)) :
    sectionPairing M n U
        (ModuleCat.exteriorPower.mk (M := (moduleDualPresheaf M).obj (op U)) Φ)
        (ModuleCat.exteriorPower.mk (M := M.val.obj (op U)) v) =
      Matrix.det (n := Fin n)
        (.of (fun i j ↦ (Φ j).val (Over.mk (𝟙 U)) (v i))) :=
  (congrArg
    (fun a ↦ exteriorPower.pairingDual (X.ringCatSheaf.obj.obj (op U)) (M.val.obj (op U)) n a
      (exteriorPower.ιMulti _ n v))
    (exteriorPower.map_apply_ιMulti (localDualAtOpen M U) Φ)).trans
    (exteriorPower.pairingDual_ιMulti_ιMulti _ _)

/-- Pure algebra: a pairing identity between two semilinear-compatible pairings, known on
spanning sets, holds everywhere. No presheaves occur, so every `isDefEq` here is cheap. -/
theorem semilinear_pairing_ext {R S E F E' F' : Type*} [CommRing R] [CommRing S]
    [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F]
    [AddCommGroup E'] [Module S E'] [AddCommGroup F'] [Module S F']
    (ρ : R →+* S) (f : E → E') (g : F → F')
    (hf_add : ∀ x y, f (x + y) = f x + f y) (hf_smul : ∀ (r : R) x, f (r • x) = ρ r • f x)
    (hg_add : ∀ x y, g (x + y) = g x + g y) (hg_smul : ∀ (r : R) x, g (r • x) = ρ r • g x)
    (P : E →ₗ[R] F →ₗ[R] R) (Q : E' →ₗ[S] F' →ₗ[S] S)
    {s : Set E} {t : Set F} (hs : Submodule.span R s = ⊤) (ht : Submodule.span R t = ⊤)
    (h : ∀ a ∈ s, ∀ b ∈ t, Q (f a) (g b) = ρ (P a b)) (α : E) (z : F) :
    Q (f α) (g z) = ρ (P α z) := by
  have hf0 : f 0 = 0 := by simpa using hf_smul 0 0
  have hg0 : g 0 = 0 := by simpa using hg_smul 0 0
  have hα : α ∈ Submodule.span R s := hs ▸ Submodule.mem_top
  have hz : z ∈ Submodule.span R t := ht ▸ Submodule.mem_top
  induction hα using Submodule.span_induction with
  | mem a ha =>
    induction hz using Submodule.span_induction with
    | mem b hb => exact h a ha b hb
    | zero => simp [hg0]
    | add x y _ _ hx hy => simp [hg_add, hx, hy]
    | smul r x _ hx => simp [hg_smul, hx]
  | zero => simp [hf0]
  | add x y _ _ hx hy => simp [hf_add, hx, hy]
  | smul r x _ hx => simp [hf_smul, hx]

-- The two-variable induction on generators is entirely in the pure algebra lemma above (no presheaves).
-- With the statement in the presheaf spelling, `exteriorRestriction_mk` matches syntactically and no
-- `(E' := …)`, `(M := …)` annotations against wrong unification are needed. The ring homomorphism must be
-- written `X.ringCatSheaf.obj.map i.op` (the same spelling as the module structure); with
-- `X.presheaf.map i.op` the instances are not found.
/-- The section pairing commutes with restriction for arbitrary exterior sections. -/
theorem sectionPairing_restrict (M : X.Modules) (n : ℕ)
    {U V : X.Opens} (i : V ⟶ U)
    (α : (moduleExteriorPresheaf X (moduleDualPresheaf M) n).obj (op U))
    (z : (moduleExteriorPresheaf X M.val n).obj (op U)) :
    sectionPairing M n V
        ((moduleExteriorPresheaf X (moduleDualPresheaf M) n).map i.op α)
        ((moduleExteriorPresheaf X M.val n).map i.op z) =
      X.presheaf.map i.op (sectionPairing M n U α z) := by
  refine semilinear_pairing_ext (X.ringCatSheaf.obj.map i.op).hom
    (fun a ↦ (moduleExteriorPresheaf X (moduleDualPresheaf M) n).map i.op a)
    (fun b ↦ (moduleExteriorPresheaf X M.val n).map i.op b)
    ?_ ?_ ?_ ?_ (sectionPairing M n U) (sectionPairing M n V)
    (exteriorPower.ιMulti_span _ n _) (exteriorPower.ιMulti_span _ n _) ?_ α z
  · exact fun x y ↦ map_add _ x y
  · exact fun r x ↦ PresheafOfModules.map_smul
      (moduleExteriorPresheaf X (moduleDualPresheaf M) n) i.op r x
  · exact fun x y ↦ map_add _ x y
  · exact fun r x ↦ PresheafOfModules.map_smul (moduleExteriorPresheaf X M.val n) i.op r x
  · rintro _ ⟨Φ, rfl⟩ _ ⟨v, rfl⟩
    have h1 := exteriorRestriction_mk X (moduleDualPresheaf M) n i.op Φ
    have h2 := exteriorRestriction_mk X M.val n i.op v
    refine (congrArg₂ (fun a b ↦ sectionPairing M n V a b) h1 h2).trans ?_
    refine (sectionPairing_pure M n V _ _).trans ?_
    refine Eq.trans ?_
      (congrArg (X.presheaf.map i.op).hom (sectionPairing_pure M n U Φ v)).symm
    rw [RingHom.map_det]
    congr 1
    ext a b
    exact localDualAtOpen_restrict M i (Φ b) (v a)

-- The codomain is Mathlib's own monoidal unit `PresheafOfModules.unit` (no detour through restriction of
-- scalars along the identity). `sectionPairing` has the same spelling as the object of `tensorObj`, so the
-- unification of `app` is syntactic, and naturality, after tensor extensionality, **is**
-- `sectionPairing_restrict`; no `change` and no `maxHeartbeats` are needed.
/-- Tensor lifting of the exterior section pairing to the actual structure presheaf. -/
def presheafPairing (M : X.Modules) (n : ℕ) :
    PresheafOfModules.Monoidal.tensorObj (R := X.presheaf)
        (moduleExteriorPresheaf X (moduleDualPresheaf M) n)
        (moduleExteriorPresheaf X M.val n) ⟶
      PresheafOfModules.unit (R := X.presheaf ⋙ forget₂ CommRingCat RingCat) where
  app U := ModuleCat.ofHom
    (Y := (PresheafOfModules.unit (R := X.presheaf ⋙ forget₂ CommRingCat RingCat)).obj U)
    (TensorProduct.lift (sectionPairing M n U.unop))
  naturality i := ModuleCat.MonoidalCategory.tensor_ext fun α z ↦
    sectionPairing_restrict M n i.unop α z

/-- The tensor-presheaf morphism evaluates each pure tensor by the section pairing. -/
@[simp]
theorem presheafPairing_tmul (M : X.Modules) (n : ℕ) (U : X.Opens)
    (α : (moduleExteriorPresheaf X (moduleDualPresheaf M) n).obj (op U))
    (z : (moduleExteriorPresheaf X M.val n).obj (op U)) :
    (presheafPairing M n).app (op U) (α ⊗ₜ[Γ(X, U)] z) =
      sectionPairing M n U α z :=
  TensorProduct.lift.tmul _ _

end AlgebraicGeometry.Scheme.Modules.ExteriorDualPresheafPairing
