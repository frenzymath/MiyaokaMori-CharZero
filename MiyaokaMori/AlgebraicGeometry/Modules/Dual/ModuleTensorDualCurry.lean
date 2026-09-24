import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModuleTensorPowers
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModuleDualSheafificationUnit
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModuleDualSectionEquiv

/-!
# Currying a tensor pairing into the canonical module dual

A pairing from the actual sheaf tensor product to the structure module gives a
morphism into the existing `moduleSheafDual`. On every open, a section of the first
factor defines a family of linear functionals on all smaller opens. Compatibility
with restriction makes it a section of the original dual presheaf, and its original
sheafification unit gives the required sheaf morphism.

The inverse of the same unit recovers the original pairing on each smaller open.
No finite-freeness or nondegeneracy hypothesis is used. The source is Stacks Project,
`modules.tex`, `lemma-internal-hom`, with structure-module target; used for the determinant/dual
comparison of §2 of the paper.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

namespace AlgebraicGeometry.Scheme.Modules.ModuleTensorDualCurry

universe u

variable {X : Scheme.{u}} (P Q : X.Modules)

set_option backward.isDefEq.respectTransparency false

private theorem tensorSection_smul_left {U : X.Opens} (r : Γ(X, U))
    (s : Γ(P, U)) (t : Γ(Q, U)) :
    moduleTensorSection (r • s) t = r • moduleTensorSection s t := by
  simpa only [one_smul, mul_one] using moduleTensorSection_smul r 1 s t

private theorem tensorSection_smul_right {U : X.Opens} (r : Γ(X, U))
    (s : Γ(P, U)) (t : Γ(Q, U)) :
    moduleTensorSection s (r • t) = r • moduleTensorSection s t := by
  simpa only [one_smul, one_mul] using moduleTensorSection_smul 1 r s t

variable (β : moduleTensor P Q ⟶ SheafOfModules.unit X.ringCatSheaf)

/-- A section of the first tensor factor determines compatible local functionals
on the second factor, using the original pairing on each smaller open. -/
def localCurry (U : X.Opens) :
    Γ(P, U) →ₗ[Γ(X, U)] LocalDualSections X Q U where
  toFun s :=
    ⟨fun V ↦
      { toFun := fun t ↦ β.app V.left
          (moduleTensorSection (P.presheaf.map V.hom.op s) t)
        map_add' := fun t t' ↦ by
          rw [moduleTensorSection_add_right, map_add]
        map_smul' := fun r t ↦ by
          simp only [tensorSection_smul_right, Scheme.Modules.Hom.app_smul,
            RingHom.id_apply] }, by
      intro V W i t
      change β.app V.left
          (moduleTensorSection (P.presheaf.map V.hom.op s)
            (Q.presheaf.map i.left.op t)) =
        X.presheaf.map i.left.op
          (β.app W.left (moduleTensorSection (P.presheaf.map W.hom.op s) t))
      rw [show V.hom = i.left ≫ W.hom from (Over.w i).symm,
        op_comp, P.presheaf.map_comp]
      change β.app V.left
          (moduleTensorSection (P.presheaf.map i.left.op (P.presheaf.map W.hom.op s))
            (Q.presheaf.map i.left.op t)) = _
      rw [← moduleTensorSection_restrict]
      exact PresheafOfModules.naturality_apply β.val i.left.op _⟩
  map_add' s s' := by
    apply Subtype.ext
    funext V
    ext t
    change β.app V.left (moduleTensorSection (P.presheaf.map V.hom.op (s + s')) t) =
      β.app V.left (moduleTensorSection (P.presheaf.map V.hom.op s) t) +
        β.app V.left (moduleTensorSection (P.presheaf.map V.hom.op s') t)
    rw [map_add, moduleTensorSection_add_left, map_add]
  map_smul' r s := by
    apply Subtype.ext
    funext V
    ext t
    change β.app V.left (moduleTensorSection (P.presheaf.map V.hom.op (r • s)) t) =
      X.presheaf.map V.hom.op r •
        β.app V.left (moduleTensorSection (P.presheaf.map V.hom.op s) t)
    simp only [Scheme.Modules.map_smul, tensorSection_smul_left, Scheme.Modules.Hom.app_smul]

/-- The local functional evaluates by applying the supplied pairing to the original tensor. -/
theorem localCurry_apply (U : X.Opens) (s : Γ(P, U))
    (V : Over U) (t : Γ(Q, V.left)) :
    (localCurry P Q β U s).val V t =
      β.app V.left (moduleTensorSection (P.presheaf.map V.hom.op s) t) := rfl

/-- The compatible functional family commutes with restriction of the first section. -/
theorem localCurry_restrict {U V : X.Opens} (i : V ⟶ U) (s : Γ(P, U)) :
    localDualRestrict Q i (localCurry P Q β U s) =
      localCurry P Q β V (P.presheaf.map i.op s) := by
  apply Subtype.ext
  funext W
  ext t
  change β.app W.left (moduleTensorSection (P.presheaf.map (W.hom ≫ i).op s) t) =
    β.app W.left (moduleTensorSection (P.presheaf.map W.hom.op
      (P.presheaf.map i.op s)) t)
  rw [op_comp, P.presheaf.map_comp]
  rfl

private def presheafCurry : P.val ⟶ moduleDualPresheaf Q where
  app U := ModuleCat.ofHom (localCurry P Q β U.unop)
  naturality {U V} i := by
    ext s
    exact (localCurry_restrict P Q β i.unop s).symm

/-- Curry the pairing into the same canonical dual sheaf via its original unit. -/
def curry : P ⟶ moduleSheafDual Q where
  val := presheafCurry P Q β ≫ (MiyaokaMori.ModuleDualSectionEquiv.unitIso Q).hom

/-- On sections, currying is the original dual-unit image of the compatible functional. -/
theorem curry_app (U : X.Opens) (s : Γ(P, U)) :
    (curry P Q β).app U s =
      MiyaokaMori.ModuleDualSectionEquiv.sectionEquiv Q U (localCurry P Q β U s) := rfl

/-- Inverting the original dual unit recovers the given pairing on every smaller open. -/
theorem curry_eval (U : X.Opens) (s : Γ(P, U)) (V : Over U) (t : Γ(Q, V.left)) :
    ((MiyaokaMori.ModuleDualSectionEquiv.sectionEquiv Q U).symm
        ((curry P Q β).app U s)).val V t =
      β.app V.left (moduleTensorSection (P.presheaf.map V.hom.op s) t) := by
  rw [curry_app, LinearEquiv.symm_apply_apply, localCurry_apply]

end AlgebraicGeometry.Scheme.Modules.ModuleTensorDualCurry
