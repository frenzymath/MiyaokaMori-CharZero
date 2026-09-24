import Mathlib.Algebra.Category.ModuleCat.Stalk
import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Stalks of module sheaves restricted along an open immersion

The canonical comparison from the stalk of a restricted module sheaf to the original
stalk is semilinear over the inverse of the actual local-ring map. Its underlying
additive equivalence is Mathlib's `Scheme.Modules.restrictStalkNatIso`, and its germ
formula retains the original section on the image open.

This supplies the scalar-compatible stalk comparison needed to transport the same
generic subspace when restricting the saturation step of the paper to an
affine chart. No integrality, quasi-coherence, finite-rank or Noetherian hypothesis is
needed. Generic subspaces, saturation and global quasi-coherence are later steps.

Sources: Stacks Project, `sheaves.tex`, `lemma-stalk-module`,
`lemma-stalk-pullback-modules` and `lemma-j-pullback`; `modules.tex`, restriction and
pullback of modules on ringed spaces. The construction uses only Mathlib's existing
restrictions, stalks and local-ring maps.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.Scheme.Modules.ModuleRestrictionStalk

set_option backward.isDefEq.respectTransparency false

/-- Expose Mathlib's canonical stalk action through the `Scheme.Modules` notation. -/
private abbrev stalkModule (X : Scheme.{u}) (E : X.Modules) (x : X) :
    Module (X.presheaf.stalk x) (E.presheaf.stalk x) := by
  change Module (X.presheaf.stalk x)
    ↑(TopCat.Presheaf.stalk
      (show _root_.PresheafOfModules (X.presheaf ⋙ forget₂ CommRingCat RingCat) from E.val).presheaf x)
  infer_instance

attribute [local instance] stalkModule

variable {X Y : Scheme.{u}} (f : Y ⟶ X) [IsOpenImmersion f]

/-- The inverse of the actual local-ring map of an open immersion. -/
def stalkRingEquiv (y : Y) : Y.presheaf.stalk y ≃+* X.presheaf.stalk (f y) :=
  ((asIso (f.stalkMap y)).symm).commRingCatIsoToRingEquiv

/-- A germ followed by the inverse local-ring map is the germ on the image open. -/
theorem germ_inv_stalkMap (y : Y) (U : Y.Opens) (hy : y ∈ U) :
    Y.presheaf.germ U y hy ≫ (asIso (f.stalkMap y)).inv =
      (f.appIso U).inv ≫ X.presheaf.germ (f ''ᵁ U) (f y) ⟨y, hy, rfl⟩ := by
  apply (cancel_mono (f.stalkMap y)).1
  simp only [Category.assoc, asIso_inv, IsIso.inv_hom_id, Category.comp_id]
  rw [Scheme.Hom.germ_stalkMap, Scheme.Hom.appIso_inv_app_assoc]
  exact (Y.presheaf.germ_res (eqToHom (f.preimage_image_eq U)) y ⟨y, hy, rfl⟩).symm

/-- The scalar comparison sends a germ to the corresponding original scalar germ. -/
@[simp]
theorem stalkRingEquiv_germ (y : Y) (U : Y.Opens) (hy : y ∈ U) (r : Γ(Y, U)) :
    stalkRingEquiv f y (Y.presheaf.germ U y hy r) =
      X.presheaf.germ (f ''ᵁ U) (f y) ⟨y, hy, rfl⟩ ((f.appIso U).inv r) :=
  congrArg (fun g ↦ g r) (germ_inv_stalkMap f y U hy)

/-- Restricting along an open immersion preserves the actual module stalk semilinearly. -/
def stalkEquiv (E : X.Modules) (y : Y) :
    let ρ := stalkRingEquiv f y
    haveI := RingHomInvPair.of_ringEquiv ρ
    haveI := RingHomInvPair.of_ringEquiv_symm ρ
    (E.restrict f).presheaf.stalk y ≃ₛₗ[
      (↑ρ : Y.presheaf.stalk y →+* X.presheaf.stalk (f y))] E.presheaf.stalk (f y) := by
  let ρ := stalkRingEquiv f y
  haveI := RingHomInvPair.of_ringEquiv ρ
  haveI := RingHomInvPair.of_ringEquiv_symm ρ
  exact
  { ((Scheme.Modules.restrictStalkNatIso f y).app E).addCommGroupIsoToAddEquiv with
    map_smul' := by
      intro r m
      obtain ⟨V, hyV, a, rfl⟩ := Y.presheaf.exists_germ_eq r
      obtain ⟨U, hUV, hyU, b, rfl⟩ :=
        (E.restrict f).presheaf.exists_le_germ_eq m hyV
      rw [← Y.presheaf.germ_res_apply (CategoryTheory.homOfLE hUV) y hyU a]
      erw [← PresheafOfModules.germ_smul (R := Y.presheaf) (E.restrict f).val]
      have hg (s : Γ(E.restrict f, U)) :
          (Scheme.Modules.restrictStalkNatIso f y).hom.app E
              ((E.restrict f).presheaf.germ U y hyU s) =
            E.presheaf.germ (f ''ᵁ U) (f y) ⟨y, hyU, rfl⟩ s :=
        congrArg (fun g ↦ g s)
          (Scheme.Modules.germ_restrictStalkNatIso_hom_app f y E hyU)
      change (Scheme.Modules.restrictStalkNatIso f y).hom.app E
          ((E.restrict f).presheaf.germ U y hyU (_ • b)) = _
      erw [hg]
      change E.presheaf.germ (f ''ᵁ U) (f y) _ (_ • b) = _
      erw [PresheafOfModules.germ_smul (R := X.presheaf) E.val]
      congr 1
      · change X.presheaf.germ (f ''ᵁ U) (f y) _
            ((f.appIso U).inv (Y.presheaf.map (CategoryTheory.homOfLE hUV).op a)) = _
        exact (stalkRingEquiv_germ f y U hyU (Y.presheaf.map (CategoryTheory.homOfLE hUV).op a)).symm
      · exact (hg b).symm }

/-- The semilinear equivalence preserves the represented section on every image open. -/
@[simp]
theorem stalkEquiv_germ (E : X.Modules) (y : Y) (U : Y.Opens) (hy : y ∈ U)
    (s : Γ(E.restrict f, U)) :
    stalkEquiv f E y ((E.restrict f).presheaf.germ U y hy s) =
      E.presheaf.germ (f ''ᵁ U) (f y) ⟨y, hy, rfl⟩ ((E.restrictAppIso f U).hom s) :=
  congrArg (fun g ↦ g s) (Scheme.Modules.germ_restrictStalkNatIso_hom_app f y E hy)

end AlgebraicGeometry.Scheme.Modules.ModuleRestrictionStalk
