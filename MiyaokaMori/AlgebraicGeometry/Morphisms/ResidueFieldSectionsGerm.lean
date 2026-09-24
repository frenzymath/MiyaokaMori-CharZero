import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Varieties.FunctionField.FunctionFieldEqResidueFieldAtGenericPoint

/-! # Functions on `Spec κ(η)` pulled back from an open of `X` are germs

For `X` integral with generic point `η`, `U ∋ η` open and `r ∈ Γ(X, U)`: the pullback of `r` along
`Spec κ(η) → X` (`fromSpecResidueField`, landing in `U`), read in `κ(η)` through `ΓSpecIso`, is the residue
of the germ of `r`; carried back to `K(X)` by `functionFieldIsoResidueField⁻¹` it is the germ of `r`
(`germToFunctionField`). Proof: `fromSpecResidueField = Spec.map (residue) ≫ fromSpecStalk`,
`Scheme.Hom.appLE_comp_appLE`, `fromSpecStalk_app` (the sections map of `fromSpecStalk` is the germ
followed by `ΓSpecIso⁻¹`) and `ΓSpecIso_inv_naturality`. -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

/-- `(Spec.map φ).appLE ⊤ ⊤ = (Spec.map φ).appTop` (`Spec.map φ ⁻¹ᵁ ⊤ = ⊤` definitionally). -/
theorem Spec_map_appLE_top_top {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (e : (⊤ : (Spec S).Opens) ≤ (Spec.map φ) ⁻¹ᵁ ⊤) :
    (Spec.map φ).appLE ⊤ ⊤ e = (Spec.map φ).appTop := by
  show (Spec.map φ).app ⊤ ≫ (Spec S).presheaf.map (homOfLE e).op = (Spec.map φ).app ⊤
  have hid : (Spec S).presheaf.map (homOfLE e).op = 𝟙 (Γ(Spec S, ⊤)) := (Spec S).presheaf.map_id (op ⊤)
  rw [hid]
  exact Category.comp_id _

/-- `ΓSpecIso ∘ (Spec κ(x) → X)^♯ = residue ∘ germ` on `Γ(X, U)`, `x ∈ U`. -/
theorem ΓSpecIso_hom_fromSpecResidueField_appLE (x : X) {U : X.Opens} (hxU : x ∈ U)
    (h : (⊤ : (Spec (X.residueField x)).Opens) ≤ (X.fromSpecResidueField x) ⁻¹ᵁ U) (r : Γ(X, U)) :
    (ΓSpecIso (X.residueField x)).hom ((X.fromSpecResidueField x).appLE U ⊤ h r) =
      X.residue x (X.presheaf.germ U x hxU r) := by
  have h' : (⊤ : (Spec (X.residueField x)).Opens) ≤
      (Spec.map (X.residue x)) ⁻¹ᵁ ((X.fromSpecStalk x) ⁻¹ᵁ U) := h
  have hc := Scheme.Hom.appLE_comp_appLE (Spec.map (X.residue x)) (X.fromSpecStalk x) U
    ((X.fromSpecStalk x) ⁻¹ᵁ U) ⊤ le_rfl h'
  have hdef : (X.fromSpecResidueField x).appLE U ⊤ h =
      (Spec.map (X.residue x) ≫ X.fromSpecStalk x).appLE U ⊤ h := rfl
  rw [hdef, ← hc, Scheme.Hom.appLE_eq_app, fromSpecStalk_app hxU, Category.assoc, Category.assoc,
    Scheme.Hom.map_appLE, Spec_map_appLE_top_top, ← ΓSpecIso_inv_naturality, CommRingCat.comp_apply,
    CommRingCat.comp_apply, Iso.inv_hom_id_apply]

/-- The generic chart coordinate route back to `K(X)`: `ι_K⁻¹ (ΓSpecIso (η^♯ r)) = germ_η r`. -/
theorem functionFieldIsoResidueField_inv_ΓSpecIso_hom_appLE [IsIntegral X] {U : X.Opens}
    (hU : genericPoint X ∈ U)
    (h : (⊤ : (Spec (X.residueField (genericPoint X))).Opens) ≤
      (X.fromSpecResidueField (genericPoint X)) ⁻¹ᵁ U) (r : Γ(X, U)) :
    X.functionFieldIsoResidueField.inv.hom
        ((ΓSpecIso (X.residueField (genericPoint X))).hom.hom
          ((X.fromSpecResidueField (genericPoint X)).appLE U ⊤ h r)) =
      X.presheaf.germ U (genericPoint X) hU r := by
  rw [ΓSpecIso_hom_fromSpecResidueField_appLE X (genericPoint X) hU h r]
  have key := congrArg (fun k : X.functionField ⟶ X.functionField =>
    k (X.presheaf.germ U (genericPoint X) hU r)) (asIso (X.residue (genericPoint X))).hom_inv_id
  exact (CommRingCat.comp_apply _ _ _).symm.trans (key.trans (CommRingCat.id_apply _ _))

end AlgebraicGeometry.Scheme

end
