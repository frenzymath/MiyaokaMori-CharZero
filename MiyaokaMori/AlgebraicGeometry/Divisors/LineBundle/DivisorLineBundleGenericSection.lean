import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Divisors.LineBundle.DivisorLineBundleFrame
import MiyaokaMori.AlgebraicGeometry.Divisors.Meromorphic.RationalSectionToFunctionField

/-! # The generic section `1` of `O_X(D)`

Let `t ∈ 𝒦^*(U)` and `t' ∈ 𝒦^*(U')` be two local equations of the Cartier divisor `D` (`U`, `U'`
nonempty) and `f, f' ∈ K(X)^×` their values at the generic point. Then in the generic stalk of `O_X(D)`,
`f • (t^{-1})_η = f' • (t'^{-1})_η`; this common element is the "rational section `1`".

Proof:
1. On `W = U ∩ U'`, `t^{-1} = c • t'^{-1}` with `c ∈ O_X(W)` (surjectivity of the frame,
   `DivisorLineBundleFrame`).
2. Taking values at the generic point gives `c_η·f'^{-1} = f^{-1}`, i.e. `f·c_η = f'` (the evaluation
   map is compatible with `O_X → 𝒦_X` and with restriction).
3. Then use the compatibility of germs with scalar multiplication and restriction
   (`PresheafOfModules.germ_smul`, `germ_res_apply`).
Source: Hartshorne II.6.13.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace CartierDivisor

variable {k : Type u} [Field k] {X : Variety k}

/-- On the image of `O_X(W)`, the map `𝒦(W) → K(X)` is the germ at the generic point (elementwise form). -/
theorem rationalSectionToFunctionField_toRat (W : X.toScheme.Opens) [Nonempty W]
    (c : Γ(X.toScheme, W)) :
    (X.toScheme.rationalSectionToFunctionField W).hom
        ((X.toScheme.toRationalFunctionsSheaf.hom.app (op W)).hom c) =
      (X.toScheme.germToFunctionField W).hom c :=
  congrArg (fun φ => φ.hom c) (X.toScheme.toRationalFunctionsSheaf_rationalSectionToFunctionField W)

/-- `𝒦(U) → K(X)` is compatible with restriction (elementwise form). -/
theorem rationalSectionToFunctionField_res_apply {U W : X.toScheme.Opens} [Nonempty U] [Nonempty W]
    (hWU : W ≤ U) (q : X.toScheme.rationalFunctionsSheaf.val.obj (op U)) :
    (X.toScheme.rationalSectionToFunctionField W).hom
        ((X.toScheme.rationalFunctionsSheaf.val.map (homOfLE hWU).op).hom q) =
      (X.toScheme.rationalSectionToFunctionField U).hom q :=
  congrArg (fun φ => φ.hom q) (X.toScheme.rationalSectionToFunctionField_res U W hWU)

/-- The value of `t^{-1}` at the generic point is `f^{-1}`. -/
theorem rationalSectionToFunctionField_unitVal_inv {U : X.toScheme.Opens} [Nonempty U]
    (t : X.toScheme.rationalFunctionsUnitsSheaf.val.obj (op U)) :
    (X.toScheme.rationalSectionToFunctionField U).hom (unitVal t⁻¹) =
      ((X.toScheme.rationalUnitsSectionToFunctionField U t : (X.toScheme.functionField)ˣ) :
        X.toScheme.functionField)⁻¹ := by
  have h := congrArg Units.val (map_inv (X.toScheme.rationalUnitsSectionToFunctionField U) t)
  rw [Units.val_inv_eq_inv_val] at h
  exact h

variable {D : CartierDivisor X} {U U' : X.toScheme.Opens}
  {t : X.toScheme.rationalFunctionsUnitsSheaf.val.obj (op U)}
  {t' : X.toScheme.rationalFunctionsUnitsSheaf.val.obj (op U')}

/-- Transition: on a common open `W`, `t^{-1} = c • t'^{-1}` with `f·c_η = f'` (`f`, `f'` the values of
`t`, `t'` at the generic point). -/
theorem IsLocalEquation.exists_transition (ht : IsLocalEquation D U t)
    (ht' : IsLocalEquation D U' t') [Nonempty U] [Nonempty U'] {W : X.toScheme.Opens}
    [Nonempty W] (hWU : W ≤ U) (hWU' : W ≤ U') :
    ∃ c : Γ(X.toScheme, W),
      (CartierDivisor.lineBundleModules D).res hWU ht.frame =
        c • (CartierDivisor.lineBundleModules D).res hWU' ht'.frame ∧
      ((X.toScheme.rationalUnitsSectionToFunctionField U t : (X.toScheme.functionField)ˣ) :
          X.toScheme.functionField) * (X.toScheme.germToFunctionField W).hom c =
        ((X.toScheme.rationalUnitsSectionToFunctionField U' t' : (X.toScheme.functionField)ˣ) :
          X.toScheme.functionField) := by
  obtain ⟨c, hc⟩ := (ht'.bijective_smul_invSection hWU').2 (ht.invSection hWU)
  refine ⟨c, ?_, ?_⟩
  · rw [ht.res_frame hWU, ht'.res_frame hWU']
    exact (congrArg (CartierDivisor.lineBundleSectionEquiv D W) hc).symm.trans
      ((CartierDivisor.lineBundleSectionEquiv D W).map_smul c _)
  · have hval := congrArg (fun z : CartierDivisor.lineBundleSections D W =>
      (X.toScheme.rationalSectionToFunctionField W).hom z.1) hc
    change (X.toScheme.rationalSectionToFunctionField W).hom
        ((X.toScheme.toRationalFunctionsSheaf.hom.app (op W)).hom c *
          (X.toScheme.rationalFunctionsSheaf.val.map (homOfLE hWU').op).hom (unitVal t'⁻¹)) =
      (X.toScheme.rationalSectionToFunctionField W).hom
        ((X.toScheme.rationalFunctionsSheaf.val.map (homOfLE hWU).op).hom (unitVal t⁻¹)) at hval
    rw [map_mul, rationalSectionToFunctionField_toRat, rationalSectionToFunctionField_res_apply,
      rationalSectionToFunctionField_res_apply, rationalSectionToFunctionField_unitVal_inv,
      rationalSectionToFunctionField_unitVal_inv] at hval
    set f : X.toScheme.functionField :=
      ((X.toScheme.rationalUnitsSectionToFunctionField U t : (X.toScheme.functionField)ˣ) :
        X.toScheme.functionField) with hf
    set f' : X.toScheme.functionField :=
      ((X.toScheme.rationalUnitsSectionToFunctionField U' t' : (X.toScheme.functionField)ˣ) :
        X.toScheme.functionField) with hf'
    have hfne : f ≠ 0 := Units.ne_zero _
    have hf'ne : f' ≠ 0 := Units.ne_zero _
    field_simp at hval
    rw [mul_comm]; exact hval

/-- Two local equations give the same element `f • (t^{-1})_η` of the generic stalk. -/
theorem IsLocalEquation.smul_germ_frame_eq (ht : IsLocalEquation D U t)
    (ht' : IsLocalEquation D U' t') [Nonempty U] [Nonempty U']
    (hη : genericPoint X.toScheme ∈ U) (hη' : genericPoint X.toScheme ∈ U') :
    (((X.toScheme.rationalUnitsSectionToFunctionField U t : (X.toScheme.functionField)ˣ) :
        X.toScheme.functionField) : X.toScheme.presheaf.stalk (genericPoint X.toScheme)) •
      (CartierDivisor.lineBundleModules D).presheaf.germ U (genericPoint X.toScheme) hη ht.frame =
    (((X.toScheme.rationalUnitsSectionToFunctionField U' t' : (X.toScheme.functionField)ˣ) :
        X.toScheme.functionField) : X.toScheme.presheaf.stalk (genericPoint X.toScheme)) •
      (CartierDivisor.lineBundleModules D).presheaf.germ U' (genericPoint X.toScheme) hη'
        ht'.frame := by
  let M := CartierDivisor.lineBundleModules D
  let η := genericPoint X.toScheme
  let W : X.toScheme.Opens := U ⊓ U'
  have hηW : η ∈ W := ⟨hη, hη'⟩
  have : Nonempty W := ⟨⟨η, hηW⟩⟩
  have hWU : W ≤ U := inf_le_left
  have hWU' : W ≤ U' := inf_le_right
  obtain ⟨c, hfr, hcf⟩ := ht.exists_transition ht' hWU hWU'
  have g1 : M.presheaf.germ U η hη ht.frame = M.presheaf.germ W η hηW (M.res hWU ht.frame) :=
    (M.presheaf.germ_res_apply (homOfLE hWU) η hηW ht.frame).symm
  have g2 : M.presheaf.germ U' η hη' ht'.frame =
      M.presheaf.germ W η hηW (M.res hWU' ht'.frame) :=
    (M.presheaf.germ_res_apply (homOfLE hWU') η hηW ht'.frame).symm
  have g3 : M.presheaf.germ W η hηW (c • M.res hWU' ht'.frame) =
      X.toScheme.presheaf.germ W η hηW c • M.presheaf.germ W η hηW (M.res hWU' ht'.frame) :=
    PresheafOfModules.germ_smul (R := X.toScheme.presheaf) M.val η W hηW c _
  rw [g1, hfr, g3, ← g2, smul_smul]
  exact congrArg (fun z : X.toScheme.presheaf.stalk η =>
    z • M.presheaf.germ U' η hη' ht'.frame) hcf

end CartierDivisor

end
