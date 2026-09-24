import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModuleTensorAssociator
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModuleTensorSymmetry
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModuleTensorUnit
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModuleDualTensorEvaluation
import MiyaokaMori.AlgebraicGeometry.Modules.ExteriorPower.ExteriorPowerSheafMul
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.ModuleDualSectionEquiv

/-!
# Tensor-power pairings and coefficient contraction

A genuine pairing of arbitrary module sheaves extends recursively to their
equal tensor powers. Degree zero uses multiplication on the structure module.
The successor step reorders the four original tensor factors and applies the
given pairing and the preceding power pairing. An additional target factor is
preserved by the original associator and the right unit isomorphism. Specializing
to the actual dual evaluation contracts the original coefficient module with
the corresponding positive tensor power.

Every construction is a sheaf morphism defined on all sections. The power
formulas describe the specified tensor-power sections; they do not assume that
arbitrary tensor-sheaf sections are globally pure or that a pairing is perfect.

Sources: the coefficient expansion (4.1) in Lemma 4.1
of the paper; Stacks Project, `modules.tex`, `section-tensor-product` and `section-internal-hom`.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.Scheme.Modules.ModuleDualPowerContraction

set_option backward.isDefEq.respectTransparency false

variable {X : Scheme.{u}}

/- `Scheme.Modules` / `Scheme.ringCatSheaf` are plain (non-reducible) `def`s, so type class search
cannot see through them and the ring structure on `Γ(SheafOfModules.unit X.ringCatSheaf, U)` is not
found (`1` has no `OfNat`). It is transported by hand here. The name carries the file as a prefix:
`local instance` only makes the **attribute** local, the name is still global. -/
local instance dualPowerContractionUnitSectionCommRing (U : X.Opens) :
    CommRing ↑(Γ(SheafOfModules.unit X.ringCatSheaf, U)) :=
  inferInstanceAs (CommRing ↑(X.presheaf.obj (op U)))

/- The tensor of two module-sheaf morphisms is `AlgebraicGeometry.Scheme.Modules.tensorMap`
(`ExteriorPowerSheafMul`: the sheafification of the presheaf `tensorHom`); `Scheme.Modules.tensor` is
`moduleTensor` by definition. The section formula is stated here as a theorem about it. -/

/-- The tensor of two morphisms acts on the two specified original tensor factors. -/
theorem tensorMap_section {P P' Q Q' : X.Modules} (f : P ⟶ P') (g : Q ⟶ Q')
    {U : X.Opens} (p : Γ(P, U)) (q : Γ(Q, U)) :
    (Scheme.Modules.tensorMap f g).app U (moduleTensorSection p q) =
      moduleTensorSection (f.app U p) (g.app U q) := by
  exact moduleSheafificationUnit_naturality X
    (PresheafOfModules.Monoidal.tensorHom (R := X.presheaf) f.val g.val) U
    (p ⊗ₜ[Γ(X, U)] q)

/-- Exchange the middle factors of four original tensor-module factors. -/
def interchange (A B C D : X.Modules) :
    moduleTensor (moduleTensor A B) (moduleTensor C D) ⟶
      moduleTensor (moduleTensor A C) (moduleTensor B D) :=
  (moduleTensorAssociator A B (moduleTensor C D)).hom ≫
    Scheme.Modules.tensorMap (𝟙 A)
      ((moduleTensorAssociator B C D).inv ≫
        Scheme.Modules.tensorMap (moduleTensorSymmetry B C).hom (𝟙 D) ≫
        (moduleTensorAssociator C B D).hom) ≫
    (moduleTensorAssociator A C (moduleTensor B D)).inv

/-- Middle-factor exchange retains each of the four specified sections. -/
theorem interchange_section {A B C D : X.Modules} {U : X.Opens}
    (a : Γ(A, U)) (b : Γ(B, U)) (c : Γ(C, U)) (d : Γ(D, U)) :
    (interchange A B C D).app U
        (moduleTensorSection (moduleTensorSection a b) (moduleTensorSection c d)) =
      moduleTensorSection (moduleTensorSection a c) (moduleTensorSection b d) := by
  -- The primary `Scheme.Modules.tensorMap` is typed with the wrapper `Scheme.Modules.tensor`
  -- (`= moduleTensor` by definition); `simp` does not see through it, so the goal is restated
  -- with `change` before each use of `tensorMap_section` (as in the proofs below).
  change (moduleTensorAssociator A C (moduleTensor B D)).inv.app U
      ((Scheme.Modules.tensorMap (𝟙 A)
        ((moduleTensorAssociator B C D).inv ≫
          Scheme.Modules.tensorMap (moduleTensorSymmetry B C).hom (𝟙 D) ≫
          (moduleTensorAssociator C B D).hom)).app U
        ((moduleTensorAssociator A B (moduleTensor C D)).hom.app U
          (moduleTensorSection (moduleTensorSection a b) (moduleTensorSection c d)))) = _
  rw [moduleTensorAssociator_hom_section, tensorMap_section]
  change (moduleTensorAssociator A C (moduleTensor B D)).inv.app U
      (moduleTensorSection a
        ((moduleTensorAssociator C B D).hom.app U
          ((Scheme.Modules.tensorMap (moduleTensorSymmetry B C).hom (𝟙 D)).app U
            ((moduleTensorAssociator B C D).inv.app U
              (moduleTensorSection b (moduleTensorSection c d)))))) = _
  rw [moduleTensorAssociator_inv_section, tensorMap_section, moduleTensorSymmetry_section]
  change (moduleTensorAssociator A C (moduleTensor B D)).inv.app U
      (moduleTensorSection a ((moduleTensorAssociator C B D).hom.app U
        (moduleTensorSection (moduleTensorSection c b) d))) = _
  rw [moduleTensorAssociator_hom_section, moduleTensorAssociator_inv_section]

/-- Extend an arbitrary genuine pairing to equal natural tensor powers, including zero. -/
def powerPairing {P Q : X.Modules}
    (β : moduleTensor P Q ⟶ SheafOfModules.unit X.ringCatSheaf) :
    (q : ℕ) → moduleTensor (moduleTensorPower P q) (moduleTensorPower Q q) ⟶
      SheafOfModules.unit X.ringCatSheaf
  | 0 => (moduleTensorLeftUnitIso (SheafOfModules.unit X.ringCatSheaf)).hom
  | q + 1 =>
    interchange P (moduleTensorPower P q) Q (moduleTensorPower Q q) ≫
      Scheme.Modules.tensorMap β (powerPairing β q) ≫
      (moduleTensorLeftUnitIso (SheafOfModules.unit X.ringCatSheaf)).hom

/-- Degree zero is the original multiplication of the structure module with itself. -/
theorem powerPairing_zero {P Q : X.Modules}
    (β : moduleTensor P Q ⟶ SheafOfModules.unit X.ringCatSheaf) :
    powerPairing β 0 =
      (moduleTensorLeftUnitIso (SheafOfModules.unit X.ringCatSheaf)).hom := rfl

/-- The pairing of repeated specified sections is the corresponding power of their pairing. -/
theorem powerPairing_section {P Q : X.Modules}
    (β : moduleTensor P Q ⟶ SheafOfModules.unit X.ringCatSheaf)
    {U : X.Opens} (p : Γ(P, U)) (t : Γ(Q, U)) (q : ℕ) :
    (powerPairing β q).app U
        (moduleTensorSection (moduleTensorPowerSection p q) (moduleTensorPowerSection t q)) =
      (show Γ(X, U) from β.app U (moduleTensorSection p t)) ^ q := by
  induction q with
  | zero =>
    change (moduleTensorLeftUnitIso (SheafOfModules.unit X.ringCatSheaf)).hom.app U
      (moduleTensorSection (M := SheafOfModules.unit X.ringCatSheaf)
        (N := SheafOfModules.unit X.ringCatSheaf) 1 1) = _
    rw [moduleTensorLeftUnitIso_hom_section]
    simp only [one_smul, pow_zero]
  | succ q ih =>
    change (moduleTensorLeftUnitIso (SheafOfModules.unit X.ringCatSheaf)).hom.app U
      ((Scheme.Modules.tensorMap β (powerPairing β q)).app U
        ((interchange P (moduleTensorPower P q) Q (moduleTensorPower Q q)).app U
          (moduleTensorSection
            (moduleTensorSection p (moduleTensorPowerSection p q))
            (moduleTensorSection t (moduleTensorPowerSection t q))))) = _
    rw [interchange_section, tensorMap_section, moduleTensorLeftUnitIso_hom_section, ih]
    change (show Γ(X, U) from β.app U (moduleTensorSection p t)) *
        (show Γ(X, U) from β.app U (moduleTensorSection p t)) ^ q = _
    exact (pow_succ' _ q).symm

/-- Restriction commutes with the power pairing on every input section. -/
theorem powerPairing_restrict {P Q : X.Modules}
    (β : moduleTensor P Q ⟶ SheafOfModules.unit X.ringCatSheaf) (q : ℕ)
    {U V : X.Opens} (i : V ⟶ U)
    (z : Γ(moduleTensor (moduleTensorPower P q) (moduleTensorPower Q q), U)) :
    (Scheme.Modules.presheaf (X := X) (SheafOfModules.unit X.ringCatSheaf)).map i.op ((powerPairing β q).app U z) =
      (powerPairing β q).app V
        ((moduleTensor (moduleTensorPower P q) (moduleTensorPower Q q)).presheaf.map i.op z) :=
  (PresheafOfModules.naturality_apply (powerPairing β q).val i.op z).symm

/-- Contract paired powers while retaining an arbitrary original target-module factor. -/
def coefficientPairing (B : X.Modules) {P Q : X.Modules}
    (β : moduleTensor P Q ⟶ SheafOfModules.unit X.ringCatSheaf) (q : ℕ) :
    moduleTensor (moduleTensor B (moduleTensorPower P q)) (moduleTensorPower Q q) ⟶ B :=
  (moduleTensorAssociator B (moduleTensorPower P q) (moduleTensorPower Q q)).hom ≫
    Scheme.Modules.tensorMap (𝟙 B) (powerPairing β q) ≫
    (moduleTensorRightUnitIso B).hom

/-- Coefficient contraction multiplies the specified target section by the pairing power. -/
theorem coefficientPairing_section (B : X.Modules) {P Q : X.Modules}
    (β : moduleTensor P Q ⟶ SheafOfModules.unit X.ringCatSheaf)
    {U : X.Opens} (b : Γ(B, U)) (p : Γ(P, U)) (t : Γ(Q, U)) (q : ℕ) :
    (coefficientPairing B β q).app U
        (moduleTensorSection (moduleTensorSection b (moduleTensorPowerSection p q))
          (moduleTensorPowerSection t q)) =
      (show Γ(X, U) from β.app U (moduleTensorSection p t)) ^ q • b := by
  change (moduleTensorRightUnitIso B).hom.app U
    ((Scheme.Modules.tensorMap (𝟙 B) (powerPairing β q)).app U
      ((moduleTensorAssociator B (moduleTensorPower P q) (moduleTensorPower Q q)).hom.app U
        (moduleTensorSection (moduleTensorSection b (moduleTensorPowerSection p q))
          (moduleTensorPowerSection t q)))) = _
  rw [moduleTensorAssociator_hom_section, tensorMap_section,
    moduleTensorRightUnitIso_hom_section, powerPairing_section]
  rfl

/-- Coefficient contraction commutes with restriction on arbitrary input sections. -/
theorem coefficientPairing_restrict (B : X.Modules) {P Q : X.Modules}
    (β : moduleTensor P Q ⟶ SheafOfModules.unit X.ringCatSheaf) (q : ℕ)
    {U V : X.Opens} (i : V ⟶ U)
    (z : Γ(moduleTensor (moduleTensor B (moduleTensorPower P q))
      (moduleTensorPower Q q), U)) :
    B.presheaf.map i.op ((coefficientPairing B β q).app U z) =
      (coefficientPairing B β q).app V
        ((moduleTensor (moduleTensor B (moduleTensorPower P q))
          (moduleTensorPower Q q)).presheaf.map i.op z) :=
  (PresheafOfModules.naturality_apply (coefficientPairing B β q).val i.op z).symm

/-- Pair the original negative and positive powers by the genuine canonical dual evaluation. -/
def dualPowerPairing (L : X.Modules) (q : ℕ) :
    moduleTensor (moduleNegativePower L q) (moduleTensorPower L q) ⟶
      SheafOfModules.unit X.ringCatSheaf :=
  powerPairing (ModuleDualTensorEvaluation.evaluation L) q

/-- In degree zero the dual-power pairing is the original structure-module multiplication. -/
theorem dualPowerPairing_zero (L : X.Modules) :
    dualPowerPairing L 0 =
      (moduleTensorLeftUnitIso (SheafOfModules.unit X.ringCatSheaf)).hom := rfl

/-- Specified dual and original powers pair by the power of the original local functional. -/
theorem dualPowerPairing_section (L : X.Modules) {U : X.Opens}
    (φ : Γ(moduleSheafDual L, U)) (s : Γ(L, U)) (q : ℕ) :
    (dualPowerPairing L q).app U
        (moduleTensorSection (moduleTensorPowerSection φ q) (moduleTensorPowerSection s q)) =
      (((MiyaokaMori.ModuleDualSectionEquiv.sectionEquiv L U).symm φ).val (Over.mk (𝟙 U)) s) ^ q := by
  change (powerPairing (ModuleDualTensorEvaluation.evaluation L) q).app U
      (moduleTensorSection (moduleTensorPowerSection φ q) (moduleTensorPowerSection s q)) = _
  rw [powerPairing_section, ModuleDualTensorEvaluation.evaluation_section]

/-- The dual-power pairing respects restriction of every section of the original tensor sheaf. -/
theorem dualPowerPairing_restrict (L : X.Modules) (q : ℕ) {U V : X.Opens} (i : V ⟶ U)
    (z : Γ(moduleTensor (moduleNegativePower L q) (moduleTensorPower L q), U)) :
    (Scheme.Modules.presheaf (X := X) (SheafOfModules.unit X.ringCatSheaf)).map i.op ((dualPowerPairing L q).app U z) =
      (dualPowerPairing L q).app V
        ((moduleTensor (moduleNegativePower L q) (moduleTensorPower L q)).presheaf.map i.op z) :=
  powerPairing_restrict (ModuleDualTensorEvaluation.evaluation L) q i z

/-- Contract the original coefficient module and positive power back into its target module. -/
def coefficientContraction (B L : X.Modules) (q : ℕ) :
    moduleTensor (coefficientLineModule B L q) (moduleTensorPower L q) ⟶ B :=
  coefficientPairing B (ModuleDualTensorEvaluation.evaluation L) q

/-- Each specified coefficient and positive-power section has the original evaluation power. -/
theorem coefficientContraction_section (B L : X.Modules) {U : X.Opens}
    (b : Γ(B, U)) (φ : Γ(moduleSheafDual L, U)) (s : Γ(L, U)) (q : ℕ) :
    (coefficientContraction B L q).app U
        (moduleTensorSection (coefficientLineSection b φ q) (moduleTensorPowerSection s q)) =
      (show Γ(X, U) from ((MiyaokaMori.ModuleDualSectionEquiv.sectionEquiv L U).symm φ).val
        (Over.mk (𝟙 U)) s) ^ q • b := by
  change (coefficientPairing B (ModuleDualTensorEvaluation.evaluation L) q).app U
      (moduleTensorSection (moduleTensorSection b (moduleTensorPowerSection φ q))
        (moduleTensorPowerSection s q)) = _
  rw [coefficientPairing_section, ModuleDualTensorEvaluation.evaluation_section]

/-- Degree-zero contraction multiplies the two arbitrary scalar factors on the target section. -/
theorem coefficientContraction_zero_section (B L : X.Modules) {U : X.Opens}
    (b : Γ(B, U)) (a c : Γ(X, U)) :
    (coefficientContraction B L 0).app U
        (moduleTensorSection
          (moduleTensorSection (N := SheafOfModules.unit X.ringCatSheaf) b a)
          (show Γ(SheafOfModules.unit X.ringCatSheaf, U) from c)) =
      (a * c) • b := by
  change (moduleTensorRightUnitIso B).hom.app U
    ((Scheme.Modules.tensorMap (𝟙 B)
      (moduleTensorLeftUnitIso (SheafOfModules.unit X.ringCatSheaf)).hom).app U
      ((moduleTensorAssociator B (SheafOfModules.unit X.ringCatSheaf)
        (SheafOfModules.unit X.ringCatSheaf)).hom.app U
        (moduleTensorSection (moduleTensorSection b a) c))) = _
  rw [moduleTensorAssociator_hom_section, tensorMap_section,
    moduleTensorLeftUnitIso_hom_section, moduleTensorRightUnitIso_hom_section]
  rfl

/-- Coefficient contraction commutes with restriction for every input section. -/
theorem coefficientContraction_restrict (B L : X.Modules) (q : ℕ)
    {U V : X.Opens} (i : V ⟶ U)
    (z : Γ(moduleTensor (coefficientLineModule B L q) (moduleTensorPower L q), U)) :
    B.presheaf.map i.op ((coefficientContraction B L q).app U z) =
      (coefficientContraction B L q).app V
        ((moduleTensor (coefficientLineModule B L q) (moduleTensorPower L q)).presheaf.map
          i.op z) :=
  coefficientPairing_restrict B (ModuleDualTensorEvaluation.evaluation L) q i z

end AlgebraicGeometry.Scheme.Modules.ModuleDualPowerContraction
