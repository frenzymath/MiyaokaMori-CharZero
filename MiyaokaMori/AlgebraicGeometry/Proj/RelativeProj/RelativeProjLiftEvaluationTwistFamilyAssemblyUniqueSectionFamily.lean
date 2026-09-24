import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjLiftEvaluationTwistFamilyAssembly

/-! # Assembly, part 3a: the absolute section family attached to a relative twist family

A relative twist family `ψ` (on `V₁ ⊇ V`) over a generalized piece `V` yields maps `toSectionFamily`,
`c_n(z) := Λ_n(ψ_n(Θ_n⁻¹ z))`, which are additive, linear and compatible with restriction (this file). The remaining
axioms (F'), (M') and the uniqueness theorem are in `RelativeProjLiftEvaluationTwistFamilyAssemblyUnique2.lean`
(split for compile time). See `RelativeProjLiftEvaluationTwistFamily.lean`. -/

set_option autoImplicit false
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open scoped CategoryTheory.MonoidalCategory

namespace AlgebraicGeometry.Scheme.relativeProj

variable {X T : AlgebraicGeometry.Scheme.{u}}

namespace LiftData

variable {S : X.GradedQCAlgebra} {f : T ⟶ X} {M : T.Modules} [M.IsLineBundle]
  (D : AlgebraicGeometry.Scheme.relativeProj.LiftData S f M)

attribute [local instance] AlgebraicGeometry.Scheme.relativeProj.isIso_powTriv



/-- Additivity of `sectionMapOfRestrictHom φ (ι ''ᵁ B')` with the sum taken in `Γ(M|_ι, B')` (the spelling produced by
`hom_app_add` for a morphism into `M|_ι`). -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.sectionMapOfRestrictHom_add_tfa {M N : X.Modules} {W : X.Opens}
    (φ : M.restrict W.ι ⟶ N.restrict W.ι) {Y : AlgebraicGeometry.Scheme.{u}} (ι : Y ⟶ X)
    [AlgebraicGeometry.IsOpenImmersion ι] (B' : Y.Opens) (hV : ι ''ᵁ B' ≤ W) (x y : Γ(M.restrict ι, B')) :
    AlgebraicGeometry.Scheme.Modules.sectionMapOfRestrictHom φ (ι ''ᵁ B') hV (x + y) =
      AlgebraicGeometry.Scheme.Modules.sectionMapOfRestrictHom φ (ι ''ᵁ B') hV x +
        AlgebraicGeometry.Scheme.Modules.sectionMapOfRestrictHom φ (ι ''ᵁ B') hV y :=
  (AlgebraicGeometry.Scheme.Modules.sectionMapOfRestrictHom φ (ι ''ᵁ B') hV).hom.map_add x y

/-- Restriction in `M|_ι`, spelled with the ambient opens. -/
theorem _root_.AlgebraicGeometry.Scheme.Modules.restrict_presheaf_map_eq_tfa (M : X.Modules)
    {Y : AlgebraicGeometry.Scheme.{u}} (ι : Y ⟶ X) [AlgebraicGeometry.IsOpenImmersion ι] {B B'' : Y.Opens}
    (h : B'' ≤ B) (hB : ι ''ᵁ B'' ≤ ι ''ᵁ B) (y : Γ(M.restrict ι, B)) :
    (M.restrict ι).presheaf.map (homOfLE h).op y = M.presheaf.map (homOfLE hB).op y := by
  rw [AlgebraicGeometry.Scheme.Modules.restrict_map]
  have e : ι.opensFunctor.map (homOfLE h) = homOfLE hB := Subsingleton.elim _ _
  rw [e]
  rfl

/-! ## From a relative twist family on an open of a piece to an absolute section family -/

section Uniqueness

variable (U : T.Opens) (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) (W : X.affineOpens)
  {V : T.Opens} (hle : V ≤ U ⊓ f ⁻¹ᵁ W.1)
  (hΦ : (HomogeneousIdeal.irrelevant (S.sectionsGrading W.1)).toIdeal.map
    (AlgebraicGeometry.Scheme.relativeProj.pieceRingHom S f M D U e W hle) = ⊤)
  (hτ : V.ι ≫ AlgebraicGeometry.Scheme.relativeProj.lift S f M D =
    AlgebraicGeometry.Proj.fromOfGlobalSections (S.sectionsGrading W.1)
        (AlgebraicGeometry.Scheme.relativeProj.pieceRingHom S f M D U e W hle) hΦ ≫
      AlgebraicGeometry.Scheme.relativeProj.chartEmbedding S W)

/-- `V.ι ''ᵁ B' ≤ V`. -/
theorem image_le_self (B' : V.toScheme.Opens) : V.ι ''ᵁ B' ≤ V := by
  conv_rhs => rw [← AlgebraicGeometry.Scheme.Opens.opensRange_ι V]
  exact AlgebraicGeometry.Scheme.Hom.image_le_opensRange _ _

/-- The absolute section family `c_n(z) := Λ_n(ψ_n(Θ_n⁻¹ z))` attached to a relative twist family `ψ` (living on
`V₁ ⊇ V`) over the generalized piece `V`. -/
def toSectionFamily {V₁ : T.Opens}
    (ψ : ∀ n : ℕ,
      ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj.lift S f M D)).obj
          (AlgebraicGeometry.Scheme.relativeProj.twist S (n : ℤ))).restrict V₁.ι ⟶
        (AlgebraicGeometry.Scheme.Modules.monoidalPow M n).restrict V₁.ι)
    (h₁ : V ≤ V₁) (n : ℕ) (B' : V.toScheme.Opens)
    (z : Γ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Proj.fromOfGlobalSections (S.sectionsGrading W.1)
        (AlgebraicGeometry.Scheme.relativeProj.pieceRingHom S f M D U e W hle) hΦ)).obj
      (AlgebraicGeometry.Proj.twist (S.sectionsGrading W.1) (n : ℤ)), B')) : Γ(V.toScheme, B') :=
  AlgebraicGeometry.Scheme.Modules.unitSectionsToRing V.toScheme B'
    ((AlgebraicGeometry.Scheme.relativeProj.powTriv f M U e W hle n).app B'
      (AlgebraicGeometry.Scheme.Modules.sectionMapOfRestrictHom (ψ n) (V.ι ''ᵁ B')
        ((AlgebraicGeometry.Scheme.relativeProj.LiftData.image_le_self B').trans h₁)
        ((D.twistTransport U e W hle hΦ hτ n).inv.app B' z)))

/-- Additivity of `toSectionFamily`. -/
theorem toSectionFamily_add {V₁ : T.Opens} (ψ : ∀ n : ℕ,
      ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj.lift S f M D)).obj
          (AlgebraicGeometry.Scheme.relativeProj.twist S (n : ℤ))).restrict V₁.ι ⟶
        (AlgebraicGeometry.Scheme.Modules.monoidalPow M n).restrict V₁.ι)
    (h₁ : V ≤ V₁) (H : D.IsTwistFamilyOnAux V₁ ψ V h₁) (n : ℕ) (B' : V.toScheme.Opens)
    (z w : Γ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Proj.fromOfGlobalSections (S.sectionsGrading W.1)
        (AlgebraicGeometry.Scheme.relativeProj.pieceRingHom S f M D U e W hle) hΦ)).obj
      (AlgebraicGeometry.Proj.twist (S.sectionsGrading W.1) (n : ℤ)), B')) :
    D.toSectionFamily U e W hle hΦ hτ ψ h₁ n B' (z + w) =
      D.toSectionFamily U e W hle hΦ hτ ψ h₁ n B' z + D.toSectionFamily U e W hle hΦ hτ ψ h₁ n B' w := by
  unfold AlgebraicGeometry.Scheme.relativeProj.LiftData.toSectionFamily
  rw [AlgebraicGeometry.Scheme.Modules.hom_app_add (D.twistTransport U e W hle hΦ hτ n).inv B' z w,
    AlgebraicGeometry.Scheme.Modules.sectionMapOfRestrictHom_add_tfa (ψ n) V.ι B',
    AlgebraicGeometry.Scheme.Modules.restrict_hom_app_add V.ι (AlgebraicGeometry.Scheme.relativeProj.powTriv f M U e W hle n) B',
    AlgebraicGeometry.Scheme.Modules.unitSectionsToRing_add]

/-- Linearity of `toSectionFamily`. -/
theorem toSectionFamily_smul {V₁ : T.Opens} (ψ : ∀ n : ℕ,
      ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj.lift S f M D)).obj
          (AlgebraicGeometry.Scheme.relativeProj.twist S (n : ℤ))).restrict V₁.ι ⟶
        (AlgebraicGeometry.Scheme.Modules.monoidalPow M n).restrict V₁.ι)
    (h₁ : V ≤ V₁) (H : D.IsTwistFamilyOnAux V₁ ψ V h₁) (n : ℕ) (B' : V.toScheme.Opens) (r : Γ(V.toScheme, B'))
    (z : Γ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Proj.fromOfGlobalSections (S.sectionsGrading W.1)
        (AlgebraicGeometry.Scheme.relativeProj.pieceRingHom S f M D U e W hle) hΦ)).obj
      (AlgebraicGeometry.Proj.twist (S.sectionsGrading W.1) (n : ℤ)), B')) :
    D.toSectionFamily U e W hle hΦ hτ ψ h₁ n B' (r • z) = r * D.toSectionFamily U e W hle hΦ hτ ψ h₁ n B' z := by
  unfold AlgebraicGeometry.Scheme.relativeProj.LiftData.toSectionFamily
  have hB := (AlgebraicGeometry.Scheme.relativeProj.LiftData.image_le_self (V := V) B').trans h₁
  rw [AlgebraicGeometry.Scheme.Modules.Hom.app_smul (D.twistTransport U e W hle hΦ hτ n).inv r z]
  have e1 := AlgebraicGeometry.Scheme.Modules.restrict_smul_eq V.ι ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj.lift S f M D)).obj
      (AlgebraicGeometry.Scheme.relativeProj.twist S (n : ℤ))) B' ((V.ι.appIso B').inv r) ((D.twistTransport U e W hle hΦ hτ n).inv.app B' z)
  rw [CommRingCat.iso_hom_inv_apply] at e1
  rw [← e1, AlgebraicGeometry.Scheme.Modules.sectionMapOfRestrictHom_smul (ψ n) (V.ι ''ᵁ B') hB,
    AlgebraicGeometry.Scheme.Modules.restrict_hom_app_smul_appIso V.ι (AlgebraicGeometry.Scheme.relativeProj.powTriv f M U e W hle n), CommRingCat.iso_hom_inv_apply,
    AlgebraicGeometry.Scheme.Modules.unitSectionsToRing_smul]

/-- `toSectionFamily` commutes with restriction. -/
theorem toSectionFamily_res {V₁ : T.Opens} (ψ : ∀ n : ℕ,
      ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj.lift S f M D)).obj
          (AlgebraicGeometry.Scheme.relativeProj.twist S (n : ℤ))).restrict V₁.ι ⟶
        (AlgebraicGeometry.Scheme.Modules.monoidalPow M n).restrict V₁.ι)
    (h₁ : V ≤ V₁) (H : D.IsTwistFamilyOnAux V₁ ψ V h₁) (n : ℕ) {B B'' : V.toScheme.Opens} (h : B'' ≤ B)
    (z : Γ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Proj.fromOfGlobalSections (S.sectionsGrading W.1)
        (AlgebraicGeometry.Scheme.relativeProj.pieceRingHom S f M D U e W hle) hΦ)).obj
      (AlgebraicGeometry.Proj.twist (S.sectionsGrading W.1) (n : ℤ)), B)) :
    D.toSectionFamily U e W hle hΦ hτ ψ h₁ n B''
        (((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Proj.fromOfGlobalSections (S.sectionsGrading W.1)
        (AlgebraicGeometry.Scheme.relativeProj.pieceRingHom S f M D U e W hle) hΦ)).obj
          (AlgebraicGeometry.Proj.twist (S.sectionsGrading W.1) (n : ℤ))).presheaf.map (homOfLE h).op z) =
      V.toScheme.presheaf.map (homOfLE h).op (D.toSectionFamily U e W hle hΦ hτ ψ h₁ n B z) := by
  unfold AlgebraicGeometry.Scheme.relativeProj.LiftData.toSectionFamily
  have hB' : V.ι ''ᵁ B'' ≤ V.ι ''ᵁ B := (V.ι.opensFunctor.map (homOfLE h)).le
  have hB := (AlgebraicGeometry.Scheme.relativeProj.LiftData.image_le_self (V := V) B).trans h₁
  have nat := ConcreteCategory.congr_hom
    (AlgebraicGeometry.Scheme.Modules.sectionMapOfRestrictHom_nat (ψ n) (V.ι ''ᵁ B) (V.ι ''ᵁ B'') hB hB')
    ((D.twistTransport U e W hle hΦ hτ n).inv.app B z)
  simp only [ConcreteCategory.comp_apply] at nat
  rw [AlgebraicGeometry.Scheme.Modules.hom_app_presheaf_map (D.twistTransport U e W hle hΦ hτ n).inv h z,
    AlgebraicGeometry.Scheme.Modules.restrict_presheaf_map_eq_tfa ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj.lift S f M D)).obj
      (AlgebraicGeometry.Scheme.relativeProj.twist S (n : ℤ))) V.ι h hB', nat,
    AlgebraicGeometry.Scheme.Modules.restrict_hom_app_map V.ι (AlgebraicGeometry.Scheme.relativeProj.powTriv f M U e W hle n) h hB']
  rfl

end Uniqueness

end LiftData

end AlgebraicGeometry.Scheme.relativeProj

end
