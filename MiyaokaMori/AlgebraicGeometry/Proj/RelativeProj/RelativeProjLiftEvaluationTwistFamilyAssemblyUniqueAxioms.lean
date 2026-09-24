import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.RelativeProjLiftEvaluationTwistFamilyAssemblyUniqueSectionFamily

/-! # Assembly, part 3b: uniqueness of twist families over an open of a piece

`toSectionFamily` (part 3a) satisfies (F') and (M') (the dictionary (D-α, D-β, D-μ, D-⊗) read backwards through `Θ⁻¹`),
hence is an absolute twist section family (`isSectionFamily_toSectionFamily`). The uniqueness theorem itself is in
`RelativeProjLiftEvaluationTwistFamilyAssemblyUnique3.lean` (split for compile time).
See `RelativeProjLiftEvaluationTwistFamily.lean`. -/

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



section Uniqueness

variable (U : T.Opens) (e : M.restrict U.ι ≅ SheafOfModules.unit U.toScheme.ringCatSheaf) (W : X.affineOpens)
  {V : T.Opens} (hle : V ≤ U ⊓ f ⁻¹ᵁ W.1)
  (hΦ : (HomogeneousIdeal.irrelevant (S.sectionsGrading W.1)).toIdeal.map
    (AlgebraicGeometry.Scheme.relativeProj.pieceRingHom S f M D U e W hle) = ⊤)
  (hτ : V.ι ≫ AlgebraicGeometry.Scheme.relativeProj.lift S f M D =
    AlgebraicGeometry.Proj.fromOfGlobalSections (S.sectionsGrading W.1)
        (AlgebraicGeometry.Scheme.relativeProj.pieceRingHom S f M D U e W hle) hΦ ≫
      AlgebraicGeometry.Scheme.relativeProj.chartEmbedding S W)

/-- (F') for `toSectionFamily`: on `φ_V^*(a/1)` it is `Φ_V(a)`. -/
theorem toSectionFamily_eval {V₁ : T.Opens} (ψ : ∀ n : ℕ,
      ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj.lift S f M D)).obj
          (AlgebraicGeometry.Scheme.relativeProj.twist S (n : ℤ))).restrict V₁.ι ⟶
        (AlgebraicGeometry.Scheme.Modules.monoidalPow M n).restrict V₁.ι)
    (h₁ : V ≤ V₁) (H : D.IsTwistFamilyOnAux V₁ ψ V h₁) (n : ℕ) (a : S.sectionsRing W.1) (ha : a ∈ S.sectionsGrading W.1 n)
    (B' : V.toScheme.Opens) :
    D.toSectionFamily U e W hle hΦ hτ ψ h₁ n B'
        (AlgebraicGeometry.Proj.TwistFamily.pullSection (S.sectionsGrading W.1)
          (AlgebraicGeometry.Scheme.relativeProj.pieceRingHom S f M D U e W hle) hΦ a ha B') =
      V.toScheme.presheaf.map (homOfLE le_top).op
        (AlgebraicGeometry.Scheme.relativeProj.pieceRingHom S f M D U e W hle a) := by
  obtain ⟨x, hx⟩ := ha
  subst hx
  have h1 := D.twistTransport_evalHom' U e W hle hΦ hτ n B' x
  have h2 := D.powTriv_dataHom' U e W hle n B' x
  have hF := H.1 n (V.ι ''ᵁ B') (AlgebraicGeometry.Scheme.relativeProj.LiftData.image_le_self B')
    (D.pulledSection U W hle n B' x)
  have e0 : AlgebraicGeometry.Proj.TwistFamily.pullSection (S.sectionsGrading W.1)
      (AlgebraicGeometry.Scheme.relativeProj.pieceRingHom S f M D U e W hle) hΦ
      (DirectSum.of (S.sectionsPiece W.1) n x) ⟨x, rfl⟩ B' =
      AlgebraicGeometry.Proj.TwistFamily.pullSection (S.sectionsGrading W.1)
        (AlgebraicGeometry.Scheme.relativeProj.pieceRingHom S f M D U e W hle) hΦ
        (S.sectionsOf W.1 n x).1 (S.sectionsOf W.1 n x).2 B' := rfl
  have e1 : (D.twistTransport U e W hle hΦ hτ n).inv.app B' (AlgebraicGeometry.Proj.TwistFamily.pullSection (S.sectionsGrading W.1)
      (AlgebraicGeometry.Scheme.relativeProj.pieceRingHom S f M D U e W hle) hΦ
      (S.sectionsOf W.1 n x).1 (S.sectionsOf W.1 n x).2 B') =
      (D.evalHomAux n).app (V.ι ''ᵁ B') (D.pulledSection U W hle n B' x) := by
    rw [← h1]
    exact AlgebraicGeometry.Scheme.Modules.iso_inv_app_hom_app_tfa (D.twistTransport U e W hle hΦ hτ n) B' _
  unfold AlgebraicGeometry.Scheme.relativeProj.LiftData.toSectionFamily
  rw [e0, e1, hF]
  exact h2

/-- (M') for `toSectionFamily`. -/
theorem toSectionFamily_mul {V₁ : T.Opens} (ψ : ∀ n : ℕ,
      ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj.lift S f M D)).obj
          (AlgebraicGeometry.Scheme.relativeProj.twist S (n : ℤ))).restrict V₁.ι ⟶
        (AlgebraicGeometry.Scheme.Modules.monoidalPow M n).restrict V₁.ι)
    (h₁ : V ≤ V₁) (H : D.IsTwistFamilyOnAux V₁ ψ V h₁) (a b : ℕ) (B' : V.toScheme.Opens)
    (z : Γ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Proj.fromOfGlobalSections (S.sectionsGrading W.1)
        (AlgebraicGeometry.Scheme.relativeProj.pieceRingHom S f M D U e W hle) hΦ)).obj
      (AlgebraicGeometry.Proj.twist (S.sectionsGrading W.1) (a : ℤ)), B'))
    (w : Γ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Proj.fromOfGlobalSections (S.sectionsGrading W.1)
        (AlgebraicGeometry.Scheme.relativeProj.pieceRingHom S f M D U e W hle) hΦ)).obj
      (AlgebraicGeometry.Proj.twist (S.sectionsGrading W.1) (b : ℤ)), B')) :
    D.toSectionFamily U e W hle hΦ hτ ψ h₁ (a + b) B'
        ((AlgebraicGeometry.Proj.TwistFamily.mulHom (S.sectionsGrading W.1)
          (AlgebraicGeometry.Scheme.relativeProj.pieceRingHom S f M D U e W hle) hΦ a b).app B'
          (AlgebraicGeometry.Scheme.Modules.tensorSections _ _ B' z w)) =
      D.toSectionFamily U e W hle hΦ hτ ψ h₁ a B' z * D.toSectionFamily U e W hle hΦ hτ ψ h₁ b B' w := by
  have hμ := D.twistTransport_twistMulHom' U e W hle hΦ hτ a b B'
    ((D.twistTransport U e W hle hΦ hτ a).inv.app B' z) ((D.twistTransport U e W hle hΦ hτ b).inv.app B' w)
  rw [AlgebraicGeometry.Scheme.Modules.iso_hom_app_inv_app (D.twistTransport U e W hle hΦ hτ a) B' z,
    AlgebraicGeometry.Scheme.Modules.iso_hom_app_inv_app (D.twistTransport U e W hle hΦ hτ b) B' w] at hμ
  have e1 : (D.twistTransport U e W hle hΦ hτ (a + b)).inv.app B'
      ((AlgebraicGeometry.Proj.TwistFamily.mulHom (S.sectionsGrading W.1)
        (AlgebraicGeometry.Scheme.relativeProj.pieceRingHom S f M D U e W hle) hΦ a b).app B'
        (AlgebraicGeometry.Scheme.Modules.tensorSections _ _ B' z w)) =
      (D.twistMulHomAux a b).app (V.ι ''ᵁ B') (AlgebraicGeometry.Scheme.Modules.tensorSections _ _ (V.ι ''ᵁ B')
        ((D.twistTransport U e W hle hΦ hτ a).inv.app B' z) ((D.twistTransport U e W hle hΦ hτ b).inv.app B' w)) := by
    rw [← hμ]
    exact AlgebraicGeometry.Scheme.Modules.iso_inv_app_hom_app_tfa (D.twistTransport U e W hle hΦ hτ (a + b)) B' _
  unfold AlgebraicGeometry.Scheme.relativeProj.LiftData.toSectionFamily
  rw [e1, H.2 a b (V.ι ''ᵁ B') (AlgebraicGeometry.Scheme.relativeProj.LiftData.image_le_self B') _ _]
  exact AlgebraicGeometry.Scheme.relativeProj.powTriv_monoidalPowCat f M U e W hle a b B' _ _

/-- **A relative twist family gives an absolute twist section family.** The five axioms are the dictionary
(D-α, D-β, D-μ, D-⊗) read backwards through `Θ⁻¹`, plus the naturality/linearity of all the maps involved. -/
theorem isSectionFamily_toSectionFamily {V₁ : T.Opens} (ψ : ∀ n : ℕ,
      ((AlgebraicGeometry.Scheme.Modules.pullback (AlgebraicGeometry.Scheme.relativeProj.lift S f M D)).obj
          (AlgebraicGeometry.Scheme.relativeProj.twist S (n : ℤ))).restrict V₁.ι ⟶
        (AlgebraicGeometry.Scheme.Modules.monoidalPow M n).restrict V₁.ι)
    (h₁ : V ≤ V₁) (H : D.IsTwistFamilyOnAux V₁ ψ V h₁) :
    AlgebraicGeometry.Proj.TwistFamily.IsSectionFamily (S.sectionsGrading W.1)
      (AlgebraicGeometry.Scheme.relativeProj.pieceRingHom S f M D U e W hle) hΦ
      (D.toSectionFamily U e W hle hΦ hτ ψ h₁) :=
  ⟨fun n B' z w => D.toSectionFamily_add U e W hle hΦ hτ ψ h₁ H n B' z w,
   fun n B' r z => D.toSectionFamily_smul U e W hle hΦ hτ ψ h₁ H n B' r z,
   fun n _ _ h z => D.toSectionFamily_res U e W hle hΦ hτ ψ h₁ H n h z,
   fun n a ha B' => D.toSectionFamily_eval U e W hle hΦ hτ ψ h₁ H n a ha B',
   fun a b B' z w => D.toSectionFamily_mul U e W hle hΦ hτ ψ h₁ H a b B' z w⟩

end Uniqueness

end LiftData

end AlgebraicGeometry.Scheme.relativeProj

end
