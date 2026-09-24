import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S3PositiveLine.JetNeighborhood.JetWeightComponentEqCoefficientGeneratesAtAux
import MiyaokaMori.AlgebraicGeometry.Modules.Differentials.OmegaTotalSpaceIsoPullbackDual
import MiyaokaMori.AlgebraicGeometry.Modules.DualMapAdditiveBiproduct
import MiyaokaMori.AlgebraicGeometry.Modules.Dual.FiberPolynomialExtensionDegreeFiberSectionsPolynomialFrameCoordinateMonomialRingEquivCoordinateDualFrame

/-! # `Γ(𝒵, π⁻¹U)` is generated over `Γ(U)` by the coordinate functions of a frame
(step (2) of `BasedJet.pieceSection_germ_mem_of_forall_isZeroAt`; proof of Lemma 3.1 of the paper)

* `AlgebraicGeometry.Scheme.totalSpace.pow_sections_induction`: on an affine open `U ⊆ Y` with a frame `a` of a
  module `A`, every predicate on `Γ(Tot(A^{⊕n}), π⁻¹U)` that contains the image of `π^♯ : Γ(U) → Γ(π⁻¹U)` and the
  `n` coordinate functions `x_ℓ = totalSpace.coordinateFunction A n ℓ U a^∨` and is closed under `+` and `*` holds
  everywhere. Proof: `Γ(Tot(A^{⊕n}), π⁻¹U)` is the symmetric algebra of `Γ((A^{⊕n})^∨, U)` over `Γ(U)` through
  `ξ ↦ ℓ_ξ` (`totalSpace.isSymmetricAlgebra_linearFunctionLinearMap`, Stacks 01N0 on sections), so
  `IsSymmetricAlgebra.induction` reduces to the generators `ℓ_ξ`; a section `ξ` of the dual of the biproduct is
  `∑_ℓ (π_ℓ)^∨ ((ι_ℓ)^∨ ξ)` (`eq_sum_dualMap_π_app`), each `(ι_ℓ)^∨ ξ ∈ Γ(A^∨, U)` is `r_ℓ • a^∨` because `a^∨` is a
  frame of `A^∨` (`IsFrame.dualSec_isFrame`), and `ℓ_{r • (π_ℓ)^∨ a^∨} = π^♯ r · x_ℓ` (`ℓ` is `Γ(U)`-linear).
* `MMSetup.cone_sections_induction`: the same for the twisted affine cone `𝒵 ⊆ Tot(A^{⊕(N+1)})`, `A = f^*O(1)`:
  `coneι = I.subschemeι` is the closed immersion of an ideal sheaf and `π⁻¹U ⊆ Tot` is affine (`Tot → C` is a
  relative Spec, hence affine, `IsAffineOpen.preimage`), so `coneι^♯ : Γ(Tot, π⁻¹U) → Γ(𝒵, π⁻¹U)` is surjective
  (Mathlib `IdealSheafData.subschemeι_app_surjective`); it is a ring homomorphism sending `π_Tot^♯ r` to `π^♯ r`
  (`coneι ≫ π_Tot = π`, `appLE_comp_appLE`) and `x_ℓ` to `x_ℓ|_𝒵 = coordinateFunctionOn … coneι` (by definition).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.totalSpace

variable {Y : AlgebraicGeometry.Scheme.{u}} (A : Y.Modules) (n : ℕ)
  [(AlgebraicGeometry.Scheme.Modules.pow A n).IsLocallyFree]
  [(AlgebraicGeometry.Scheme.Modules.pow A n).IsFiniteType]

/-- **Induction principle for functions on `Tot(A^{⊕n})` over an affine open with a frame**: a predicate containing
`π^♯(Γ(U))` and the coordinate functions `x_ℓ^{a^∨}`, closed under `+` and `*`, holds on all of `Γ(Tot, π⁻¹U)`
(`isSymmetricAlgebra_linearFunctionLinearMap` + `eq_sum_dualMap_π_app` + `IsFrame.dualSec_isFrame`). -/
theorem pow_sections_induction (U : Y.affineOpens) {a : Γ(A, U.1)}
    (hf : AlgebraicGeometry.Scheme.Modules.IsFrame A U.1 a)
    (P : Γ((AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A n)).left,
      (AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A n)).hom ⁻¹ᵁ U.1) → Prop)
    (hunit : ∀ r : Γ(Y, U.1), P (((AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A n)).hom.appLE
      U.1 ((AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A n)).hom ⁻¹ᵁ U.1) le_rfl).hom r))
    (hcoord : ∀ ℓ : Fin n, P (AlgebraicGeometry.Scheme.totalSpace.coordinateFunction A n ℓ U.1 hf.dualSec))
    (hadd : ∀ b c, P b → P c → P (b + c)) (hmul : ∀ b c, P b → P c → P (b * c)) :
    ∀ b, P b := by
  intro b
  let _ := ((AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A n)).hom.appLE U.1
    ((AlgebraicGeometry.Scheme.totalSpace (AlgebraicGeometry.Scheme.Modules.pow A n)).hom ⁻¹ᵁ U.1) le_rfl).hom.toAlgebra
  have hS := isSymmetricAlgebra_linearFunctionLinearMap (AlgebraicGeometry.Scheme.Modules.pow A n) U
  refine hS.induction (motive := P) hunit ?_ hmul hadd b
  intro ξ
  have h0 : P 0 := by
    have := hunit 0
    rwa [map_zero] at this
  have hξ := AlgebraicGeometry.Scheme.Modules.eq_sum_dualMap_π_app (fun _ : Fin n => A) U.1 ξ
  have hsum : linearFunctionLinearMap (AlgebraicGeometry.Scheme.Modules.pow A n) U.1 ξ =
      ∑ ℓ : Fin n, linearFunctionLinearMap (AlgebraicGeometry.Scheme.Modules.pow A n) U.1
        ((AlgebraicGeometry.Scheme.Modules.dualMap (biproduct.π (fun _ : Fin n => A) ℓ)).app U.1
          ((AlgebraicGeometry.Scheme.Modules.dualMap (biproduct.ι (fun _ : Fin n => A) ℓ)).app U.1 ξ)) := by
    conv_lhs => rw [hξ]
    exact map_sum _ _ _
  change P (linearFunctionLinearMap (AlgebraicGeometry.Scheme.Modules.pow A n) U.1 ξ)
  rw [hsum]
  refine Finset.sum_induction _ P hadd h0 ?_
  intro ℓ _
  obtain ⟨r, hr⟩ := (hf.dualSec_isFrame U.1 le_rfl).2
    ((AlgebraicGeometry.Scheme.Modules.dualMap (biproduct.ι (fun _ : Fin n => A) ℓ)).app U.1 ξ)
  rw [AlgebraicGeometry.Scheme.Modules.res_self] at hr
  have hsm : (AlgebraicGeometry.Scheme.Modules.dualMap (biproduct.π (fun _ : Fin n => A) ℓ)).app U.1 (r • hf.dualSec) =
      r • (AlgebraicGeometry.Scheme.Modules.dualMap (biproduct.π (fun _ : Fin n => A) ℓ)).app U.1 hf.dualSec :=
    AlgebraicGeometry.Scheme.Modules.Hom.app_smul _ _ _
  have e1 : linearFunctionLinearMap (AlgebraicGeometry.Scheme.Modules.pow A n) U.1
      ((AlgebraicGeometry.Scheme.Modules.dualMap (biproduct.π (fun _ : Fin n => A) ℓ)).app U.1 (r • hf.dualSec)) =
      linearFunctionLinearMap (AlgebraicGeometry.Scheme.Modules.pow A n) U.1
        (r • (AlgebraicGeometry.Scheme.Modules.dualMap (biproduct.π (fun _ : Fin n => A) ℓ)).app U.1 hf.dualSec) :=
    congrArg (fun z : Γ(AlgebraicGeometry.Scheme.Modules.dual (AlgebraicGeometry.Scheme.Modules.pow A n), U.1) =>
      linearFunctionLinearMap (AlgebraicGeometry.Scheme.Modules.pow A n) U.1 z) hsm
  have e2 : linearFunctionLinearMap (AlgebraicGeometry.Scheme.Modules.pow A n) U.1
      (r • (AlgebraicGeometry.Scheme.Modules.dualMap (biproduct.π (fun _ : Fin n => A) ℓ)).app U.1 hf.dualSec) =
      r • linearFunctionLinearMap (AlgebraicGeometry.Scheme.Modules.pow A n) U.1
        ((AlgebraicGeometry.Scheme.Modules.dualMap (biproduct.π (fun _ : Fin n => A) ℓ)).app U.1 hf.dualSec) :=
    LinearMap.map_smul _ r _
  rw [← hr, e1, e2, Algebra.smul_def]
  exact hmul _ _ (hunit r) (hcoord ℓ)

end AlgebraicGeometry.Scheme.totalSpace

variable {k : Type u} [Field k] {X : SmoothProjectiveVariety k} {C : SmoothProjectiveCurve k}
  (f : C.toScheme ⟶ X.toScheme) [D : MMSetup f]

/-- **Induction principle for functions on the cone `𝒵` over an affine open `U` with a frame `a` of `A = f^*O(1)`**:
a predicate on `Γ(𝒵, π⁻¹U)` containing `π^♯(Γ(U))` and the restricted coordinate functions `x_ℓ^{a^∨}|_𝒵`, closed
under `+` and `*`, holds everywhere (`coneι^♯` is surjective: `IdealSheafData.subschemeι_app_surjective` on the affine
open `π_Tot⁻¹U`; then `totalSpace.pow_sections_induction`). -/
theorem MMSetup.cone_sections_induction (U : C.toScheme.AffineZariskiSite)
    {a : Γ(seedLineBundle X.embedding f, U.1)}
    (hf : AlgebraicGeometry.Scheme.Modules.IsFrame (seedLineBundle X.embedding f) U.1 a)
    (hleb : (MMSetup.cone f).hom ⁻¹ᵁ U.1 ≤ BasedJet.coneι f ⁻¹ᵁ
      ((AlgebraicGeometry.Scheme.totalSpace
        (AlgebraicGeometry.Scheme.Modules.pow (seedLineBundle X.embedding f) (X.embDim + 1))).hom ⁻¹ᵁ U.1))
    (P : Γ((MMSetup.cone f).left, (MMSetup.cone f).hom ⁻¹ᵁ U.1) → Prop)
    (hunit : ∀ r : Γ(C.toScheme, U.1), P (((MMSetup.cone f).hom.app U.1).hom r))
    (hcoord : ∀ ℓ : Fin (X.embDim + 1), P (AlgebraicGeometry.Scheme.totalSpace.coordinateFunctionOn
      (seedLineBundle X.embedding f) (X.embDim + 1) ℓ U.1 hf.dualSec (BasedJet.coneι f)
      ((MMSetup.cone f).hom ⁻¹ᵁ U.1) hleb))
    (hadd : ∀ b c, P b → P c → P (b + c)) (hmul : ∀ b c, P b → P c → P (b * c)) :
    ∀ c, P c := by
  intro c
  have : AlgebraicGeometry.IsAffineHom (AlgebraicGeometry.Scheme.totalSpace
      (AlgebraicGeometry.Scheme.Modules.pow (seedLineBundle X.embedding f) (X.embDim + 1))).hom :=
    AlgebraicGeometry.Scheme.relativeSpec_isAffineHom _
  have hU' : AlgebraicGeometry.IsAffineOpen ((AlgebraicGeometry.Scheme.totalSpace
      (AlgebraicGeometry.Scheme.Modules.pow (seedLineBundle X.embedding f) (X.embDim + 1))).hom ⁻¹ᵁ U.1) :=
    U.2.preimage _
  obtain ⟨b, hb⟩ : ∃ b : Γ((AlgebraicGeometry.Scheme.totalSpace
      (AlgebraicGeometry.Scheme.Modules.pow (seedLineBundle X.embedding f) (X.embDim + 1))).left,
      (AlgebraicGeometry.Scheme.totalSpace
        (AlgebraicGeometry.Scheme.Modules.pow (seedLineBundle X.embedding f) (X.embDim + 1))).hom ⁻¹ᵁ U.1),
      ((BasedJet.coneι f).appLE _ _ hleb).hom b = c := by
    obtain ⟨b, hb⟩ := AlgebraicGeometry.Scheme.IdealSheafData.subschemeι_app_surjective
      (I := ⨆ j, AlgebraicGeometry.Scheme.idealSheafOfSection _
        (homogeneousEquationSection (seedLineBundle X.embedding f) X.embDim (D.E.F j) (D.E.homogeneous j)))
      ⟨_, hU'⟩ c
    refine ⟨b, ?_⟩
    have e := congrArg (fun φ : Γ((AlgebraicGeometry.Scheme.totalSpace
        (AlgebraicGeometry.Scheme.Modules.pow (seedLineBundle X.embedding f) (X.embDim + 1))).left,
        (AlgebraicGeometry.Scheme.totalSpace
          (AlgebraicGeometry.Scheme.Modules.pow (seedLineBundle X.embedding f) (X.embDim + 1))).hom ⁻¹ᵁ U.1) ⟶
        Γ((MMSetup.cone f).left, (MMSetup.cone f).hom ⁻¹ᵁ U.1) => φ.hom b)
      (AlgebraicGeometry.Scheme.Hom.appLE_eq_app (BasedJet.coneι f) (U := (AlgebraicGeometry.Scheme.totalSpace
        (AlgebraicGeometry.Scheme.Modules.pow (seedLineBundle X.embedding f) (X.embDim + 1))).hom ⁻¹ᵁ U.1))
    exact e.trans hb
  rw [← hb]
  refine AlgebraicGeometry.Scheme.totalSpace.pow_sections_induction (seedLineBundle X.embedding f) (X.embDim + 1)
    ⟨U.1, U.2⟩ hf (fun b => P (((BasedJet.coneι f).appLE _ _ hleb).hom b)) ?_ ?_ ?_ ?_ b
  · intro r
    have e := congrArg (fun φ : Γ(C.toScheme, U.1) ⟶ Γ((MMSetup.cone f).left, (MMSetup.cone f).hom ⁻¹ᵁ U.1) => φ.hom r)
      (AlgebraicGeometry.Scheme.Hom.appLE_comp_appLE (BasedJet.coneι f) (AlgebraicGeometry.Scheme.totalSpace
        (AlgebraicGeometry.Scheme.Modules.pow (seedLineBundle X.embedding f) (X.embDim + 1))).hom U.1 _ _ le_rfl hleb)
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at e
    show P (((BasedJet.coneι f).appLE _ _ hleb).hom (((AlgebraicGeometry.Scheme.totalSpace
      (AlgebraicGeometry.Scheme.Modules.pow (seedLineBundle X.embedding f) (X.embDim + 1))).hom.appLE U.1 _ le_rfl).hom r))
    rw [e, AlgebraicGeometry.Scheme.Hom.appLE_congr_hom (BasedJet.coneι_comp_hom f) U.1 _ _ le_rfl,
      AlgebraicGeometry.Scheme.Hom.appLE_eq_app]
    exact hunit r
  · intro ℓ
    exact hcoord ℓ
  · intro b c hb hc
    show P (((BasedJet.coneι f).appLE _ _ hleb).hom (b + c))
    rw [map_add]
    exact hadd _ _ hb hc
  · intro b c hb hc
    show P (((BasedJet.coneι f).appLE _ _ hleb).hom (b * c))
    rw [map_mul]
    exact hmul _ _ hb hc

end
