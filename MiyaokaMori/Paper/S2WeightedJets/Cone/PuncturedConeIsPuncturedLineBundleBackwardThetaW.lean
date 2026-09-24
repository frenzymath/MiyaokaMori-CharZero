import MiyaokaMori.Prelude
import MiyaokaMori.Paper.S2WeightedJets.Cone.PuncturedConeIsPuncturedLineBundleContract
import MiyaokaMori.Paper.S2WeightedJets.Cone.PuncturedConeIsPuncturedLineBundleContractInjectiveEvalIso
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorSectionsCoherence
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.ModuleSheafFrameIso
import MiyaokaMori.AlgebraicGeometry.Modules.Stalk.SectionIsZeroAtIso

/-! # `θ_w : T.hom^*pr₂^*O_X(1) ≅ T.hom^*pr₁^*A` — the line-bundle isomorphism given by a frame `w` and `contract`

For `T` over `C ×_k X` and a global frame `w` of `T.hom^*L` (`L = conePuncturedLineBundle e A = pr₁^*A ⊗ pr₂^*O_X(-1)`),
`conePuncturedLineBundle.thetaW e A T hw` is the isomorphism `q ↦ ⟨w, q⟩`, and `thetaW_hom_app` identifies its
global-section map with `contractSections T w`. This is used by the construction of the backward morphism
`β` (module `…PuncturedConeIsPuncturedLineBundleBackward`):
`contract` is an isomorphism (`isIso_contract`, Stacks 01CT, module `…ContractInjectiveEvalIso`), and `θ_w` is the
composite of the left unitor, the trivialization `O ≅ T.hom^*L` given by the frame (`IsFrame.unitIso`, Stacks 01CY),
`pullbackTensorObjIso` (Stacks 01CD) and `T.hom^*contract`.

Also: small variable-level bookkeeping (`leftUnitor_inv_app_top`, `whiskerRight_app_tensorSections'`,
`IsFrame.unitIso_hom_app_one`, `Hom.comp_app_apply`, `hom_app_top_eq` (from `HomogeneousEquationSectionAtTotalSpaceSectionCoordinate`), `Iso.trans_trans_hom_val_app_apply`,
`isZeroAt_natIso_hom_app_iff`, `isZeroAt_iso_iff'`).

Source: eq. (2.1) of the paper (`t^*A ⊗ x^*O_X(−1) = Hom(x^*O_X(1), t^*A)`). -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
open scoped CategoryTheory.MonoidalCategory

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- Evaluating a composite on a section (definitional). -/
theorem Hom.comp_app_apply {M N K : X.Modules} (φ : M ⟶ N) (ψ : N ⟶ K) (U : X.Opens) (x : Γ(M, U)) :
    (φ ≫ ψ).app U x = ψ.app U (φ.app U x) := rfl

/-- `(λ_ Q).inv` on a global section: `q ↦ 1 ⊗ q`. -/
theorem leftUnitor_inv_app_top (Q : X.Modules) (q : Γ(Q, ⊤)) :
    (λ_ Q).inv.app ⊤ q = tensorSections (𝟙_ X.Modules) Q ⊤ (1 : Γ(X, ⊤)) q := by
  have h := leftUnitor_app_tensorSections Q ⊤ (1 : Γ(X, ⊤)) q
  rw [one_smul] at h
  have h2 : (λ_ Q).inv.app ⊤ ((λ_ Q).hom.app ⊤ (tensorSections (𝟙_ X.Modules) Q ⊤ (1 : Γ(X, ⊤)) q)) =
      tensorSections (𝟙_ X.Modules) Q ⊤ (1 : Γ(X, ⊤)) q :=
    congrArg (fun φ : (𝟙_ X.Modules) ⊗ Q ⟶ (𝟙_ X.Modules) ⊗ Q =>
      φ.app ⊤ (tensorSections (𝟙_ X.Modules) Q ⊤ (1 : Γ(X, ⊤)) q)) (λ_ Q).hom_inv_id
  rw [h] at h2
  exact h2

/-- Right whiskering on a section pairing: `(f ▷ B)(a ⊗ b) = f a ⊗ b`. -/
theorem whiskerRight_app_tensorSections' {A A' B : X.Modules} (f : A ⟶ A') (U : X.Opens)
    (a : Γ(A, U)) (b : Γ(B, U)) :
    (f ▷ B).app U (tensorSections A B U a b) = tensorSections A' B U (f.app U a) b := by
  rw [← MonoidalCategory.tensorHom_id]
  exact tensorHom_tensorSections f (𝟙 B) U a b

/-- The global trivialization `O_X ≅ M` of a global frame, stated in the category `X.Modules` (so that the
monoidal structure of `X.Modules` applies to it; `topTrivialization` lives in `SheafOfModules _`). -/
noncomputable def IsFrame.unitIso {M : X.Modules} {w : Γ(M, ⊤)} (hw : IsFrame M ⊤ w) :
    (𝟙_ X.Modules) ≅ M :=
  hw.topTrivialization

/-- The global trivialization of a frame sends `1` to the frame. -/
theorem IsFrame.unitIso_hom_app_one {M : X.Modules} {w : Γ(M, ⊤)} (hw : IsFrame M ⊤ w) :
    hw.unitIso.hom.app ⊤ (1 : Γ(X, ⊤)) = w := by
  show (homOfSection M w).val.app (op ⊤) (1 : Γ(X, ⊤)) = w
  rw [homOfSection_app_one]
  exact res_self M w

/-- Evaluating a threefold composite of isomorphisms on a global section (definitional). -/
theorem Iso.trans_trans_hom_val_app_apply {M N P R : X.Modules} (α : M ≅ N) (β : N ≅ P) (γ : P ≅ R)
    (x : (M.val.obj (Opposite.op ⊤) : Type u)) :
    ((α ≪≫ β ≪≫ γ).hom.val.app (Opposite.op ⊤)).hom x =
      (γ.hom.val.app (Opposite.op ⊤)).hom ((β.hom.val.app (Opposite.op ⊤)).hom ((α.hom.val.app (Opposite.op ⊤)).hom x)) :=
  rfl

/-- `IsZeroAt` is invariant under the component of a natural isomorphism. -/
theorem isZeroAt_natIso_hom_app_iff {Y : AlgebraicGeometry.Scheme.{u}} {F G : Y.Modules ⥤ X.Modules} (α : F ≅ G)
    (M : Y.Modules) (s : ((F.obj M).val.obj (Opposite.op ⊤) : Type u)) (x : X) :
    IsZeroAt (((α.hom.app M).val.app (Opposite.op ⊤)).hom s) x ↔ IsZeroAt s x :=
  isZeroAt_iso_iff (α.app M) s x

/-- `isZeroAt_iso_iff` in the `.val.app` spelling. -/
theorem isZeroAt_iso_iff' {M M' : X.Modules} (θ : M ≅ M')
    (s : (M.val.obj (Opposite.op ⊤) : Type u)) (x : X) :
    IsZeroAt ((θ.hom.val.app (Opposite.op ⊤)).hom s) x ↔ IsZeroAt s x :=
  isZeroAt_iso_iff θ s x

end AlgebraicGeometry.Scheme.Modules

/-- **θ_w.** For `T` over `C ×_k X` and a global frame `w` of `T.hom^*L` (`L = conePuncturedLineBundle e A`),
the isomorphism `T.hom^*pr₂^*O_X(1) ≅ T.hom^*pr₁^*A`, `q ↦ ⟨w, q⟩`: left unitor, `O ≅ T.hom^*L` (`1 ↦ w`),
`T.hom^*L ⊗ T.hom^*Q ≅ T.hom^*(L ⊗ Q)` and `T.hom^*contract` (an isomorphism by `isIso_contract`, Stacks 01CT). -/
noncomputable def conePuncturedLineBundle.thetaW {k : Type u} [Field k] {C X : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {N : ℕ}
    (e : ProjectiveEmbedding k X N) (A : C.Modules) [A.IsLineBundle]
    (T : CategoryTheory.Over (CategoryTheory.Limits.pullback (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
      (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))))
    {w : (((AlgebraicGeometry.Scheme.Modules.pullback T.hom).obj (conePuncturedLineBundle e A)).val.obj
      (Opposite.op ⊤) : Type u)}
    (hw : AlgebraicGeometry.Scheme.Modules.IsFrame
      ((AlgebraicGeometry.Scheme.Modules.pullback T.hom).obj (conePuncturedLineBundle e A)) ⊤ w) :
    (AlgebraicGeometry.Scheme.Modules.pullback T.hom).obj
        ((AlgebraicGeometry.Scheme.Modules.pullback
          (CategoryTheory.Limits.pullback.snd (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
            (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).obj
          (e.oX 1)) ≅
      (AlgebraicGeometry.Scheme.Modules.pullback T.hom).obj
        ((AlgebraicGeometry.Scheme.Modules.pullback
          (CategoryTheory.Limits.pullback.fst (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
            (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).obj A) :=
  haveI : CategoryTheory.IsIso (conePuncturedLineBundle.contract e A) := conePuncturedLineBundle.isIso_contract e A
  (λ_ _).symm ≪≫ MonoidalCategory.whiskerRightIso hw.unitIso _ ≪≫
    (AlgebraicGeometry.Scheme.Modules.pullbackTensorObjIso T.hom _ _).symm ≪≫
    CategoryTheory.asIso ((AlgebraicGeometry.Scheme.Modules.pullback T.hom).map (conePuncturedLineBundle.contract e A))

/-- On global sections, `θ_w` is the pairing with `w`: `θ_w(q) = ⟨w, q⟩ = contractSections T w q`. -/
theorem conePuncturedLineBundle.thetaW_hom_app {k : Type u} [Field k] {C X : AlgebraicGeometry.Scheme.{u}}
    [C.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))] {N : ℕ}
    (e : ProjectiveEmbedding k X N) (A : C.Modules) [A.IsLineBundle]
    (T : CategoryTheory.Over (CategoryTheory.Limits.pullback (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
      (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k))))
    {w : (((AlgebraicGeometry.Scheme.Modules.pullback T.hom).obj (conePuncturedLineBundle e A)).val.obj
      (Opposite.op ⊤) : Type u)}
    (hw : AlgebraicGeometry.Scheme.Modules.IsFrame
      ((AlgebraicGeometry.Scheme.Modules.pullback T.hom).obj (conePuncturedLineBundle e A)) ⊤ w)
    (q : (((AlgebraicGeometry.Scheme.Modules.pullback T.hom).obj
      ((AlgebraicGeometry.Scheme.Modules.pullback
        (CategoryTheory.Limits.pullback.snd (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
          (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).obj
        (e.oX 1))).val.obj (Opposite.op ⊤) : Type u)) :
    (conePuncturedLineBundle.thetaW e A T hw).hom.app ⊤ q = conePuncturedLineBundle.contractSections e A T w q := by
  unfold conePuncturedLineBundle.thetaW conePuncturedLineBundle.contractSections
  simp only [Iso.trans_hom, Iso.symm_hom, asIso_hom, MonoidalCategory.whiskerRightIso_hom]
  erw [AlgebraicGeometry.Scheme.Modules.Hom.comp_app_apply, AlgebraicGeometry.Scheme.Modules.Hom.comp_app_apply,
    AlgebraicGeometry.Scheme.Modules.Hom.comp_app_apply]
  rw [AlgebraicGeometry.Scheme.Modules.leftUnitor_inv_app_top (X := T.left) ((AlgebraicGeometry.Scheme.Modules.pullback T.hom).obj
        ((AlgebraicGeometry.Scheme.Modules.pullback
          (CategoryTheory.Limits.pullback.snd (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
            (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).obj
          (e.oX 1))) q]
  rw [AlgebraicGeometry.Scheme.Modules.whiskerRight_app_tensorSections' (X := T.left) (B := ((AlgebraicGeometry.Scheme.Modules.pullback T.hom).obj
        ((AlgebraicGeometry.Scheme.Modules.pullback
          (CategoryTheory.Limits.pullback.snd (C ↘ AlgebraicGeometry.Spec (CommRingCat.of k))
            (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)))).obj
          (e.oX 1))))
    hw.unitIso.hom ⊤ (1 : Γ(T.left, ⊤)) q]
  rw [AlgebraicGeometry.Scheme.Modules.IsFrame.unitIso_hom_app_one hw]
  rfl

end
