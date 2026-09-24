import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.SectionTensor
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorSectionsCoherence
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.LineBundleNonvanishingLocus
import MiyaokaMori.AlgebraicGeometry.Modules.LineBundle.SheafOfModulesIsLineBundle
import MiyaokaMori.AlgebraicGeometry.Modules.Stacks0892_TensorPowIsos

/-! # Raising the exponent in Stacks 01PW (2)

**Raising the exponent in Stacks 01PW (2).** If a section `t ∈ Γ(X_s, F)` has been written as
`σ|_{X_s} = t ⊗ s^{⊗k}|_{X_s}` with `σ ∈ Γ(X, F ⊗ L^{⊗k})`, then for every `k' ≥ k` it can also be
written as `σ'|_{X_s} = t ⊗ s^{⊗k'}|_{X_s}` with `σ' ∈ Γ(X, F ⊗ L^{⊗k'})`: multiply `σ` by `s^{⊗(k'-k)}`.
This is what makes the exponents of finitely many applications of Stacks 01PW
(`Scheme.Modules.exists_tensorPow_section_restrict_eq`) uniform (Stacks 01Q3, proof of (1)⇒(5):
"we may choose the same `n` for all `i`").

Proof. Induction on `k'` from `k` (`Nat.le_induction`). For the step `j ↦ j + 1` put
`σ' := θ (σ ⊗ s)`, where `σ ⊗ s := sectionTensor σ s ∈ Γ(X, (F ⊗ L^{⊗j}) ⊗ L)` and
`θ := tensorAssocIso F L^{⊗j} L : (F ⊗ L^{⊗j}) ⊗ L ≅ F ⊗ (L^{⊗j} ⊗ L) = F ⊗ L^{⊗(j+1)}`
(`tensorPow L (j+1) = tensor (tensorPow L j) L` by definition). Restricting to `X_s`:
`θ` commutes with restriction (`Hom.app_res`), restriction of a pure tensor is the pure tensor of the
restrictions (`moduleTensorSection_restrict`), the induction hypothesis rewrites
`σ|_{X_s} = t ⊗ s^{⊗j}|`, and the associator sends `(t ⊗ s^{⊗j}) ⊗ s` to `t ⊗ (s^{⊗j} ⊗ s)`
(`tensorAssocIso_hom_app_moduleTensorSection` below, from `associator_app_tensorSections` and the
functoriality `tensorHom_tensorSections` of the pure tensor sections); finally `s^{⊗j} ⊗ s = s^{⊗(j+1)}`
is the definition of `tensorPowSection`.

Also here: `tensorCongrRightIso_hom_app_moduleTensorSection` (`F ⊗ θ` on a pure tensor is the pure
tensor of `θ`'s value), used to transport `σ'` along `(L^{⊗m})^{⊗k} ≅ L^{⊗n}`.

Edge cases: `k' = k` (take `σ' = σ`); `X_s = ∅` (all restrictions live in the zero module); `F = 0`.
References: Stacks 01PW (`properties-lemma-invert-s-sections`) and 01Q3 (proof of (1)⇒(5)). -/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry
open scoped CategoryTheory.MonoidalCategory

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : AlgebraicGeometry.Scheme.{u}}

/-- `(tensorIsoTensorObj A B).hom` on a pure tensor section (definitional). -/
theorem tensorIsoTensorObj_hom_app_moduleTensorSection' (A B : X.Modules) (U : X.Opens)
    (a : Γ(A, U)) (b : Γ(B, U)) :
    (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj A B).hom.app U (AlgebraicGeometry.Scheme.Modules.moduleTensorSection a b) =
      AlgebraicGeometry.Scheme.Modules.tensorSections A B U a b := rfl

/-- `(tensorIsoTensorObj A B).inv` on a pure tensor section. -/
theorem tensorIsoTensorObj_inv_app_tensorSections' (A B : X.Modules) (U : X.Opens)
    (a : Γ(A, U)) (b : Γ(B, U)) :
    (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj A B).inv.app U
        (AlgebraicGeometry.Scheme.Modules.tensorSections A B U a b) =
      AlgebraicGeometry.Scheme.Modules.moduleTensorSection a b :=
  congrArg (fun φ : AlgebraicGeometry.Scheme.Modules.tensor A B ⟶ AlgebraicGeometry.Scheme.Modules.tensor A B =>
    φ.app U (AlgebraicGeometry.Scheme.Modules.moduleTensorSection a b)) (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj A B).hom_inv_id

/-- Left whiskering on a pure tensor section: `(A ◁ f)(a ⊗ b) = a ⊗ f(b)`. -/
theorem whiskerLeft_app_tensorSections'' {A B B' : X.Modules} (f : B ⟶ B') (U : X.Opens)
    (a : Γ(A, U)) (b : Γ(B, U)) :
    (A ◁ f).app U (AlgebraicGeometry.Scheme.Modules.tensorSections A B U a b) =
      AlgebraicGeometry.Scheme.Modules.tensorSections A B' U a (f.app U b) := by
  rw [← MonoidalCategory.id_tensorHom]
  exact AlgebraicGeometry.Scheme.Modules.tensorHom_tensorSections (𝟙 A) f U a b

/-- Right whiskering on a pure tensor section: `(f ▷ B)(a ⊗ b) = f(a) ⊗ b`. -/
theorem whiskerRight_app_tensorSections'' {A A' B : X.Modules} (f : A ⟶ A') (U : X.Opens)
    (a : Γ(A, U)) (b : Γ(B, U)) :
    (f ▷ B).app U (AlgebraicGeometry.Scheme.Modules.tensorSections A B U a b) =
      AlgebraicGeometry.Scheme.Modules.tensorSections A' B U (f.app U a) b := by
  rw [← MonoidalCategory.tensorHom_id]
  exact AlgebraicGeometry.Scheme.Modules.tensorHom_tensorSections f (𝟙 B) U a b

/-- **`F ⊗ θ` on a pure tensor section**: `(tensorCongrRightIso F θ).hom (a ⊗ b) = a ⊗ θ(b)`. -/
theorem tensorCongrRightIso_hom_app_moduleTensorSection (F : X.Modules) {A B : X.Modules} (θ : A ≅ B)
    (U : X.Opens) (a : Γ(F, U)) (b : Γ(A, U)) :
    (AlgebraicGeometry.Scheme.Modules.tensorCongrRightIso F θ).hom.app U (AlgebraicGeometry.Scheme.Modules.moduleTensorSection a b) =
      AlgebraicGeometry.Scheme.Modules.moduleTensorSection a (θ.hom.app U b) := by
  show (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj F B).inv.app U
    ((F ◁ θ.hom).app U
      ((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj F A).hom.app U (AlgebraicGeometry.Scheme.Modules.moduleTensorSection a b))) = _
  rw [tensorIsoTensorObj_hom_app_moduleTensorSection', whiskerLeft_app_tensorSections'',
    tensorIsoTensorObj_inv_app_tensorSections']

/-- Morphisms of `O_X`-modules commute with restriction (elementwise form). -/
theorem Hom.app_map' {M N : X.Modules} (φ : M ⟶ N) {W W' : X.Opens} (h : W' ≤ W) (x : Γ(M, W)) :
    φ.app W' (M.presheaf.map (homOfLE h).op x) = N.presheaf.map (homOfLE h).op (φ.app W x) :=
  ConcreteCategory.congr_hom (φ.mapPresheaf.naturality (homOfLE h).op) x

/-- **The associator on pure tensor sections**:
`(tensorAssocIso A B C).hom ((a ⊗ b) ⊗ c) = a ⊗ (b ⊗ c)`. -/
theorem tensorAssocIso_hom_app_moduleTensorSection (A B C : X.Modules) (U : X.Opens)
    (a : Γ(A, U)) (b : Γ(B, U)) (c : Γ(C, U)) :
    (AlgebraicGeometry.Scheme.Modules.tensorAssocIso A B C).hom.app U
        (AlgebraicGeometry.Scheme.Modules.moduleTensorSection (AlgebraicGeometry.Scheme.Modules.moduleTensorSection a b) c) =
      AlgebraicGeometry.Scheme.Modules.moduleTensorSection a (AlgebraicGeometry.Scheme.Modules.moduleTensorSection b c) := by
  have h1 : ((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj A B).hom ▷ C).app U
      (AlgebraicGeometry.Scheme.Modules.tensorSections (AlgebraicGeometry.Scheme.Modules.tensor A B) C U
        (AlgebraicGeometry.Scheme.Modules.moduleTensorSection a b) c) =
      AlgebraicGeometry.Scheme.Modules.tensorSections (A ⊗ B) C U
        (AlgebraicGeometry.Scheme.Modules.tensorSections A B U a b) c :=
    whiskerRight_app_tensorSections'' (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj A B).hom U
      (AlgebraicGeometry.Scheme.Modules.moduleTensorSection a b) c
  have h2 := AlgebraicGeometry.Scheme.Modules.associator_app_tensorSections A B C U a b c
  have h3 : (A ◁ (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj B C).inv).app U
      (AlgebraicGeometry.Scheme.Modules.tensorSections A (B ⊗ C) U a
        (AlgebraicGeometry.Scheme.Modules.tensorSections B C U b c)) =
      AlgebraicGeometry.Scheme.Modules.tensorSections A (AlgebraicGeometry.Scheme.Modules.tensor B C) U a
        (AlgebraicGeometry.Scheme.Modules.moduleTensorSection b c) :=
    (whiskerLeft_app_tensorSections'' (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj B C).inv U a
      (AlgebraicGeometry.Scheme.Modules.tensorSections B C U b c)).trans
      (congrArg (fun z : Γ(AlgebraicGeometry.Scheme.Modules.tensor B C, U) =>
        AlgebraicGeometry.Scheme.Modules.tensorSections A (AlgebraicGeometry.Scheme.Modules.tensor B C) U a z)
        (tensorIsoTensorObj_inv_app_tensorSections' B C U b c))
  have h4 := tensorIsoTensorObj_inv_app_tensorSections' A (AlgebraicGeometry.Scheme.Modules.tensor B C) U a
    (AlgebraicGeometry.Scheme.Modules.moduleTensorSection b c)
  show (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj A (AlgebraicGeometry.Scheme.Modules.tensor B C)).inv.app U
    ((A ◁ (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj B C).inv).app U
      ((α_ A B C).hom.app U
        (((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj A B).hom ▷ C).app U
          ((AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj (AlgebraicGeometry.Scheme.Modules.tensor A B) C).hom.app U
            (AlgebraicGeometry.Scheme.Modules.moduleTensorSection (AlgebraicGeometry.Scheme.Modules.moduleTensorSection a b) c))))) = _
  exact (congrArg (fun z => (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj A
      (AlgebraicGeometry.Scheme.Modules.tensor B C)).inv.app U
      ((A ◁ (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj B C).inv).app U ((α_ A B C).hom.app U z))) h1).trans
    ((congrArg (fun z => (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj A
      (AlgebraicGeometry.Scheme.Modules.tensor B C)).inv.app U
      ((A ◁ (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj B C).inv).app U z)) h2).trans
    ((congrArg (fun z => (AlgebraicGeometry.Scheme.Modules.tensorIsoTensorObj A
      (AlgebraicGeometry.Scheme.Modules.tensor B C)).inv.app U z) h3).trans h4))

/-- **Raising the exponent in Stacks 01PW (2)**: from `σ|_{X_s} = t ⊗ s^{⊗k}|` with
`σ ∈ Γ(X, F ⊗ L^{⊗k})` to `σ'|_{X_s} = t ⊗ s^{⊗k'}|` with `σ' ∈ Γ(X, F ⊗ L^{⊗k'})`, for every `k' ≥ k`
(multiply by `s^{⊗(k'-k)}`). -/
theorem exists_tensorPow_section_restrict_eq_of_le (L : X.Modules) [L.IsLineBundle] (s : Γ(L, ⊤))
    (F : X.Modules) (t : Γ(F, L.nonvanishingLocus s)) {k : ℕ}
    (σ : Γ(AlgebraicGeometry.Scheme.Modules.tensor F (AlgebraicGeometry.Scheme.Modules.tensorPow L k), ⊤))
    (hσ : (AlgebraicGeometry.Scheme.Modules.tensor F (AlgebraicGeometry.Scheme.Modules.tensorPow L k)).presheaf.map
        (homOfLE (le_top : L.nonvanishingLocus s ≤ ⊤)).op σ =
      AlgebraicGeometry.Scheme.Modules.moduleTensorSection t
        ((AlgebraicGeometry.Scheme.Modules.tensorPow L k).presheaf.map
          (homOfLE (le_top : L.nonvanishingLocus s ≤ ⊤)).op
          (AlgebraicGeometry.Scheme.Modules.tensorPowSection s k)))
    {k' : ℕ} (hk : k ≤ k') :
    ∃ σ' : Γ(AlgebraicGeometry.Scheme.Modules.tensor F (AlgebraicGeometry.Scheme.Modules.tensorPow L k'), ⊤),
      (AlgebraicGeometry.Scheme.Modules.tensor F (AlgebraicGeometry.Scheme.Modules.tensorPow L k')).presheaf.map
          (homOfLE (le_top : L.nonvanishingLocus s ≤ ⊤)).op σ' =
        AlgebraicGeometry.Scheme.Modules.moduleTensorSection t
          ((AlgebraicGeometry.Scheme.Modules.tensorPow L k').presheaf.map
            (homOfLE (le_top : L.nonvanishingLocus s ≤ ⊤)).op
            (AlgebraicGeometry.Scheme.Modules.tensorPowSection s k')) := by
  induction k', hk using Nat.le_induction with
  | base => exact ⟨σ, hσ⟩
  | succ j _ ih =>
    obtain ⟨σ', hσ'⟩ := ih
    let U : X.Opens := L.nonvanishingLocus s
    let ρ : U ⟶ ⊤ := homOfLE le_top
    let Pj : X.Modules := AlgebraicGeometry.Scheme.Modules.tensorPow L j
    let θ : AlgebraicGeometry.Scheme.Modules.tensor (AlgebraicGeometry.Scheme.Modules.tensor F Pj) L ≅
        AlgebraicGeometry.Scheme.Modules.tensor F (AlgebraicGeometry.Scheme.Modules.tensor Pj L) :=
      AlgebraicGeometry.Scheme.Modules.tensorAssocIso F Pj L
    refine ⟨θ.hom.app ⊤ (sectionTensor σ' s), ?_⟩
    change (AlgebraicGeometry.Scheme.Modules.tensor F (AlgebraicGeometry.Scheme.Modules.tensor Pj L)).presheaf.map ρ.op
        (θ.hom.app ⊤ (sectionTensor σ' s)) =
      AlgebraicGeometry.Scheme.Modules.moduleTensorSection t
        ((AlgebraicGeometry.Scheme.Modules.tensor Pj L).presheaf.map ρ.op
          (sectionTensor (AlgebraicGeometry.Scheme.Modules.tensorPowSection s j) s))
    have e1 : (AlgebraicGeometry.Scheme.Modules.tensor F (AlgebraicGeometry.Scheme.Modules.tensor Pj L)).presheaf.map ρ.op
          (θ.hom.app ⊤ (sectionTensor σ' s)) =
        θ.hom.app U ((AlgebraicGeometry.Scheme.Modules.tensor
          (AlgebraicGeometry.Scheme.Modules.tensor F Pj) L).presheaf.map ρ.op (sectionTensor σ' s)) :=
      (Hom.app_map' θ.hom (le_top : U ≤ ⊤) (sectionTensor σ' s)).symm
    have e2 : (AlgebraicGeometry.Scheme.Modules.tensor
          (AlgebraicGeometry.Scheme.Modules.tensor F Pj) L).presheaf.map ρ.op (sectionTensor σ' s) =
        AlgebraicGeometry.Scheme.Modules.moduleTensorSection
          ((AlgebraicGeometry.Scheme.Modules.tensor F Pj).presheaf.map ρ.op σ') (L.presheaf.map ρ.op s) :=
      AlgebraicGeometry.Scheme.Modules.moduleTensorSection_restrict ρ σ' s
    have e3 : θ.hom.app U (AlgebraicGeometry.Scheme.Modules.moduleTensorSection
          ((AlgebraicGeometry.Scheme.Modules.tensor F Pj).presheaf.map ρ.op σ') (L.presheaf.map ρ.op s)) =
        θ.hom.app U (AlgebraicGeometry.Scheme.Modules.moduleTensorSection
          (AlgebraicGeometry.Scheme.Modules.moduleTensorSection t
            (Pj.presheaf.map ρ.op (AlgebraicGeometry.Scheme.Modules.tensorPowSection s j)))
          (L.presheaf.map ρ.op s)) :=
      congrArg (fun z : Γ(AlgebraicGeometry.Scheme.Modules.tensor F Pj, U) =>
        θ.hom.app U (AlgebraicGeometry.Scheme.Modules.moduleTensorSection z (L.presheaf.map ρ.op s))) hσ'
    have e4 : θ.hom.app U (AlgebraicGeometry.Scheme.Modules.moduleTensorSection
          (AlgebraicGeometry.Scheme.Modules.moduleTensorSection t
            (Pj.presheaf.map ρ.op (AlgebraicGeometry.Scheme.Modules.tensorPowSection s j)))
          (L.presheaf.map ρ.op s)) =
        AlgebraicGeometry.Scheme.Modules.moduleTensorSection t
          (AlgebraicGeometry.Scheme.Modules.moduleTensorSection
            (Pj.presheaf.map ρ.op (AlgebraicGeometry.Scheme.Modules.tensorPowSection s j))
            (L.presheaf.map ρ.op s)) :=
      tensorAssocIso_hom_app_moduleTensorSection F Pj L U t _ _
    have e5 : (AlgebraicGeometry.Scheme.Modules.tensor Pj L).presheaf.map ρ.op
          (sectionTensor (AlgebraicGeometry.Scheme.Modules.tensorPowSection s j) s) =
        AlgebraicGeometry.Scheme.Modules.moduleTensorSection
          (Pj.presheaf.map ρ.op (AlgebraicGeometry.Scheme.Modules.tensorPowSection s j))
          (L.presheaf.map ρ.op s) :=
      AlgebraicGeometry.Scheme.Modules.moduleTensorSection_restrict ρ (AlgebraicGeometry.Scheme.Modules.tensorPowSection s j) s
    exact e1.trans ((congrArg (fun z => θ.hom.app U z) e2).trans (e3.trans (e4.trans
      (congrArg (fun z => AlgebraicGeometry.Scheme.Modules.moduleTensorSection t z) e5.symm))))

end AlgebraicGeometry.Scheme.Modules

end
