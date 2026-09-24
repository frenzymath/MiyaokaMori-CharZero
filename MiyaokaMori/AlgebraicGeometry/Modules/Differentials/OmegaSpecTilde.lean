import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.OmegaUniversalDerivation
import MiyaokaMori.AlgebraicGeometry.Modules.DerivationsAffineTilde
import MiyaokaMori.AlgebraicGeometry.Modules.DerivationExtAffine
import MiyaokaMori.AlgebraicGeometry.Modules.OmegaOpenImmersionSquare

/-! # `Ω_{Spec A/Spec R}` is the tilde of `Ω_{A/R}`

Let `φ : R → A` be a homomorphism of commutative rings and `f = Spec φ : Spec A → Spec R`. Then
1. `Ω_{Spec A/Spec R} ≅ (Ω_{A/R})~` (`Omega.specTildeIso`), so `Ω_{Spec A/Spec R}` is quasi-coherent;
2. the `A`-linear map `ι₀ : Ω_{A/R} → Γ(Spec A, Ω_{Spec A/Spec R})`, `d a ↦ d_⊤(a)` (with `a` viewed
   as a global section through `A ≅ Γ(Spec A, O)`; `Omega.specKaehlerToΓ`) is bijective
   (Stacks 01UT in the case of `Spec`).

Proof sketch. Two `f⁻¹O_S`-derivations on an affine scheme with values in any `O_X`-module agree
if they agree on global sections. The map `a ↦ d_⊤(a)` is an `R`-derivation `A → Γ(Spec A, Ω)`
(it vanishes on `φ(R)`, since `φ(r)` is in the image of `f.appLE ⊤ ⊤`), so the universal property
of Kähler differentials gives `ι₀`, and the adjunction `tilde ⊣ Γ` gives
`ι : (Ω_{A/R})~ → Ω` with `ι_⊤ ∘ (Ω_{A/R} ≅ Γ((Ω_{A/R})~)) = ι₀`. In the other direction, the
universal derivation `d : A → Ω_{A/R}` lifts to a sheaf derivation `D~ : O → (Ω_{A/R})~` with
`D~_⊤(a) = d a`, and the universal property of `Ω` gives `ρ : Ω → (Ω_{A/R})~` with `ρ(d a) = D~(a)`.
`ρ ≫ ι = 1` is checked by `hom_ext` on the derivations `ι_W(D~_W a)` and `d_W a`, which agree on
global sections; `ι ≫ ρ = 1` reduces through the adjunction to the generators `d a`. Finally `ι`
an isomorphism makes `Γ(ι)` an isomorphism, so `ι₀` is bijective, and the tilde is quasi-coherent.

Reference: Stacks 01UT (the `Spec` case; universal property together with 01UO).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry

local notation "dΩ[" f "]" => Omega.homEquivDerivation f (Omega f) (𝟙 (Omega f))

variable {R A : CommRingCat.{u}} (φ : R ⟶ A)

theorem Omega.smul_Spec_top {A : CommRingCat.{u}} (M : (Spec A).Modules) (a : A) (x : Γ(M, ⊤)) :
    a • x = ((Scheme.ΓSpecIso A).inv.hom a) • x := by
  rw [Scheme.Modules.smul_Spec_def]
  have h1 : (Opens.leTop (⊤ : (Spec A).Opens)).op = 𝟙 _ := Subsingleton.elim _ _
  rw [h1, CategoryTheory.Functor.map_id]
  rfl

/-- The derivation `A → Γ(Spec A, Ω)`, `a ↦ d(a)`, on global sections. -/
def Omega.specΓDerivation :
    (moduleSpecΓFunctor.obj (Omega (Spec.map φ))).Derivation φ :=
  ModuleCat.Derivation.mk
    (fun a => (dΩ[Spec.map φ]).d (X := op ⊤) ((Scheme.ΓSpecIso A).inv.hom a))
    (fun a b => by
      exact (congrArg ((dΩ[Spec.map φ]).d (X := op ⊤)) (map_add (Scheme.ΓSpecIso A).inv.hom a b)).trans
        (map_add _ _ _))
    (fun a b => by
      refine (congrArg ((dΩ[Spec.map φ]).d (X := op ⊤))
        (map_mul (Scheme.ΓSpecIso A).inv.hom a b)).trans ?_
      refine ((dΩ[Spec.map φ]).d_mul (X := op ⊤) _ _).trans ?_
      exact (congrArg₂ (· + ·) (Omega.smul_Spec_top (Omega (Spec.map φ)) a _)
        (Omega.smul_Spec_top (Omega (Spec.map φ)) b _)).symm)
    (fun r => by
      have h1 : (Scheme.ΓSpecIso A).inv.hom (φ.hom r) =
          ((Spec.map φ).appLE ⊤ ⊤ le_top).hom ((Scheme.ΓSpecIso R).inv.hom r) := by
        have h0 := Scheme.ΓSpecIso_inv_naturality φ
        rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE] at h0
        exact congrArg (fun t => t.hom r) h0
      exact (congrArg ((dΩ[Spec.map φ]).d (X := op ⊤)) h1).trans
        (Omega.derivation_appLE (Spec.map φ) _ ⊤ ⊤ le_top _))


/-- `ι₀ : Ω_{A/R} → Γ(Spec A, Ω)`, `d a ↦ d(a)`. -/
def Omega.specKaehlerToΓ :
    CommRingCat.KaehlerDifferential φ ⟶ moduleSpecΓFunctor.obj (Omega (Spec.map φ)) :=
  (Omega.specΓDerivation φ).desc

theorem Omega.specKaehlerToΓ_d (a : A) :
    (Omega.specKaehlerToΓ φ).hom (CommRingCat.KaehlerDifferential.d a) =
      (dΩ[Spec.map φ]).d (X := op ⊤) ((Scheme.ΓSpecIso A).inv.hom a) :=
  (Omega.specΓDerivation φ).desc_d a

/-- `ι : (Ω_{A/R})~ → Ω`, the transpose of `ι₀` under `tilde ⊣ Γ`. -/
def Omega.specTildeHom : tilde (CommRingCat.KaehlerDifferential φ) ⟶ Omega (Spec.map φ) :=
  ((tilde.adjunction (R := A)).homEquiv _ _).symm (Omega.specKaehlerToΓ φ)

/-- The derivation `O_{Spec A} → (Ω_{A/R})~` obtained from the universal derivation. -/
def Omega.specTildeDerivation :
    ((tilde (CommRingCat.KaehlerDifferential φ)).val).Derivation'
      (Scheme.inverseImageStructureMap (Spec.map φ)) :=
  (derivationTildeEquiv φ (CommRingCat.KaehlerDifferential φ)).symm
    (CommRingCat.KaehlerDifferential.D φ)

/-- `ρ : Ω → (Ω_{A/R})~`, from the universal property of `Ω`. -/
def Omega.specTildeInv : Omega (Spec.map φ) ⟶ tilde (CommRingCat.KaehlerDifferential φ) :=
  (Omega.homEquivDerivation (Spec.map φ) _).symm (Omega.specTildeDerivation φ)

theorem Omega.specTildeDerivation_top (a : A) :
    (Omega.specTildeDerivation φ).d (X := op ⊤) ((Scheme.ΓSpecIso A).inv.hom a) =
      (tilde.isoTop (CommRingCat.KaehlerDifferential φ)).hom.hom
        (CommRingCat.KaehlerDifferential.d a) := by
  have h := (derivationTildeEquiv φ (CommRingCat.KaehlerDifferential φ)).apply_symm_apply
    (CommRingCat.KaehlerDifferential.D φ)
  have h2 : (tilde.isoTop (CommRingCat.KaehlerDifferential φ)).inv.hom
      ((Omega.specTildeDerivation φ).d (X := op ⊤) ((Scheme.ΓSpecIso A).inv.hom a)) =
      CommRingCat.KaehlerDifferential.d a :=
    congrArg (fun D' => ModuleCat.Derivation.d (M := CommRingCat.KaehlerDifferential φ) (f := φ) D' a) h
  have h3 := congrArg (tilde.isoTop (CommRingCat.KaehlerDifferential φ)).hom.hom h2
  refine Eq.trans ?_ h3
  exact (congrArg (fun t => t.hom ((Omega.specTildeDerivation φ).d (X := op ⊤)
    ((Scheme.ΓSpecIso A).inv.hom a))) (tilde.isoTop (CommRingCat.KaehlerDifferential φ)).inv_hom_id).symm


theorem Omega.specTildeHom_app_top (x : CommRingCat.KaehlerDifferential φ) :
    (Omega.specTildeHom φ).app ⊤ ((tilde.isoTop (CommRingCat.KaehlerDifferential φ)).hom.hom x) =
      (Omega.specKaehlerToΓ φ).hom x := by
  have h := (tilde.adjunction (R := A)).homEquiv_unit
    (X := CommRingCat.KaehlerDifferential φ) (Y := Omega (Spec.map φ)) (f := Omega.specTildeHom φ)
  have h0 : ((tilde.adjunction (R := A)).homEquiv _ _) (Omega.specTildeHom φ) =
      Omega.specKaehlerToΓ φ := Equiv.apply_symm_apply _ _
  rw [h0] at h
  exact (congrArg (fun t => t.hom x) h).symm


theorem Omega.specTildeHom_app_derivation (W : (Spec A).Opens) (a : Γ(Spec A, W)) :
    (Omega.specTildeHom φ).app W ((Omega.specTildeDerivation φ).d (X := op W) a) =
      (dΩ[Spec.map φ]).d (X := op W) a := by
  have hE : (Omega.specTildeDerivation φ).postcomp (Omega.specTildeHom φ).val = dΩ[Spec.map φ] := by
    apply Omega.derivation_ext_of_isAffine
    intro a'
    obtain ⟨a, rfl⟩ : ∃ a : A, (Scheme.ΓSpecIso A).inv.hom a = a' :=
      ⟨(Scheme.ΓSpecIso A).hom.hom a', congrArg (fun t => t.hom a') (Scheme.ΓSpecIso A).hom_inv_id⟩
    refine Eq.trans ?_ (Omega.specKaehlerToΓ_d φ a)
    refine Eq.trans ?_ (Omega.specTildeHom_app_top φ _)
    exact congrArg ((Omega.specTildeHom φ).app ⊤) (Omega.specTildeDerivation_top φ a)
  exact PresheafOfModules.Derivation.congr_d hE a

theorem Omega.specTildeInv_specTildeHom :
    Omega.specTildeInv φ ≫ Omega.specTildeHom φ = 𝟙 _ := by
  apply Omega.hom_ext
  intro W a
  rw [Scheme.Modules.Hom.comp_app]
  exact (congrArg ((Omega.specTildeHom φ).app W)
    (Omega.homEquivDerivation_symm_d (Spec.map φ) (Omega.specTildeDerivation φ) W a)).trans
    (Omega.specTildeHom_app_derivation φ W a)


theorem Omega.specTildeHom_specTildeInv :
    Omega.specTildeHom φ ≫ Omega.specTildeInv φ = 𝟙 _ := by
  apply ((tilde.adjunction (R := A)).homEquiv (CommRingCat.KaehlerDifferential φ) _).injective
  have h0 : ((tilde.adjunction (R := A)).homEquiv _ _) (Omega.specTildeHom φ) =
      Omega.specKaehlerToΓ φ := Equiv.apply_symm_apply _ _
  refine ((tilde.adjunction (R := A)).homEquiv_naturality_right _ _).trans ?_
  rw [h0]
  refine Eq.trans ?_ ((tilde.adjunction (R := A)).homEquiv_unit
    (X := CommRingCat.KaehlerDifferential φ) (f := 𝟙 _)).symm
  apply CommRingCat.KaehlerDifferential.ext
  intro a
  have h1 : (Omega.specTildeInv φ).app ⊤ ((Omega.specKaehlerToΓ φ).hom
      (CommRingCat.KaehlerDifferential.d a)) =
      (tilde.isoTop (CommRingCat.KaehlerDifferential φ)).hom.hom
        (CommRingCat.KaehlerDifferential.d a) :=
    (congrArg ((Omega.specTildeInv φ).app ⊤) (Omega.specKaehlerToΓ_d φ a)).trans
      ((Omega.homEquivDerivation_symm_d (Spec.map φ) (Omega.specTildeDerivation φ) ⊤ _).trans
        (Omega.specTildeDerivation_top φ a))
  have h2 : (tilde.adjunction (R := A)).unit.app (CommRingCat.KaehlerDifferential φ) ≫
      moduleSpecΓFunctor.map (𝟙 ((tilde.functor A).obj (CommRingCat.KaehlerDifferential φ))) =
      (tilde.isoTop (CommRingCat.KaehlerDifferential φ)).hom := by
    refine (congrArg (fun t => (tilde.adjunction (R := A)).unit.app
      (CommRingCat.KaehlerDifferential φ) ≫ t) (moduleSpecΓFunctor.map_id
        ((tilde.functor A).obj (CommRingCat.KaehlerDifferential φ)))).trans ?_
    exact Category.comp_id _
  refine Eq.trans ?_ (congrArg (fun t => t.hom (CommRingCat.KaehlerDifferential.d a)) h2).symm
  exact h1


/-- The affine case: `Ω_{Spec A/Spec R} ≅ (Ω_{A/R})~`. -/
def Omega.specTildeIso : tilde (CommRingCat.KaehlerDifferential φ) ≅ Omega (Spec.map φ) where
  hom := Omega.specTildeHom φ
  inv := Omega.specTildeInv φ
  hom_inv_id := Omega.specTildeHom_specTildeInv φ
  inv_hom_id := Omega.specTildeInv_specTildeHom φ

theorem Omega.specKaehlerToΓ_bijective : Function.Bijective (Omega.specKaehlerToΓ φ).hom := by
  have h := (tilde.adjunction (R := A)).homEquiv_unit
    (X := CommRingCat.KaehlerDifferential φ) (Y := Omega (Spec.map φ)) (f := Omega.specTildeHom φ)
  have h0 : ((tilde.adjunction (R := A)).homEquiv _ _) (Omega.specTildeHom φ) =
      Omega.specKaehlerToΓ φ := Equiv.apply_symm_apply _ _
  rw [h0] at h
  have : IsIso (Omega.specTildeHom φ) := (Omega.specTildeIso φ).isIso_hom
  have : IsIso (Omega.specKaehlerToΓ φ) := by
    rw [h]
    have h1 : IsIso ((tilde.adjunction (R := A)).unit.app (CommRingCat.KaehlerDifferential φ)) :=
      inferInstance
    have h2 : IsIso (moduleSpecΓFunctor.map (Omega.specTildeHom φ)) := Functor.map_isIso _ _
    exact IsIso.comp_isIso' h1 h2
  exact ConcreteCategory.bijective_of_isIso (Omega.specKaehlerToΓ φ)

instance Omega.spec_isQuasicoherent : (Omega (Spec.map φ)).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent (Spec A).ringCatSheaf).prop_of_iso (Omega.specTildeIso φ)
    (inferInstanceAs (tilde (CommRingCat.KaehlerDifferential φ)).IsQuasicoherent)

end AlgebraicGeometry
