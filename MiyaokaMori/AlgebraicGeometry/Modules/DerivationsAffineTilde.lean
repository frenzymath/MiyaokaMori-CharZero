import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Differentials.RelativeDifferentials
import MiyaokaMori.AlgebraicGeometry.Modules.DerivationExtAffine
import MiyaokaMori.AlgebraicGeometry.Modules.Differentials.DerivationLocalizedModule
import MiyaokaMori.AlgebraicGeometry.Modules.Differentials.InverseImagePresheafSections

/-! # Derivations in the affine case

Derivations in the affine case: for `X = Spec A`, `S = Spec R` and an `A`-module `N`,
`Der_{f⁻¹O_S}(O_X, Ñ) ≃ Der_R(A, N)` (taking global sections).

Proof: additivity, Leibniz and `R`-linearity of the forward map follow from `d_mul`, `d_app` of
sheaf derivations and the `A`-linearity of `isoTop`; injectivity is `Omega.derivation_ext_of_isAffine`
(derivations on an affine scheme are determined by their global sections); for surjectivity an
`R`-derivation `D` is extended pointwise (quotient rule) to the sheaf derivation
`derivationTilde φ N D`, whose global sections give back `D` (`derivationTilde_top`).

Reference: Stacks 01UO.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry

/-- Extension of an `R`-derivation `D : A → N` to a sheaf derivation `O_{Spec A} → Ñ` (pointwise,
by the quotient rule). -/
def derivationTilde {R A : CommRingCat.{u}} (φ : R ⟶ A) (N : ModuleCat.{u} A)
    (D : letI := φ.hom.toAlgebra; letI : Module R N := Module.compHom N φ.hom; Derivation R A N) :
    ((tilde N).val).Derivation' (Scheme.inverseImageStructureMap (Spec.map φ)) :=
  letI := φ.hom.toAlgebra
  letI : Module R N := Module.compHom N φ.hom
  haveI : IsScalarTower R A N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  { d := fun {X} => StructureSheaf.derivationSections D X.unop
    d_mul := fun {X} a b => StructureSheaf.derivationSections_mul D X.unop a b
    d_map := fun {X Y} f x => rfl
    d_app := fun {X} a => by
      obtain ⟨V, e, r, h⟩ := Scheme.inverseImageStructureMap_app_eq_appLE (Spec.map φ) X.unop a
      refine (congrArg (StructureSheaf.derivationSections D X.unop) h).trans ?_
      exact StructureSheaf.derivationSections_comap D V X.unop e r }

theorem derivationTilde_top {R A : CommRingCat.{u}} (φ : R ⟶ A) (N : ModuleCat.{u} A)
    (D : letI := φ.hom.toAlgebra; letI : Module R N := Module.compHom N φ.hom; Derivation R A N)
    (a : A) :
    (derivationTilde φ N D).d (X := op ⊤) ((Scheme.ΓSpecIso A).inv.hom a) =
      (tilde.isoTop N).hom.hom (D a) :=
  letI := φ.hom.toAlgebra
  letI : Module R N := Module.compHom N φ.hom
  haveI : IsScalarTower R A N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  StructureSheaf.derivationSections_algebraMap D ⊤ a

private theorem smul_Spec_top' {A : CommRingCat.{u}} (M : (Spec A).Modules) (a : A) (x : Γ(M, ⊤)) :
    a • x = ((Scheme.ΓSpecIso A).inv.hom a) • x := by
  rw [Scheme.Modules.smul_Spec_def]
  have h1 : (Opens.leTop (⊤ : (Spec A).Opens)).op = 𝟙 _ := Subsingleton.elim _ _
  rw [h1, CategoryTheory.Functor.map_id]
  rfl

section
variable {R A : CommRingCat.{u}} (φ : R ⟶ A) (N : ModuleCat.{u} A)
  (d : ((tilde N).val).Derivation' (Scheme.inverseImageStructureMap (Spec.map φ)))

/-- The global sections `A → N` of a sheaf derivation. -/
private def topFun (a : A) : N :=
  (tilde.isoTop N).inv.hom (d.d (X := op ⊤) ((Scheme.ΓSpecIso A).inv.hom a))

private theorem topFun_add (a b : A) : topFun φ N d (a + b) = topFun φ N d a + topFun φ N d b := by
  refine (congrArg (tilde.isoTop N).inv.hom ((congrArg (d.d (X := op ⊤))
    (map_add (Scheme.ΓSpecIso A).inv.hom a b)).trans (map_add _ _ _))).trans ?_
  exact map_add (tilde.isoTop N).inv.hom _ _

private theorem topFun_mul (a b : A) :
    topFun φ N d (a * b) = a • topFun φ N d b + b • topFun φ N d a := by
  have h : d.d (X := op ⊤) ((Scheme.ΓSpecIso A).inv.hom (a * b)) =
      (a • (show Γ(tilde N, ⊤) from d.d (X := op ⊤) ((Scheme.ΓSpecIso A).inv.hom b)) +
        b • (show Γ(tilde N, ⊤) from d.d (X := op ⊤) ((Scheme.ΓSpecIso A).inv.hom a)) :
        Γ(tilde N, ⊤)) := by
    refine (congrArg (d.d (X := op ⊤)) (map_mul (Scheme.ΓSpecIso A).inv.hom a b)).trans ?_
    refine (d.d_mul (X := op ⊤) _ _).trans ?_
    exact (congrArg₂ (· + ·) (smul_Spec_top' (tilde N) a _) (smul_Spec_top' (tilde N) b _)).symm
  refine (congrArg (tilde.isoTop N).inv.hom h).trans ?_
  refine (map_add (tilde.isoTop N).inv.hom _ _).trans ?_
  exact congrArg₂ (· + ·) (map_smul (tilde.isoTop N).inv.hom a _)
    (map_smul (tilde.isoTop N).inv.hom b _)

private theorem topFun_map (r : R) : topFun φ N d (φ.hom r) = 0 := by
  have h1 : (Scheme.ΓSpecIso A).inv.hom (φ.hom r) =
      ((Spec.map φ).appLE ⊤ ⊤ le_top).hom ((Scheme.ΓSpecIso R).inv.hom r) := by
    have h0 := Scheme.ΓSpecIso_inv_naturality φ
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE] at h0
    exact congrArg (fun t => t.hom r) h0
  refine (congrArg (tilde.isoTop N).inv.hom ((congrArg (d.d (X := op ⊤)) h1).trans
    (Omega.derivation_appLE (F := tilde N) (Spec.map φ) d ⊤ ⊤ le_top _))).trans ?_
  exact map_zero (tilde.isoTop N).inv.hom

end

end AlgebraicGeometry

noncomputable def AlgebraicGeometry.derivationTildeEquiv {R A : CommRingCat.{u}} (φ : R ⟶ A) (N : ModuleCat.{u} A) :
    (let M : PresheafOfModules.{u} ((AlgebraicGeometry.Spec A).presheaf ⋙ CategoryTheory.forget₂ CommRingCat RingCat) :=
        (AlgebraicGeometry.tilde N).val;
      M.Derivation' (AlgebraicGeometry.Scheme.inverseImageStructureMap (AlgebraicGeometry.Spec.map φ))) ≃
      (letI := φ.hom.toAlgebra; letI : Module R N := Module.compHom N φ.hom; Derivation R A N) :=
  -- take global sections: `A ≅ Γ(Spec A, ⊤)` (`ΓSpecIso`), `Γ(Ñ, ⊤) ≅ N` (`tilde.isoTop`);
  -- bijectivity is Stacks 01UO
  Equiv.ofBijective
    (fun d =>
      letI := φ.hom.toAlgebra
      letI : Module R N := Module.compHom N φ.hom
      Derivation.mk'
        { toFun := fun a => (AlgebraicGeometry.tilde.isoTop N).inv.hom
            (d.d (X := Opposite.op ⊤) ((AlgebraicGeometry.Scheme.ΓSpecIso A).inv.hom a))
          map_add' := AlgebraicGeometry.topFun_add φ N d
          map_smul' := fun r a => by
            refine (congrArg (AlgebraicGeometry.topFun φ N d) (Algebra.smul_def r a)).trans ?_
            refine (AlgebraicGeometry.topFun_mul φ N d _ _).trans ?_
            rw [show AlgebraicGeometry.topFun φ N d (algebraMap R A r) = 0 from
              AlgebraicGeometry.topFun_map φ N d r, smul_zero, add_zero]
            rfl }
        (AlgebraicGeometry.topFun_mul φ N d))
    (by
      let _ := φ.hom.toAlgebra
      let _ : Module R N := Module.compHom N φ.hom
      constructor
      · intro d₁ d₂ h
        refine AlgebraicGeometry.Omega.derivation_ext_of_isAffine (F := AlgebraicGeometry.tilde N)
          (AlgebraicGeometry.Spec.map φ) d₁ d₂ fun a' => ?_
        obtain ⟨a, rfl⟩ : ∃ a : A, (AlgebraicGeometry.Scheme.ΓSpecIso A).inv.hom a = a' :=
          ⟨(AlgebraicGeometry.Scheme.ΓSpecIso A).hom.hom a',
            congrArg (fun t => t.hom a') (AlgebraicGeometry.Scheme.ΓSpecIso A).hom_inv_id⟩
        have h2 : AlgebraicGeometry.topFun φ N d₁ a = AlgebraicGeometry.topFun φ N d₂ a :=
          DFunLike.congr_fun h a
        exact ((ConcreteCategory.bijective_of_isIso (AlgebraicGeometry.tilde.isoTop N).inv).1) h2
      · intro D
        refine ⟨AlgebraicGeometry.derivationTilde φ N D, Derivation.ext fun a => ?_⟩
        refine (congrArg (AlgebraicGeometry.tilde.isoTop N).inv.hom
          (AlgebraicGeometry.derivationTilde_top φ N D a)).trans ?_
        exact congrArg (fun t => t.hom (D a)) (AlgebraicGeometry.tilde.isoTop N).hom_inv_id)

end
