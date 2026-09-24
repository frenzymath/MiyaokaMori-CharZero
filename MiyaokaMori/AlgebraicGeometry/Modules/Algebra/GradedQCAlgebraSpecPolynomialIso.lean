import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.LocallyFree.SpecModulesFreeOfBasis
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedQCAlgebraPieceBasis
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.GradedQcAlgebraCategory
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedPolynomialQCAlgebra
import MiyaokaMori.AlgebraicGeometry.Modules.FreeTensorFreeIso
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorSectionsCoherence
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorMonoidalIso

/-! # A graded algebra on `Spec R` with polynomial section ring is a weighted polynomial algebra

Let `R` be a commutative ring and `T` a graded quasi-coherent algebra on `Spec R` whose global section
ring satisfies `T.sectionsRing ⊤ ≃+* MvPolynomial σ Γ(Spec R, ⊤)` (graded pieces ↔ weighted homogeneous
components of weight `w`, structure map ↔ constants `C`; the data of a `WeightedPolynomialAtlas` on the chart
`⊤`). Then `T` is isomorphic, as a graded quasi-coherent algebra, to the weighted polynomial algebra
`weightedPolynomialQCAlgebra (Spec R) w hw` (`exists_iso_weightedPolynomialQCAlgebra_of_sectionsRing_equiv`;
the statement allows a chart `V` with the hypothesis `V = ⊤`, so that callers can feed a chart of an atlas
directly).

Proof:
1. Each graded piece `Γ(⊤, T_m)` has a `Γ(Spec R, ⊤)`-basis `polyGen m d` (the `m`-th component of the
   preimage of the monomial `X^d` of weight `m`, `GradedQCAlgebraPieceBasis.lean`), transported along
   `ΓSpecIso : Γ(Spec R, ⊤) ≅ R` to an `R`-basis with `Basis.mapCoeffs` (`smul_Spec_def` says the two scalar
   actions agree).
2. `T_m` is quasi-coherent (`T.quasicoherent m`), so the canonical morphism
   `free (weightedMonomials w m) ⟶ T_m` ("generator ↦ basis vector") is an isomorphism (via Mathlib's
   `fromTildeΓ`). Call it `polyPieceHom m`, with isomorphism `polyPieceIso m`.
3. Compatibility with multiplication: both sides are morphisms `free I ⊗ free J ⟶ T_{m+n}`; via
   `freeTensorFreeIso` they become morphisms out of `free (I × J)`, compared on generators `ιFree (d, d')`
   (`Cofan.IsColimit.hom_ext`); `ιFree (d,d') ≫ freeTensorFreeIso.inv = (λ_).inv ≫ (ιFree d ⊗ ιFree d')`, and
   morphisms out of the structure sheaf are determined by the image of `1` on `⊤` (`unitHomEquivTop`), so
   the identity reduces to the section identity `T.mul (polyGen m d ⊗ polyGen n d') = polyGen (m+n) (d+d')`,
   i.e. `sectionsGMul_polyGen` (`leftUnitor_app_tensorSections`, `tensorHom_tensorSections` compute `(λ_).inv`
   and `⊗ₘ` on section pairings).
4. Compatibility with the unit: `oneHom = ιFree 0`, reducing to `polyGen 0 0 = sectionsGOne` (`polyGen_zero`).
5. Piecewise inverses give the `Hom` in the other direction (compatibility from 3, 4 and `Iso.hom_inv_id`);
   the two `Hom`s are inverse to each other (piecewise `Iso.hom_inv_id`).

Reference: the local model on fibres is a weighted polynomial algebra (§2 of the paper); Stacks 01I7
(quasi-coherent sheaves on affine schemes are determined by global sections).
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped AlgebraicGeometry CategoryTheory.MonoidalCategory

noncomputable section

namespace AlgebraicGeometry.Scheme.GradedQCAlgebra

attribute [local instance] pieceModule

/-! ## Assembly on `Spec R` -/

/-- The section `ιFree i (1)` on `⊤` of the `i`-th generator of the free sheaf. -/
def _root_.AlgebraicGeometry.Scheme.Modules.freeGen {X : Scheme.{u}} {I : Type u} (i : I) :
    Γ((SheafOfModules.free (R := X.ringCatSheaf) I : X.Modules), ⊤) :=
  Scheme.Modules.Hom.app (M := (SheafOfModules.unit X.ringCatSheaf : X.Modules))
    (N := (SheafOfModules.free (R := X.ringCatSheaf) I : X.Modules))
    (SheafOfModules.ιFree (R := X.ringCatSheaf) i) ⊤ (1 : Γ(X, ⊤))

section SpecAssembly

variable {R : CommRingCat.{u}} (T : (Spec R).GradedQCAlgebra) {σ : Type u} (w : σ → ℕ)
  (e : T.sectionsRing ⊤ ≃+* MvPolynomial σ Γ(Spec R, ⊤))
  (he : ∀ (m : ℕ) (a : T.sectionsRing ⊤),
    a ∈ T.sectionsGrading ⊤ m ↔ (e a).IsWeightedHomogeneous w m)
  (hu : ∀ r : Γ(Spec R, ⊤), e (T.sectionsUnitHom ⊤ r) = MvPolynomial.C r)

/-- The `R`-module structure on `Γ(⊤, T_m)` (Mathlib's instance is on `Γ(T.part m, ⊤)`). -/
local instance pieceModuleR (m : ℕ) : Module R (T.sectionsPiece ⊤ m) :=
  inferInstanceAs (Module R Γ(T.part m, ⊤))

theorem ΓSpecIso_hom_smul (m : ℕ) (c : Γ(Spec R, ⊤)) (x : T.sectionsPiece ⊤ m) :
    ((Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv c) • x = c • x := by
  have h := Scheme.Modules.smul_Spec_def (M := T.part m) (U := ⊤) ((Scheme.ΓSpecIso R).hom c)
    (x : Γ(T.part m, ⊤))
  refine h.trans ?_
  have h1 : (Scheme.ΓSpecIso R).inv ((Scheme.ΓSpecIso R).hom c) = c := by
    rw [← CommRingCat.comp_apply, Iso.hom_inv_id]; rfl
  rw [h1, show (⊤ : (Spec R).Opens).leTop = 𝟙 _ from rfl, op_id, (Spec R).presheaf.map_id]
  rfl

/-- The `R`-basis of `Γ(⊤, T_m)` (coefficients transported to `R` along `ΓSpecIso`). -/
def pieceBasisR (m : ℕ) : Module.Basis (weightedMonomials w m) R (T.sectionsPiece ⊤ m) :=
  (pieceBasis T ⊤ w e he hu m).mapCoeffs (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv
    (ΓSpecIso_hom_smul T m)

theorem pieceBasisR_apply (m : ℕ) (d : weightedMonomials w m) :
    pieceBasisR T w e he hu m d = polyGen T ⊤ w e m d := by
  unfold pieceBasisR
  rw [Module.Basis.mapCoeffs_apply, pieceBasis_apply]

/-- The canonical morphism from the free sheaf to the `m`-th piece: generator `d ↦ polyGen m d`. -/
def polyPieceHom (m : ℕ) :
    (SheafOfModules.free (R := (Spec R).ringCatSheaf) (weightedMonomials w m) : (Spec R).Modules) ⟶
      T.part m :=
  Scheme.Modules.freeHomOfTopSections (T.part m) (fun d => pieceBasisR T w e he hu m d)

theorem isIso_polyPieceHom (m : ℕ) : IsIso (polyPieceHom T w e he hu m) :=
  haveI := T.quasicoherent m
  Scheme.Modules.isIso_freeHomOfTopSections_basis (T.part m) (pieceBasisR T w e he hu m)

theorem polyPieceHom_app_top_ιFree (m : ℕ) (d : weightedMonomials w m) :
    Scheme.Modules.Hom.app (polyPieceHom T w e he hu m) ⊤ (Scheme.Modules.freeGen d) =
      polyGen T ⊤ w e m d :=
  (Scheme.Modules.freeHomOfTopSections_app_top_ιFree (T.part m) _ d).trans
    (pieceBasisR_apply T w e he hu m d)


/-! ### Compatibility with multiplication and unit -/

/-- Morphisms out of the structure sheaf are determined by the image of `1` on `⊤`. -/
theorem unit_hom_ext' {X : Scheme.{u}} {M : X.Modules}
    {f g : (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⟶ M}
    (h : Scheme.Modules.Hom.app f ⊤ (1 : Γ(X, ⊤)) = Scheme.Modules.Hom.app g ⊤ (1 : Γ(X, ⊤))) :
    f = g :=
  (Scheme.Modules.unitHomEquivTop M).injective h

/-- `tensorHom_tensorSections`, written with `Hom.app`. -/
theorem tensorHom_app_tensorSections {X : Scheme.{u}} {A B A' B' : X.Modules}
    (φ : A ⟶ A') (ψ : B ⟶ B') (U : X.Opens) (a : Γ(A, U)) (b : Γ(B, U)) :
    Scheme.Modules.Hom.app (MonoidalCategoryStruct.tensorHom (C := X.Modules) φ ψ) U
        (Scheme.Modules.tensorSections A B U a b) =
      Scheme.Modules.tensorSections A' B' U (φ.app U a) (ψ.app U b) :=
  Scheme.Modules.tensorHom_tensorSections φ ψ U a b

theorem leftUnitor_inv_app_top_one {X : Scheme.{u}} :
    Scheme.Modules.Hom.app (λ_ (𝟙_ X.Modules)).inv ⊤ (1 : Γ(X, ⊤)) =
      Scheme.Modules.tensorSections (𝟙_ X.Modules) (𝟙_ X.Modules) ⊤ (1 : Γ(X, ⊤)) (1 : Γ(X, ⊤)) := by
  have h1 : Scheme.Modules.Hom.app (λ_ (𝟙_ X.Modules)).hom ⊤
      (Scheme.Modules.tensorSections (𝟙_ X.Modules) (𝟙_ X.Modules) ⊤ (1 : Γ(X, ⊤)) (1 : Γ(X, ⊤))) =
      (1 : Γ(X, ⊤)) :=
    (Scheme.Modules.leftUnitor_app_tensorSections (X := X) (𝟙_ X.Modules) ⊤
      (1 : Γ(X, ⊤)) (1 : Γ(X, ⊤))).trans (one_smul Γ(X, ⊤) (1 : Γ(X, ⊤)))
  have h2 := congrArg (fun k => Scheme.Modules.Hom.app k ⊤
    (Scheme.Modules.tensorSections (𝟙_ X.Modules) (𝟙_ X.Modules) ⊤ (1 : Γ(X, ⊤)) (1 : Γ(X, ⊤))))
    (λ_ (𝟙_ X.Modules)).hom_inv_id
  change Scheme.Modules.Hom.app (λ_ (𝟙_ X.Modules)).inv ⊤
    (Scheme.Modules.Hom.app (λ_ (𝟙_ X.Modules)).hom ⊤
      (Scheme.Modules.tensorSections (𝟙_ X.Modules) (𝟙_ X.Modules) ⊤ (1 : Γ(X, ⊤)) (1 : Γ(X, ⊤)))) =
    Scheme.Modules.tensorSections (𝟙_ X.Modules) (𝟙_ X.Modules) ⊤ (1 : Γ(X, ⊤)) (1 : Γ(X, ⊤)) at h2
  rw [h1] at h2
  exact h2

theorem ιFree_comp_freeTensorFreeIso_inv {X : Scheme.{u}} {I J : Type u} (p : I × J) :
    SheafOfModules.ιFree (R := X.ringCatSheaf) p ≫
        (Scheme.Modules.freeTensorFreeIso (X := X) I J).inv =
      (λ_ (𝟙_ X.Modules)).inv ≫
        MonoidalCategoryStruct.tensorHom (C := X.Modules)
          (SheafOfModules.ιFree (R := X.ringCatSheaf) p.1)
          (SheafOfModules.ιFree (R := X.ringCatSheaf) p.2) := by
  rw [Scheme.Modules.freeTensorFreeIso_inv]
  exact Sigma.ι_desc _ _

/-- Adding monomial exponents of weights `m` and `n`. -/
def addMonomial {m n : ℕ} (p : weightedMonomials w m × weightedMonomials w n) :
    weightedMonomials w (m + n) :=
  ⟨p.1.1 + p.2.1, by simp [map_add, p.1.2, p.2.2]⟩

/-- **Compatibility with multiplication on generators.** -/
theorem polyPieceHom_mul (m n : ℕ) :
    MonoidalCategoryStruct.tensorHom (C := (Spec R).Modules)
        (polyPieceHom T w e he hu m) (polyPieceHom T w e he hu n) ≫ T.mul m n =
      Scheme.weightedPolynomialQCAlgebra.mulHom (Spec R) w m n ≫ polyPieceHom T w e he hu (m + n) := by
  refine (Iso.cancel_iso_inv_left (Scheme.Modules.freeTensorFreeIso (X := Spec R)
    (weightedMonomials w m) (weightedMonomials w n)) _ _).mp ?_
  refine Cofan.IsColimit.hom_ext (SheafOfModules.isColimitFreeCofan (R := (Spec R).ringCatSheaf)
    (weightedMonomials w m × weightedMonomials w n)) _ _ (fun p => ?_)
  rw [SheafOfModules.freeCofan_inj]
  have hR : SheafOfModules.ιFree (R := (Spec R).ringCatSheaf) p ≫
      (Scheme.Modules.freeTensorFreeIso (X := Spec R) (weightedMonomials w m) (weightedMonomials w n)).inv ≫
        (Scheme.weightedPolynomialQCAlgebra.mulHom (Spec R) w m n ≫ polyPieceHom T w e he hu (m + n)) =
      SheafOfModules.ιFree (R := (Spec R).ringCatSheaf) (addMonomial w p) ≫
        polyPieceHom T w e he hu (m + n) := by
    unfold Scheme.weightedPolynomialQCAlgebra.mulHom
    exact (congrArg (fun k => SheafOfModules.ιFree p ≫ k) (Iso.inv_hom_id_assoc _ _)).trans
      (SheafOfModules.ιFree_freeMap_assoc _ _ _)
  have hL : SheafOfModules.ιFree (R := (Spec R).ringCatSheaf) p ≫
      (Scheme.Modules.freeTensorFreeIso (X := Spec R) (weightedMonomials w m) (weightedMonomials w n)).inv ≫
        (MonoidalCategoryStruct.tensorHom (C := (Spec R).Modules)
          (polyPieceHom T w e he hu m) (polyPieceHom T w e he hu n) ≫ T.mul m n) =
      (λ_ (𝟙_ (Spec R).Modules)).inv ≫
        MonoidalCategoryStruct.tensorHom (C := (Spec R).Modules)
          (SheafOfModules.ιFree (R := (Spec R).ringCatSheaf) p.1)
          (SheafOfModules.ιFree (R := (Spec R).ringCatSheaf) p.2) ≫
        (MonoidalCategoryStruct.tensorHom (C := (Spec R).Modules)
          (polyPieceHom T w e he hu m) (polyPieceHom T w e he hu n) ≫ T.mul m n) := by
    refine (Category.assoc _ _ _).symm.trans ?_
    refine Eq.trans ?_ (Category.assoc _ _ _)
    exact congrArg (fun k => k ≫ (MonoidalCategoryStruct.tensorHom (C := (Spec R).Modules)
      (polyPieceHom T w e he hu m) (polyPieceHom T w e he hu n) ≫ T.mul m n))
      (ιFree_comp_freeTensorFreeIso_inv p)
  refine hL.trans (Eq.trans ?_ hR.symm)
  apply unit_hom_ext'
  change Scheme.Modules.Hom.app (T.mul m n) ⊤
      (Scheme.Modules.Hom.app (MonoidalCategoryStruct.tensorHom (C := (Spec R).Modules)
          (polyPieceHom T w e he hu m) (polyPieceHom T w e he hu n)) ⊤
        (Scheme.Modules.Hom.app (MonoidalCategoryStruct.tensorHom (C := (Spec R).Modules)
            (SheafOfModules.ιFree (R := (Spec R).ringCatSheaf) p.1)
            (SheafOfModules.ιFree (R := (Spec R).ringCatSheaf) p.2)) ⊤
          (Scheme.Modules.Hom.app (λ_ (𝟙_ (Spec R).Modules)).inv ⊤ (1 : Γ(Spec R, ⊤))))) =
    Scheme.Modules.Hom.app (polyPieceHom T w e he hu (m + n)) ⊤
      (Scheme.Modules.freeGen (addMonomial w p))
  have s1 : Scheme.Modules.Hom.app (MonoidalCategoryStruct.tensorHom (C := (Spec R).Modules)
        (SheafOfModules.ιFree (R := (Spec R).ringCatSheaf) p.1)
        (SheafOfModules.ιFree (R := (Spec R).ringCatSheaf) p.2)) ⊤
      (Scheme.Modules.tensorSections (𝟙_ (Spec R).Modules) (𝟙_ (Spec R).Modules) ⊤
        (1 : Γ(Spec R, ⊤)) (1 : Γ(Spec R, ⊤))) =
      Scheme.Modules.tensorSections _ _ ⊤ (Scheme.Modules.freeGen p.1) (Scheme.Modules.freeGen p.2) :=
    tensorHom_app_tensorSections _ _ ⊤ _ _
  have s2 : Scheme.Modules.Hom.app (MonoidalCategoryStruct.tensorHom (C := (Spec R).Modules)
        (polyPieceHom T w e he hu m) (polyPieceHom T w e he hu n)) ⊤
      (Scheme.Modules.tensorSections _ _ ⊤ (Scheme.Modules.freeGen p.1) (Scheme.Modules.freeGen p.2)) =
      Scheme.Modules.tensorSections (T.part m) (T.part n) ⊤
        (Scheme.Modules.Hom.app (polyPieceHom T w e he hu m) ⊤ (Scheme.Modules.freeGen p.1))
        (Scheme.Modules.Hom.app (polyPieceHom T w e he hu n) ⊤ (Scheme.Modules.freeGen p.2)) :=
    tensorHom_app_tensorSections _ _ ⊤ _ _
  refine Eq.trans (congrArg (fun x => Scheme.Modules.Hom.app (T.mul m n) ⊤
    (Scheme.Modules.Hom.app (MonoidalCategoryStruct.tensorHom (C := (Spec R).Modules)
      (polyPieceHom T w e he hu m) (polyPieceHom T w e he hu n)) ⊤
      (Scheme.Modules.Hom.app (MonoidalCategoryStruct.tensorHom (C := (Spec R).Modules)
        (SheafOfModules.ιFree (R := (Spec R).ringCatSheaf) p.1)
        (SheafOfModules.ιFree (R := (Spec R).ringCatSheaf) p.2)) ⊤ x)))
    (leftUnitor_inv_app_top_one (X := Spec R))) ?_
  refine Eq.trans (congrArg (fun x => Scheme.Modules.Hom.app (T.mul m n) ⊤
    (Scheme.Modules.Hom.app (MonoidalCategoryStruct.tensorHom (C := (Spec R).Modules)
      (polyPieceHom T w e he hu m) (polyPieceHom T w e he hu n)) ⊤ x)) s1) ?_
  refine Eq.trans (congrArg (fun x => Scheme.Modules.Hom.app (T.mul m n) ⊤ x) s2) ?_
  refine Eq.trans (congrArg (fun x => Scheme.Modules.Hom.app (T.mul m n) ⊤ x)
    (congrArg₂ (Scheme.Modules.tensorSections (T.part m) (T.part n) ⊤)
      (polyPieceHom_app_top_ιFree T w e he hu m p.1)
      (polyPieceHom_app_top_ιFree T w e he hu n p.2))) ?_
  exact (sectionsGMul_polyGen T ⊤ w e he p.1 p.2).trans
    (polyPieceHom_app_top_ιFree T w e he hu (m + n) (addMonomial w p)).symm

/-- **Compatibility with the unit.** -/
theorem polyPieceHom_one :
    Scheme.weightedPolynomialQCAlgebra.oneHom (Spec R) w ≫ polyPieceHom T w e he hu 0 = T.one := by
  apply unit_hom_ext'
  change Scheme.Modules.Hom.app (polyPieceHom T w e he hu 0) ⊤
      (Scheme.Modules.freeGen (⟨0, map_zero _⟩ : weightedMonomials w 0)) =
    Scheme.Modules.Hom.app T.one ⊤ (1 : Γ(Spec R, ⊤))
  rw [polyPieceHom_app_top_ιFree]
  exact polyGen_zero T ⊤ w e he hu

/-! ### Assembly into an isomorphism of graded algebras -/

private theorem hom_ext' {X : Scheme.{u}} {S S' : X.GradedQCAlgebra}
    (φ ψ : GradedQCAlgebra.Hom S S') (h : ∀ m, φ.app m = ψ.app m) : φ = ψ := by
  cases φ with
  | mk φ hmul hone =>
    cases ψ with
    | mk ψ hmul' hone' =>
      simp only at h
      cases funext h
      rfl

/-- The isomorphism between the free sheaf and the `m`-th piece. -/
def polyPieceIso (m : ℕ) :
    (SheafOfModules.free (R := (Spec R).ringCatSheaf) (weightedMonomials w m) : (Spec R).Modules) ≅
      T.part m :=
  @asIso _ _ _ _ (polyPieceHom T w e he hu m) (isIso_polyPieceHom T w e he hu m)

theorem polyPieceIso_hom (m : ℕ) : (polyPieceIso T w e he hu m).hom = polyPieceHom T w e he hu m := rfl

theorem polyHom_mul_inv (m n : ℕ) :
    T.mul m n ≫ (polyPieceIso T w e he hu (m + n)).inv =
      MonoidalCategoryStruct.tensorHom (C := (Spec R).Modules)
        (polyPieceIso T w e he hu m).inv (polyPieceIso T w e he hu n).inv ≫
        Scheme.weightedPolynomialQCAlgebra.mulHom (Spec R) w m n := by
  have h1 : MonoidalCategoryStruct.tensorHom (C := (Spec R).Modules)
      (polyPieceIso T w e he hu m).inv (polyPieceIso T w e he hu n).inv ≫
      MonoidalCategoryStruct.tensorHom (C := (Spec R).Modules)
        (polyPieceHom T w e he hu m) (polyPieceHom T w e he hu n) = 𝟙 _ := by
    refine (MonoidalCategory.tensorHom_comp_tensorHom _ _ _ _).trans ?_
    refine Eq.trans ?_ (MonoidalCategory.id_tensorHom_id _ _)
    exact congrArg₂ (MonoidalCategoryStruct.tensorHom (C := (Spec R).Modules))
      (Iso.inv_hom_id (polyPieceIso T w e he hu m)) (Iso.inv_hom_id (polyPieceIso T w e he hu n))
  have h2 := polyPieceHom_mul T w e he hu m n
  have h3 : polyPieceHom T w e he hu (m + n) ≫ (polyPieceIso T w e he hu (m + n)).inv = 𝟙 _ :=
    Iso.hom_inv_id (polyPieceIso T w e he hu (m + n))
  refine Eq.trans ((congrArg (fun k => k ≫ (T.mul m n ≫ (polyPieceIso T w e he hu (m + n)).inv)) h1).trans
    (Category.id_comp _)).symm ?_
  refine (Category.assoc _ _ _).trans ?_
  refine congrArg (fun k => MonoidalCategoryStruct.tensorHom (C := (Spec R).Modules)
    (polyPieceIso T w e he hu m).inv (polyPieceIso T w e he hu n).inv ≫ k) ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (fun k => k ≫ (polyPieceIso T w e he hu (m + n)).inv) h2).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun k => Scheme.weightedPolynomialQCAlgebra.mulHom (Spec R) w m n ≫ k) h3).trans ?_
  exact Category.comp_id _

theorem polyHom_one_inv :
    T.one ≫ (polyPieceIso T w e he hu 0).inv = Scheme.weightedPolynomialQCAlgebra.oneHom (Spec R) w := by
  have h3 : polyPieceHom T w e he hu 0 ≫ (polyPieceIso T w e he hu 0).inv = 𝟙 _ :=
    Iso.hom_inv_id (polyPieceIso T w e he hu 0)
  refine (congrArg (fun k => k ≫ (polyPieceIso T w e he hu 0).inv) (polyPieceHom_one T w e he hu).symm).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (fun k => Scheme.weightedPolynomialQCAlgebra.oneHom (Spec R) w ≫ k) h3).trans ?_
  exact Category.comp_id _

variable [Finite σ] (hw : ∀ i, 0 < w i)

/-- The weighted polynomial algebra `→ T`. -/
def polyHom : GradedQCAlgebra.Hom (Scheme.weightedPolynomialQCAlgebra (Spec R) w hw) T :=
  ⟨fun m => polyPieceHom T w e he hu m, fun m n => (polyPieceHom_mul T w e he hu m n).symm,
    polyPieceHom_one T w e he hu⟩

/-- `T →` the weighted polynomial algebra (piecewise inverses). -/
def polyHomInv : GradedQCAlgebra.Hom T (Scheme.weightedPolynomialQCAlgebra (Spec R) w hw) :=
  ⟨fun m => (polyPieceIso T w e he hu m).inv, polyHom_mul_inv T w e he hu, polyHom_one_inv T w e he hu⟩

/-- **A graded quasi-coherent algebra on `Spec R` whose section ring is a weighted polynomial ring is
isomorphic to the weighted polynomial algebra.** -/
def polyIso : T ≅ Scheme.weightedPolynomialQCAlgebra (Spec R) w hw where
  hom := polyHomInv T w e he hu hw
  inv := polyHom T w e he hu hw
  hom_inv_id := hom_ext' _ _ (fun m => Iso.inv_hom_id (polyPieceIso T w e he hu m))
  inv_hom_id := hom_ext' _ _ (fun m => Iso.hom_inv_id (polyPieceIso T w e he hu m))

end SpecAssembly

/-- **Main theorem (the form with `V = ⊤`).** -/
theorem exists_iso_weightedPolynomialQCAlgebra_of_sectionsRing_equiv
    {R : CommRingCat.{u}} (T : (Spec R).GradedQCAlgebra) {σ : Type u} [Finite σ] (w : σ → ℕ)
    (hw : ∀ i, 0 < w i) (V : (Spec R).Opens) (hV : V = ⊤)
    (e : T.sectionsRing V ≃+* MvPolynomial σ Γ(Spec R, V))
    (he : ∀ (m : ℕ) (a : T.sectionsRing V),
      a ∈ T.sectionsGrading V m ↔ (e a).IsWeightedHomogeneous w m)
    (hu : ∀ r : Γ(Spec R, V), e (T.sectionsUnitHom V r) = MvPolynomial.C r) :
    Nonempty (T ≅ Scheme.weightedPolynomialQCAlgebra (Spec R) w hw) := by
  subst hV
  exact ⟨polyIso T w e he hu hw⟩

end AlgebraicGeometry.Scheme.GradedQCAlgebra

end
