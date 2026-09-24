import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.GradedQcAlgebraCategory
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.OfGradedQCAlgebra
import MiyaokaMori.AlgebraicGeometry.Modules.Tensor.ModulesTensorMonoidalIso

/-! # Sections ring homomorphism induced by a morphism of graded quasi-coherent algebras

Helper module for `reesDeformation_isLocallyWeightedPolynomial`. A morphism `φ : S ⟶ T` of graded
quasi-coherent algebras (`GradedQCAlgebra.Hom`: componentwise `φ.app m : S_m ⟶ T_m`, compatible with `mul`/`one`) induces
on every open `U` a ring homomorphism of section rings `S(U) = ⊕_m Γ(U, S_m) → T(U)`, `of_m a ↦ of_m (φ_m a)`
(`DirectSum.toSemiring`), which preserves the grading and the structure maps, and is injective when every `φ_m` is
injective on `Γ(U, ·)` (e.g. when every `φ_m` is a monomorphism, `Mono` is preserved by evaluation). This is the same
construction as `pullbackSectionsRingHom` in `WeightedPolynomialAtlasPullback`, with `pullbackPiece` replaced by
`(φ.app m).app U`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry CategoryTheory.MonoidalCategory

noncomputable section

namespace AlgebraicGeometry.Scheme.GradedQCAlgebra

variable {X : AlgebraicGeometry.Scheme.{u}} {S T : X.GradedQCAlgebra} (φ : S ⟶ T) (U : X.Opens)

/-- `φ_0` sends the graded unit to the graded unit (`φ.map_one`). -/
theorem Hom.app_app_sectionsGOne : (φ.app 0).app U (S.sectionsGOne U) = T.sectionsGOne U :=
  congrArg (fun ψ : 𝟙_ X.Modules ⟶ T.part 0 => ψ.app U (1 : Γ(X, U))) φ.map_one

/-- `φ_0 ∘ S.one = T.one` on sections. -/
theorem Hom.app_app_one_app (r : Γ(X, U)) : (φ.app 0).app U (S.one.app U r) = T.one.app U r :=
  congrArg (fun ψ : 𝟙_ X.Modules ⟶ T.part 0 => ψ.app U r) φ.map_one

/-- `φ` is multiplicative on graded sections (`φ.map_mul` + `tensorHom_tensorSections`). -/
theorem Hom.app_app_sectionsGMul {m n : ℕ} (a : S.sectionsPiece U m) (b : S.sectionsPiece U n) :
    (φ.app (m + n)).app U (S.sectionsGMul U a b) =
      T.sectionsGMul U ((φ.app m).app U a) ((φ.app n).app U b) := by
  have h := congrArg (fun ψ : S.part m ⊗ S.part n ⟶ T.part (m + n) =>
    ψ.app U (AlgebraicGeometry.Scheme.Modules.tensorSections (S.part m) (S.part n) U a b)) (φ.map_mul m n)
  change (φ.app (m + n)).app U ((S.mul m n).app U _) = (T.mul m n).app U ((φ.app m ⊗ₘ φ.app n).app U _) at h
  unfold sectionsGMul
  rw [h]
  congr 1
  exact AlgebraicGeometry.Scheme.Modules.tensorHom_tensorSections (φ.app m) (φ.app n) U a b

/-- The ring homomorphism of section rings `S(U) →+* T(U)` induced by `φ` (componentwise `(φ.app m).app U`). -/
def Hom.sectionsRingHom : S.sectionsRing U →+* T.sectionsRing U :=
  DirectSum.toSemiring
    (fun m => (DirectSum.of (T.sectionsPiece U) m).comp ((φ.app m).app U).hom)
    (by
      show DirectSum.of (T.sectionsPiece U) 0 ((φ.app 0).app U (S.sectionsGOne U)) = 1
      rw [Hom.app_app_sectionsGOne]
      rfl)
    (fun {i j} a b => by
      show DirectSum.of (T.sectionsPiece U) (i + j) ((φ.app (i + j)).app U (S.sectionsGMul U a b)) = _
      rw [Hom.app_app_sectionsGMul]
      exact (DirectSum.of_mul_of _ _).symm)

theorem Hom.sectionsRingHom_of (m : ℕ) (a : S.sectionsPiece U m) :
    φ.sectionsRingHom U (DirectSum.of (S.sectionsPiece U) m a) =
      DirectSum.of (T.sectionsPiece U) m ((φ.app m).app U a) :=
  DirectSum.toSemiring_of _ _ _ m a

theorem Hom.sectionsRingHom_ofPiece (m : ℕ) (a : S.sectionsPiece U m) :
    φ.sectionsRingHom U (S.ofPiece U m a) = T.ofPiece U m ((φ.app m).app U a) :=
  φ.sectionsRingHom_of U m a

/-- Compatibility with the structure maps. -/
theorem Hom.sectionsRingHom_sectionsUnitHom (r : Γ(X, U)) :
    φ.sectionsRingHom U (S.sectionsUnitHom U r) = T.sectionsUnitHom U r := by
  have h1 : S.sectionsUnitHom U r = DirectSum.of (S.sectionsPiece U) 0 (S.one.app U r) := rfl
  have h2 : T.sectionsUnitHom U r = DirectSum.of (T.sectionsPiece U) 0 (T.one.app U r) := rfl
  rw [h1, h2, φ.sectionsRingHom_of U 0 (S.one.app U r), φ.app_app_one_app U r]

/-- The induced ring homomorphism preserves the grading. -/
theorem Hom.sectionsRingHom_mem {m : ℕ} {a : S.sectionsRing U} (ha : a ∈ S.sectionsGrading U m) :
    φ.sectionsRingHom U a ∈ T.sectionsGrading U m := by
  obtain ⟨a', rfl⟩ := ha
  exact ⟨(φ.app m).app U a', (φ.sectionsRingHom_of U m a').symm⟩

/-- The induced ring homomorphism as a graded ring homomorphism. -/
def Hom.sectionsGradedRingHom : S.sectionsGrading U →+*ᵍ T.sectionsGrading U where
  toRingHom := φ.sectionsRingHom U
  map_mem := fun ha => φ.sectionsRingHom_mem U ha

theorem Hom.sectionsGradedRingHom_apply (a : S.sectionsRing U) :
    φ.sectionsGradedRingHom U a = φ.sectionsRingHom U a := rfl

/-- The underlying additive map is `DirectSum.map` of the componentwise maps. -/
theorem Hom.sectionsRingHom_toAddMonoidHom :
    (φ.sectionsRingHom U).toAddMonoidHom = DirectSum.map (fun m => ((φ.app m).app U).hom) :=
  DirectSum.addHom_ext fun m a =>
    (φ.sectionsRingHom_of U m a).trans (DirectSum.map_of (fun m => ((φ.app m).app U).hom) m a).symm

/-- Components of the image: `(φ(x))_m = φ_m (x_m)`. -/
theorem Hom.sectionsRingHom_component (m : ℕ) (x : S.sectionsRing U) :
    T.component U m (φ.sectionsRingHom U x) = (φ.app m).app U (S.component U m x) := by
  have hx : (φ.sectionsRingHom U).toAddMonoidHom x = DirectSum.map (fun m => ((φ.app m).app U).hom) x :=
    congrArg (fun ψ => ψ x) (φ.sectionsRingHom_toAddMonoidHom U)
  exact (congrArg (fun (y : DirectSum ℕ (T.sectionsPiece U)) => y m) hx).trans
    (DirectSum.map_apply (fun m => ((φ.app m).app U).hom) m x)

/-- If every `φ_m` is injective on `Γ(U, ·)`, the induced ring homomorphism is injective. -/
theorem Hom.sectionsRingHom_injective (h : ∀ m, Function.Injective ((φ.app m).app U)) :
    Function.Injective (φ.sectionsRingHom U) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  have hext : ∀ y : DirectSum ℕ (S.sectionsPiece U), (∀ m, y m = 0) → y = 0 := fun y hy =>
    DirectSum.ext fun m => (hy m).trans (DirectSum.zero_apply m).symm
  refine hext x fun m => ?_
  have h1 := φ.sectionsRingHom_component U m x
  rw [hx] at h1
  have h0 : T.component U m (0 : T.sectionsRing U) = 0 := DirectSum.zero_apply m
  rw [h0] at h1
  exact h m (h1.symm.trans (map_zero _).symm)

end AlgebraicGeometry.Scheme.GradedQCAlgebra

end
