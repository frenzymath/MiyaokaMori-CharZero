import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Proj.RelativeProj.GradedQcAlgebraCategory
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.GradedQcAlgebraSectionsRing

/-! # Isomorphic graded algebras have isomorphic relative Proj, step 1: sections-level graded ring homomorphism

A morphism `φ : S ⟶ T` of graded quasi-coherent algebras (`GradedQCAlgebra.Hom`: a family of
`O_X`-linear maps `S_m ⟶ T_m` compatible with multiplication and unit) induces, on every open `U`,
a **graded ring homomorphism** of the sections rings
`A_S(U) = ⊕_m Γ(U, S_m) → A_T(U) = ⊕_m Γ(U, T_m)` (`GradedQCAlgebra.Hom.sectionsGradedHom`).

Contents:
* `Hom.homPiece φ U m` — the additive map `Γ(U, S_m) →+ Γ(U, T_m)`;
* `Hom.homPiece_gOne` / `Hom.homPiece_gMul` — `φ.map_one` / `φ.map_mul` evaluated on sections
  (via `Modules.tensorHom_tensorSections`: `(φ_m ⊗ φ_n)(a ⊗ b) = φ_m a ⊗ φ_n b`);
* `Hom.sectionsHom φ U : A_S(U) →+* A_T(U)` (`DirectSum.toSemiring`) and `sectionsHom_of`;
* `Hom.sectionsGradedHom φ U : S.sectionsGrading U →+*ᵍ T.sectionsGrading U`;
* functoriality `sectionsGradedHom_id`, `sectionsGradedHom_comp`;
* naturality with respect to restriction `sectionsGradedHom_restrict`
  (from the naturality of the sheaf morphisms `φ.app m`);
* compatibility with the structure map `sectionsGradedHom_sectionsUnit` (from `φ.map_one`).

Source: Stacks 01NP (functoriality of relative Proj) — the algebra-level input; the paper
uses it implicitly whenever "S ≅ T as graded O_X-algebras" is turned into "Proj_X S ≅ Proj_X T".
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

open scoped CategoryTheory.MonoidalCategory DirectSum

namespace AlgebraicGeometry.Scheme.GradedQCAlgebra

variable {X : AlgebraicGeometry.Scheme.{u}} {S T : X.GradedQCAlgebra}

/-- `φ` on the `m`-th graded piece over `U`, as an additive map `Γ(U, S_m) →+ Γ(U, T_m)`. -/
def Hom.homPiece (φ : S ⟶ T) (U : X.Opens) (m : ℕ) : S.sectionsPiece U m →+ T.sectionsPiece U m :=
  ((φ.app m).val.app (op U)).hom.toAddMonoidHom

theorem Hom.homPiece_apply (φ : S ⟶ T) (U : X.Opens) (m : ℕ) (a : S.sectionsPiece U m) :
    φ.homPiece U m a = (φ.app m).app U a := rfl

/-- `φ.map_one` on sections: `φ_0 (1_S) = 1_T`. -/
theorem Hom.homPiece_gOne (φ : S ⟶ T) (U : X.Opens) :
    φ.homPiece U 0 (S.sectionsGOne U) = T.sectionsGOne U := by
  have h := congrArg (fun (α : 𝟙_ X.Modules ⟶ T.part 0) => α.app U (1 : Γ(X, U))) φ.map_one
  exact h

/-- `φ.map_mul` on sections: `φ_{m+n} (a · b) = φ_m a · φ_n b`. -/
theorem Hom.homPiece_gMul (φ : S ⟶ T) (U : X.Opens) {m n : ℕ}
    (a : S.sectionsPiece U m) (b : S.sectionsPiece U n) :
    φ.homPiece U (m + n) (S.sectionsGMul U a b) =
      T.sectionsGMul U (φ.homPiece U m a) (φ.homPiece U n b) := by
  have h := congrArg
    (fun (α : CategoryTheory.MonoidalCategoryStruct.tensorObj (C := X.Modules)
        (S.part m) (S.part n) ⟶ T.part (m + n)) =>
      α.app U (AlgebraicGeometry.Scheme.Modules.tensorSections (S.part m) (S.part n) U a b))
    (φ.map_mul m n)
  have hT := AlgebraicGeometry.Scheme.Modules.tensorHom_tensorSections (φ.app m) (φ.app n) U a b
  refine h.trans ?_
  show (T.mul m n).app U
      ((CategoryTheory.MonoidalCategoryStruct.tensorHom (C := X.Modules) (φ.app m) (φ.app n)).val.app
        (op U) (AlgebraicGeometry.Scheme.Modules.tensorSections (S.part m) (S.part n) U a b)) = _
  rw [hT]
  rfl

/-- The ring homomorphism `A_S(U) → A_T(U)` induced by `φ` (piecewise `φ_m`). -/
def Hom.sectionsHom (φ : S ⟶ T) (U : X.Opens) : S.sectionsRing U →+* T.sectionsRing U :=
  DirectSum.toSemiring
    (fun m => (DirectSum.of (T.sectionsPiece U) m).comp (φ.homPiece U m))
    (by
      show DirectSum.of (T.sectionsPiece U) 0 (φ.homPiece U 0 (S.sectionsGOne U)) = 1
      rw [φ.homPiece_gOne U]
      rfl)
    (fun {i j} a b => by
      show DirectSum.of (T.sectionsPiece U) (i + j) (φ.homPiece U (i + j) (S.sectionsGMul U a b)) = _
      rw [φ.homPiece_gMul U a b]
      exact (DirectSum.of_mul_of _ _).symm)

theorem Hom.sectionsHom_of (φ : S ⟶ T) (U : X.Opens) (m : ℕ) (a : S.sectionsPiece U m) :
    φ.sectionsHom U (DirectSum.of (S.sectionsPiece U) m a)
      = DirectSum.of (T.sectionsPiece U) m (φ.homPiece U m a) :=
  DirectSum.toSemiring_of _ _ _ m a

/-- The graded ring homomorphism `A_S(U) → A_T(U)` induced by `φ`. -/
def Hom.sectionsGradedHom (φ : S ⟶ T) (U : X.Opens) :
    S.sectionsGrading U →+*ᵍ T.sectionsGrading U where
  toRingHom := φ.sectionsHom U
  map_mem := by
    rintro i x ⟨a, rfl⟩
    exact ⟨φ.homPiece U i a, (φ.sectionsHom_of U i a).symm⟩

theorem Hom.sectionsGradedHom_apply (φ : S ⟶ T) (U : X.Opens) (x : S.sectionsRing U) :
    φ.sectionsGradedHom U x = φ.sectionsHom U x := rfl

theorem Hom.sectionsGradedHom_of (φ : S ⟶ T) (U : X.Opens) (m : ℕ) (a : S.sectionsPiece U m) :
    φ.sectionsGradedHom U (DirectSum.of (S.sectionsPiece U) m a)
      = DirectSum.of (T.sectionsPiece U) m (φ.homPiece U m a) :=
  φ.sectionsHom_of U m a

/-! ## Functoriality -/

theorem Hom.sectionsHom_id (U : X.Opens) :
    Hom.sectionsHom (𝟙 S) U = RingHom.id (S.sectionsRing U) :=
  DirectSum.ringHom_ext fun m a => by
    refine (Hom.sectionsHom_of (𝟙 S) U m a).trans ?_
    rfl

theorem Hom.sectionsGradedHom_id (U : X.Opens) :
    Hom.sectionsGradedHom (𝟙 S) U = GradedRingHom.id (S.sectionsGrading U) :=
  GradedRingHom.ext fun x => DFunLike.congr_fun (Hom.sectionsHom_id (S := S) U) x

theorem Hom.sectionsHom_comp {R : X.GradedQCAlgebra} (φ : S ⟶ T) (ψ : T ⟶ R) (U : X.Opens) :
    Hom.sectionsHom (φ ≫ ψ) U = (ψ.sectionsHom U).comp (φ.sectionsHom U) :=
  DirectSum.ringHom_ext fun m a => by
    refine (Hom.sectionsHom_of (φ ≫ ψ) U m a).trans ?_
    refine Eq.trans ?_ (congrArg (ψ.sectionsHom U) (φ.sectionsHom_of U m a)).symm
    refine Eq.trans ?_ (ψ.sectionsHom_of U m _).symm
    rfl

theorem Hom.sectionsGradedHom_comp {R : X.GradedQCAlgebra} (φ : S ⟶ T) (ψ : T ⟶ R) (U : X.Opens) :
    Hom.sectionsGradedHom (φ ≫ ψ) U = (ψ.sectionsGradedHom U).comp (φ.sectionsGradedHom U) :=
  GradedRingHom.ext fun x => DFunLike.congr_fun (Hom.sectionsHom_comp φ ψ U) x

/-! ## Naturality with respect to restriction -/

/-- `φ_m` commutes with restriction (naturality of the sheaf morphism `φ.app m`). -/
theorem Hom.homPiece_restrict (φ : S ⟶ T) {U V : X.Opens} (h : U ≤ V) (m : ℕ)
    (a : S.sectionsPiece V m) :
    φ.homPiece U m (S.sectionsRestrictPiece h m a)
      = T.sectionsRestrictPiece h m (φ.homPiece V m a) :=
  _root_.PresheafOfModules.naturality_apply (φ.app m).val (homOfLE h).op a

theorem Hom.sectionsHom_restrict (φ : S ⟶ T) {U V : X.Opens} (h : U ≤ V) :
    (φ.sectionsHom U).comp (S.sectionsRestrictRingHom h)
      = (T.sectionsRestrictRingHom h).comp (φ.sectionsHom V) :=
  DirectSum.ringHom_ext fun m a => by
    show φ.sectionsHom U (S.sectionsRestrictRingHom h (DirectSum.of (S.sectionsPiece V) m a))
      = T.sectionsRestrictRingHom h (φ.sectionsHom V (DirectSum.of (S.sectionsPiece V) m a))
    rw [S.sectionsRestrictRingHom_of h m a, φ.sectionsHom_of U m _, φ.sectionsHom_of V m a,
      T.sectionsRestrictRingHom_of h m _, φ.homPiece_restrict h m a]

theorem Hom.sectionsGradedHom_restrict (φ : S ⟶ T) {U V : X.Opens} (h : U ≤ V) :
    (φ.sectionsGradedHom U).comp (S.sectionsRestrict h)
      = (T.sectionsRestrict h).comp (φ.sectionsGradedHom V) :=
  GradedRingHom.ext fun x => DFunLike.congr_fun (φ.sectionsHom_restrict h) x

/-! ## Compatibility with the structure map -/

/-- `φ` is a morphism of `O_X`-algebras: on sections it commutes with the unit `Γ(X,U) → A(U)_0`. -/
theorem Hom.sectionsHom_sectionsUnit (φ : S ⟶ T) (U : X.Opens) (r : Γ(X, U)) :
    φ.sectionsHom U (S.sectionsUnit U r : S.sectionsRing U) = (T.sectionsUnit U r : T.sectionsRing U) := by
  have h := congrArg (fun (α : 𝟙_ X.Modules ⟶ T.part 0) => α.app U r) φ.map_one
  exact (φ.sectionsHom_of U 0 (S.one.app U r)).trans
    (congrArg (DirectSum.of (T.sectionsPiece U) 0) h)

theorem Hom.sectionsGradedHom_sectionsUnit (φ : S ⟶ T) (U : X.Opens) (r : Γ(X, U)) :
    φ.sectionsGradedHom U (S.sectionsUnit U r : S.sectionsRing U)
      = (T.sectionsUnit U r : T.sectionsRing U) :=
  φ.sectionsHom_sectionsUnit U r

end AlgebraicGeometry.Scheme.GradedQCAlgebra

end
