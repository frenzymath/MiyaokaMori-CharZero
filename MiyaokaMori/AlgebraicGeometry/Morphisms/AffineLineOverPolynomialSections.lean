import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Morphisms.AffineLineOver
import MiyaokaMori.AlgebraicGeometry.Modules.MatrixCocycle
import MiyaokaMori.Algebra.LambdaConjugateMatrix

/-! # Polynomial sections on the affine line over a scheme

The ring homomorphism `Γ(X, W)[λ] → Γ(A¹_X, toBase⁻¹ W)` sending a polynomial `p` to `p(λ)`, where
constants are pulled back along `toBase` and `λ` is the coordinate function `AffineSpace.coord`.
It is compatible with restriction (`polyHom_res`), and evaluating at `λ = t` (`evalAt`) substitutes the
constant `t` for `λ` (`evalAt_polyHom`). Consequently, conjugating an upper triangular matrix cocycle
`g` on the base entrywise by `Λ(λ)` (`Matrix.lambdaConjugate`) and mapping it into `A¹_X` yields a
matrix cocycle on `A¹_X` for the open cover `toBase⁻¹ U_α` (`isMatrixCocycle_lambdaConjugate_polyHom`).

This is the gluing of the deformation family `𝒱` along `G_{αα'} ∈ GL_r(Γ(U_{αα'})[λ])` in the
reduction to a split weighted bundle, Lemma 2.3 of the paper.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u v w u' v'

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.affineLineOver

variable (X : AlgebraicGeometry.Scheme.{u})

/-- The coordinate function `λ` (`AffineSpace.coord X ⟨0⟩`) as a global section of `A¹_X`. -/
def coordTop : Γ(AlgebraicGeometry.Scheme.affineLineOver X, ⊤) :=
  AlgebraicGeometry.AffineSpace.coord X ⟨0⟩

/-- The coordinate function `λ` restricted to `toBase⁻¹ W`. -/
def lambdaCoord (W : X.Opens) :
    Γ(AlgebraicGeometry.Scheme.affineLineOver X, AlgebraicGeometry.Scheme.affineLineOver.toBase X ⁻¹ᵁ W) :=
  (AlgebraicGeometry.Scheme.affineLineOver X).presheaf.map (homOfLE le_top).op (coordTop X)

/-- `Γ(X, W)[λ] → Γ(A¹_X, toBase⁻¹ W)`: constants are pulled back along `toBase`, and `λ` is sent to
the coordinate function. -/
def polyHom (W : X.Opens) :
    Polynomial Γ(X, W) →+*
      Γ(AlgebraicGeometry.Scheme.affineLineOver X, AlgebraicGeometry.Scheme.affineLineOver.toBase X ⁻¹ᵁ W) :=
  Polynomial.eval₂RingHom ((AlgebraicGeometry.Scheme.affineLineOver.toBase X).app W).hom (lambdaCoord X W)

theorem polyHom_C (W : X.Opens) (a : Γ(X, W)) :
    polyHom X W (Polynomial.C a) = (AlgebraicGeometry.Scheme.affineLineOver.toBase X).app W a := by
  simp [polyHom]

theorem polyHom_X (W : X.Opens) : polyHom X W Polynomial.X = lambdaCoord X W := by
  simp [polyHom]

/-- Restricting `λ` gives `λ` again. -/
theorem lambdaCoord_res {W W' : X.Opens}
    (h' : AlgebraicGeometry.Scheme.affineLineOver.toBase X ⁻¹ᵁ W' ≤
      AlgebraicGeometry.Scheme.affineLineOver.toBase X ⁻¹ᵁ W) :
    (AlgebraicGeometry.Scheme.affineLineOver X).presheaf.map (homOfLE h').op (lambdaCoord X W) =
      lambdaCoord X W' := by
  simp only [lambdaCoord, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp, homOfLE_comp]

/-- `polyHom` is compatible with restriction: mapping into `A¹_X` and then restricting equals
restricting the coefficients first and then mapping into `A¹_X`. -/
theorem polyHom_res {W W' : X.Opens} (h : W' ≤ W)
    (h' : AlgebraicGeometry.Scheme.affineLineOver.toBase X ⁻¹ᵁ W' ≤
      AlgebraicGeometry.Scheme.affineLineOver.toBase X ⁻¹ᵁ W) (p : Polynomial Γ(X, W)) :
    (AlgebraicGeometry.Scheme.affineLineOver X).presheaf.map (homOfLE h').op (polyHom X W p) =
      polyHom X W' (p.map (X.presheaf.map (homOfLE h).op).hom) := by
  have key : ((AlgebraicGeometry.Scheme.affineLineOver X).presheaf.map (homOfLE h').op).hom.comp
      (polyHom X W) =
      (polyHom X W').comp (Polynomial.mapRingHom (X.presheaf.map (homOfLE h).op).hom) := by
    apply Polynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_C, polyHom_C]
      rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply,
        (AlgebraicGeometry.Scheme.affineLineOver.toBase X).naturality]
      rfl
    · simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_X, polyHom_X]
      exact lambdaCoord_res X h'
  exact RingHom.congr_fun key p

/-- `polyHom_res` for matrices of polynomials. -/
theorem matrix_map_polyHom_res {r : ℕ} {W W' : X.Opens} (h : W' ≤ W)
    (h' : AlgebraicGeometry.Scheme.affineLineOver.toBase X ⁻¹ᵁ W' ≤
      AlgebraicGeometry.Scheme.affineLineOver.toBase X ⁻¹ᵁ W)
    (M : Matrix (Fin r) (Fin r) (Polynomial Γ(X, W))) :
    (M.map (polyHom X W)).map
        ((AlgebraicGeometry.Scheme.affineLineOver X).presheaf.map (homOfLE h').op).hom =
      (M.map (Polynomial.mapRingHom (X.presheaf.map (homOfLE h).op).hom)).map (polyHom X W') := by
  ext i j
  simp only [Matrix.map_apply, Polynomial.coe_mapRingHom]
  exact polyHom_res X h h' (M i j)

section Eval

variable {k : Type u} [Field k] [X.Over (AlgebraicGeometry.Spec (CommRingCat.of k))]

/-- The constant `t ∈ k` as a section over `W` (pulled back along the structure morphism, then restricted). -/
def constAt (W : X.Opens) (t : k) : Γ(X, W) :=
  X.presheaf.map (homOfLE le_top).op
    ((X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)).appTop
      ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv t))

theorem constAt_one (W : X.Opens) : constAt X W (1 : k) = 1 := by
  simp [constAt]

theorem constAt_zero (W : X.Opens) : constAt X W (0 : k) = 0 := by
  simp [constAt]

/-- An endomorphism equal to the identity has `appLE W W` equal to the identity (the morphism is kept
general to avoid rewriting under dependent proof terms). -/
theorem appLE_self_of_eq_id {Y : AlgebraicGeometry.Scheme.{u}} (φ : Y ⟶ Y) (hφ : φ = 𝟙 Y)
    (W : Y.Opens) (e : W ≤ φ ⁻¹ᵁ W) (a : Γ(Y, W)) : φ.appLE W W e a = a := by
  subst hφ
  -- `(𝟙 Y) ⁻¹ᵁ W` and `W` are definitionally equal (`Opens.map_id_obj` is `rfl`); `Opens` is a thin category
  have h1 : (homOfLE e : W ⟶ (CategoryTheory.CategoryStruct.id Y) ⁻¹ᵁ W) =
      CategoryTheory.CategoryStruct.id W := Subsingleton.elim _ _
  show ((CategoryTheory.CategoryStruct.id Y).app W ≫ Y.presheaf.map (homOfLE e).op) a = a
  rw [h1]
  show (Y.presheaf.map (CategoryTheory.CategoryStruct.id (op W))) a = a
  rw [Y.presheaf.map_id]
  rfl

/-- Evaluating at `λ = t` sends a constant pulled back along `toBase` to itself. -/
theorem evalAt_toBase_app (t : k) (W : X.Opens) (a : Γ(X, W)) :
    AlgebraicGeometry.Scheme.affineLineOver.evalAt X t W
      ((AlgebraicGeometry.Scheme.affineLineOver.toBase X).app W a) = a := by
  exact appLE_self_of_eq_id (AlgebraicGeometry.Scheme.affineLineOver.sectionAt X t ≫
    AlgebraicGeometry.Scheme.affineLineOver.toBase X)
    (AlgebraicGeometry.AffineSpace.homOfVector_over _ _) W
    (by
      have e : AlgebraicGeometry.Scheme.affineLineOver.sectionAt X t ≫
          AlgebraicGeometry.Scheme.affineLineOver.toBase X = CategoryTheory.CategoryStruct.id X :=
        AlgebraicGeometry.AffineSpace.homOfVector_over _ _
      rw [e]; exact le_rfl) a

/-- Evaluating at `λ = t` sends the coordinate function `λ` to the constant `t`. -/
theorem evalAt_lambdaCoord (t : k) (W : X.Opens) :
    AlgebraicGeometry.Scheme.affineLineOver.evalAt X t W (lambdaCoord X W) = constAt X W t := by
  have hc : (AlgebraicGeometry.Scheme.affineLineOver.sectionAt X t).appTop (coordTop X) =
      (X ↘ AlgebraicGeometry.Spec (CommRingCat.of k)).appTop
        ((AlgebraicGeometry.Scheme.ΓSpecIso (CommRingCat.of k)).inv t) :=
    AlgebraicGeometry.AffineSpace.homOfVector_appTop_coord _ _ _
  rw [AlgebraicGeometry.Scheme.affineLineOver.evalAt, lambdaCoord, ← ConcreteCategory.comp_apply,
    AlgebraicGeometry.Scheme.Hom.map_appLE, AlgebraicGeometry.Scheme.Hom.appLE,
    ConcreteCategory.comp_apply, constAt]
  exact congrArg _ hc

/-- Evaluating at `λ = t` substitutes `t` for `λ` in the polynomial. -/
theorem evalAt_polyHom (t : k) (W : X.Opens) (p : Polynomial Γ(X, W)) :
    AlgebraicGeometry.Scheme.affineLineOver.evalAt X t W (polyHom X W p) =
      p.eval (constAt X W t) := by
  have key : (AlgebraicGeometry.Scheme.affineLineOver.evalAt X t W).hom.comp (polyHom X W) =
      Polynomial.evalRingHom (constAt X W t) := by
    apply Polynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, polyHom_C, Polynomial.coe_evalRingHom, Polynomial.eval_C]
      exact evalAt_toBase_app X t W a
    · simp only [RingHom.comp_apply, polyHom_X, Polynomial.coe_evalRingHom, Polynomial.eval_X]
      exact evalAt_lambdaCoord X t W
  exact RingHom.congr_fun key p

/-- Evaluation at `λ = t` for matrices of polynomials. -/
theorem matrix_map_polyHom_evalAt {r : ℕ} (t : k) (W : X.Opens)
    (M : Matrix (Fin r) (Fin r) (Polynomial Γ(X, W))) :
    (M.map (polyHom X W)).map (AlgebraicGeometry.Scheme.affineLineOver.evalAt X t W) =
      M.map (Polynomial.evalRingHom (constAt X W t)) := by
  ext i j
  simp only [Matrix.map_apply, Polynomial.coe_evalRingHom]
  exact evalAt_polyHom X t W (M i j)

end Eval

/-- Conjugating an upper triangular matrix cocycle `g` on the base scheme entrywise by `Λ(λ)` and
mapping it into `A¹_X` via `polyHom` gives a matrix cocycle on `A¹_X` for the open cover `toBase⁻¹ U_α`.
Determinants: `det (lambdaConjugate g) = C (det g)` is a unit. Cocycle condition: restriction commutes
with `polyHom` (`matrix_map_polyHom_res`) and with conjugation (`Matrix.lambdaConjugate_map`),
conjugation is multiplicative on upper triangular matrices (`Matrix.lambdaConjugate_mul`), and finally
the cocycle condition for `g` is used. -/
theorem isMatrixCocycle_lambdaConjugate_polyHom {ι : Type u} {r : ℕ} (U : ι → X.Opens)
    (g : ∀ α α' : ι, Matrix (Fin r) (Fin r) Γ(X, U α ⊓ U α'))
    (hg : IsMatrixCocycle U g) (htri : ∀ α α', (g α α').BlockTriangular id) :
    IsMatrixCocycle (fun α => AlgebraicGeometry.Scheme.affineLineOver.toBase X ⁻¹ᵁ U α)
      (fun α α' => (g α α').lambdaConjugate.map (polyHom X (U α ⊓ U α'))) := by
  obtain ⟨hdet, hcoc⟩ := hg
  refine ⟨fun α α' => ?_, fun α α' α'' => ?_⟩
  · show IsUnit ((g α α').lambdaConjugate.map (polyHom X (U α ⊓ U α'))).det
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (Matrix.lambdaConjugate_det_isUnit _ (htri α α') (hdet α α')).map _
  · have h1 : U α ⊓ U α' ⊓ U α'' ≤ U α ⊓ U α' := inf_le_left
    have h2 : U α ⊓ U α' ⊓ U α'' ≤ U α' ⊓ U α'' :=
      le_inf (le_trans inf_le_left inf_le_right) inf_le_right
    have h3 : U α ⊓ U α' ⊓ U α'' ≤ U α ⊓ U α'' :=
      le_inf (le_trans inf_le_left inf_le_left) inf_le_right
    have e1 := matrix_map_polyHom_res X h1
      (inf_le_left : AlgebraicGeometry.Scheme.affineLineOver.toBase X ⁻¹ᵁ U α ⊓
        AlgebraicGeometry.Scheme.affineLineOver.toBase X ⁻¹ᵁ U α' ⊓
        AlgebraicGeometry.Scheme.affineLineOver.toBase X ⁻¹ᵁ U α'' ≤
        AlgebraicGeometry.Scheme.affineLineOver.toBase X ⁻¹ᵁ U α ⊓
        AlgebraicGeometry.Scheme.affineLineOver.toBase X ⁻¹ᵁ U α')
      (g α α').lambdaConjugate
    have e2 := matrix_map_polyHom_res X h2
      (le_inf (le_trans inf_le_left inf_le_right) inf_le_right :
        AlgebraicGeometry.Scheme.affineLineOver.toBase X ⁻¹ᵁ U α ⊓
        AlgebraicGeometry.Scheme.affineLineOver.toBase X ⁻¹ᵁ U α' ⊓
        AlgebraicGeometry.Scheme.affineLineOver.toBase X ⁻¹ᵁ U α'' ≤
        AlgebraicGeometry.Scheme.affineLineOver.toBase X ⁻¹ᵁ U α' ⊓
        AlgebraicGeometry.Scheme.affineLineOver.toBase X ⁻¹ᵁ U α'')
      (g α' α'').lambdaConjugate
    have e3 := matrix_map_polyHom_res X h3
      (le_inf (le_trans inf_le_left inf_le_left) inf_le_right :
        AlgebraicGeometry.Scheme.affineLineOver.toBase X ⁻¹ᵁ U α ⊓
        AlgebraicGeometry.Scheme.affineLineOver.toBase X ⁻¹ᵁ U α' ⊓
        AlgebraicGeometry.Scheme.affineLineOver.toBase X ⁻¹ᵁ U α'' ≤
        AlgebraicGeometry.Scheme.affineLineOver.toBase X ⁻¹ᵁ U α ⊓
        AlgebraicGeometry.Scheme.affineLineOver.toBase X ⁻¹ᵁ U α'')
      (g α α'').lambdaConjugate
    -- the cocycle identity at the level of polynomials (all coefficients restricted to the triple
    -- intersection T = U α ⊓ U α' ⊓ U α'')
    have hmul :
        ((g α α').lambdaConjugate.map
            (Polynomial.mapRingHom (X.presheaf.map (homOfLE h1).op).hom)).map
              (polyHom X (U α ⊓ U α' ⊓ U α'')) *
          ((g α' α'').lambdaConjugate.map
            (Polynomial.mapRingHom (X.presheaf.map (homOfLE h2).op).hom)).map
              (polyHom X (U α ⊓ U α' ⊓ U α'')) =
        ((g α α'').lambdaConjugate.map
            (Polynomial.mapRingHom (X.presheaf.map (homOfLE h3).op).hom)).map
              (polyHom X (U α ⊓ U α' ⊓ U α'')) := by
      rw [← Matrix.map_mul, Matrix.lambdaConjugate_map, Matrix.lambdaConjugate_map,
        Matrix.lambdaConjugate_map,
        Matrix.lambdaConjugate_mul _ _ ((htri α α').map _) ((htri α' α'').map _), hcoc α α' α'']
    exact (congrArg₂ (· * ·) e1 e2).trans (hmul.trans e3.symm)

end AlgebraicGeometry.Scheme.affineLineOver

end
