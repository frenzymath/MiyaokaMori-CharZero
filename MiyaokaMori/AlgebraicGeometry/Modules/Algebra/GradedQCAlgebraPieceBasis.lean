import MiyaokaMori.Prelude
import MiyaokaMori.AlgebraicGeometry.Modules.Algebra.OfGradedQCAlgebra
import MiyaokaMori.AlgebraicGeometry.Proj.WeightedProj.WeightedPolynomialQCAlgebra
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous

/-! # Bases of the graded pieces of a graded algebra from a polynomial chart

Let `T` be a graded quasi-coherent algebra on a scheme `X`, `V` an open, and
`e : T.sectionsRing V ≃+* MvPolynomial σ Γ(X, V)` a ring isomorphism matching the `m`-th graded piece
with the weighted homogeneous component of weight `m` and the structure map `sectionsUnitHom` with the
constants `C` (the data of a `WeightedPolynomialAtlas` on one chart). Then for every `m`, the `m`-th
components of the sections `polyGen m d := e⁻¹(X^d)` (`d` ranging over the monomial exponents
`weightedMonomials w m` of weight `m`) form a `Γ(X, V)`-basis `pieceBasis m` of `Γ(V, T_m)`; the graded
multiplication of these generators adds exponents (`sectionsGMul_polyGen`), and `polyGen 0 0` is the
graded unit `sectionsGOne` (`polyGen_zero`).

Proof:
1. `Γ(V, T_m) ≃+ (T.sectionsGrading V m)` (`sectionsPieceEquivGrading`: take the `m`-th component /
   `DirectSum.of`); via `e` and `he` this is `≃+ weightedHomogeneousSubmodule Γ(X,V) w m`, and by Mathlib's
   `weightedHomogeneousSubmodule_eq_finsupp_supported` and `AddMonoidAlgebra.supportedEquivFinsupp` it is
   `≃ₗ (weightedMonomials w m →₀ Γ(X,V))`. `Γ(X,V)`-linearity: `r • a` in the section ring is
   `sectionsUnitHom r * ofPiece a` (`sectionsUnitHom_mul_ofPiece`), which under `e` is `C r * _ = r • _`
 (`hu`, `MvPolynomial.C_mul'`).
2. The basis `pieceBasis m := Basis.ofRepr` of the linear isomorphism of step 1; `pieceBasis m d = polyGen m d`
   because the linear isomorphism sends `polyGen m d` to `Finsupp.single d 1`
 (`Finsupp.supportedEquivFinsupp_symm_single`).
3. `sectionsGMul_polyGen`: `ofPiece` is injective (`ofPiece_injective`);
   `ofPiece (sectionsGMul a b) = ofPiece a * ofPiece b` (`DirectSum.of_mul_of`); `e⁻¹` is multiplicative and
   `MvPolynomial.monomial_mul` gives `e⁻¹(X^{d+d'})`.
4. `polyGen_zero`: `e⁻¹(X^0) = e⁻¹(C 1) = sectionsUnitHom 1 = ofPiece 0 (T.one.app V 1)`.

Reference: the local model on fibres is a weighted polynomial algebra (§2 of the paper); Mathlib
`MvPolynomial.weightedHomogeneousSubmodule`.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.GradedQCAlgebra

variable {X : Scheme.{u}} (T : X.GradedQCAlgebra) (V : X.Opens) {σ : Type u} (w : σ → ℕ)
  (e : T.sectionsRing V ≃+* MvPolynomial σ Γ(X, V))

/-- The `m`-th component of the preimage under `e⁻¹` of the monomial `X^d` of weight `m`. -/
def polyGen (m : ℕ) (d : weightedMonomials w m) : T.sectionsPiece V m :=
  T.component V m (e.symm (MvPolynomial.monomial d.1 1))

theorem symm_monomial_mem
    (he : ∀ (m : ℕ) (a : T.sectionsRing V),
      a ∈ T.sectionsGrading V m ↔ (e a).IsWeightedHomogeneous w m)
    (m : ℕ) (d : weightedMonomials w m) :
    e.symm (MvPolynomial.monomial d.1 1) ∈ T.sectionsGrading V m :=
  (he m _).mpr (by
    rw [RingEquiv.apply_symm_apply]
    exact MvPolynomial.isWeightedHomogeneous_monomial w d.1 1 d.2)

theorem ofPiece_polyGen
    (he : ∀ (m : ℕ) (a : T.sectionsRing V),
      a ∈ T.sectionsGrading V m ↔ (e a).IsWeightedHomogeneous w m)
    (m : ℕ) (d : weightedMonomials w m) :
    T.ofPiece V m (polyGen T V w e m d) = e.symm (MvPolynomial.monomial d.1 1) :=
  (T.mem_sectionsGrading_iff V m _).mp (symm_monomial_mem T V w e he m d)

/-- `ofPiece` turns the graded multiplication into the multiplication of the section ring. -/
theorem ofPiece_sectionsGMul {m n : ℕ} (a : T.sectionsPiece V m) (b : T.sectionsPiece V n) :
    T.ofPiece V (m + n) (T.sectionsGMul V a b) = T.ofPiece V m a * T.ofPiece V n b :=
  (DirectSum.of_mul_of (A := T.sectionsPiece V) a b).symm

/-- **Graded multiplication of the generators adds the monomial exponents.** -/
theorem sectionsGMul_polyGen
    (he : ∀ (m : ℕ) (a : T.sectionsRing V),
      a ∈ T.sectionsGrading V m ↔ (e a).IsWeightedHomogeneous w m)
    {m n : ℕ} (d : weightedMonomials w m) (d' : weightedMonomials w n) :
    T.sectionsGMul V (polyGen T V w e m d) (polyGen T V w e n d') =
      polyGen T V w e (m + n) ⟨d.1 + d'.1, by rw [map_add, d.2, d'.2]⟩ := by
  apply T.ofPiece_injective V (m + n)
  rw [ofPiece_sectionsGMul, ofPiece_polyGen T V w e he, ofPiece_polyGen T V w e he,
    ofPiece_polyGen T V w e he, ← map_mul, MvPolynomial.monomial_mul, _root_.one_mul]

/-- **The degree-zero generator is the graded unit.** -/
theorem polyGen_zero
    (he : ∀ (m : ℕ) (a : T.sectionsRing V),
      a ∈ T.sectionsGrading V m ↔ (e a).IsWeightedHomogeneous w m)
    (hu : ∀ r : Γ(X, V), e (T.sectionsUnitHom V r) = MvPolynomial.C r) :
    polyGen T V w e 0 ⟨0, by simp⟩ = T.sectionsGOne V := by
  apply T.ofPiece_injective V 0
  rw [ofPiece_polyGen T V w e he]
  have h1 : e.symm (MvPolynomial.monomial (0 : σ →₀ ℕ) (1 : Γ(X, V))) = T.sectionsUnitHom V 1 := by
    rw [← MvPolynomial.C_apply, ← hu 1, RingEquiv.symm_apply_apply]
  exact h1

/-! ## The basis -/

/-- The `Γ(X,V)`-module structure on `Γ(V, T_m)` (Mathlib's instance is on `Γ(T.part m, V)`; the syntax
differs, so it is registered again). -/
local instance pieceModule (m : ℕ) : Module Γ(X, V) (T.sectionsPiece V m) :=
  inferInstanceAs (Module Γ(X, V) Γ(T.part m, V))

/-- The additive isomorphism, via `e`, between the `m`-th piece and the homogeneous component of weight `m`. -/
def gradingEquivHomogeneous
    (he : ∀ (m : ℕ) (a : T.sectionsRing V),
      a ∈ T.sectionsGrading V m ↔ (e a).IsWeightedHomogeneous w m) (m : ℕ) :
    T.sectionsGrading V m ≃+ MvPolynomial.weightedHomogeneousSubmodule Γ(X, V) w m where
  toFun a := ⟨e a.1, (he m a.1).mp a.2⟩
  invFun p := ⟨e.symm p.1, (he m _).mpr (by rw [RingEquiv.apply_symm_apply]; exact p.2)⟩
  left_inv a := Subtype.ext (e.symm_apply_apply a.1)
  right_inv p := Subtype.ext (e.apply_symm_apply p.1)
  map_add' a b := Subtype.ext (map_add e a.1 b.1)

/-- The homogeneous component of weight `m` `≃ₗ` finitely supported functions on the monomials of weight
`m` (Mathlib). -/
def homogeneousEquivFinsupp (m : ℕ) :
    MvPolynomial.weightedHomogeneousSubmodule Γ(X, V) w m ≃ₗ[Γ(X, V)]
      (weightedMonomials w m →₀ Γ(X, V)) :=
  (LinearEquiv.ofEq _ _
    (MvPolynomial.weightedHomogeneousSubmodule_eq_finsupp_supported Γ(X, V) w m)).trans
    (AddMonoidAlgebra.supportedEquivFinsupp {d | Finsupp.weight w d = m})

theorem homogeneousEquivFinsupp_symm_single (m : ℕ) (d : weightedMonomials w m) :
    ((homogeneousEquivFinsupp V w m).symm (Finsupp.single d 1) :
      MvPolynomial σ Γ(X, V)) = MvPolynomial.monomial d.1 1 := by
  simp [homogeneousEquivFinsupp, AddMonoidAlgebra.supportedEquivFinsupp]
  rw [Finsupp.supportedEquivFinsupp_symm_single]
  rfl

/-- `Γ(V, T_m) ≃ₗ[Γ(X,V)] (weightedMonomials w m →₀ Γ(X,V))`. -/
def pieceEquivFinsupp
    (he : ∀ (m : ℕ) (a : T.sectionsRing V),
      a ∈ T.sectionsGrading V m ↔ (e a).IsWeightedHomogeneous w m)
    (hu : ∀ r : Γ(X, V), e (T.sectionsUnitHom V r) = MvPolynomial.C r) (m : ℕ) :
    T.sectionsPiece V m ≃ₗ[Γ(X, V)] (weightedMonomials w m →₀ Γ(X, V)) :=
  AddEquiv.toLinearEquiv
    (((T.sectionsPieceEquivGrading V m).trans (gradingEquivHomogeneous T V w e he m)).trans
      (homogeneousEquivFinsupp V w m).toAddEquiv)
    (by
      intro c x
      show (homogeneousEquivFinsupp V w m)
          ((gradingEquivHomogeneous T V w e he m) ((T.sectionsPieceEquivGrading V m) (c • x))) =
        c • (homogeneousEquivFinsupp V w m)
          ((gradingEquivHomogeneous T V w e he m) ((T.sectionsPieceEquivGrading V m) x))
      rw [← map_smul]
      congr 1
      apply Subtype.ext
      show e ((T.sectionsPieceEquivGrading V m (c • x) : T.sectionsGrading V m) : T.sectionsRing V) =
        c • e ((T.sectionsPieceEquivGrading V m x : T.sectionsGrading V m) : T.sectionsRing V)
      have h := T.sectionsPieceEquivGrading_smul V m c x
      calc e ((T.sectionsPieceEquivGrading V m (c • x) : T.sectionsGrading V m) : T.sectionsRing V)
          = e (T.sectionsUnitHom V c *
              ((T.sectionsPieceEquivGrading V m x : T.sectionsGrading V m) : T.sectionsRing V)) :=
            congrArg e h.symm
        _ = e (T.sectionsUnitHom V c) *
              e ((T.sectionsPieceEquivGrading V m x : T.sectionsGrading V m) : T.sectionsRing V) :=
            map_mul e _ _
        _ = c • e ((T.sectionsPieceEquivGrading V m x : T.sectionsGrading V m) : T.sectionsRing V) := by
            rw [hu, MvPolynomial.C_mul'])

/-- The `Γ(X,V)`-basis of `Γ(V, T_m)`: the preimages of the monomials of weight `m`. -/
def pieceBasis
    (he : ∀ (m : ℕ) (a : T.sectionsRing V),
      a ∈ T.sectionsGrading V m ↔ (e a).IsWeightedHomogeneous w m)
    (hu : ∀ r : Γ(X, V), e (T.sectionsUnitHom V r) = MvPolynomial.C r) (m : ℕ) :
    Module.Basis (weightedMonomials w m) Γ(X, V) (T.sectionsPiece V m) :=
  Module.Basis.ofRepr (pieceEquivFinsupp T V w e he hu m)

theorem pieceEquivFinsupp_polyGen
    (he : ∀ (m : ℕ) (a : T.sectionsRing V),
      a ∈ T.sectionsGrading V m ↔ (e a).IsWeightedHomogeneous w m)
    (hu : ∀ r : Γ(X, V), e (T.sectionsUnitHom V r) = MvPolynomial.C r)
    (m : ℕ) (d : weightedMonomials w m) :
    pieceEquivFinsupp T V w e he hu m (polyGen T V w e m d) = Finsupp.single d 1 := by
  show (homogeneousEquivFinsupp V w m)
      ((gradingEquivHomogeneous T V w e he m)
        ((T.sectionsPieceEquivGrading V m) (polyGen T V w e m d))) = _
  rw [← LinearEquiv.eq_symm_apply]
  apply Subtype.ext
  rw [homogeneousEquivFinsupp_symm_single]
  show e (T.ofPiece V m (polyGen T V w e m d)) = _
  rw [ofPiece_polyGen T V w e he, RingEquiv.apply_symm_apply]

theorem pieceBasis_apply
    (he : ∀ (m : ℕ) (a : T.sectionsRing V),
      a ∈ T.sectionsGrading V m ↔ (e a).IsWeightedHomogeneous w m)
    (hu : ∀ r : Γ(X, V), e (T.sectionsUnitHom V r) = MvPolynomial.C r)
    (m : ℕ) (d : weightedMonomials w m) :
    pieceBasis T V w e he hu m d = polyGen T V w e m d := by
  unfold pieceBasis
  rw [Module.Basis.coe_ofRepr]
  exact (LinearEquiv.symm_apply_eq _).mpr (pieceEquivFinsupp_polyGen T V w e he hu m d).symm

end AlgebraicGeometry.Scheme.GradedQCAlgebra

end
